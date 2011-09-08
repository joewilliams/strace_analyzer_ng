#!/usr/bin/perl -w
#
# Copyright 2008-2009 Jeffrey B. Layton
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.
#

#
# Assumptions in code:
# (1) Units are not reused for different file names (i.e. one-to-one
#     mapping between unit and filename
#
#
# Notes:
#  (1) Need to add the ability for the simulator to create data files
#      for when a unit is opened and immediately read from (not written)
#
# strace -e trace=open,close,_llseek,read,write -ttt -o strace.out
#
# strace -T -e trace=open,close,_llseet,read,write -ttt
#
# Add ability to track file offset on a per file basis (9/2/2009)
#   - Do lseek offset computations (watch "offset" in lseek - parse constants)
#   - Need to add some defensive programming as well
#

use strict;
use Getopt::Long;
use POSIX qw(ceil floor);


# Other Variables:
my ($LineNum, $time, $cmd, $cmdtmp);
my ($cmd_unit, $sec);
my ($elapsed_time);   # elapsed time of function
my $Numlines;
my ($lineOutput);
my (%CmdCounter);
my $lineCount;

# ============
# IO Variables
# ============
# Time Variables
my ($BeginTime, $EndTime);

# "Open" sys call variables
# -------------------------
# Array of hash for Open syscalls
my (@Open);
#  $Open[syscall number]->{line_number} = $LineNum;       # Line number in strace of syscall call
#  $Open[syscall number]->{sec} = $epoch_sec;             # Seconds since epoch for syscall call
#  $Open[syscall number]->{file} = $filename;             # filename in open syscall call
#  $Open[syscall number]->{unit} = $unit;                 # unit (file descriptor) associated with file
#  $Open[syscall number]->{elapsed_time} = $elapsed_time  # elapsed time of syscall call

my (%OpenMax);           # Hash of slowest open syscall
#  $OpenMax{"line"} = line number of strace where slowest open occurred
#  $OpenMax{"MaxTime"} = elapsed time for slowest open syscall

my (@Open_Filename);     # Array of currently opened units
my ($oflags, $mode);

# "Write" syscalls variables and arrays:
# --------------------------------------
my (@Write);
# $Write[syscall number]->{line_number} = Line Number
# $Write[syscall number]->{sec} = $epoch_sec;          # Seconds since epoch for syscall
# $Write[syscall number]->{elapsed_time} = elepased time for syscall number
# $Write[syscall number]->{byte_sec} = Write throughput for syscall number
# $Write[syscall number]->{bytes} = Number of bytes in syscall
# $Write[syscall number]->{unit} = file descriptor for write syscall number

my ($WriteBytesTotal);   # Total number of bytes written (all fd's and files)
my (%WriteMax);          # Hash of slowest write syscall
#   $WriteMax{"line"} = line number of strace where slowest write occurred
#   $WriteMax{"MaxTime"} = elapsed time for slowest write syscall

my ($WriteLarge);        # Largest Write syscall
my ($WriteSmall);        # Smallest Write syscall

# "Write" Statistics
# ------------------
my (@Local_Write_Array);
my ($My_Median, $Test_Average, $Std_Dev);

# "Read" syscalls variables and arrays:
# -------------------------------------
my (@Read);
# $Read[syscall number]->{line_number} = Line Number
# $Read[syscall number]->{sec} = $epoch_sec;          # Seconds since epoch for syscall
# $Read[syscall number]->{elapsed_time} = elpased time for syscall number
# $Read[syscall number]->{byte_sec} = Read throughput for syscall number
# $Read[syscall number]->{bytes} = Number of bytes in syscall
# $Read[syscall number]->{unit} = file descriptor for read syscall number

my ($ReadBytesTotal);     # Total number of bytes read by all files

my (%ReadMax);            # Hash of slowest read syscall
#   $ReadMax{"line"} = line number of strace where slowest read occurred
#   $ReadMax{"MaxTime"} = elapsed time for slowest read syscall

my ($ReadLarge);          # Largest Read syscall
my ($ReadSmall);          # Smallest Read syscall

# "Read" Statistics
# -----------------
my (@Local_Read_Array);

# "Close" syscalls variables and arrays
# -------------------------------------
my (@Close);
# $Close[syscall number]->{line_number} = line number in strace file
# $Close[syscall number]->{sec} = time of syscall (seconds since epoch)
# $Close[syscall number]->{unit} = file descriptor for close syscall
# $Close[syscall number]->{elapsed_time} = elapsed time (secs) for syscall
         
my (%CloseMax);           # Hash of slowest close syscall
#   $CloseMax{"line"} = line number of strace where slowest close occurred
#   $CloseMax{"MaxTime"} = elapsed time for slowest close syscall

my (@Close_Unit_Ops);
# Open variables and arrays


# "lseek" syscall variables and arrays
# ------------------------------------
my (%LseekMax);           # Hash of slowest lseek syscall
#   $LseekMax{"line"} = line number in strace where slowest syscall occurred
#   $LseekMax{"MaxTime"} = elapsed time for slowest lseek syscall

my (@lseek_activity);
my ($offset, $whence, $offset_success, $offset_junk, $offset_results);
my ($current_offset, $parts_length, $ip);
my (@lseek_activity_counter, @lseek_unit);

# Hash and array for file sizes
my (@FileSizes, %FileSizeCounter);

# IOPS variables and arrays (hashes)
# ----------------------------------
# Variables for computing IOPS
my (@IOPS_Total, @IOPS_Read, @IOPS_Write);
my (@IOPS_Read_Unit);
#   $IOPS_Read_Unit[unit][time interval] = number of read IOPS
my (@IOPS_Write_Unit);
#   $IOPS_Write_Unit[unit][time interval] = number of write IOPS
my ($IOPS_Total_Avg, $IOPS_Read_Avg, $IOPS_Write_Avg);
my ($IOPS_Write_Final, $IOPS_Read_Final, $IOPS_Total_Final);

# Offsets Tracking
# ----------------
my (@Offset);            # Offset hash array (2D array)
# $Offset[unit][timestep]->{time} = time of syscall relative to beginning of run
# $Offset[unit][timestep]->{offset} = offset in bytes of syscall

my (@Offset_point);
# $Offset[$unit] = current file pointer location of $unit (in bytes)

# Hash for storing data on a per file basis:
my (@File_Stats);
#   $File_Stats[$unit]->{file} = $filename; 
#   $File_Stats[$unit]->{read_bytes} += $byte;
#   $File_Stats[$unit]->{write_bytes} += $byte; 
#   $File_Stats[$iloop]->{read_rate_count}
#   $File_Stats[$iloop]->{read_rate_sum}
#   $File_Stats[$iloop]->{write_rate_sum}
#   $File_Stats[$iloop]->{write_rate_count

my (@File_Stats_2);
#   @File_Stats_2[$unit]->{read_bytes} = Number of bytes read (total) per unit
#   @File_Stata_2[$unit]->{write_bytes} = number of bytes written (total) per unit
#   @File_Stats_2[$unit]->{file} = filename 
#   @File_Stats_2[$unit]->{read_rate_sum} = sum of read throughput per unit
#   @File_Stats_2[$unit]->{read_rate_count} = total number of read functions per unit
#   @File_Stats_2[$unit]->{write_rate_sum} = sum or write throughtput per unit
#   @File_Stats_2[$unit]->{write_rate_count} = tota number of write functions per unit


# Temporary variables and arrays:
# -------------------------------
my (@parts);
my ($temp);
my ($junk, $junk1, $junk2, $junk3, $junk4, $junk5, $junk6, $junk7, $sum, $unit, $byte);
my ($ielement, $size, $size_2, $size_3);
my ($zero, $equal);
my ($before, $filename, $after, $index);
my ($iloop, $jloop, $kloop, $icount, $key);
my ($IOTimeSum, $IOTime_count);
my ($IOPS_max_temp, $index_max, $sec_begin);
my ($sec_local);
my ($jwalker, $kwalker);

# Command line arguments
my ($base_directory);
my ($filesizeinput, $debug, $helpflag, $shortflag,  $datflag);
my ($open_sim_flag);


# Define IO functions we are interested in
my $OPEN     = "open";      # done
my $READ     = "read";      # done
my $WRITE    = "write";     # done
my $CLOSE    = "close";     # done
my $LSEEK    = "lseek";     # done
my $LLSEEK   = "llseek";    # done
my $LSEEK64  = "lseek64";   # done
my $STAT     = "stat";      # counter only done
my $STAT64   = "stat64";    # counter only done
my $FSTAT    = "fstat";     # counter only done
my $CHMOD    = "chmod";     # counter only done
my $ACCESS   = "access";    # counter only done
my $RENAME   = "rename";    # counter only done
my $MKDIR    = "mkdir";     # counter only done
my $GETDENTS = "getdents";  # counter only done
my $FCNTL    = "fcntl";     # counter only done
my $UNLINK   = "unlink";    # counter only done
my $FSEEK    = "fseek";     # counter only done
my $REWIND   = "rewind";    # counter only done
my $FTELL    = "ftell";     # counter only done
my $FGETPOS  = "fgetpos";   # counter only done
my $FSETPOS  = "fsetpos";   # counter only done
my $FCLOSE   = "fclose";    # counter only done
my $FSYNC    = "fsync";     # counter only done
my $CREAT    = "creat";     # counter only done
my $READDIR  = "readdir";   # counter only done
my $OPENDIR  = "opendir";   # counter only done
my $REWINDDIR = "rewinddir";   # counter only done
my $SCANDIR  = "scandir";   # counter only done
my $SEEKDIR  = "seekdir";   # counter only done
my $TELLDIR  = "telldir";   # counter only done
my $FLOCK    = "flock";     # counter only done
my $LOCKF    = "lockf";     # counter only done


#
# Intialization
#
$debug = 0;
$filesizeinput = 0;
$helpflag = 0;
$shortflag = 0;
$datflag = 0;
$Numlines = 0;
$LineNum = 0;
$zero = 0.0;
$CloseMax{"line"} = 0;
$CloseMax{"MaxTime"} = -1.0;
$ReadMax{"line"} = 0;
$ReadMax{"MaxTime"} = -1.0;
$WriteMax{"line"} = 0;
$WriteMax{"MaxTime"} = -1.0;
$OpenMax{"line"} = 0;
$OpenMax{"MaxTime"} = -1.0;
$LseekMax{"line"} = -1.0;
$LseekMax{"MaxTime"} = -1.0;
$BeginTime = -1.0;
$EndTime = -1.0;
$IOTimeSum = 0.0;
$IOTime_count = 0;
$WriteBytesTotal = 0.0;
$base_directory = '.';
$open_sim_flag = 0;
$equal = "=";
$WriteLarge = 0;
$WriteSmall = 100000000000;
$ReadLarge = 0;
$ReadSmall = 100000000000;

$jwalker = 0;
$kwalker = 0;


GetOptions('f|file=s' => \$filesizeinput,
            "debug" => \$debug,
            "h|help" => \$helpflag,
            "dat" => \$datflag,
            "short" => \$shortflag );
if ($helpflag > 0)
{
   helpoutput();
   exit;
}


open(STRACE_LOG, '>strace_analyzer.log');
printf(STRACE_LOG "Diagnostic Output: \n");
printf(STRACE_LOG "================== \n");
printf(STRACE_LOG " \n");


#
# Loop over lines in file
#
while(<>) {
   chomp;
   # Split current line using spaces
   ($sec, $cmdtmp, @parts) = split;
   # Increment Line Number
   $LineNum++;
   
   # Echo input line to output
   $lineOutput = $sec . " "  . $cmdtmp . " ";
   foreach my $specific_part (@parts) {
      if (defined $specific_part) {
         $lineOutput = $lineOutput . $specific_part . " ";
      }
   }
   if ($debug > 0) {
      printf(STRACE_LOG "(%d)\t%s \n",$LineNum, $lineOutput);
   }
   
   
   # Split the temporary command ($cmdtmp) to get the correct "syscall"
   ($cmd, $cmd_unit) = split(/\(/,$cmdtmp);
   $cmd =~ s/^_{1,}(\S+)/$1/;
   if ($debug > 0) {
      printf(STRACE_LOG "   cmd: %s   cmd_unit: %s   LineNum: %s \n",$cmd, $cmd_unit, $LineNum);
      printf(STRACE_LOG "   sec = %s \n",$sec);
   }
   
   # Extract elapsed time from end of line (stored in parts array)
   $junk1 = @parts;             # length of parts array
   $junk4 = $parts[$junk1-1];   # The last element of @parts is elapsed time
   $junk2 = length($junk4);     # Length of elapsed time string
   $elapsed_time = substr($junk4, 1, $junk2-2);   # Extract value dropping leading and trailing "<>"
                                                  # This is the elapsed time
   if ($debug > 0) {
      printf(STRACE_LOG "   real elapsed time: %s \n", $elapsed_time);
   }
   
   # Store beginning time
   if ($LineNum == 1) {
      $BeginTime = $sec;
      $sec_begin = $sec;
   }
   $Numlines++;
   
   
   # =========================
   # If ladder to process data
   # =========================
   if ($cmd eq $OPEN){
      if ($debug > 0) {
         printf(STRACE_LOG "   Found an OPEN function call \n");
         #printf(STRACE_LOG "      setting iopen to 1 \n");
      }
      # Increment total IO time and syscall counters
      $IOTimeSum = $IOTimeSum + $elapsed_time;
      $IOTime_count++;
      
      # initialization
      $ielement = $#Open;   # Number of elements in @Open hash
      $oflags = "";
      $mode = "";

      #   file name is contained in cmdtemp
      #   opening options are contained in @parts - usually parts(1) with a comma or ")" at the end
      #      Unit is contained after the "=" in the @parts
      
      &Open_Processing();
   } elsif ($cmd eq $STAT) {
      if ($debug > 0) {
         printf(STRACE_LOG "FOUND A STAT!!!\n");
      }
      $CmdCounter{"stat"}++;
      $temp = floor($sec - $BeginTime) + 1;  # Time in second referenced to beginning time
      $IOPS_Total[$temp]++;
      
      # Increment total IO time and command counters
      $IOTimeSum = $IOTimeSum + $elapsed_time;
      $IOTime_count++;
   } elsif ($cmd eq $FSTAT) {
      if ($debug > 0) {
         printf(STRACE_LOG "FOUND A FSTAT!!!\n");
      }
      $CmdCounter{"fstat"}++;
      $temp = floor($sec - $BeginTime) + 1;  # Time in second referenced to beginning time
      $IOPS_Total[$temp]++;
      
      # Increment total IO time and command counters
      $IOTimeSum = $IOTimeSum + $elapsed_time;
      $IOTime_count++;
   } elsif ($cmd eq $STAT64) {
      if ($debug > 0) {
         printf(STRACE_LOG "FOUND A STAT64!!!\n");
      }
      $CmdCounter{"stat64"}++;
      $temp = floor($sec - $BeginTime) + 1;  # Time in second referenced to beginning time
      $IOPS_Total[$temp]++;
      
      # Increment total IO time and command counters
      $IOTimeSum = $IOTimeSum + $elapsed_time;
      $IOTime_count++;
   } elsif ($cmd eq $LSEEK){
      if ($debug > 0) {
         printf(STRACE_LOG "FOUND AN LSEEK!!!\n");
      }
      $CmdCounter{"lseek"}++;
      # Increment total IO time and command counters
      $IOTimeSum = $IOTimeSum + $elapsed_time;
      $IOTime_count++;
          
      &Lseek_Processing();
   } elsif ($cmd eq $LLSEEK){
      if ($debug > 0) {
         printf(STRACE_LOG "FOUND AN LLSEEK!!!\n");
      }
      # Increment total IO time and command counters
      $IOTimeSum = $IOTimeSum + $elapsed_time;
      $IOTime_count++;
          
      &LLseek_Processing();
   } elsif ($cmd eq $LSEEK64) {
      if ($debug > 0) {
         printf(STRACE_LOG "FOUND AN LSEEK64!!!\n");
      }
      # Increment total IO time and command counters
      $IOTimeSum = $IOTimeSum + $elapsed_time;
      $IOTime_count++;
          
      &Lseek_Processing();
   } elsif ($cmd eq $CHMOD){
      $CmdCounter{"chmod"}++;
      $temp = floor($sec - $BeginTime) + 1;  # Time in second referenced to beginning time
      $IOPS_Total[$temp]++;
      
      # Increment total IO time and command counters
      $IOTimeSum = $IOTimeSum + $elapsed_time;
      $IOTime_count++;
   } elsif ($cmd eq $ACCESS){
      $CmdCounter{"access"}++;
      $temp = floor($sec - $BeginTime) + 1;  # Time in second referenced to beginning time
      $IOPS_Total[$temp]++;
      
      # Increment total IO time and command counters
      $IOTimeSum = $IOTimeSum + $elapsed_time;
      $IOTime_count++;
   } elsif ($cmd eq $RENAME){
      $CmdCounter{"rename"}++;
      $temp = floor($sec - $BeginTime) + 1;  # Time in second referenced to beginning time
      $IOPS_Total[$temp]++;
      
      # Increment total IO time and command counters
      $IOTimeSum = $IOTimeSum + $elapsed_time;
      $IOTime_count++;
   } elsif ($cmd eq $MKDIR){
      $CmdCounter{"mkdir"}++;
      $temp = floor($sec - $BeginTime) + 1;  # Time in second referenced to beginning time
      $IOPS_Total[$temp]++;
      
      # Increment total IO time and command counters
      $IOTimeSum = $IOTimeSum + $elapsed_time;
      $IOTime_count++;
   } elsif ($cmd eq $GETDENTS){
      $CmdCounter{"getdents"}++;
      $temp = floor($sec - $BeginTime) + 1;  # Time in second referenced to beginning time
      $IOPS_Total[$temp]++;
       
       # Increment total IO time and command counters
      $IOTimeSum = $IOTimeSum + $elapsed_time;
      $IOTime_count++;
   } elsif ($cmd eq $FCNTL){
      $CmdCounter{"fcntl"}++;
      $temp = floor($sec - $BeginTime) + 1;  # Time in second referenced to beginning time
      $IOPS_Total[$temp]++;
      
      # Increment total IO time and command counters
      $IOTimeSum = $IOTimeSum + $elapsed_time;
      $IOTime_count++;
   } elsif ($cmd eq $UNLINK){
      $CmdCounter{"unlink"}++;
      $temp = floor($sec - $BeginTime) + 1;  # Time in second referenced to beginning time
      $IOPS_Total[$temp]++;
      
      # Increment total IO time and command counters
      $IOTimeSum = $IOTimeSum + $elapsed_time;
      $IOTime_count++;
   } elsif ($cmd eq $FSEEK){
      $CmdCounter{"fseek"}++;
      $temp = floor($sec - $BeginTime) + 1;  # Time in second referenced to beginning time
      $IOPS_Total[$temp]++;
      
      # Increment total IO time and command counters
      $IOTimeSum = $IOTimeSum + $elapsed_time;
      $IOTime_count++;
   } elsif ($cmd eq $REWIND){
      $CmdCounter{"rewind"}++;
      $temp = floor($sec - $BeginTime) + 1;  # Time in second referenced to beginning time
      $IOPS_Total[$temp]++;
      
      # Increment total IO time and command counters
      $IOTimeSum = $IOTimeSum + $elapsed_time;
      $IOTime_count++;
   } elsif ($cmd eq $FTELL){
      $CmdCounter{"ftell"}++;
      $temp = floor($sec - $BeginTime) + 1;  # Time in second referenced to beginning time
      $IOPS_Total[$temp]++;
      
      # Increment total IO time and command counters
      $IOTimeSum = $IOTimeSum + $elapsed_time;
      $IOTime_count++;
   } elsif ($cmd eq $FGETPOS){
      $CmdCounter{"fgetpos"}++;
      $temp = floor($sec - $BeginTime) + 1;  # Time in second referenced to beginning time
      $IOPS_Total[$temp]++;
      
      # Increment total IO time and command counters
      $IOTimeSum = $IOTimeSum + $elapsed_time;
      $IOTime_count++;
   } elsif ($cmd eq $FCLOSE){
      $CmdCounter{"fclose"}++;
      $temp = floor($sec - $BeginTime) + 1;  # Time in second referenced to beginning time
      $IOPS_Total[$temp]++;
      
      # Increment total IO time and command counters
      $IOTimeSum = $IOTimeSum + $elapsed_time;
      $IOTime_count++;
   } elsif ($cmd eq $FSYNC){
      $CmdCounter{"fsync"}++;
      $temp = floor($sec - $BeginTime) + 1;  # Time in second referenced to beginning time
      $IOPS_Total[$temp]++;
      
      # Increment total IO time and command counters
      $IOTimeSum = $IOTimeSum + $elapsed_time;
      $IOTime_count++;
   } elsif ($cmd eq $CREAT){
      $CmdCounter{"creat"}++;
      $temp = floor($sec - $BeginTime) + 1;  # Time in second referenced to beginning time
      $IOPS_Total[$temp]++;
      
      # Increment total IO time and command counters
      $IOTimeSum = $IOTimeSum + $elapsed_time;
      $IOTime_count++;
   } elsif ($cmd eq $READDIR){
      $CmdCounter{"readdir"}++;
      $temp = floor($sec - $BeginTime) + 1;  # Time in second referenced to beginning time
      $IOPS_Total[$temp]++;
      
      # Increment total IO time and command counters
      $IOTimeSum = $IOTimeSum + $elapsed_time;
      $IOTime_count++;
   } elsif ($cmd eq $OPENDIR){
      $CmdCounter{"opendir"}++;
      $temp = floor($sec - $BeginTime) + 1;  # Time in second referenced to beginning time
      $IOPS_Total[$temp]++;
      
      # Increment total IO time and command counters
      $IOTimeSum = $IOTimeSum + $elapsed_time;
      $IOTime_count++;
   } elsif ($cmd eq $REWINDDIR){
      $CmdCounter{"rewinddir"}++;
      $temp = floor($sec - $BeginTime) + 1;  # Time in second referenced to beginning time
      $IOPS_Total[$temp]++;
      
      # Increment total IO time and command counters
      $IOTimeSum = $IOTimeSum + $elapsed_time;
      $IOTime_count++;
   } elsif ($cmd eq $SCANDIR){
      $CmdCounter{"scandir"}++;
      $temp = floor($sec - $BeginTime) + 1;  # Time in second referenced to beginning time
      $IOPS_Total[$temp]++;
      
      # Increment total IO time and command counters
      $IOTimeSum = $IOTimeSum + $elapsed_time;
      $IOTime_count++;
   } elsif ($cmd eq $SEEKDIR){
      $CmdCounter{"seekdir"}++;
      $temp = floor($sec - $BeginTime) + 1;  # Time in second referenced to beginning time
      $IOPS_Total[$temp]++;
      
      # Increment total IO time and command counters
      $IOTimeSum = $IOTimeSum + $elapsed_time;
      $IOTime_count++;
   } elsif ($cmd eq $TELLDIR){
      $CmdCounter{"telldir"}++;
      $temp = floor($sec - $BeginTime) + 1;  # Time in second referenced to beginning time
      $IOPS_Total[$temp]++;
      
      # Increment total IO time and command counters
      $IOTimeSum = $IOTimeSum + $elapsed_time;
      $IOTime_count++;
   } elsif ($cmd eq $FLOCK){
      $CmdCounter{"flock"}++;
      $temp = floor($sec - $BeginTime) + 1;  # Time in second referenced to beginning time
      $IOPS_Total[$temp]++;
      
      # Increment total IO time and command counters
      $IOTimeSum = $IOTimeSum + $elapsed_time;
      $IOTime_count++;
   } elsif ($cmd eq $LOCKF){
      $CmdCounter{"lockf"}++;
      $temp = floor($sec - $BeginTime) + 1;  # Time in second referenced to beginning time
      $IOPS_Total[$temp]++;
      
      # Increment total IO time and command counters
      $IOTimeSum = $IOTimeSum + $elapsed_time;
      $IOTime_count++;
   } elsif  ($cmd eq $READ) {
      $ielement = $#Read;
      if ($debug > 0) {
         printf(STRACE_LOG "   ** Found a READ function call \n");
      }
      # Increment total IO time and command counters
      $IOTimeSum = $IOTimeSum + $elapsed_time;
      $IOTime_count++;
      
      &Read_Processing();
   } elsif ($cmd eq $WRITE) {
      $ielement = $#Write;
      if ($debug > 0) {
         printf(STRACE_LOG "   ** Found a WRITE function call \n");
      }
      # Increment total IO time and command counters
      $IOTimeSum = $IOTimeSum + $elapsed_time;
      $IOTime_count++;
          
      &Write_Processing();
   } elsif ($cmd eq $CLOSE) {
      $ielement = $#Close;
      if ($debug > 0) {
         printf(STRACE_LOG "   ** Found a CLOSE function call \n");
         printf(STRACE_LOG "      Calling Close_Processing \n");
      }
      # Increment total IO time and command counters
      $IOTimeSum = $IOTimeSum + $elapsed_time;
      $IOTime_count++;
          
      &Close_Processing();
   } else {
      #$CmdStore[$LineNum] = $cmd;
   }
}

$EndTime = $sec;

# ============================================================================
# ============================================================================
# ============================   Output Summary   ============================
# ============================================================================
# ============================================================================

printf(" \n \n");
printf("Analysis Output \n");
printf("=============== \n");

printf("\nNumber of Lines in strace file: %d \n",$Numlines);
printf("\n");

# Initialize file sizes (used for summary of read/write functions)
$FileSizes[0] = 1000;            # 1KB
$FileSizes[1] = 8000;            # 8KB
$FileSizes[2] = 32000;           # 32KB
$FileSizes[3] = 128000;          # 128KB
$FileSizes[4] = 256000;          # 256KB
$FileSizes[5] = 512000;          # 512KB
$FileSizes[6] = 1000000;         # 1MB
$FileSizes[7] = 10000000;        # 10MB
$FileSizes[8] = 100000000;       # 100MB
$FileSizes[9] = 1000000000;      # 1GB
$FileSizes[10] = 10000000000;    # 10GB
$FileSizes[11] = 100000000000;   # 100GB
$FileSizes[12] = 1000000000000;  # 1TB
$FileSizes[13] = 10000000000000; # 10TB


#$FileSizes[4] = $FileSizes[3]*1024;
#$FileSizes[5] = $FileSizes[4]*1024;
# Initialize File size counters
$FileSizeCounter{1000} = 0;
$FileSizeCounter{8000} = 0;
$FileSizeCounter{32000} = 0;
$FileSizeCounter{128000} = 0;
$FileSizeCounter{256000} = 0;
$FileSizeCounter{512000} = 0;
$FileSizeCounter{1000000} = 0;
$FileSizeCounter{10000000} = 0;
$FileSizeCounter{100000000} = 0;
$FileSizeCounter{1000000000} = 0;
$FileSizeCounter{10000000000} = 0;
$FileSizeCounter{100000000000} = 0;
$FileSizeCounter{1000000000000} = 0;
$FileSizeCounter{10000000000000} = 0;



# ===============
# Time statistics
# ===============

# Elapsed Time for run length
printf("----------------\n");
printf("-- Time Stats --\n");
printf("----------------\n");

printf("Elapsed Time for run: %f (secs) \n", ($EndTime - $BeginTime) );
printf("Total IO Time: %f (secs) \n", $IOTimeSum);
printf("Total IO Time Counter: %d \n",$IOTime_count);
printf("   Percentage of Total Time = %f%% \n", (($IOTimeSum/($EndTime - $BeginTime))*100.0) );


# =====================
# IO Command statistics
# =====================

printf(" \n\n");
printf("---------------------- \n");
printf("-- IO Command Count -- \n");
printf("---------------------- \n");
printf("%-9s\t\t%6s\n",
       "Command", "Count");
printf("==============================\n");

foreach my $key (keys %CmdCounter) {
   printf("%-9s\t\t%6d \n", $key, $CmdCounter{$key} );
}
printf(" \n\n");



# ================
# Write statistics
# ================
if (defined $CmdCounter{"write"} ) {
   &Write_Statistics();
}

# ===============
# Read statistics
# ===============
#
if (defined $CmdCounter{"read"} ) {
   &Read_Statistics();
}

# ================
# Close statistics
# ================
if (defined $CmdCounter{"close"} ) {
   &Close_Statistics();
}


# ===============
# Open statistics
# ===============
if (defined $CmdCounter{"open"} ) {
   &Open_Statistics();
}


# ==============================
# lseek unit activity statistics
# ==============================
if (defined $CmdCounter{"lseek"} ) {
   &Lseek_Activity();
}




# ===============
# IOPS statistics
# ===============
$IOPS_Read_Final = 0;
$IOPS_Write_Final = 0;
$IOPS_Total_Final = 0;
printf("--------------------- \n");
printf("-- IOPS Statistics -- \n");
printf("--------------------- \n\n");

if (defined $CmdCounter{"write"} ) {
   &IOPS_write_summary();
}

if (defined $CmdCounter{"read"} ) {
   &IOPS_read_summary();
}

&IOPS_output();


# ===================
# Per File Statistics
# ===================
# Write Summary on a per unit basis
#if ( (defined $CmdCounter{"open"} ) && ($shortflag == 0) ) {
#   &Per_File_Stats();
#}
if ( defined $CmdCounter{"open"} ) {
   &Per_File_Stats();
}



# ==========
# ==========
# Data Files
# ==========
# ==========
&Data_File_Output();







#####################################################################################################################
#####################################################################################################################
#####################################################################################################################
###################################################   Functions   ###################################################
#####################################################################################################################
#####################################################################################################################
#####################################################################################################################


sub commify {
   local $_  = shift;
   1 while s/^([-+]?\d+)(\d{3})/$1,$2/;
   return $_;
}
   

sub commify2 {
   # commify a number. Perl Cookbook, 2.17, p. 64
   my $text = reverse $_[0];
   $text =~ s/(\d\d\d)(?=\d)(?!\d*\.)/$1,/g;
   return scalar reverse $text;
}


sub FileSizeStr {
   my ($junk) = @_;
   my $junk_str;
   
   #printf("FileSizeStr function: junk = %s \n", $junk);
   if ($junk < 1048576) {
      $junk_str = sprintf("%3d",($junk/1000) );
      $junk_str = $junk_str . "KB";
   } elsif ($junk >= 1000000 && $junk < 1000000000 ) {
      $junk_str = sprintf("%3d", ($junk/1000000) );
      $junk_str = $junk_str . "MB";
   } elsif ($junk >= 1000000000  && $junk < 1000000000000 ) {
      $junk_str = sprintf("%3d", ($junk/1000000000) );
      $junk_str = $junk_str . "GB";
   } elsif ($junk >= 1000000000000) {
      $junk_str = sprintf("%3d", ($junk/1000000000000) );
      $junk_str = $junk_str . "TB";
   } else {
      $junk_str = sprintf("Are you sure that is correct? That is a huge file size");
   }
   return $junk_str;
}



sub helpoutput {
   printf("Usage: strace-analyze [OPTION]... [FILE] \n");
   printf("Analyzes strace output for IO functions. It creates statistics \n");
   printf("on IO functions and performance of the read and write functions.\n");
   printf("The strace file should have been run with 'strace -T -ttt [PROGRAM] \n");
   printf(" \n");
   printf("  -d         Debug - echo the input lines to stdout and provide debugging information\n");
   printf("  -debug        same as -d \n");
   printf("  --d           same as -d \n");
   printf("  --debug       same as -d \n");
   printf("  -h         Produces help output (this message) \n");
   printf("  -help         same as -h \n");
   printf("  --h           same as -h \n");
   printf("  --help        same as -h \n");
   printf("  -dat       Produce .dat files for plotting \n");
   printf("  --dat         same as -dat \n");
   printf("  -short     Short version of output \n");
   printf("  --short       same as -short \n");
}


sub Open_Processing {
   # Sample:
   #   1252621029.776202 open("/etc/ld.so.cache", O_RDONLY) = 3 <0.000017>
   
   # **** Split $cmdtmp to get the file name
   ($before, $filename, $after) = split('"', $cmdtmp);
   
   if ($debug > 0) {
      foreach my $specific_part (@parts) {
         printf(STRACE_LOG "      specific_part: %s \n",$specific_part);
      }
   }

   # **** Find unit associated with open function (after "=")
   $iloop = 0;
   foreach my $specific_part (@parts) {
      if ($iloop == 1) {
         $junk = $specific_part;
         $iloop = 0;
      }
      if ($specific_part eq "=") { $iloop = 1; }
   }
   $unit = $junk;
   
   # If $unit is negative, then open function was not successful
   if ($debug > 0) {
      if ($unit < 0) { 
         printf(STRACE_LOG "      Open did not succeed on fd: %d  So not adding fd to statistics \n", $unit);
      } else {
         printf(STRACE_LOG "      unit: %d \n",$unit);
      }
   }

   # If unit is positive (i.e. it was successfully opened)
   if ($unit > 0)
   {
      # Increment the open counter (number of open function calls)
      $CmdCounter{"open"}++;
      
      # Update Maxmimum open time (if necessary)
      if ($elapsed_time > $OpenMax{"MaxTime"} ) {
         $OpenMax{"MaxTime"} = $elapsed_time;
         $OpenMax{"line"} = $LineNum - 1;
      }
   
      # **** Check if filename already exists (stored by unit): 
      #      @Open_Filename[$unit] = $filename;
      if (defined $Open_Filename[$unit]) {
         if ($Open_Filename[$unit] eq $filename) {
            printf(STRACE_LOG "*** Warning: Filename %s for unit %s already exists \n",$filename, $unit);
         } else {
            printf(STRACE_LOG "*** Comment: unit %s is being reused for new file name %s \n", $unit, $filename);
         }
      } else {
         # File name doesn't exist so add it to hash
         $Open_Filename[$unit] = $filename;
      }
      
      if ($debug > 0) {
         printf(STRACE_LOG "      filename: %s \n",$filename);
      }
      
      # **** File open options (oflags)
      if ($parts[1] eq "=") {
         ($junk1, $junk2)=split(/\)/,$parts[0]);
         $oflags = $junk1;
         $mode = "";
      } elsif ($parts[2] eq "=") {
         #printf("            second option \n");
         ($junk1, $junk2)=split(/,/,$parts[0]);
         $oflags = $junk1;
         ($junk1, $junk2)=split(/\)/,$parts[1]);
         $mode = $junk1;
      }
   
      if ($debug > 0) {
         printf(STRACE_LOG "      oflags: %s \n",$oflags);
         printf(STRACE_LOG "      mode: %s \n",$mode);
      }
      
      # Add data to Open hash
      $Open[$ielement+1]->{line_number} = $LineNum;
      $Open[$ielement+1]->{sec} = $sec;
      $Open[$ielement+1]->{file} = $filename;
      $Open[$ielement+1]->{unit} = $unit;
      $Open[$ielement+1]->{elapsed_time} = $zero;

      $temp = floor($sec - $BeginTime) + 1;
      $IOPS_Total[$temp]++;

      $File_Stats[$unit]->{file} = $filename; 
      $File_Stats[$unit]->{read_bytes} = 0;
      $File_Stats[$unit]->{write_bytes} = 0; 
      $File_Stats[$iloop]->{read_rate_count} = 0;
      $File_Stats[$iloop]->{read_rate_sum} = 0;
      $File_Stats[$iloop]->{write_rate_sum} = 0;
      $File_Stats[$iloop]->{write_rate_count} = 0;
      
      # Add line to simulator output
      
      # Check if number of cols in $unit is greater than zero
      #    If so, then $unit has been used before - write warning to log
      #    but don't do anything else (just now).
      #
      # Current length of the $unit-th row
      $junk1 = $#{$Offset[$unit]} + 1;   # Number of Cols.
      if ($junk1 > 0) {
         printf(STRACE_LOG "*** WARNING: In open_processing. unit = %d has been used before \n", $unit);
         printf(STRACE_LOG "    Number of columns in Offset array is = %d \n", $junk1);
         printf(STRACE_LOG "    It should be zero \n");
      }
      # Delete previous array elements
      delete $Offset[$unit];
      # Start tracking file offset
      $Offset_point[$unit] = 0;
      $Offset[$unit][0]->{time} = $sec - $BeginTime;
      $Offset[$unit][0]->{offset} = 0;
   }
}

sub Lseek_Processing {
   # Clean up offset
   ($junk1, $junk2)=split(/\,/,$parts[0]);
   $offset = $junk1;
   
   # Clean up Whence part of call
   ($junk1, $junk2)=split(/\)/,$parts[1]);
   $whence = $junk1;
   
   # Determine current offset (result of lseek)
   $parts_length = @parts;
   $current_offset = $parts[$parts_length-2];
   
   # Determine unit (file descriptor)
   ($junk1, $junk2)=split(/\,/,$cmd_unit);
   $unit = $junk1;
   if ($debug > 0) {
      printf(STRACE_LOG "unit: %d \n",$unit);
   }
   
   # Search if unit is already stored
   $junk4 = grep { $_ eq $unit } @lseek_unit;
   if ($junk4 == 0) {     # New unit so push it onto the array @lseek_unit
       if ($debug > 0) {
          printf(STRACE_LOG "Found new lseek unit %d \n",$unit);
       }
       $ip = @lseek_activity_counter;
       push(@lseek_unit,$unit);
       push(@lseek_activity_counter,1);
       $ip = 1; 
       if ($debug > 0) {
          printf(STRACE_LOG "   Pushed onto array. New Pointer: %d  \n",$ip);
       }
   } else {
       $iloop = 0;
       foreach my $key (@lseek_unit) {
          if ($key == $unit) {
             last;
          }
          $iloop++;
       }
       $lseek_activity_counter[$iloop]++;
       $ip = $lseek_activity_counter[$iloop];
       if ($debug > 0) {
          printf(STRACE_LOG "   Existing unit %d  determining pointer %d \n",$unit, $ip);
       }
   }
   # ip is the number of lseek calls for the current unit ($unit)
   if ($debug > 0) {
      printf(STRACE_LOG "      * unit: %d \n",$unit);
      printf(STRACE_LOG "      * ip: %d \n",$ip);
      printf(STRACE_LOG "      * lseek_unit: %d \n",$lseek_unit[$iloop-1]);
      printf(STRACE_LOG "      * current_offset: %d \n",$current_offset);
   }
   
   # Increment data counter and time (relative to beginning of code)
   $lseek_activity[$unit][$ip-1]->{data}=1.0;
   $temp = $sec - $BeginTime;
   $lseek_activity[$unit][$ip-1]->{time} = $temp;
   if ($debug > 0) {
      printf(STRACE_LOG "      * lseek_activity[%d][%d]->time: %f  lseek_activity[%d][%d]->data: %f  \n",
             $unit, ($ip-1), $lseek_activity[$unit][$ip-1]->{time},
             $unit, ($ip-1), $lseek_activity[$unit][$ip-1]->{data});
      printf(STRACE_LOG "      * current_offset: %d \n",$current_offset);
   }
   
   # Insert data into data structures
   #$CmdCounter{"lseek"}++;
   $temp = floor($sec - $BeginTime) + 1;  # Time in second referenced to beginning time
   $IOPS_Total[$temp]++;
   
   # Adjust Offset array
   if (defined $Open_Filename[$unit]) {
      #printf(STRACE_LOG "In Lseek_Processing routine Adding to offset array\n");
      if ($debug > 0) {
         printf(STRACE_LOG "      In Lseek_Processing routine Adding to offset array\n");
      }
      $junk1 = $#{$Offset[$unit]} + 1;
      $junk2 = $sec - $BeginTime;
      if ($debug > 0) {
         printf(STRACE_LOG "         unit = %d \n",$unit);
         printf(STRACE_LOG "         length of row = %d \n", $junk1);
         printf(STRACE_LOG "         time = %f \n", $junk2);
         printf(STRACE_LOG "         current fs pointer location = %d \n", $Offset_point[$unit]);
         printf(STRACE_LOG "         offset = %d \n", $offset);
         printf(STRACE_LOG "         resulting offset location = %d \n", $current_offset);
      }
      if ($whence eq "SEEK_CUR") {
         $Offset_point[$unit] = $current_offset;
         $Offset[$unit][$junk1]->{time} = $junk2;
         $Offset[$unit][$junk1]->{offset} = $Offset_point[$unit];
      } elsif ($whence eq "SEEK_SET") {
         $Offset_point[$unit] = $current_offset;
         $Offset[$unit][$junk1]->{time} = $junk2;
         $Offset[$unit][$junk1]->{offset} = $current_offset;
      } elsif ($whence eq "SEEK_SET") {
         # ABAQUS/s1.trace:20:54:45.691522 lseek(6, 0, SEEK_END)   = 5266
         $Offset_point[$unit] = $current_offset;
         $Offset[$unit][$junk1]->{time} = $junk2;
         $Offset[$unit][$junk1]->{offset} = $current_offset;
      } else {
         printf(STRACE_LOG "Problem - no whence in lseek \n");
      }
      
      # Update Maxmimum seek time (if necessary)
      if ($elapsed_time > $LseekMax{"MaxTime"} ) {
         $LseekMax{"MaxTime"} = $elapsed_time;
         $LseekMax{"line"} = $LineNum - 1;
      }
   }
}




sub LLseek_Processing {
   #  int _llseek(unsigned int fd, unsigned long offset_high,
   #               unsigned long offset_low, loff_t *result,
   #               unsigned int whence);
   if ($debug > 0) {
      printf(STRACE_LOG "**** llseek_processing: \n");
   }
   
   # Clean up offset
   ($junk1, $junk2)=split(/\,/,$parts[0]);
   $offset = $junk1;

   # Check result of llseek first
   #   search through parts array looking for "="
   $junk1 = 0;
   foreach my $specific_part (@parts) {
      $junk1 = $junk1 + 1;
      if ($specific_part eq "=") {
         $junk2 = $junk1;
      }
   }
   $offset_success = $parts[$junk2];
   if ($debug > 0) {
      printf(STRACE_LOG "    offset_success = %d \n", $offset_success);
   }
   
   # Check results
   #   if successful the process and store function
   #   if not successful add the IOP to the list but don't store anything else
   if ($offset_success > -1) {
      if ($debug > 0) {
         printf(STRACE_LOG "   **** llseek was successful \n");
      }
      $offset_junk = $parts[0];
      $offset_results = $parts[1];
   
      # Clean up Whence part of call
      ($junk1, $junk2)=split(/\)/,$parts[2]);
      $whence = $junk1;
      
      # if whence = SEEK_SET then $offset_results should be in the form [888]
      my $offset_length = length($offset_results);
      if ( substr( $offset_results, 0, 1) eq "[") {
         $junk3 = substr($offset_results, 1, $offset_length-3);
      } else {
         $junk3 = substr($offset_results, 0, $offset_length-1);
      }
      # Set current offset (result of llseek)
      $current_offset = $junk3;
   
      # Determine unit (file descriptor)
      ($junk1, $junk2)=split(/\,/,$cmd_unit);
      $unit = $junk1;
      if ($debug > 0) {
         printf(STRACE_LOG "    whence: %s \n", $whence);
         printf(STRACE_LOG "    offset results: %s \n", $junk3 );
         printf(STRACE_LOG "    unit: %d \n",$unit);
      }
   
      # Search if unit is already stored (i.e. it's already opened)
      $junk4 = grep { $_ eq $unit } @lseek_unit;
      if ($junk4 == 0) {     # New unit so push it onto the array @lseek_unit
          if ($debug > 0) {
             printf(STRACE_LOG "Found new llseek unit %d \n",$unit);
          }
          $ip = @lseek_activity_counter;
          push(@lseek_unit,$unit);
          push(@lseek_activity_counter,1);
          $ip = 1; 
          if ($debug > 0) {
             printf(STRACE_LOG "   Pushed onto array. New Pointer: %d  \n",$ip);
          }
      } else {
          $iloop = 0;
          foreach my $key (@lseek_unit) {
             if ($key == $unit) {
                last;
             }
             $iloop++;
          }
          $lseek_activity_counter[$iloop]++;
          $ip = $lseek_activity_counter[$iloop];
          if ($debug > 0) {
             printf(STRACE_LOG "   Existing unit %d  determining pointer %d \n",$unit, $ip);
          }
      }
      # ip is the number of llseek calls for the current unit ($unit)
      if ($debug > 0) {
         printf(STRACE_LOG "      * unit: %d \n",$unit);
         printf(STRACE_LOG "      * ip: %d \n",$ip);
         printf(STRACE_LOG "      * llseek_unit: %d \n",$lseek_unit[$iloop-1]);
      }
   
      # Increment data counter and time (relative to beginning of code)
      $lseek_activity[$unit][$ip-1]->{data}=1.0;
      $temp = $sec - $BeginTime;
      $lseek_activity[$unit][$ip-1]->{time} = $temp;
      if ($debug > 0) {
         printf(STRACE_LOG "      * llseek_activity[%d][%d]->time: %f  lseek_activity[%d][%d]->data: %f  \n",
                $unit, ($ip-1), $lseek_activity[$unit][$ip-1]->{time},
                $unit, ($ip-1), $lseek_activity[$unit][$ip-1]->{data});
      }
   
      # Insert data into data structures
      $CmdCounter{"lseek"}++;
      $temp = floor($sec - $BeginTime) + 1;  # Time in second referenced to beginning time
      $IOPS_Total[$temp]++;
   
      # Adjust Offset array
      if (defined $Open_Filename[$unit]) {
         if ($debug > 0) {
            printf(STRACE_LOG "      In LLseek_Processing routine Adding to offset array\n");
         }
         $junk1 = $#{$Offset[$unit]} + 1;
         $junk2 = $sec - $BeginTime;
         if ($debug > 0) {
            printf(STRACE_LOG "         unit = %d \n",$unit);
            printf(STRACE_LOG "         length of row = %d \n", $junk1);
            printf(STRACE_LOG "         time = %f \n", $junk2);
            printf(STRACE_LOG "         current fs pointer location = %d \n", $Offset_point[$unit]);
            printf(STRACE_LOG "         offset = %d \n", $offset);
            printf(STRACE_LOG "         resulting offset location = %d \n", $current_offset);
         }
         if ($whence eq "SEEK_CUR") {
            $Offset_point[$unit] = $current_offset;
            $Offset[$unit][$junk1]->{time} = $junk2;
            $Offset[$unit][$junk1]->{offset} = $Offset_point[$unit];
         } elsif ($whence eq "SEEK_SET") {
            $Offset_point[$unit] = $current_offset;
            $Offset[$unit][$junk1]->{time} = $junk2;
            $Offset[$unit][$junk1]->{offset} = $current_offset;
         } elsif ($whence eq "SEEK_SET") {
            # ABAQUS/s1.trace:20:54:45.691522 lseek(6, 0, SEEK_END)   = 5266
            $Offset_point[$unit] = $current_offset;
            $Offset[$unit][$junk1]->{time} = $junk2;
            $Offset[$unit][$junk1]->{offset} = $current_offset;
         } else {
            printf(STRACE_LOG "Problem - no whence in llseek \n");
         }
      }
      
      # Update Maxmimum seek time (if necessary)
      if ($elapsed_time > $LseekMax{"MaxTime"} ) {
         $LseekMax{"MaxTime"} = $elapsed_time;
         $LseekMax{"line"} = $LineNum - 1;
      }
   } else {
      if ($debug > 0) {
         printf(STRACE_LOG "   **** llseek was unsuccessful \n");
         printf(STRACE_LOG "        just incrementing IOPS counter \n");
      }
      $temp = floor($sec - $BeginTime);
      $IOPS_Total[$temp]++;
   }
}


sub Read_Processing {
   # Increment the read counter (number of reads)
   $CmdCounter{"read"}++;
   if ($debug > 0) {
      printf(STRACE_LOG "   *** In read_processing routine\n");
   }
   
   # Increment counter for total bytes read:
   #   For a read the number of bytes read is stored in the last defined array
   #   element in @parts
   $junk1 = 0;
   foreach my $specific_part (@parts) {
      if ((defined $specific_part) && ($junk1 == 1) ) {
            $junk = $specific_part;
            $junk1 = 0;
      }
      if ( (defined $specific_part) && ($specific_part eq "=") ) {
            $junk1 = 1;
      }
   }
   $junk =~ s/[^0-9]//g;
   if ($junk > 0) {
      $byte = $junk;
   } else {
      $byte = 0;
   }

   # Clean up read unit
   ($junk1, $junk2)=split(/\,/,$cmd_unit);
   $unit = $junk1;
   if ($debug > 0) {
      printf(STRACE_LOG "      unit = %d \n",$unit);
      printf(STRACE_LOG "      Number of bytes: %d \n", $byte);
      printf(STRACE_LOG "      Elapsed time: %f \n", $elapsed_time);
      printf(STRACE_LOG "      Throughput (byte/s): %f \n", $byte/$elapsed_time);
   }
   
   # Update maximum read time (if necessary)
   if ($elapsed_time > $ReadMax{"MaxTime"} ) {
      $ReadMax{"MaxTime"} = $elapsed_time;
      $ReadMax{"line"} = $LineNum - 1;
   }

   # Note: Socket functions and other functions will perform IO to an fd
   #       Need to check if the unit is connected to a file - if so, then
   #       store data - otherwise, ignore it
   if (defined $Open_Filename[$unit]) {
      # Add to hash
      $Read[$ielement+1]->{line_number} = $LineNum;
      $Read[$ielement+1]->{sec} = $sec;
      if ($byte eq "" || $byte < 0) {
         $Read[$ielement+1]->{bytes} = -1;
      } else {
         # Increment read hash
         $Read[$ielement+1]->{bytes} = $byte;
         # Keep track of total number bytes read
         $ReadBytesTotal += $byte; 
         # Increment individual file stats
         $File_Stats[$unit]->{read_bytes} += $byte;
         $File_Stats[$unit]->{read_rate_sum} += ($byte/$elapsed_time);
         $File_Stats[$unit]->{read_rate_count} += 1;
      }
      # Store throughput
      $Read[$ielement+1]->{byte_sec} = $byte/$elapsed_time;
      # Store elapsed time for syscall
      $Read[$ielement+1]->{elapsed_time} = $elapsed_time;
      # Store unit
      $Read[$ielement+1]->{unit} = $unit;

      # Update IOPS_Read array (and IOPS_Total)
      $temp = floor($sec - $BeginTime) + 1;    # Time increment (in seconds)
      $IOPS_Read[$temp]++;
      $IOPS_Total[$temp]++;
      $IOPS_Read_Unit[$unit][$temp]++;
      if ($debug > 0) {
         printf(STRACE_LOG "      IOPS time = %f \n",$temp);;
      }

      # Check below since this may not be needed
      #if ($unit > 0) {
      #   $File_Stats[$unit]->{read_bytes} += $byte;
      #}
      
      # Update Offset information (used for pattern observation)
      #    Update $unit offset
      #    Current length of the $unit-th row
      if ($debug > 0) {
         printf(STRACE_LOG "      In Read_Processing routine Adding to offset array\n");
      }
      $junk1 = $#{$Offset[$unit]} + 1;
      $junk2 = $sec - $BeginTime;
      if ($debug > 0) {
         printf(STRACE_LOG "         unit = %d \n",$unit);
         printf(STRACE_LOG "         length of row in Offset array = %d \n", $junk1);
         printf(STRACE_LOG "         time = %f \n", $junk2);
         printf(STRACE_LOG "         offset = %d \n", $byte);
      }
      #printf("byte: %d \n",$byte);
      #printf("Offset_point[ %d ]: %d \n",$unit, $byte);
      #$Offset_point[$unit] += $byte;
      $Offset_point[$unit] = $Offset_point[$unit] + $byte;
      $Offset[$unit][$junk1]->{time} = $junk2;
      $Offset[$unit][$junk1]->{offset} = $Offset_point[$unit];
   }
   else {
      printf(STRACE_LOG "Read: No file attached to unit %s - could be a socket\n", $unit);
      printf(STRACE_LOG "   Line Number: %d \n",$LineNum);
      printf(STRACE_LOG "   Line: %s\n",$lineOutput);
   }
   if ($debug > 0) {
      printf(STRACE_LOG "*** Leaving read_processing routine\n");
   }
}


sub Write_Processing {
   # Increment the write counter (number of writes)
   $CmdCounter{"write"}++;
   if ($debug > 0) {
      printf(STRACE_LOG "   *** In write_processing routine\n");
   }
   
   # Increment counter for total bytes written
   #   For a write the number of bytes written is stored in the array element
   #   in @parts, just after the "=" sign
   $junk1 = 0;
   foreach my $specific_part (@parts) {
      if ((defined $specific_part) && ($junk1 == 1) ) {
            $junk = $specific_part;
            $junk1 = 0;
      }
      if ( (defined $specific_part) && ($specific_part eq "=") ) {
            $junk1 = 1;
      }
   }
   $junk =~ s/[^0-9]//g;
   if ($junk > 0) {
      $byte = $junk;
   } else {
      $byte = 0;
   }

   # Clean up write unit
   ($junk1, $junk2)=split(/\,/,$cmd_unit);
   $unit = $junk1;   # $unit indicates success of function
   
   if ($debug > 0) {
      printf(STRACE_LOG "      unit = %d \n",$unit);
      printf(STRACE_LOG "      Number of bytes: %d \n", $byte);
      printf(STRACE_LOG "      Elapsed time: %f \n", $elapsed_time);
      printf(STRACE_LOG "      Throughput (byte/s): %f \n", $byte/$elapsed_time);
   }
   
   # Update Maximum write time (if necceasry)
   if ($elapsed_time > $WriteMax{"MaxTime"} )  {
       $WriteMax{"MaxTime"} = $elapsed_time;
       $WriteMax{"line"} = $LineNum - 1;
   }
   
   # Note: Socket functions and other functions will perform IO to an fd
   #       Need to check if the unit is connected to a file - if so, then
   #       store data - otherwise, ignore it
   if ( (defined $Open_Filename[$unit]) || ($unit == 1) )     {
      # Add data to hash
      $Write[$ielement+1]->{line_number} = $LineNum;
      $Write[$ielement+1]->{sec} = $sec;
      if ($byte eq "" || $byte < 0)  {
         $Write[$ielement+1]->{bytes} = -1;
      } else {
         $Write[$ielement+1]->{bytes} = $byte;
         # Keep track of total number bytes written
         $WriteBytesTotal += $byte;
      }
      # Store throughput
      $Write[$ielement+1]->{byte_sec} = $byte/$elapsed_time;
      # Store elapsed time
      $Write[$ielement+1]->{elapsed_time} = $elapsed_time;
      # Store unit
      $Write[$ielement+1]->{unit} = $unit;

      # Update IOPS_Write array
      $temp = floor($sec - $BeginTime) + 1;   # Time in seconds referenced to starting time
      $IOPS_Write[$temp]++;
      $IOPS_Total[$temp]++;
      $IOPS_Write_Unit[$unit][$temp]++;
      if ($debug > 0) {
         printf(STRACE_LOG "      IOPS time = %f \n",$temp);;
      }

      if ($unit > 0) {
         $File_Stats[$unit]->{write_bytes} += $byte; 
         $File_Stats[$unit]->{write_rate_sum} += ($byte/$elapsed_time);
         $File_Stats[$unit]->{write_rate_count} += 1;
      }
      
      
      # Update $unit offset
      # Current length of the $unit-th row
      if ($debug > 0) {
         printf(STRACE_LOG "      In Write_Processing routine Adding to offset array\n");
      }
      $junk1 = $#{$Offset[$unit]} + 1;
      $junk2 = $sec - $BeginTime;
      if ($debug > 0) {
         printf(STRACE_LOG "         unit = %d \n",$unit);
         printf(STRACE_LOG "         length of row in Offset array = %d \n", $junk1);
         printf(STRACE_LOG "         time = %f \n", $junk2);
         printf(STRACE_LOG "         offset = %d \n", $byte);
      }
      $Offset_point[$unit] += $byte;
      $Offset[$unit][$junk1]->{time} = $junk2;
      $Offset[$unit][$junk1]->{offset} = $Offset_point[$unit];
      
      $kwalker++;
      #printf("Processed Write: kwalker: %d   LineNum: %d \n",$kwalker, $LineNum);
   }
   else {
      printf(STRACE_LOG "Write: No file attached to unit %s - could be a socket\n", $unit);
      printf(STRACE_LOG "   Line Number: %d \n",$LineNum);
      printf(STRACE_LOG "   Line: %s\n",$lineOutput);
      $jwalker++;
      #printf("Processed Write: jwalker: %d   LineNum: %d \n",$jwalker, $LineNum);
   }
   if ($debug > 0) {
      printf(STRACE_LOG "*** Leaving write_processing routine\n");
   }
}




sub Close_Processing {
   # Increment the write counter (number of writes)
   $CmdCounter{"close"}++;
   if ($debug > 0) {
      printf(STRACE_LOG "   *** In close_processing routine\n");
   }
   
   # Extract unit from cmdtmp
   $junk = $cmdtmp;
   $junk =~ s/[^0-9]//g;
   $unit = $junk;
   
   if ($debug > 0) {
      printf(STRACE_LOG "      In Close_Processing routine \n");
      printf(STRACE_LOG "         ielement: %s \n", $ielement);
   }
   
   # Update maximum close time (if necessary)
   if ($elapsed_time > $CloseMax{"MaxTime"} ) {
      $CloseMax{"MaxTime"} = $elapsed_time;
      $CloseMax{"line"} = $LineNum - 1;
   }
      
   # Check if filename already exists (stored by unit)
   #    @Open_Filename[$unit] = $filename;
   # Continue on if the unit exists in the Open_Filename array (means it was opened)
   if ($unit > 0) {
      if (defined $Open_Filename[$unit]) {
         # Update data structures
         # Add to hash
         $Close[$ielement+1]->{line_number} = $LineNum;
         $Close[$ielement+1]->{sec} = $sec;
         $Close[$ielement+1]->{unit} = $unit;
         $Close[$ielement+1]->{elapsed_time} = $elapsed_time;
         if ($debug > 0) {
            printf(STRACE_LOG "         unit = %d \n",$unit);
            printf(STRACE_LOG "         Elapsed time: %f \n", $elapsed_time);
         }

         # Update IOPS_Total array
         $temp = floor($sec - $BeginTime) + 1;
         $IOPS_Total[$temp]++;

         $Close_Unit_Ops[$junk][$temp]++;
   
         # Undefine unit in Open array (i.e. the file was closed so show it wasn't opened)
         undef $Open_Filename[$unit];
         if ($debug > 0) {
            printf(STRACE_LOG "      *** Undefined unit: %d from Open_Filename array \n",$unit);
         }
      } else {
         printf(STRACE_LOG "      Cannot undefine Open_Filename[%d] \n", $unit);
         printf(STRACE_LOG "          Could be a socket? \n");
         printf(STRACE_LOG "          Line number: %d \n", $LineNum);
         printf(STRACE_LOG "          Length of Open_Filename array = %d \n", scalar(@Open_Filename) );
         $iloop = 0;
         foreach $junk (@Open_Filename) {
            $iloop++;
            if (defined $junk) {
               printf(STRACE_LOG "          Open_FileName[%d] = %s \n", $iloop, $junk);
            }   
         }
      }
   }

}


sub Write_Statistics {
   if ($CmdCounter{"write"} > 0) {
      printf("---------------------- \n");
      printf("-- Write Statistics -- \n");
      printf("---------------------- \n");
      if ($shortflag == 0) {
         printf("-- Write syscall History --\n");
         printf("%-4s\t\t%15s\t\t%4s\t%15s\t\t%20s\t\t%16s \n",
                "Time", "Command", "Unit", "Bytes",
                "Bandwidth (Bytes/s)", "Bandwidth (MB/s)");
      }
      $junk1 = "=";
      for ($iloop=0; $iloop < 119; $iloop++) {
         $junk1 = $junk1 . "=";
      }
      if ($shortflag == 0) {
         printf("%s \n", $junk1);
      }

      $sum = 0.0;
      foreach my $specific_hash (@Write) {
         $sum = $sum + $specific_hash->{elapsed_time};
         $junk1 = sprintf("%.2f",$specific_hash->{byte_sec} );
         $junk2 = sprintf("%.2f",($specific_hash->{byte_sec}/1000000.0) );
         if ($shortflag == 0) {
            printf("%.6f\t%4s\t\t%4d\t%15s\t\t%20s\t\t%16s \n",
                   $specific_hash->{sec},
                   "write", $specific_hash->{unit}, 
                   commify2( $specific_hash->{bytes} ),
                   commify2( $junk1 ),commify2( $junk2 ) );
         }
      }
      
      # Re-initialize File size counters with a for loop,
      # so that we don't include file sizes from write calls
      foreach my $FileSize (@FileSizes)
      {
          $FileSizeCounter{$FileSize} = 0;
      }
      
      #
      # File Size Interval Summary
      #
      $junk3= $#FileSizes;  # Number of File sizes
      foreach my $specific_hash (@Write)
      {
         $junk = $specific_hash->{bytes};
         if ($junk < $FileSizes[0]) {
            $FileSizeCounter{$FileSizes[0]}++;
         } elsif ($junk > $FileSizes[$junk3] ) {
            $FileSizeCounter{$FileSizes[$junk3]}++;
         } else {
            $iloop = 0;
            for ($icount=1; $icount < ($junk3+1); $icount++) {
               if ($junk < $FileSizes[$icount] && $junk > $FileSizes[$icount-1] ) {
                  $iloop = $icount;
               }
            }
            $FileSizeCounter{$FileSizes[$iloop]}++;
         }
         if ($junk > $WriteLarge)
         {
            $WriteLarge = $junk;
         }
         if ($junk < $WriteSmall)
         {
            $WriteSmall = $junk;
         }
      }
   
      # print out intervals and count
      printf(" \n");
      printf("-- File sizes for write() syscall --\n\n");
      printf("%-21s \t\t%23s \n",
             "IO Size Range", "    Number of syscalls");
      printf("=======================================================\n");
      # 
      # Do First File Size interval 
      $iloop = 1;
      # FileSizes[0]:
      my $junk1_str = FileSizeStr( $FileSizes[0] );
      printf("(%3d) %6s <   < %6s\t\t%15d \n", $iloop, "0KB", $junk1_str, $FileSizeCounter{$FileSizes[0]} );
      # Rest of the File Size Intervals
      for ($icount=1; $icount < ($junk3+1); $icount++) {
         $iloop++;
         $junk1 = $FileSizes[$icount];
         $junk2 = $FileSizes[$icount-1];
         my $junk1_str = FileSizeStr( $junk1 );
         my $junk2_str = FileSizeStr( $junk2 );
         printf("(%3d) %6s <   < %6s\t\t%15d \n", $iloop, $junk2_str, $junk1_str, $FileSizeCounter{$FileSizes[$iloop-1]} );
      }
      
      # Find average and standard deviation
      $sum = 0.0;
      $junk1 = 0;
      my $sum2 = 0.0;
      foreach my $specific_hash (@Write) {
         $sum = $sum + $specific_hash->{bytes};
         push(@Local_Write_Array, $specific_hash->{bytes});
         $junk1 = $junk1 + 1;
         $sum2 = $sum2 + ($specific_hash->{bytes} * $specific_hash->{bytes});
      }
      $Test_Average = $sum / $junk1;
      $Std_Dev = sqrt( ($sum2/$junk1) - ($Test_Average*$Test_Average) );
      
      # Find median value
      #@Local_Write_Array = sort(@Local_Write_Array);
      @Local_Write_Array = sort by_number @Local_Write_Array;
      $junk2 = @Local_Write_Array;     # length of array
      if ($junk2 % 2) {
         # number is odd
         my $middle = $junk2 / 2;
         $My_Median = $Local_Write_Array[$middle];
      } else {
         # number is even
         my $middle = ($junk2 / 2) - 1;
         $My_Median = ( $Local_Write_Array[$middle] + $Local_Write_Array[$middle+1]) / 2.0;
      }
      
      # Find average absolute deviations
      $sum = 0.0;
      $sum2 = 0.0;
      foreach my $specific_hash (@Write) {
         $sum = $sum + abs( $specific_hash->{bytes} - $Std_Dev );
         $sum2 = $sum2 + abs( $specific_hash->{bytes} - $My_Median );
      }
      my $Mean_abs_dev = (1.0/$junk1)*$sum;
      my $Median_abs_dev = (1.0/$junk1)*$sum2;

      #
      # Write summary
      #
      printf(" \n\n");
      printf("-- WRITE SUMMARY -- \n");
      printf("Total number of Bytes written = %s (%s  MB) \n",commify2($WriteBytesTotal),
              commify2($WriteBytesTotal / 1000000.0) );
      printf("Number of Write syscalls = %8s \n\n",commify2($CmdCounter{"write"}) ); 
      #printf("Average Bytes per call = %13s (bytes) (%s  MB)\n", commify($WriteBytesTotal / $CmdCounter{"write"}),
      #        commify(($WriteBytesTotal / $CmdCounter{"write"})/1000000.0 ) );
      printf("Average (mean) Bytes per syscall = %13s (bytes) (%s  MB)\n", commify($Test_Average),
              commify($Test_Average/1000000.0 ) );
      printf("   Standard Deviation: %13s (bytes) (%s  MB)\n", commify($Std_Dev),
              commify($Std_Dev/1000000.0) );
      printf("   Mean Absolute Deviation: %13s (bytes) (%s  MB) \n", commify($Mean_abs_dev),
              commify($Mean_abs_dev/1000000.0) );
      printf("Median Bytes per syscall = %13s (bytes) (%s MB)\n", commify($My_Median), 
             commify($My_Median/1000000.0) );
      printf("   Median Absolute Deviation: %13s (bytes) (%s  MB) \n\n", commify($Median_abs_dev),
              commify($Median_abs_dev/1000000.0) );
      printf("Time for slowest write syscall (secs) = %f \n",$WriteMax{"MaxTime"} );
      printf("   Line location in file: %d \n", $WriteMax{"line"} );
      printf(" \n");
      printf("Smallest write syscall size: %d (Bytes) \n",$WriteSmall);
      printf("Largest write syscall size: %d (Bytes) \n",$WriteLarge);
      printf(" \n");
   }
}


sub Read_Statistics {
   if ($CmdCounter{"read"} > 0) {
      printf(" \n");
      printf("--------------------- \n");
      printf("-- Read Statistics -- \n");
      printf("--------------------- \n");
      if ($shortflag == 0) {
         printf("%-4s\t\t\t%7s\t\t%4s\t%15s\t\t%20s\t\t%16s \n",
                "Time", "Command", "Unit", "Bytes",
                "Bandwidth (Bytes/s)", "Bandwidth (MB/s)");
      }
      $junk1 = "=";
      for ($iloop=0; $iloop < 119; $iloop++) {
         $junk1 = $junk1 . "=";
      }
      if ($shortflag == 0) {
         printf("%s \n", $junk1);
      }

      $sum = 0.0;
      foreach my $specific_hash (@Read) {
         $sum = $sum + $specific_hash->{elapsed_time};
         $junk1 = sprintf("%.2f",$specific_hash->{byte_sec} );
         $junk2 = sprintf("%.2f",($specific_hash->{byte_sec}/1000000.0) );
         if ($shortflag == 0) {
            if ($specific_hash->{bytes} < 0) {
                #printf("%2d:%2d:%d.%6s\t%15s\t\t%4d\t%15s\t\t%20s\t\t%16s \n",
                #      $specific_hash->{hour}, $specific_hash->{min}, 
                #      $specific_hash->{sec}, $specific_hash->{usec},
                #      "*read", $specific_hash->{unit}, 
                #      commify2( $specific_hash->{bytes} ),
                #      commify2( $junk1 ),commify2( $junk2 ) );
                printf("%.6f\t%5s\t\t%4d\t%15s\t\t%20s\t\t%16s \n",
                      $specific_hash->{sec},
                      "*read", $specific_hash->{unit}, 
                      commify2( $specific_hash->{bytes} ),
                      commify2( $junk1 ),commify2( $junk2 ) );
            } else {
               #printf("%2d:%2d:%d.%6s\t%15s\t\t%4d\t%15s\t\t%20s\t\t%16s \n",
               #       $specific_hash->{hour}, $specific_hash->{min}, 
               #       $specific_hash->{sec}, $specific_hash->{usec},
               #       "read", $specific_hash->{unit}, 
               #       commify2( $specific_hash->{bytes} ),
               #       commify2( $junk1 ),commify2( $junk2 ) );
               printf("%.6f\t%4s\t\t%4d\t%15s\t\t%20s\t\t%16s \n",
                      $specific_hash->{sec},
                      "read", $specific_hash->{unit}, 
                      commify2( $specific_hash->{bytes} ),
                      commify2( $junk1 ),commify2( $junk2 ) );
            }
         }
      }

      # Re-initialize File size counters with a for loop,
      # so that we don't include file sizes from write calls
      foreach my $FileSize (@FileSizes)
      {
          $FileSizeCounter{$FileSize} = 0;
      }
      
      #
      # File Size Interval Summary
      #
      #$FileSizeCounter{1024} = 0;
      #$FileSizeCounter{8192} = 0;
      #$FileSizeCounter{32768} = 0;
      #$FileSizeCounter{1048576} = 0;
      $junk3= $#FileSizes;  # Number of File sizes
      foreach my $specific_hash (@Read) {
         $junk = $specific_hash->{bytes};
         if ($junk <= $FileSizes[0]) {
            $FileSizeCounter{$FileSizes[0]}++;
         } elsif ($junk >= $FileSizes[$junk3] ) {
            $FileSizeCounter{$FileSizes[$junk3]}++;
         } else {
            $iloop = 0;
            for ($icount=1; $icount < ($junk3+1); $icount++) {
               if ($junk <= $FileSizes[$icount] && $junk >= $FileSizes[$icount-1] ) {
                  $iloop = $icount;
               }
            }
            $FileSizeCounter{$FileSizes[$iloop]}++;
         }
         if ($junk > $ReadLarge)
         {
            $ReadLarge = $junk;
         }
         if ($junk < $ReadSmall)
         {
            $ReadSmall = $junk;
         }
      }
   
      # print out intervals and count
      printf(" \n");
      printf("-- File sizes for read() syscalls -- \n\n");
      printf("%-21s \t\t%23s \n",
             "IO Size Range", "    Number of syscalls");
      printf("=======================================================\n");
      # Do First File Size interval 
      $iloop = 1;
      # FileSizes[0]:
      my $junk1_str = FileSizeStr( $FileSizes[0] );
      printf("(%3d) %6s <   < %6s\t\t%15d \n", $iloop, "0KB", $junk1_str, $FileSizeCounter{$FileSizes[0]} );
      # Rest of the File Size Intervals
      for ($icount=1; $icount < ($junk3+1); $icount++) {
         $iloop++;
         $junk1 = $FileSizes[$icount];
         $junk2 = $FileSizes[$icount-1];
         my $junk1_str = FileSizeStr( $junk1 );
         my $junk2_str = FileSizeStr( $junk2 );
         printf("(%3d) %6s <   < %6s\t\t%15d \n", $iloop, $junk2_str, $junk1_str, $FileSizeCounter{$FileSizes[$iloop-1]} );
      }

      # Find average and standard deviation
      $sum = 0.0;
      $junk1 = 0;
      my $sum2 = 0.0;
      my $icounter = 0;
      foreach my $specific_hash (@Read) {
      $icounter = $icounter + 1;
         $sum = $sum + $specific_hash->{bytes};
         #printf("read size(%d): %d \n",$icounter,$specific_hash->{bytes});
         push(@Local_Read_Array, $specific_hash->{bytes});
         $junk1 = $junk1 + 1;
         $sum2 = $sum2 + ($specific_hash->{bytes} * $specific_hash->{bytes});
      }
      $Test_Average = $sum / $junk1;
      $Std_Dev = sqrt( ($sum2/$junk1) - ($Test_Average*$Test_Average) );
      
      # Find median value
      @Local_Read_Array = sort by_number @Local_Read_Array;
      $junk2 = @Local_Read_Array;     # length of array
      if ($junk2 % 2) {
         # number is odd
         my $middle = $junk2 / 2;
         $My_Median = $Local_Read_Array[$middle];
      } else {
         # number is even
         my $middle = ($junk2 / 2) - 1;
         $My_Median = ( $Local_Read_Array[$middle] + $Local_Read_Array[$middle+1]) / 2.0;
      }
      
      # Find average absolute deviations
      $sum = 0.0;
      $sum2 = 0.0;
      foreach my $specific_hash (@Read) {
         $sum = $sum + abs( $specific_hash->{bytes} - $Std_Dev );
         $sum2 = $sum2 + abs( $specific_hash->{bytes} - $My_Median );
      }
      my $Mean_abs_dev = (1.0/$junk1)*$sum;
      my $Median_abs_dev = (1.0/$junk1)*$sum2;

      #
      # Read summary
      #
      printf(" \n\n");
      printf("-- READ SUMMARY -- \n");
      printf("Total number of Bytes read = %s (%s  MB)\n",commify2($ReadBytesTotal), 
              commify2($ReadBytesTotal / 1000000.0) );
      printf("Number of Read syscalls = %8s \n\n",commify2($CmdCounter{"read"}) ); 
      #printf("Average Bytes per call = %s (bytes) (%s  MB)\n", commify($ReadBytesTotal / $CmdCounter{"read"}), 
      #        commify(($ReadBytesTotal / $CmdCounter{"read"})/1000000.0 ) );
      printf("Average (mean) Bytes per syscall = %13s (bytes) (%s  MB)\n", commify($Test_Average),
              commify($Test_Average/1000000.0 ) );
      printf("   Standard Deviation: %13s (bytes) (%s  MB)\n", commify($Std_Dev),
              commify($Std_Dev/1000000.0) );
      printf("   Mean Absolute Deviation: %13s (bytes) (%s  MB) \n", commify($Mean_abs_dev),
              commify($Mean_abs_dev/1000000.0) );
      printf("Median Bytes per syscall = %13s (bytes) (%s MB)\n", commify($My_Median), 
             commify($My_Median/1000000.0) );
      printf("   Median Absolute Deviation: %13s (bytes) (%s  MB) \n\n", commify($Median_abs_dev),
              commify($Median_abs_dev/1000000.0) );
      printf("Time for slowest read syscall (secs) = %f \n",$ReadMax{"MaxTime"} );
      printf("   Line location in file: %d \n", $ReadMax{"line"} );
      printf(" \n");
      printf("Smallest read syscall size: %d (Bytes) \n",$ReadSmall);
      printf("Largest read syscall size: %d (Bytes) \n",$ReadLarge);
      printf(" \n");
   }
}


sub Close_Statistics {
   if ($CmdCounter{"close"} > 0) {
      printf(" \n");
      printf("---------------------- \n");
      printf("-- Close Statistics -- \n");
      printf("---------------------- \n");
      if ($shortflag == 0) {
         printf("%-4s\t\t\t%7s\t\t%4s\t%19s \n",
                "Time", "Command", "Unit", "Elapsed Time (sec)");
      }
      $junk1 = "=";
      for ($iloop=0; $iloop < 66; $iloop++) {
         $junk1 = $junk1 . "=";
      }
      if ( (scalar(@Close) > 0) && ($shortflag == 0) ) {
         printf("%s \n", $junk1);
      }

      $sum = 0.0;
      foreach my $specific_hash (@Close) {
         $sum = $sum + $specific_hash->{elapsed_time};
         if ($shortflag == 0) {
            printf("%.6f\t%5s\t\t%4d\t%19s \n",
                   $specific_hash->{sec},
                   "close", $specific_hash->{unit}, 
                   commify2( $specific_hash->{elapsed_time} ) );
         }
      }


      #
      # Close summary
      #
      printf(" \n");
      printf("-- CLOSE SUMMARY -- \n");
      printf("Total number of close syscalls = %d \n", $CmdCounter{"close"} );
      printf("Average time for close syscalls (secs) = %f \n", commify2( $sum/$CmdCounter{"close"} ) );
      printf("Maximum Time for close syscalls (secs) = %f \n",$CloseMax{"MaxTime"} );
      printf("   Line location in file: %d \n", $CloseMax{"line"} );
      printf(" \n");
   }
}



sub Open_Statistics {
   if ($CmdCounter{"open"} > 0) {
      printf(" \n");
      printf("--------------------- \n");
      printf("-- Open Statistics -- \n");
      printf("--------------------- \n");
      if ($shortflag == 0) {
         printf("-- Open function History --\n");
         printf("%-4s\t\t\t%7s\t\t%4s \t%-90s\t%18s \n",
                "Time", "Command", "Unit", "File", "Elapsed Time (sec)");
      }
      $junk1 = "=";
      for ($iloop=0; $iloop < 161; $iloop++) {
         $junk1 = $junk1 . "=";
      }
      if ($shortflag == 0) {
         printf("%s \n", $junk1);
      }

      $sum = 0.0;
      foreach my $specific_hash (@Open) {
         $sum = $sum + $specific_hash->{elapsed_time};
         if ($shortflag == 0) {
            printf("%.6f\t%4s\t\t%4d\t%-90s\t%18s \n",
                   $specific_hash->{sec},
                   "open", $specific_hash->{unit},
                   $specific_hash->{file}, 
                   commify2( $specific_hash->{elapsed_time} ) );
         }
      }


      #
      # Open summary
      #
      printf(" \n");
      printf("-- OPEN SUMMARY -- \n");
      printf("Total number of open syscalls = %d \n", $CmdCounter{"open"} );
      printf("Average time for open syscalls (secs) = %f \n", commify2( $sum/$CmdCounter{"open"} ) );
      printf("Maximum Time for open syscalls (secs) = %f \n",$OpenMax{"MaxTime"} );
      printf("   Line location in file: %d \n", $OpenMax{"line"} );
      printf(" \n");
   }
}



sub Lseek_Activity {
   if ($CmdCounter{"lseek"} > 0) {
      printf(" \n");
      printf("------------------------------------ \n");
      printf("-- lseek unit activity Statistics -- \n");
      printf("------------------------------------ \n\n");

      printf("%-4s \t%16s \n",
             "unit", "Number of lseeks");
      printf("======================== \n");
   
      $junk = scalar (@lseek_unit);
      for ($iloop=0; $iloop < $junk; $iloop++) {
         $unit = $lseek_unit[$iloop];
         $ip = $lseek_activity_counter[$iloop];
         printf("%-4d\t%16d\n",$unit, $ip);
      }
      printf(" \n\n");
   }
}



sub IOPS_write_summary {
   if ($CmdCounter{"write"} > 0) {
      if ($shortflag == 0) {
         printf("** IOPS Write Statistics: ** \n");
         printf("(Time is based on beginning of run) \n\n");
         printf("%-11s \t%16s \n",
                "Time (secs)", "Number of Writes");
         printf("================================ \n");
      }
      $IOPS_max_temp = 0;
      $index_max = 0;
      $index = 0;
      $sum = 0.0;
      $icount = 0;
      foreach $key (@IOPS_Write) {
         if ( defined($IOPS_Write[$index]) ) {
             if ( $IOPS_Write[$index] > $IOPS_max_temp) {
	        $index_max = $index;
	        $IOPS_max_temp = $IOPS_Write[$index];
	     }
             if ($shortflag == 0) {
                printf("%-11d\t%16d \n",$index, $IOPS_Write[$index] );
             }
             $sum = $sum + $IOPS_Write[$index];
             $icount++;
         } else {
             if ( $index > $sec_begin) {
                if ($shortflag == 0) {
                   printf("%-11d\t%16d \n",$index, 0 );
                }
	     }
         }
         $index++;
      }
      printf("\nMaximum Write IOPS = %d  occurred at %d seconds\n",
             $IOPS_max_temp, $index_max);
      $IOPS_Write_Final = $sum/$icount;
      printf("Average Write IOPS = %d \n\n", $IOPS_Write_Final);
   }
}


sub IOPS_read_summary {
   if ($CmdCounter{"read"} > 0) {
      if ($shortflag == 0) {
         printf("** IOPS Read Statistics: ** \n");
         printf("(Time is based on beginning of run) \n\n");
         printf("%-11s\t%16s \n",
                "Time (secs)", "Number of Reads");
         printf("================================ \n");
      }

      $IOPS_max_temp = 0;
      $index_max = 0;
      $index = 0;
      $sum = 0.0;
      $icount = 0;
      foreach $key (@IOPS_Read) {
         if ( defined($IOPS_Read[$index]) ) {
             if ( $IOPS_Read[$index] > $IOPS_max_temp) {
	        $index_max = $index;
	        $IOPS_max_temp = $IOPS_Read[$index];
	     }
             if ($shortflag == 0) {
                printf("%-11d\t%16d \n",$index, $IOPS_Read[$index] );
             }
             $sum = $sum + $IOPS_Read[$index];
             $icount++;
         } else {
             if ( $index > $sec_begin) {
                if ($shortflag == 0) {
                   printf("%-11d\t%16d \n",$index, 0 );
                }
	     }
         }
         $index++;
      }
      printf("\nMaximum Read IOPS = %d  occurred at %d seconds\n",
             $IOPS_max_temp, $index_max);
      $IOPS_Read_Final = $sum/$icount;
      printf("Average Read IOPS = %d \n\n",$IOPS_Read_Final);
   }
}


sub IOPS_output {
   if ($shortflag == 0) {
      printf("** IOPS Total Statistics: ** \n");
      printf("(Time is based on beginning of run) \n\n");
      printf("%-11s\t%30s \n",
             "Time (secs)", "Number of IO functions called");
      printf("============================================== \n");
   }
   
   $IOPS_max_temp = 0;
   $index_max = 0;
   $index = 0;
   $sum = 0.0;
   $icount = 0;
   foreach $key (@IOPS_Total) {
      if ( defined($IOPS_Total[$index]) ) {
          if ( $IOPS_Total[$index] > $IOPS_max_temp) {
	     $index_max = $index;
	     $IOPS_max_temp = $IOPS_Total[$index];
          }
          if ($shortflag == 0) {
             printf("%-11d\t%30d \n",$index, $IOPS_Total[$index] );
          }
          $sum = $sum + $IOPS_Total[$index];
          $icount++;
      } else {
          if ( $index > $sec_begin) {
             if ($shortflag == 0) {
                printf("%-11d\t%30d \n",$index, 0 );
             }
          }
      }
      $index++;
   }
   printf("\nMaximum Total IOPS = %d  occurred at %d seconds\n",
          $IOPS_max_temp, $index_max);
   $IOPS_Total_Final = $sum/$icount;
   printf("Average Total IOPS = %d \n\n",$IOPS_Total_Final);

   printf("*****************\n");
   printf("Final IOPS report\n");
   printf("Average Write IOPS = %d \n", $IOPS_Write_Final);
   printf("Average Read IOPS = %d \n", $IOPS_Read_Final);
   printf("Average Total IOPS = %d \n", $IOPS_Total_Final);
   printf("*****************\n\n\n");
}



sub Data_File_Output {

   # Write all data files to subdirectory called RESULTS_DATA
   my $dirname ="./RESULTS_DAT";
   mkdir $dirname;

   # Data files to be written: (.dat and .csv files)
   #   (1) Write record size syscalls histogram (write record size for all units)
   #   (2) Cumulative Write syscall size histogram (total amount written vs. time for all units)
   #   (3) Write record throughput syscalls histogram (write throughput for all units)
   #   (4) Read size syscalls histogram (amount of data read for all units)
   #   (5) Cumulative Read histogram (total amount read vs. time for all units)
   #   (6) Read record throughput syscalls histogram (read throughput for all units)
   #   (7) Individual unit Write record size syscalls histogram (write record size per unit)
   #   (8) Individual unit Write syscalls throughput histogram (write throughput per unit)
   #   (9) Individual unit Read record size syscalls histogram (read record size per unit)
   #   (10) Individual unit Read syscalls throughput histogram (read throughput per unit)
   #   (11) Total IOPS write histogram
   #   (12) Total IOPS read histogram
   #   (13) Total IOPS total histogram
   #   (14) LSEEK activity (CSV only)
   #   (15) LSEEK activity per file (CSV only)
   #   (16) Individual Read IOPS histogram
   #   (17) Individual Write IOPS histogram


   #   TODOs:
   #   (18) Individual unit offset histogram
   #

   #
   # (1) (2), (3): Write syscall size and throughput
   # --------------------
   # Write size histogram
   # --------------------
   # Open CSV file
   open(CSVFILE, '+>./RESULTS_DAT/write_size_all.csv') or die $!;
   open(CSVFILE2, '+>./RESULTS_DAT/write_throughput_all.csv') or die $!;
   # Open .dat file for write
   if ($datflag > 0) {
      open(DATFILE, '+>./RESULTS_DAT/write_syscall_size_all.dat') or die $!;
      printf(DATFILE "# This data file contains the size of the write syscalls \n");
      printf(DATFILE "#   versus time for all files. \n");
      printf(DATFILE "# The x axis data is time relative to the beginning of the run \n");
      printf(DATFILE "#   where 0 is the start of the run. \n");
      printf(DATFILE "# The y axis data is the number of bytes for each write syscall \n");
      printf(DATFILE "#   for all files in bytes. \n");
      printf(DATFILE "#  \n");
      printf(DATFILE "# It is best to plot this data as a scatter chart with no lines \n");
      printf(DATFILE "#   connecting the data points. \n");
      printf(DATFILE "# \n");
      printf(DATFILE "0.0 0.0 \n");   # Insert beginning data point
      
      open(DATFILE2, '+>./RESULTS_DAT/write_syscall_size_all_cumulative.dat') or die $!;
      printf(DATFILE2 "# This data file contains the cumulative sizes of the write function  \n");
      printf(DATFILE2 "#   calls versus time for all output files. \n");
      printf(DATFILE2 "# The x axis data is time relative to the beginning of the run \n");
      printf(DATFILE2 "#   where 0 is the start of the run. \n");
      printf(DATFILE2 "# The y axis data is the cumulative sizes of the write function calls \n");
      printf(DATFILE2 "#   in Megabytes for all write functions for all files. \n");
      printf(DATFILE2 "#  \n");
      printf(DATFILE2 "# It is best to plot this data as a scatter chart with no lines \n");
      printf(DATFILE2 "#   connecting the data points. \n");
      printf(DATFILE2 "# \n");
      printf(DATFILE2 "0.0 0.0 \n");    # Insert beginning data point
      
      open(DATFILE3, '+>./RESULTS_DAT/write_syscall_throughput_all.dat') or die $!;
      printf(DATFILE3 "# This data file contains the throughput (MB/s) of the write syscalls \n");
      printf(DATFILE3 "#   versus time for all files. \n");
      printf(DATFILE3 "# The x axis data is time relative to the beginning of the run \n");
      printf(DATFILE3 "#   where 0 is the start of the run. \n");
      printf(DATFILE3 "# The y axis data is the throughput (MB/s) for each write syscall \n");
      printf(DATFILE3 "#   for all files. \n");
      printf(DATFILE3 "#  \n");
      printf(DATFILE3 "# It is best to plot this data as a scatter chart with no lines \n");
      printf(DATFILE3 "#   connecting the data points. \n");
      printf(DATFILE3 "# \n");
      printf(DATFILE3 "0.0 0.0 \n");   # Insert beginning data point
   }
   
   printf(CSVFILE "time,write (bytes),total write (bytes),,time (start=0),write (bytes),total write (bytes) \n");
   printf(CSVFILE2 "time,write throughput (MB/s),,time (start=0),write throughput (MB/s) \n");
   $junk2 = 0.0;
   if (defined $CmdCounter{"write"} ) {
      if ($CmdCounter{"write"} > 0) {
         foreach my $specific_hash (@Write) {
            $junk = $specific_hash->{sec};
            $junk2 = $junk2 + $specific_hash->{bytes};
            $junk3 = $junk2/1000000.0;
            $junk4 = sprintf("%.2f",($specific_hash->{byte_sec}/1000000.0) );
            printf(CSVFILE "%.6f,%d,%d,,%.6f,%d,%d \n",$junk, $specific_hash->{bytes}, $junk2,
                 ($junk-$BeginTime),$specific_hash->{bytes}, $junk2 );
            printf(CSVFILE2 "%.6f,%d,,%.6f,%d \n",$junk, $junk4,($junk-$BeginTime),$junk4 );
            if ($datflag > 0) {
               printf(DATFILE "%.6f %.6f \n", ($junk-$BeginTime), $specific_hash->{bytes});
               printf(DATFILE2 "%.6f %.6f \n", ($junk-$BeginTime), $junk3 ); 
               printf(DATFILE3 "%.6f %.6f \n", ($junk-$BeginTime), $junk4);
            }
         }
      }
   }
   # Add final data point (end of run)
   if ($datflag > 0) {
      printf(DATFILE "%.6f 0.0 \n", ($EndTime - $BeginTime) );
      close(DATFILE);
      #printf(DATFILE2 "%.6f %.6f \n", ($EndTime - $BeginTime), $junk3 );
      printf(DATFILE2 "%.6f %.6f \n", ($EndTime - $BeginTime), 0.0 );
      close(DATFILE2);
      printf(DATFILE3 "%.6f %.6f \n", ($EndTime - $BeginTime), 0.0 );
      close(DATFILE3);
   }
   # Add space to end of csv file
   printf(CSVFILE " \n");
   printf(CSVFILE2 " \n");
   # Close CSV file
   close(CSVFILE);
   close(CSVFILE2);


   # (4), (5), (6): Read
   # --------------
   # Read Histogram
   # --------------
   # Open CSV file
   open (CSVFILE, '+>./RESULTS_DAT/read_size_all.csv') or die $!;
   open (CSVFILE2, '+>./RESULTS_DAT/read_throughput_all.csv') or die $!;

   # Open .dat file for read
   if ($datflag > 0) {
      open (DATFILE, '+>./RESULTS_DAT/read_syscall_size_all.dat') or die $!;
      printf(DATFILE "# This data file contains the size of the read syscalls \n");
      printf(DATFILE "#   versus time for all files. \n");
      printf(DATFILE "# The x axis data is time relative to the beginning of the run \n");
      printf(DATFILE "#   where 0 is the start of the run. \n");
      printf(DATFILE "# The y axis data is the number of bytes for each read syscall \n");
      printf(DATFILE "#   for all files in bytes. \n");
      printf(DATFILE "#  \n");
      printf(DATFILE "# It is best to plot this data as a scatter chart with no lines \n");
      printf(DATFILE "#   connecting the data points. \n");
      printf(DATFILE "# \n");
      printf(DATFILE "0.0 0.0 \n");   # Insert beginning data point
      
      open (DATFILE2, '+>./RESULTS_DAT/read_syscall_size_all_cumulative.dat') or die $!;
      printf(DATFILE2 "# This data file contains the cumulative sizes of the read function  \n");
      printf(DATFILE2 "#   calls versus time for all output files. \n");
      printf(DATFILE2 "# The x axis data is time relative to the beginning of the run \n");
      printf(DATFILE2 "#   where 0 is the start of the run. \n");
      printf(DATFILE2 "# The y axis data is the cumulative sizes of the read function calls \n");
      printf(DATFILE2 "#   in Megabytes for all read functions for all files. \n");
      printf(DATFILE2 "#  \n");
      printf(DATFILE2 "# It is best to plot this data as a scatter chart with no lines \n");
      printf(DATFILE2 "#   connecting the data points. \n");
      printf(DATFILE2 "# \n");
      printf(DATFILE2 "0.0 0.0 \n");    # Insert beginning data point
      
      open (DATFILE3, '+>./RESULTS_DAT/read_syscall_throughput_all.dat') or die $!;
      printf(DATFILE3 "# This data file contains the throughput (MB/s) of the read syscalls \n");
      printf(DATFILE3 "#   versus time for all files. \n");
      printf(DATFILE3 "# The x axis data is time relative to the beginning of the run \n");
      printf(DATFILE3 "#   where 0 is the start of the run. \n");
      printf(DATFILE3 "# The y axis data is the throughput (MB/s) for each read syscall \n");
      printf(DATFILE3 "#   for all files. \n");
      printf(DATFILE3 "#  \n");
      printf(DATFILE3 "# It is best to plot this data as a scatter chart with no lines \n");
      printf(DATFILE3 "#   connecting the data points. \n");
      printf(DATFILE3 "# \n");
      printf(DATFILE3 "0.0 0.0 \n");   # Insert beginning data point
   }

   printf(CSVFILE "time,read (bytes),total read (bytes),,time (start=0),read (bytes),total read (bytes)\n");
   printf(CSVFILE2 "time,read throughput (MB/s),,time (start=0),read throughput (MB/s) \n");
   $junk2 = 0.0;
   if (defined $CmdCounter{"read"}  ) {
      if ($CmdCounter{"read"} > 0) {
         foreach my $specific_hash (@Read) {
            $junk = $specific_hash->{sec};
            $junk2 = $junk2 + $specific_hash->{bytes};
            $junk3 = $junk2 / 1000000.0;
            $junk4 = sprintf("%.2f",($specific_hash->{byte_sec}/1000000.0) );
            printf(CSVFILE "%.6f,%d,%d,,%.6f,%d,%d \n",$junk, $specific_hash->{bytes}, $junk2,
                  ($junk-$BeginTime), $specific_hash->{bytes}, $junk2 );
            printf(CSVFILE2 "%.6f,%d,,%.6f,%d \n",$junk, $junk4,
                  ($junk-$BeginTime), $junk4 );
            if ($datflag > 0) {
               printf(DATFILE "%.6f %.6f \n", ($junk-$BeginTime), $specific_hash->{bytes} );
               printf(DATFILE2 "%.6f %.6f \n", ($junk-$BeginTime),$junk3 );
               printf(DATFILE3 "%.6f %.6f \n", ($junk-$BeginTime), $junk4 );           
            }
         }
      }
   }
   if ($datflag > 0) {
      # Add final data point (end of run)
      printf(DATFILE "%.6f 0.0 \n", ($EndTime - $BeginTime) );
      close(DATFILE);
      printf(DATFILE2 "%.6f %.6f \n", ($EndTime - $BeginTime), $junk3 );
      close(DATFILE2);
      # Add final data point (end of run)
      printf(DATFILE3 "%.6f 0.0 \n", ($EndTime - $BeginTime) );
      close(DATFILE3);
   }
   # Add space to end of csv file
   printf(CSVFILE " \n");
   printf(CSVFILE2 " \n");
   # Close CSV file
   close(CSVFILE);
   close(CSVFILE2);



   # (7), (8): Individual Write syscall size and throughput
   $junk = scalar (@File_Stats);
   for ($iloop=0; $iloop < $junk; $iloop++) {    # Loop over length of File_Stats
      if (exists $File_Stats[$iloop]->{file} ) {  #JEFFWASHERE
         $junk2 = sprintf("%i", $iloop);
         $junk3 = '+>./RESULTS_DAT/write_syscall_size_' . $junk2 . '.dat';
         open(DATFILE, $junk3) or die $!; 
         printf(DATFILE "# This data file contains the size of the write syscalls \n");
         printf(DATFILE "#   versus time for a specific file. \n");
         printf(DATFILE "# The x axis data is time relative to the beginning of the run \n");
         printf(DATFILE "#   where 0 is the start of the run. \n");
         printf(DATFILE "# The y axis data is the number of bytes for each write syscall \n");
         printf(DATFILE "#   for the specific file (in bytes). \n");
         printf(DATFILE "# \n");
         printf(DATFILE "# File: %s \n",$File_Stats[$iloop]->{file});
         printf(DATFILE "# \n");
         printf(DATFILE "# It is best to plot this data as a scatter chart with no lines \n");
         printf(DATFILE "#   connecting the data points. \n");
         printf(DATFILE "# \n");
         printf(DATFILE "0.0 0.0 \n");   # Insert beginning data point
         
         $junk3 = '+>./RESULTS_DAT/write_syscall_throughput_' . $junk2 . '.dat';
         open(DATFILE2, $junk3) or die $!;      
         printf(DATFILE2 "# This data file contains the throughput in MB/s of each write syscall \n");
         printf(DATFILE2 "#   call versus time for a specific file. \n");
         printf(DATFILE2 "# The x axis data is time relative to the beginning of the run \n");
         printf(DATFILE2 "#   where 0 is the start of the run. \n");
         printf(DATFILE2 "# The y axis data is the throughput in MB/s for each write syscall  \n");
         printf(DATFILE2 "#   for each file. \n");
         printf(DATFILE2 "# \n");
         printf(DATFILE2 "# File: %s \n",$File_Stats[$iloop]->{file});
         printf(DATFILE2 "# \n");
         printf(DATFILE2 "# It is best to plot this data as a scatter chart with no lines \n");
         printf(DATFILE2 "#   connecting the data points. \n");
         printf(DATFILE2 "# \n");
         printf(DATFILE2 "0.0 0.0 \n");   # Insert beginning data point

         # Loop over @Write looking for unit
         foreach my $specific_hash (@Write) {
            if ($specific_hash->{unit} = $iloop) {
               $junk4 = $specific_hash->{sec};
               $junk6 = sprintf("%.2f",($specific_hash->{byte_sec}/1000000.0) );
               if ($datflag > 0) {
                  printf(DATFILE "%.6f %.6f \n", ($junk4-$BeginTime), $specific_hash->{bytes});
                  printf(DATFILE2 "%.6f %.6f \n", ($junk4-$BeginTime), $junk6);
               }
            }
         }
         # Add final data point (end of run)
         if ($datflag > 0) {
            printf(DATFILE "%.6f %.6f \n", ($EndTime - $BeginTime), 0.0 );
            close(DATFILE);
            printf(DATFILE2 "%.6f %.6f \n", ($EndTime - $BeginTime), 0.0 ); 
            close(DATFILE2);
         }  
      }
   }
   
   # (9), (10): Individual read syscall size and throughput
   $junk = scalar (@File_Stats);
   for ($iloop=0; $iloop < $junk; $iloop++) {    # Loop over length of File_Stats
      if (exists $File_Stats[$iloop]->{file} ) {
         $junk2 = sprintf("%i", $iloop);
         $junk3 = '+>./RESULTS_DAT/read_syscall_size_' . $junk2 . '.dat';
         open (DATFILE, $junk3) or die $!; 
         printf(DATFILE "# This data file contains the size of the read syscalls \n");
         printf(DATFILE "#   versus time for a specific file. \n");
         printf(DATFILE "# The x axis data is time relative to the beginning of the run \n");
         printf(DATFILE "#   where 0 is the start of the run. \n");
         printf(DATFILE "# The y axis data is the number of bytes for each read syscall \n");
         printf(DATFILE "#   for the specific file (in bytes). \n");
         printf(DATFILE "# \n");
         printf(DATFILE "# File: %s \n",$File_Stats[$iloop]->{file});
         printf(DATFILE "# \n");
         printf(DATFILE "# It is best to plot this data as a scatter chart with no lines \n");
         printf(DATFILE "#   connecting the data points. \n");
         printf(DATFILE "# \n");
         printf(DATFILE "0.0 0.0 \n");   # Insert beginning data point
         
         $junk3 = '+>./RESULTS_DAT/read_syscall_throughput_' . $junk2 . '.dat';
         open (DATFILE2, $junk3) or die $!;      
         printf(DATFILE2 "# This data file contains the throughput in MB/s of each read syscall \n");
         printf(DATFILE2 "#   call versus time for a specific file. \n");
         printf(DATFILE2 "# The x axis data is time relative to the beginning of the run \n");
         printf(DATFILE2 "#   where 0 is the start of the run. \n");
         printf(DATFILE2 "# The y axis data is the throughput in MB/s for each read syscall  \n");
         printf(DATFILE2 "#   for each file. \n");
         printf(DATFILE2 "# \n");
         printf(DATFILE2 "# File: %s \n",$File_Stats[$iloop]->{file});
         printf(DATFILE2 "# \n");
         printf(DATFILE2 "# It is best to plot this data as a scatter chart with no lines \n");
         printf(DATFILE2 "#   connecting the data points. \n");
         printf(DATFILE2 "# \n");
         printf(DATFILE2 "0.0 0.0 \n");   # Insert beginning data point

         # Loop over @Read looking for unit
         foreach my $specific_hash (@Read) {
            if ($specific_hash->{unit} = $iloop) {
               $junk4 = $specific_hash->{sec};
               $junk6 = sprintf("%.2f",($specific_hash->{byte_sec}/1000000.0) );
               if ($datflag > 0) {
                  printf(DATFILE "%.6f %.6f \n", ($junk4-$BeginTime), $specific_hash->{bytes});
                  printf(DATFILE2 "%.6f %.6f \n", ($junk4-$BeginTime), $junk6);
               }
            }
         }
         # Add final data point (end of run)
         if ($datflag > 0) {
            printf(DATFILE "%.6f %.6f \n", ($EndTime - $BeginTime), 0.0 );
            close(DATFILE);
            printf(DATFILE2 "%.6f %.6f \n", ($EndTime - $BeginTime), 0.0 );
            close(DATFILE2);
         }  
      }
   }


   # (11): Write IOPS
   # ----------------------
   # IOPS - Write histogram
   # ----------------------
   # Open CSV file
   open (CSVFILE, '+>./RESULTS_DAT/iops_write.csv') or die $!;

   # Open .dat file for write IOPS
   if ($datflag > 0) {
      open(DATFILE, '+>./RESULTS_DAT/iops_write.dat') or die $!;
      printf(DATFILE "# This data file contains the write IOPS versus time for all files. \n");
      printf(DATFILE "# The x axis data is time relative to the beginning of the run \n");
      printf(DATFILE "#   where 0 is the start of the run. \n");
      printf(DATFILE "# The y axis data is the write IOPS for all files. It is computed \n");
      printf(DATFILE "#    in 1 second intervals. \n");
      printf(DATFILE "# \n");
      printf(DATFILE "# It is best to plot this data as a scatter chart with no lines \n");
      printf(DATFILE "#   connecting the data points. \n");
      printf(DATFILE "# \n");
      # Insert beginning data point
      printf(DATFILE "0 0 \n");
   }
   printf(CSVFILE "time,Write IOPS\n");
   if (defined $CmdCounter{"write"} ) {
      if ($CmdCounter{"write"} > 0) {
         $index = 0;
         foreach $key (@IOPS_Write) {
            if ( defined($IOPS_Write[$index]) ) {
                printf(CSVFILE "%d,%d \n",$index, $IOPS_Write[$index] );
                if ($datflag > 0) {
                  printf(DATFILE "%d %d \n", $index, $IOPS_Write[$index] );
                }
            }   
            $index++;
         }
      }
   }
   # Add space to end of csv file
   printf(CSVFILE " \n");
   if ($datflag > 0) {
      # Add final data point (end of run)
      #printf(DATFILE "%.6f 0 \n", ($EndTime - $BeginTime) );
      #printf(DATFILE " \n");
      close(DATFILE);
   }
   
   
   # (12): Read IOPS
   # ---------------------
   # IOPS - Read histogram
   # ---------------------
   # Open .dat file for write IOPS
   if ($datflag > 0) {
      open(DATFILE, '+>./RESULTS_DAT/iops_read.dat') or die $!;
      printf(DATFILE "# This data file contains the read IOPS versus time for all files. \n");
      printf(DATFILE "# The x axis data is time relative to the beginning of the run \n");
      printf(DATFILE "#   where 0 is the start of the run. \n");
      printf(DATFILE "# The y axis data is the read IOPS for all files. It is computed \n");
      printf(DATFILE "#    in 1 second intervals. \n");
      printf(DATFILE "# \n");
      printf(DATFILE "# It is best to plot this data as a scatter chart with no lines \n");
      printf(DATFILE "#   connecting the data points. \n");
      printf(DATFILE "# \n");
      # Insert beginning data point
      printf(DATFILE "0 0 \n");
   }
   
   printf(CSVFILE "time,Read IOPS\n");
   if (defined $CmdCounter{"read"} ) {
       if ($CmdCounter{"read"} > 0) {
        $index = 0;
         foreach $key (@IOPS_Read) {
            if ( defined($IOPS_Read[$index]) ) {
                printf(CSVFILE "%d,%d \n",$index, $IOPS_Read[$index] );
                if ($datflag > 0) {
                   printf(DATFILE "%d %d \n",$index, $IOPS_Read[$index] );
                }
            }
            $index++;
         }
      }
   }
   # Add space to end of csv file
   printf(CSVFILE " \n");
   if ($datflag > 0) {
      # Add final data point (end of run)
      #printf(DATFILE "%.6f 0 \n", ($EndTime - $BeginTime) );
      #printf(DATFILE " \n");
      close(DATFILE);
   }
   
   
   # (13): Total IOPS
   # ----------------------
   # IOPS - Total histogram
   # ----------------------
   # Open .dat file for total IOPS
   if ($datflag > 0) {
      open (DATFILE, '+>./RESULTS_DAT/iops_total.dat') or die $!;
      printf(DATFILE "# This data file contains the total IOPS versus time for all files. \n");
      printf(DATFILE "# The x axis data is time relative to the beginning of the run \n");
      printf(DATFILE "#   where 0 is the start of the run. \n");
      printf(DATFILE "# The y axis data is the total IOPS  for all files. It is computed \n");
      printf(DATFILE "#    in 1 second intervals. \n");
      printf(DATFILE "# \n");
      printf(DATFILE "# It is best to plot this data as a scatter chart with no lines \n");
      printf(DATFILE "#   connecting the data points. \n");
      printf(DATFILE "# \n");
      # Insert beginning data point
      printf(DATFILE "0 0 \n");
   }
   
   printf(CSVFILE "time,Total IOPS\n");
   $index = 0;
   foreach $key (@IOPS_Total) {
      if ( defined($IOPS_Total[$index]) ) {
          printf(CSVFILE "%d,%d \n",$index, $IOPS_Total[$index] );
          if ($datflag > 0) {
             printf(DATFILE "%d %d \n",$index, $IOPS_Total[$index] );
          }
      }
      $index++;
   }
   # Add space to end of csv file
   printf(CSVFILE " \n");
   if ($datflag > 0) {
      # Add final data point (end of run)
      #printf(DATFILE "%.6f 0 \n", ($EndTime - $BeginTime) );
      #printf(DATFILE " \n");
      close(DATFILE);
   }
   
   
   # (14) LSEEK activity (CSV only)
   # ----------------------
   # LSEEK Activity Summary
   # ----------------------
   printf(CSVFILE "Unit lseek activity summary\n");
   printf(CSVFILE "unit,lseek count\n");
   $junk = scalar (@lseek_unit);
   for ($iloop=0; $iloop < $junk; $iloop++) {
      $unit = $lseek_unit[$iloop];
      $ip = $lseek_activity_counter[$iloop];
      #printf("*** unit: %d  ip: %d \n",$unit,$ip);
      printf(CSVFILE "%d,%d \n",$unit,$ip);
   }
   printf(CSVFILE " \n");


   # (15) LSEEK activity per file (CSV only)
   # -----------------------------
   # LSEEK Activity unit histogram
   # -----------------------------
   printf(CSVFILE "lseek histogram\n");
   $junk = scalar (@lseek_unit);    # Number of lseek units
   for ($iloop=0; $iloop < $junk; $iloop++) {
      $unit = $lseek_unit[$iloop];
      $ip = $lseek_activity_counter[$iloop];
      #printf("*** unit: %d  ip: %d \n",$unit,$ip);
      printf(CSVFILE "unit,%d\n",$unit);
      printf(CSVFILE "time,lseek\n");
      for ($jloop=0; $jloop < ($ip); $jloop++) {
         #printf("    unit: %d  jloop: %d \n",$unit, $jloop);
         $junk1 = $lseek_activity[$unit][$jloop]->{time};
         $junk2 = $lseek_activity[$unit][$jloop]->{data};
         #printf("      time: %f  data: %f \n",$junk1, $junk2);
         printf(CSVFILE "%f,%f\n",$junk1,$junk2);
      }
      printf(CSVFILE "\n");
   }


   # Close CSV file
   close(CSVFILE);
   
   
   # (16): Read IOPS per unit
   #       $IOPS_Read_Unit[$unit][$temp]++;
   # ---------------------
   # IOPS - Read histogram
   # ---------------------
   $junk = scalar (@File_Stats);
   for ($iloop=0; $iloop < $junk; $iloop++) {    # Loop over length of File_Stats
      if (exists $File_Stats[$iloop]->{file} ) {
         $junk2 = sprintf("%i", $iloop);
         $junk3 = '+>./RESULTS_DAT/iops_read_unit_' . $junk2 . '.dat';
         open (DATFILE, $junk3) or die $!; 
         # Open .dat file for write IOPS
         if ($datflag > 0) {
            printf(DATFILE "# This data file contains the Read IOPS versus time for a specific file. \n");
            printf(DATFILE "# The x axis data is time relative to the beginning of the run \n");
            printf(DATFILE "#   where 0 is the start of the run. \n");
            printf(DATFILE "# The y axis data is the read IOPS for all files. It is computed \n");
            printf(DATFILE "#    in 1 second intervals. \n");
            printf(DATFILE "# \n");
            printf(DATFILE "# It is best to plot this data as a scatter chart with no lines \n");
            printf(DATFILE "#   connecting the data points. \n");
            printf(DATFILE "# \n");
            printf(DATFILE "# File name: %s \n",$junk3);
            printf(DATFILE "# \n");
            # Insert beginning data point
            printf(DATFILE "0 0 \n");
         }    
   
         # Loop over IOPS_Read_Unit
         $size_2 = $#{$IOPS_Read_Unit[$iloop]} + 1;
         for ($jloop=0; $jloop < $size_2; $jloop++) {
            if (exists $IOPS_Read_Unit[$iloop][$jloop]) {
               printf(DATFILE "%d %d \n", $jloop, $IOPS_Read_Unit[$iloop][$jloop]);
            }
         }
         # Add final data point (end of run)
         if ($datflag > 0) {
            #printf(DATFILE "%.6f %.6f \n", ($EndTime - $BeginTime), 0.0 );
            #printf(DATFILE " \n"); 
            close(DATFILE);
         }  
      }
   }
   
   
   
   # (17): Write IOPS per unit
   #       $IOPS_Write_Unit[$unit][$temp]++;
   # ----------------------
   # IOPS - Write histogram
   # ----------------------
   $junk = scalar (@File_Stats);
   for ($iloop=0; $iloop < $junk; $iloop++) {    # Loop over length of File_Stats
      if (exists $File_Stats[$iloop]->{file} ) {
         $junk2 = sprintf("%i", $iloop);
         $junk3 = '+>./RESULTS_DAT/iops_write_unit_' . $junk2 . '.dat';
         open (DATFILE, $junk3) or die $!; 
         # Open .dat file for write IOPS
         if ($datflag > 0) {
            printf(DATFILE "# This data file contains the Write IOPS versus time for a specific file. \n");
            printf(DATFILE "# The x axis data is time relative to the beginning of the run \n");
            printf(DATFILE "#   where 0 is the start of the run. \n");
            printf(DATFILE "# The y axis data is the Write IOPS for all files. It is computed \n");
            printf(DATFILE "#    in 1 second intervals. \n");
            printf(DATFILE "# \n");
            printf(DATFILE "# It is best to plot this data as a scatter chart with no lines \n");
            printf(DATFILE "#   connecting the data points. \n");
            printf(DATFILE "# \n");
            printf(DATFILE "# File name: %s \n",$junk3);
            printf(DATFILE "# \n");
            # Insert beginning data point
            printf(DATFILE "0 0 \n");
         }    
   
         # Loop over IOPS_Write_Unit
         $size_2 = $#{$IOPS_Write_Unit[$iloop]} + 1;
         for ($jloop=0; $jloop < $size_2; $jloop++) {
            if (exists $IOPS_Write_Unit[$iloop][$jloop]) {
               printf(DATFILE "%d %d \n", $jloop, $IOPS_Write_Unit[$iloop][$jloop]);
            }
         }
         # Add final data point (end of run)
         if ($datflag > 0) {
            #printf(DATFILE "%.6f %.6f \n", ($EndTime - $BeginTime), 0.0 );
            #printf(DATFILE " \n"); 
            close(DATFILE);
         }  
      }
   } # End (17)
   
   # (18): Individual File offsets
   #       $IOPS_Write_Unit[$unit][$temp]++;
   # ----------------------
   # IOPS - Write histogram
   # ----------------------
   # $Offset[unit][timestep]->{time} = time of syscall relative to beginning of run
   # $Offset[unit][timestep]->{offset} = offset in bytes of syscall
   $junk = scalar (@Offset);   # Number of units?

   for ($iloop=0; $iloop < $junk; $iloop++) {
      if (exists $File_Stats[$iloop]->{file} ) {
         $junk2 = $Offset[$iloop];
         $junk3 = @$junk2;
         $junk4 = sprintf("%i", $iloop);
         $junk5 = '+>./RESULTS_DAT/offset_' . $junk4 . '.dat';
         open (DATFILE, $junk5) or die $!; 
         printf(DATFILE "# This data file contains the size of the offset in bytes \n");
         printf(DATFILE "#   versus time for a specific file. \n");
         printf(DATFILE "# The x axis data is time relative to the beginning of the run \n");
         printf(DATFILE "#   where 0 is the start of the run. \n");
         printf(DATFILE "# The y axis data is the offset in bytes for the specific file.\n");
         printf(DATFILE "# \n");
         printf(DATFILE "# File: %s \n",$File_Stats[$iloop]->{file});
         printf(DATFILE "# \n");
         printf(DATFILE "# It is best to plot this data as a scatter chart with no lines \n");
         printf(DATFILE "#   connecting the data points. \n");
         printf(DATFILE "# \n");
         printf(DATFILE "0.0 0.0 \n");   # Insert beginning data point

         # Loop over @Read looking for unit
         foreach my $specific_hash (@$junk2) {
            $junk6 = $specific_hash->{time};
            $junk7 = $specific_hash->{offset};
            if ($datflag > 0) {
               printf(DATFILE "%.6f %d \n", ($junk6), $junk7);
            }
         }
         # Add final data point (end of run)
         if ($datflag > 0) {
            printf(DATFILE "%.6f %.6f \n", ($EndTime - $BeginTime), 0.0 );
            close(DATFILE);
         }  
         
         
      }
   } # end of for loop
   
   
   # (19): Write syscall distribution
   # Step 0 - initialize array
   my @junk_array = ();
   # Step 1 - extract syscall size values into array
   foreach my $specific_hash (@Write) {
      $junk = $specific_hash->{bytes};
      push(@junk_array, $junk);
   }
   # Step 2 - sort array
   #@junk_array = sort(@junk_array);
   @junk_array = sort by_number @junk_array;
   # Count duplicates
   my %counts = ();
   for (@junk_array) {
      $counts{$_}++;
   }
   
   # Open .dat file for write syscall display
   if ($datflag > 0) {
      open(DATFILE, '+>./RESULTS_DAT/write_syscall_distribution.dat') or die $!;
      printf(DATFILE "# This data file contains the write syscall distribution for all files. \n");
      printf(DATFILE "# The x axis data is the size of the write syscall in bytes \n");
      printf(DATFILE "# The y axis data is the number of write syscalls with that value. \n");
      printf(DATFILE "# \n");
      printf(DATFILE "# It is best to plot this data as a scatter chart with no lines \n");
      printf(DATFILE "#   connecting the data points. \n");
      printf(DATFILE "# \n");
   }
   foreach my $keys (keys %counts) {
      #print "$keys = $counts{$keys}\n";
      if ($datflag > 0) {
         printf(DATFILE "%.6f %d \n", ($keys), $counts{$keys});
      }
   }
   # Add final data point (end of run)
   if ($datflag > 0) {
      close(DATFILE);
   } 
   
   # (20): Read syscall distribution
   # Step 0 - initialize array
   @junk_array = ();
   # Step 1 - extract syscall size values into array
   foreach my $specific_hash (@Read) {
      $junk = $specific_hash->{bytes};
      push(@junk_array, $junk);
   }
   # Step 2 - sort array
   #@junk_array = sort(@junk_array);
   @junk_array = sort by_number @junk_array;
   
   # Count duplicates
   %counts = ();
   for (@junk_array) {
      $counts{$_}++;
   }
   
   # Open .dat file for write syscall display
   if ($datflag > 0) {
      open(DATFILE, '+>./RESULTS_DAT/read_syscall_distribution.dat') or die $!;
      printf(DATFILE "# This data file contains the read syscall distribution for all files. \n");
      printf(DATFILE "# The x axis data is the size of the read syscall in bytes \n");
      printf(DATFILE "# The y axis data is the number of read syscalls with that value. \n");
      printf(DATFILE "# \n");
      printf(DATFILE "# It is best to plot this data as a scatter chart with no lines \n");
      printf(DATFILE "#   connecting the data points. \n");
      printf(DATFILE "# \n");
   }
   foreach my $keys (keys %counts) {
      #print "$keys = $counts{$keys}\n";
      if ($datflag > 0) {
         printf(DATFILE "%.6f %d \n", ($keys), $counts{$keys});
      }
   }
   # Add final data point (end of run)
   if ($datflag > 0) {
      close(DATFILE);
   } 
   
   
}


sub Per_File_Stats {
   if ($CmdCounter{"open"} > 0) {
      printf(" \n\n");
      printf("-- File Statistics (per file basis) --\n\n");
      printf("%-90s\t%15s\t%17s\t%15s\t%17s\n",
             "Filename", "    Read Bytes", "   Avg. Bytes/sec", "Write Bytes",
             "Avg. Bytes/sec");
      $junk1 = "=";
      for ($iloop=0; $iloop < 168; $iloop++) {
         $junk1 = $junk1 . "=";
      }
      printf("%s \n", $junk1);
      $junk = scalar (@File_Stats);
      for ($iloop=0; $iloop < $junk; $iloop++) {    # Loop over length of File_Stats
         if (exists $File_Stats[$iloop]->{file} ) {
            if ( (exists $File_Stats[$iloop]->{read_rate_count}) && (exists $File_Stats[$iloop]->{read_rate_sum}) ) {
               $junk1 = sprintf("%.2f",($File_Stats[$iloop]->{read_rate_sum}/$File_Stats[$iloop]->{read_rate_count}) );
            } else {
               $junk1 = 0;
            }
            if ( (exists $File_Stats[$iloop]->{write_rate_count}) && (exists $File_Stats[$iloop]->{write_rate_sum}) )  {
               $junk2 = sprintf("%.2f",($File_Stats[$iloop]->{write_rate_sum}/$File_Stats[$iloop]->{write_rate_count}) );
            } else {
               $junk2 = 0;
            }
            if (exists $File_Stats[$iloop]->{read_bytes}) {
               $junk3 = $File_Stats[$iloop]->{read_bytes};
            } else {
               $junk3 = 0;
            }
            if (exists $File_Stats[$iloop]->{write_bytes}) {
               $junk4 = $File_Stats[$iloop]->{write_bytes};
            } else {
               $junk4 = 0;
            }
            printf("%-90s\t%15s\t%17s\t%15s\t%17s\n",
                   $File_Stats[$iloop]->{file},
                   commify2($junk3), commify2($junk1),
                   commify2($junk4), commify2($junk2) );
         }
      }
      printf("DONE\n");
   }
}


sub by_number {
   if ($a < $b) {
      -1;
   } elsif ($a == $b) {
      0;
   } elsif ($a > $b) {
      1;
   }
}


/- Level 13 kernel check, shards 0..80. NO axioms. -/
import Collatz.KL13Data

set_option exponentiation.threshold 2000
set_option maxRecDepth 100000

namespace Collatz
namespace K13
open G50

set_option maxHeartbeats 0 in
theorem ok_0 : okRange check 12 0 2187 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_1 : okRange check 12 2187 4374 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_2 : okRange check 12 4374 6561 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_3 : okRange check 12 6561 8748 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_4 : okRange check 12 8748 10935 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_5 : okRange check 12 10935 13122 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_6 : okRange check 12 13122 15309 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_7 : okRange check 12 15309 17496 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_8 : okRange check 12 17496 19683 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_9 : okRange check 12 19683 21870 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_10 : okRange check 12 21870 24057 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_11 : okRange check 12 24057 26244 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_12 : okRange check 12 26244 28431 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_13 : okRange check 12 28431 30618 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_14 : okRange check 12 30618 32805 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_15 : okRange check 12 32805 34992 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_16 : okRange check 12 34992 37179 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_17 : okRange check 12 37179 39366 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_18 : okRange check 12 39366 41553 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_19 : okRange check 12 41553 43740 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_20 : okRange check 12 43740 45927 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_21 : okRange check 12 45927 48114 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_22 : okRange check 12 48114 50301 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_23 : okRange check 12 50301 52488 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_24 : okRange check 12 52488 54675 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_25 : okRange check 12 54675 56862 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_26 : okRange check 12 56862 59049 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_27 : okRange check 12 59049 61236 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_28 : okRange check 12 61236 63423 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_29 : okRange check 12 63423 65610 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_30 : okRange check 12 65610 67797 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_31 : okRange check 12 67797 69984 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_32 : okRange check 12 69984 72171 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_33 : okRange check 12 72171 74358 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_34 : okRange check 12 74358 76545 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_35 : okRange check 12 76545 78732 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_36 : okRange check 12 78732 80919 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_37 : okRange check 12 80919 83106 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_38 : okRange check 12 83106 85293 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_39 : okRange check 12 85293 87480 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_40 : okRange check 12 87480 89667 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_41 : okRange check 12 89667 91854 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_42 : okRange check 12 91854 94041 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_43 : okRange check 12 94041 96228 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_44 : okRange check 12 96228 98415 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_45 : okRange check 12 98415 100602 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_46 : okRange check 12 100602 102789 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_47 : okRange check 12 102789 104976 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_48 : okRange check 12 104976 107163 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_49 : okRange check 12 107163 109350 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_50 : okRange check 12 109350 111537 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_51 : okRange check 12 111537 113724 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_52 : okRange check 12 113724 115911 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_53 : okRange check 12 115911 118098 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_54 : okRange check 12 118098 120285 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_55 : okRange check 12 120285 122472 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_56 : okRange check 12 122472 124659 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_57 : okRange check 12 124659 126846 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_58 : okRange check 12 126846 129033 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_59 : okRange check 12 129033 131220 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_60 : okRange check 12 131220 133407 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_61 : okRange check 12 133407 135594 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_62 : okRange check 12 135594 137781 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_63 : okRange check 12 137781 139968 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_64 : okRange check 12 139968 142155 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_65 : okRange check 12 142155 144342 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_66 : okRange check 12 144342 146529 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_67 : okRange check 12 146529 148716 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_68 : okRange check 12 148716 150903 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_69 : okRange check 12 150903 153090 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_70 : okRange check 12 153090 155277 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_71 : okRange check 12 155277 157464 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_72 : okRange check 12 157464 159651 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_73 : okRange check 12 159651 161838 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_74 : okRange check 12 161838 164025 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_75 : okRange check 12 164025 166212 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_76 : okRange check 12 166212 168399 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_77 : okRange check 12 168399 170586 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_78 : okRange check 12 170586 172773 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_79 : okRange check 12 172773 174960 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok_80 : okRange check 12 174960 177147 = true := by decide +kernel

end K13
end Collatz

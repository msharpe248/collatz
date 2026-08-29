/-
  Collatz — A machine-verified density exponent at level k = 13:
  γ = 50·log₂(101195/100000) = 0.8567, beating the 2003 record 0.84.
  Same structure as KL12.lean; the certificate has 531441 classes.
  This file contains NO axioms and NO claim to prove the conjecture.
-/
import Collatz.KL13Check0
import Collatz.KL13Check1
import Collatz.KL13Check2

set_option exponentiation.threshold 2000
set_option maxRecDepth 100000

namespace Collatz
namespace K13
open G50

theorem check_all (i : ℕ) (hi : i < 531441) : check i = true := by
  rcases Nat.lt_or_ge i 2187 with h0 | h0
  · exact okRange_sound check 12 0 2187 ok_0 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 4374 with h1 | h1
  · exact okRange_sound check 12 2187 4374 ok_1 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 6561 with h2 | h2
  · exact okRange_sound check 12 4374 6561 ok_2 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 8748 with h3 | h3
  · exact okRange_sound check 12 6561 8748 ok_3 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 10935 with h4 | h4
  · exact okRange_sound check 12 8748 10935 ok_4 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 13122 with h5 | h5
  · exact okRange_sound check 12 10935 13122 ok_5 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 15309 with h6 | h6
  · exact okRange_sound check 12 13122 15309 ok_6 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 17496 with h7 | h7
  · exact okRange_sound check 12 15309 17496 ok_7 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 19683 with h8 | h8
  · exact okRange_sound check 12 17496 19683 ok_8 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 21870 with h9 | h9
  · exact okRange_sound check 12 19683 21870 ok_9 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 24057 with h10 | h10
  · exact okRange_sound check 12 21870 24057 ok_10 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 26244 with h11 | h11
  · exact okRange_sound check 12 24057 26244 ok_11 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 28431 with h12 | h12
  · exact okRange_sound check 12 26244 28431 ok_12 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 30618 with h13 | h13
  · exact okRange_sound check 12 28431 30618 ok_13 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 32805 with h14 | h14
  · exact okRange_sound check 12 30618 32805 ok_14 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 34992 with h15 | h15
  · exact okRange_sound check 12 32805 34992 ok_15 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 37179 with h16 | h16
  · exact okRange_sound check 12 34992 37179 ok_16 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 39366 with h17 | h17
  · exact okRange_sound check 12 37179 39366 ok_17 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 41553 with h18 | h18
  · exact okRange_sound check 12 39366 41553 ok_18 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 43740 with h19 | h19
  · exact okRange_sound check 12 41553 43740 ok_19 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 45927 with h20 | h20
  · exact okRange_sound check 12 43740 45927 ok_20 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 48114 with h21 | h21
  · exact okRange_sound check 12 45927 48114 ok_21 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 50301 with h22 | h22
  · exact okRange_sound check 12 48114 50301 ok_22 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 52488 with h23 | h23
  · exact okRange_sound check 12 50301 52488 ok_23 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 54675 with h24 | h24
  · exact okRange_sound check 12 52488 54675 ok_24 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 56862 with h25 | h25
  · exact okRange_sound check 12 54675 56862 ok_25 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 59049 with h26 | h26
  · exact okRange_sound check 12 56862 59049 ok_26 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 61236 with h27 | h27
  · exact okRange_sound check 12 59049 61236 ok_27 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 63423 with h28 | h28
  · exact okRange_sound check 12 61236 63423 ok_28 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 65610 with h29 | h29
  · exact okRange_sound check 12 63423 65610 ok_29 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 67797 with h30 | h30
  · exact okRange_sound check 12 65610 67797 ok_30 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 69984 with h31 | h31
  · exact okRange_sound check 12 67797 69984 ok_31 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 72171 with h32 | h32
  · exact okRange_sound check 12 69984 72171 ok_32 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 74358 with h33 | h33
  · exact okRange_sound check 12 72171 74358 ok_33 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 76545 with h34 | h34
  · exact okRange_sound check 12 74358 76545 ok_34 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 78732 with h35 | h35
  · exact okRange_sound check 12 76545 78732 ok_35 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 80919 with h36 | h36
  · exact okRange_sound check 12 78732 80919 ok_36 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 83106 with h37 | h37
  · exact okRange_sound check 12 80919 83106 ok_37 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 85293 with h38 | h38
  · exact okRange_sound check 12 83106 85293 ok_38 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 87480 with h39 | h39
  · exact okRange_sound check 12 85293 87480 ok_39 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 89667 with h40 | h40
  · exact okRange_sound check 12 87480 89667 ok_40 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 91854 with h41 | h41
  · exact okRange_sound check 12 89667 91854 ok_41 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 94041 with h42 | h42
  · exact okRange_sound check 12 91854 94041 ok_42 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 96228 with h43 | h43
  · exact okRange_sound check 12 94041 96228 ok_43 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 98415 with h44 | h44
  · exact okRange_sound check 12 96228 98415 ok_44 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 100602 with h45 | h45
  · exact okRange_sound check 12 98415 100602 ok_45 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 102789 with h46 | h46
  · exact okRange_sound check 12 100602 102789 ok_46 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 104976 with h47 | h47
  · exact okRange_sound check 12 102789 104976 ok_47 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 107163 with h48 | h48
  · exact okRange_sound check 12 104976 107163 ok_48 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 109350 with h49 | h49
  · exact okRange_sound check 12 107163 109350 ok_49 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 111537 with h50 | h50
  · exact okRange_sound check 12 109350 111537 ok_50 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 113724 with h51 | h51
  · exact okRange_sound check 12 111537 113724 ok_51 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 115911 with h52 | h52
  · exact okRange_sound check 12 113724 115911 ok_52 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 118098 with h53 | h53
  · exact okRange_sound check 12 115911 118098 ok_53 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 120285 with h54 | h54
  · exact okRange_sound check 12 118098 120285 ok_54 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 122472 with h55 | h55
  · exact okRange_sound check 12 120285 122472 ok_55 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 124659 with h56 | h56
  · exact okRange_sound check 12 122472 124659 ok_56 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 126846 with h57 | h57
  · exact okRange_sound check 12 124659 126846 ok_57 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 129033 with h58 | h58
  · exact okRange_sound check 12 126846 129033 ok_58 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 131220 with h59 | h59
  · exact okRange_sound check 12 129033 131220 ok_59 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 133407 with h60 | h60
  · exact okRange_sound check 12 131220 133407 ok_60 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 135594 with h61 | h61
  · exact okRange_sound check 12 133407 135594 ok_61 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 137781 with h62 | h62
  · exact okRange_sound check 12 135594 137781 ok_62 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 139968 with h63 | h63
  · exact okRange_sound check 12 137781 139968 ok_63 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 142155 with h64 | h64
  · exact okRange_sound check 12 139968 142155 ok_64 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 144342 with h65 | h65
  · exact okRange_sound check 12 142155 144342 ok_65 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 146529 with h66 | h66
  · exact okRange_sound check 12 144342 146529 ok_66 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 148716 with h67 | h67
  · exact okRange_sound check 12 146529 148716 ok_67 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 150903 with h68 | h68
  · exact okRange_sound check 12 148716 150903 ok_68 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 153090 with h69 | h69
  · exact okRange_sound check 12 150903 153090 ok_69 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 155277 with h70 | h70
  · exact okRange_sound check 12 153090 155277 ok_70 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 157464 with h71 | h71
  · exact okRange_sound check 12 155277 157464 ok_71 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 159651 with h72 | h72
  · exact okRange_sound check 12 157464 159651 ok_72 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 161838 with h73 | h73
  · exact okRange_sound check 12 159651 161838 ok_73 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 164025 with h74 | h74
  · exact okRange_sound check 12 161838 164025 ok_74 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 166212 with h75 | h75
  · exact okRange_sound check 12 164025 166212 ok_75 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 168399 with h76 | h76
  · exact okRange_sound check 12 166212 168399 ok_76 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 170586 with h77 | h77
  · exact okRange_sound check 12 168399 170586 ok_77 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 172773 with h78 | h78
  · exact okRange_sound check 12 170586 172773 ok_78 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 174960 with h79 | h79
  · exact okRange_sound check 12 172773 174960 ok_79 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 177147 with h80 | h80
  · exact okRange_sound check 12 174960 177147 ok_80 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 179334 with h81 | h81
  · exact okRange_sound check 12 177147 179334 ok_81 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 181521 with h82 | h82
  · exact okRange_sound check 12 179334 181521 ok_82 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 183708 with h83 | h83
  · exact okRange_sound check 12 181521 183708 ok_83 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 185895 with h84 | h84
  · exact okRange_sound check 12 183708 185895 ok_84 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 188082 with h85 | h85
  · exact okRange_sound check 12 185895 188082 ok_85 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 190269 with h86 | h86
  · exact okRange_sound check 12 188082 190269 ok_86 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 192456 with h87 | h87
  · exact okRange_sound check 12 190269 192456 ok_87 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 194643 with h88 | h88
  · exact okRange_sound check 12 192456 194643 ok_88 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 196830 with h89 | h89
  · exact okRange_sound check 12 194643 196830 ok_89 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 199017 with h90 | h90
  · exact okRange_sound check 12 196830 199017 ok_90 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 201204 with h91 | h91
  · exact okRange_sound check 12 199017 201204 ok_91 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 203391 with h92 | h92
  · exact okRange_sound check 12 201204 203391 ok_92 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 205578 with h93 | h93
  · exact okRange_sound check 12 203391 205578 ok_93 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 207765 with h94 | h94
  · exact okRange_sound check 12 205578 207765 ok_94 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 209952 with h95 | h95
  · exact okRange_sound check 12 207765 209952 ok_95 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 212139 with h96 | h96
  · exact okRange_sound check 12 209952 212139 ok_96 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 214326 with h97 | h97
  · exact okRange_sound check 12 212139 214326 ok_97 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 216513 with h98 | h98
  · exact okRange_sound check 12 214326 216513 ok_98 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 218700 with h99 | h99
  · exact okRange_sound check 12 216513 218700 ok_99 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 220887 with h100 | h100
  · exact okRange_sound check 12 218700 220887 ok_100 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 223074 with h101 | h101
  · exact okRange_sound check 12 220887 223074 ok_101 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 225261 with h102 | h102
  · exact okRange_sound check 12 223074 225261 ok_102 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 227448 with h103 | h103
  · exact okRange_sound check 12 225261 227448 ok_103 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 229635 with h104 | h104
  · exact okRange_sound check 12 227448 229635 ok_104 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 231822 with h105 | h105
  · exact okRange_sound check 12 229635 231822 ok_105 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 234009 with h106 | h106
  · exact okRange_sound check 12 231822 234009 ok_106 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 236196 with h107 | h107
  · exact okRange_sound check 12 234009 236196 ok_107 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 238383 with h108 | h108
  · exact okRange_sound check 12 236196 238383 ok_108 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 240570 with h109 | h109
  · exact okRange_sound check 12 238383 240570 ok_109 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 242757 with h110 | h110
  · exact okRange_sound check 12 240570 242757 ok_110 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 244944 with h111 | h111
  · exact okRange_sound check 12 242757 244944 ok_111 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 247131 with h112 | h112
  · exact okRange_sound check 12 244944 247131 ok_112 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 249318 with h113 | h113
  · exact okRange_sound check 12 247131 249318 ok_113 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 251505 with h114 | h114
  · exact okRange_sound check 12 249318 251505 ok_114 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 253692 with h115 | h115
  · exact okRange_sound check 12 251505 253692 ok_115 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 255879 with h116 | h116
  · exact okRange_sound check 12 253692 255879 ok_116 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 258066 with h117 | h117
  · exact okRange_sound check 12 255879 258066 ok_117 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 260253 with h118 | h118
  · exact okRange_sound check 12 258066 260253 ok_118 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 262440 with h119 | h119
  · exact okRange_sound check 12 260253 262440 ok_119 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 264627 with h120 | h120
  · exact okRange_sound check 12 262440 264627 ok_120 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 266814 with h121 | h121
  · exact okRange_sound check 12 264627 266814 ok_121 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 269001 with h122 | h122
  · exact okRange_sound check 12 266814 269001 ok_122 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 271188 with h123 | h123
  · exact okRange_sound check 12 269001 271188 ok_123 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 273375 with h124 | h124
  · exact okRange_sound check 12 271188 273375 ok_124 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 275562 with h125 | h125
  · exact okRange_sound check 12 273375 275562 ok_125 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 277749 with h126 | h126
  · exact okRange_sound check 12 275562 277749 ok_126 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 279936 with h127 | h127
  · exact okRange_sound check 12 277749 279936 ok_127 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 282123 with h128 | h128
  · exact okRange_sound check 12 279936 282123 ok_128 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 284310 with h129 | h129
  · exact okRange_sound check 12 282123 284310 ok_129 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 286497 with h130 | h130
  · exact okRange_sound check 12 284310 286497 ok_130 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 288684 with h131 | h131
  · exact okRange_sound check 12 286497 288684 ok_131 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 290871 with h132 | h132
  · exact okRange_sound check 12 288684 290871 ok_132 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 293058 with h133 | h133
  · exact okRange_sound check 12 290871 293058 ok_133 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 295245 with h134 | h134
  · exact okRange_sound check 12 293058 295245 ok_134 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 297432 with h135 | h135
  · exact okRange_sound check 12 295245 297432 ok_135 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 299619 with h136 | h136
  · exact okRange_sound check 12 297432 299619 ok_136 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 301806 with h137 | h137
  · exact okRange_sound check 12 299619 301806 ok_137 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 303993 with h138 | h138
  · exact okRange_sound check 12 301806 303993 ok_138 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 306180 with h139 | h139
  · exact okRange_sound check 12 303993 306180 ok_139 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 308367 with h140 | h140
  · exact okRange_sound check 12 306180 308367 ok_140 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 310554 with h141 | h141
  · exact okRange_sound check 12 308367 310554 ok_141 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 312741 with h142 | h142
  · exact okRange_sound check 12 310554 312741 ok_142 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 314928 with h143 | h143
  · exact okRange_sound check 12 312741 314928 ok_143 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 317115 with h144 | h144
  · exact okRange_sound check 12 314928 317115 ok_144 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 319302 with h145 | h145
  · exact okRange_sound check 12 317115 319302 ok_145 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 321489 with h146 | h146
  · exact okRange_sound check 12 319302 321489 ok_146 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 323676 with h147 | h147
  · exact okRange_sound check 12 321489 323676 ok_147 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 325863 with h148 | h148
  · exact okRange_sound check 12 323676 325863 ok_148 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 328050 with h149 | h149
  · exact okRange_sound check 12 325863 328050 ok_149 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 330237 with h150 | h150
  · exact okRange_sound check 12 328050 330237 ok_150 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 332424 with h151 | h151
  · exact okRange_sound check 12 330237 332424 ok_151 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 334611 with h152 | h152
  · exact okRange_sound check 12 332424 334611 ok_152 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 336798 with h153 | h153
  · exact okRange_sound check 12 334611 336798 ok_153 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 338985 with h154 | h154
  · exact okRange_sound check 12 336798 338985 ok_154 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 341172 with h155 | h155
  · exact okRange_sound check 12 338985 341172 ok_155 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 343359 with h156 | h156
  · exact okRange_sound check 12 341172 343359 ok_156 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 345546 with h157 | h157
  · exact okRange_sound check 12 343359 345546 ok_157 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 347733 with h158 | h158
  · exact okRange_sound check 12 345546 347733 ok_158 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 349920 with h159 | h159
  · exact okRange_sound check 12 347733 349920 ok_159 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 352107 with h160 | h160
  · exact okRange_sound check 12 349920 352107 ok_160 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 354294 with h161 | h161
  · exact okRange_sound check 12 352107 354294 ok_161 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 356481 with h162 | h162
  · exact okRange_sound check 12 354294 356481 ok_162 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 358668 with h163 | h163
  · exact okRange_sound check 12 356481 358668 ok_163 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 360855 with h164 | h164
  · exact okRange_sound check 12 358668 360855 ok_164 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 363042 with h165 | h165
  · exact okRange_sound check 12 360855 363042 ok_165 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 365229 with h166 | h166
  · exact okRange_sound check 12 363042 365229 ok_166 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 367416 with h167 | h167
  · exact okRange_sound check 12 365229 367416 ok_167 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 369603 with h168 | h168
  · exact okRange_sound check 12 367416 369603 ok_168 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 371790 with h169 | h169
  · exact okRange_sound check 12 369603 371790 ok_169 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 373977 with h170 | h170
  · exact okRange_sound check 12 371790 373977 ok_170 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 376164 with h171 | h171
  · exact okRange_sound check 12 373977 376164 ok_171 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 378351 with h172 | h172
  · exact okRange_sound check 12 376164 378351 ok_172 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 380538 with h173 | h173
  · exact okRange_sound check 12 378351 380538 ok_173 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 382725 with h174 | h174
  · exact okRange_sound check 12 380538 382725 ok_174 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 384912 with h175 | h175
  · exact okRange_sound check 12 382725 384912 ok_175 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 387099 with h176 | h176
  · exact okRange_sound check 12 384912 387099 ok_176 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 389286 with h177 | h177
  · exact okRange_sound check 12 387099 389286 ok_177 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 391473 with h178 | h178
  · exact okRange_sound check 12 389286 391473 ok_178 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 393660 with h179 | h179
  · exact okRange_sound check 12 391473 393660 ok_179 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 395847 with h180 | h180
  · exact okRange_sound check 12 393660 395847 ok_180 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 398034 with h181 | h181
  · exact okRange_sound check 12 395847 398034 ok_181 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 400221 with h182 | h182
  · exact okRange_sound check 12 398034 400221 ok_182 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 402408 with h183 | h183
  · exact okRange_sound check 12 400221 402408 ok_183 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 404595 with h184 | h184
  · exact okRange_sound check 12 402408 404595 ok_184 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 406782 with h185 | h185
  · exact okRange_sound check 12 404595 406782 ok_185 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 408969 with h186 | h186
  · exact okRange_sound check 12 406782 408969 ok_186 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 411156 with h187 | h187
  · exact okRange_sound check 12 408969 411156 ok_187 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 413343 with h188 | h188
  · exact okRange_sound check 12 411156 413343 ok_188 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 415530 with h189 | h189
  · exact okRange_sound check 12 413343 415530 ok_189 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 417717 with h190 | h190
  · exact okRange_sound check 12 415530 417717 ok_190 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 419904 with h191 | h191
  · exact okRange_sound check 12 417717 419904 ok_191 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 422091 with h192 | h192
  · exact okRange_sound check 12 419904 422091 ok_192 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 424278 with h193 | h193
  · exact okRange_sound check 12 422091 424278 ok_193 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 426465 with h194 | h194
  · exact okRange_sound check 12 424278 426465 ok_194 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 428652 with h195 | h195
  · exact okRange_sound check 12 426465 428652 ok_195 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 430839 with h196 | h196
  · exact okRange_sound check 12 428652 430839 ok_196 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 433026 with h197 | h197
  · exact okRange_sound check 12 430839 433026 ok_197 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 435213 with h198 | h198
  · exact okRange_sound check 12 433026 435213 ok_198 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 437400 with h199 | h199
  · exact okRange_sound check 12 435213 437400 ok_199 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 439587 with h200 | h200
  · exact okRange_sound check 12 437400 439587 ok_200 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 441774 with h201 | h201
  · exact okRange_sound check 12 439587 441774 ok_201 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 443961 with h202 | h202
  · exact okRange_sound check 12 441774 443961 ok_202 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 446148 with h203 | h203
  · exact okRange_sound check 12 443961 446148 ok_203 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 448335 with h204 | h204
  · exact okRange_sound check 12 446148 448335 ok_204 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 450522 with h205 | h205
  · exact okRange_sound check 12 448335 450522 ok_205 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 452709 with h206 | h206
  · exact okRange_sound check 12 450522 452709 ok_206 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 454896 with h207 | h207
  · exact okRange_sound check 12 452709 454896 ok_207 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 457083 with h208 | h208
  · exact okRange_sound check 12 454896 457083 ok_208 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 459270 with h209 | h209
  · exact okRange_sound check 12 457083 459270 ok_209 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 461457 with h210 | h210
  · exact okRange_sound check 12 459270 461457 ok_210 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 463644 with h211 | h211
  · exact okRange_sound check 12 461457 463644 ok_211 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 465831 with h212 | h212
  · exact okRange_sound check 12 463644 465831 ok_212 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 468018 with h213 | h213
  · exact okRange_sound check 12 465831 468018 ok_213 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 470205 with h214 | h214
  · exact okRange_sound check 12 468018 470205 ok_214 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 472392 with h215 | h215
  · exact okRange_sound check 12 470205 472392 ok_215 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 474579 with h216 | h216
  · exact okRange_sound check 12 472392 474579 ok_216 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 476766 with h217 | h217
  · exact okRange_sound check 12 474579 476766 ok_217 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 478953 with h218 | h218
  · exact okRange_sound check 12 476766 478953 ok_218 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 481140 with h219 | h219
  · exact okRange_sound check 12 478953 481140 ok_219 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 483327 with h220 | h220
  · exact okRange_sound check 12 481140 483327 ok_220 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 485514 with h221 | h221
  · exact okRange_sound check 12 483327 485514 ok_221 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 487701 with h222 | h222
  · exact okRange_sound check 12 485514 487701 ok_222 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 489888 with h223 | h223
  · exact okRange_sound check 12 487701 489888 ok_223 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 492075 with h224 | h224
  · exact okRange_sound check 12 489888 492075 ok_224 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 494262 with h225 | h225
  · exact okRange_sound check 12 492075 494262 ok_225 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 496449 with h226 | h226
  · exact okRange_sound check 12 494262 496449 ok_226 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 498636 with h227 | h227
  · exact okRange_sound check 12 496449 498636 ok_227 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 500823 with h228 | h228
  · exact okRange_sound check 12 498636 500823 ok_228 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 503010 with h229 | h229
  · exact okRange_sound check 12 500823 503010 ok_229 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 505197 with h230 | h230
  · exact okRange_sound check 12 503010 505197 ok_230 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 507384 with h231 | h231
  · exact okRange_sound check 12 505197 507384 ok_231 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 509571 with h232 | h232
  · exact okRange_sound check 12 507384 509571 ok_232 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 511758 with h233 | h233
  · exact okRange_sound check 12 509571 511758 ok_233 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 513945 with h234 | h234
  · exact okRange_sound check 12 511758 513945 ok_234 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 516132 with h235 | h235
  · exact okRange_sound check 12 513945 516132 ok_235 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 518319 with h236 | h236
  · exact okRange_sound check 12 516132 518319 ok_236 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 520506 with h237 | h237
  · exact okRange_sound check 12 518319 520506 ok_237 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 522693 with h238 | h238
  · exact okRange_sound check 12 520506 522693 ok_238 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 524880 with h239 | h239
  · exact okRange_sound check 12 522693 524880 ok_239 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 527067 with h240 | h240
  · exact okRange_sound check 12 524880 527067 ok_240 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 529254 with h241 | h241
  · exact okRange_sound check 12 527067 529254 ok_241 i (by omega) (by omega)
  exact okRange_sound check 12 529254 531441 ok_242 i (by omega) (by omega)

theorem classOK_all (m : ℕ) (hm : m < 3 ^ 13) (hm3 : m % 3 = 2) : ClassOK m := by
  have e : m = 3 * ((m - 2) / 3) + 2 := by omega
  have hi : (m - 2) / 3 < 531441 := by
    have : (3 : ℕ) ^ 13 = 1594323 := by norm_num
    omega
  rw [e]
  exact classOK_of_checkM _ (check_all _ hi)

theorem hbounds : ∀ m, m < 3 ^ 13 → m % 3 = 2 → 1 ≤ c m ∧ c m ≤ Cmax :=
  fun m hm hm3 => (classOK_all m hm hm3).1

theorem hcert : CertOK 13 pp qq c := by
  intro m hm hm3
  have h := classOK_all m hm hm3
  have e : (3 : ℕ) ^ 13 = 1594323 := by norm_num
  rw [e]
  exact h.2

set_option maxHeartbeats 0 in
theorem c_eight : c 8 = 387326 := by decide +kernel

/-- THE THEOREM at level 13: γ = 50·log₂(101195/100000) = 0.8567. -/
theorem density_bound (y : ℕ) :
    387326 * 101195 ^ (50 * y) * 100000 ^ 100 ≤
      reachesOneCount (80000 * 2 ^ y + 1) *
        (16777216 * 100000 ^ (50 * y) * 101195 ^ 100) := by
  classical
  have hgrow := growth_root 13 (by norm_num) pp qq Cmax (by norm_num [pp, qq])
    (by norm_num [qq]) c hbounds hcert (10 * (50 * y) + L 8) (50 * y) 8 rfl
    (by norm_num) (by norm_num) ⟨0, rfl⟩
  have h8 : (8 : ℕ) % 3 ^ 13 = 8 := by norm_num
  rw [h8, c_eight] at hgrow
  have hcap : cap (50 * y) * 8 = 80000 * 2 ^ y := by
    unfold cap
    have h1 : 50 * y / 50 = y := by omega
    have h2 : 50 * y % 50 = 0 := by omega
    rw [h1, h2, show rt 0 = 10000 by decide]
    ring
  have hsub : treeSet 8 (cap (50 * y) * 8)
      ⊆ @Finset.filter _ (fun n => ∃ t, terras_iter t n = 1)
        (Classical.decPred _) (Finset.range (80000 * 2 ^ y + 1)) := by
    intro n hn
    rw [mem_treeSet] at hn
    rw [Finset.mem_filter, Finset.mem_range]
    obtain ⟨j, hj, _⟩ := hn.2
    constructor
    · rw [hcap] at hn
      omega
    · exact ⟨j + 3, by
        rw [← terras_iter_add, hj, terras_iter_three_eight]⟩
  have hcnt : cnt 8 (cap (50 * y) * 8) ≤
      reachesOneCount (80000 * 2 ^ y + 1) := by
    unfold reachesOneCount cnt
    exact Finset.card_le_card hsub
  unfold pp qq Cmax at hgrow
  calc 387326 * 101195 ^ (50 * y) * 100000 ^ 100
      ≤ cnt 8 (cap (50 * y) * 8) * (16777216 * 100000 ^ (50 * y) * 101195 ^ 100) := hgrow
    _ ≤ reachesOneCount (80000 * 2 ^ y + 1) *
        (16777216 * 100000 ^ (50 * y) * 101195 ^ 100) :=
        Nat.mul_le_mul_right _ hcnt

end K13
end Collatz

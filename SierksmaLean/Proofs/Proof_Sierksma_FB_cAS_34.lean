import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem proof_Sierksma_FB_cAS_34 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [61, 654, 1403]) (Sierksma.FB.xa0K 22 173) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 656, 1403]) (Sierksma.FB.xa0K 22 174) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 657, 1403]) (Sierksma.FB.xa0K 22 175) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 658, 1403]) (Sierksma.FB.xa0K 22 176) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 661, 1403]) (Sierksma.FB.xa0K 22 177) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 664, 1403]) (Sierksma.FB.xa0K 22 178) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 665, 1403]) (Sierksma.FB.xa0K 22 179) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 670, 1403]) (Sierksma.FB.xa0K 22 180) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 671, 1403]) (Sierksma.FB.xa0K 22 181) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 672, 1403]) (Sierksma.FB.xa0K 22 182) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 673, 1403]) (Sierksma.FB.xa0K 22 183) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 674, 1403]) (Sierksma.FB.xa0K 22 184) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 675, 1403]) (Sierksma.FB.xa0K 22 185) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 684, 1403]) (Sierksma.FB.xa0K 22 186) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 685, 1403]) (Sierksma.FB.xa0K 22 187) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 686, 1403]) (Sierksma.FB.xa0K 22 188) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 687, 1403]) (Sierksma.FB.xa0K 22 189) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 688, 1403]) (Sierksma.FB.xa0K 22 190) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 689, 1403]) (Sierksma.FB.xa0K 22 191) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 696, 1403]) (Sierksma.FB.xa0K 22 192) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 698, 1403]) (Sierksma.FB.xa0K 22 193) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 699, 1403]) (Sierksma.FB.xa0K 22 194) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 701, 1403]) (Sierksma.FB.xa0K 22 195) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 704, 1403]) (Sierksma.FB.xa0K 22 196) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 705, 1403]) (Sierksma.FB.xa0K 22 197) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 707, 1403]) (Sierksma.FB.xa0K 22 198) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 708, 1403]) (Sierksma.FB.xa0K 22 199) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 709, 1403]) (Sierksma.FB.xa0K 22 200) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 710, 1403]) (Sierksma.FB.xa0K 22 201) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 711, 1403]) (Sierksma.FB.xa0K 22 202) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 712, 1403]) (Sierksma.FB.xa0K 22 203) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 741, 1403]) (Sierksma.FB.xa0K 22 204) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 742, 1403]) (Sierksma.FB.xa0K 22 205) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 743, 1403]) (Sierksma.FB.xa0K 22 206) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 746, 1403]) (Sierksma.FB.xa0K 22 207) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 750, 1403]) (Sierksma.FB.xa0K 22 208) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 752, 1403]) (Sierksma.FB.xa0K 22 209) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 753, 1403]) (Sierksma.FB.xa0K 22 210) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 755, 1403]) (Sierksma.FB.xa0K 22 211) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 766, 1403]) (Sierksma.FB.xa0K 22 212) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 767, 1403]) (Sierksma.FB.xa0K 22 213) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 770, 1403]) (Sierksma.FB.xa0K 22 214) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 771, 1403]) (Sierksma.FB.xa0K 22 215) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 777, 1403]) (Sierksma.FB.xa0K 22 216) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 778, 1403]) (Sierksma.FB.xa0K 22 217) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 779, 1403]) (Sierksma.FB.xa0K 22 218) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 780, 1403]) (Sierksma.FB.xa0K 22 219) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 781, 1403]) (Sierksma.FB.xa0K 22 220) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 782, 1403]) (Sierksma.FB.xa0K 22 221) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 784, 1403]) (Sierksma.FB.xa0K 22 222) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 785, 1403]) (Sierksma.FB.xa0K 22 223) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 786, 1403]) (Sierksma.FB.xa0K 22 224) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 789, 1403]) (Sierksma.FB.xa0K 22 225) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 812, 1403]) (Sierksma.FB.xa0K 22 226) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 813, 1403]) (Sierksma.FB.xa0K 22 227) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 822, 1403]) (Sierksma.FB.xa0K 22 228) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 823, 1403]) (Sierksma.FB.xa0K 22 229) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 824, 1403]) (Sierksma.FB.xa0K 22 230) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 827, 1403]) (Sierksma.FB.xa0K 22 231) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 830, 1403]) (Sierksma.FB.xa0K 22 232) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 831, 1403]) (Sierksma.FB.xa0K 22 233) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 832, 1403]) (Sierksma.FB.xa0K 22 234) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 833, 1403]) (Sierksma.FB.xa0K 22 235) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 834, 1403]) (Sierksma.FB.xa0K 22 236) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 835, 1403]) (Sierksma.FB.xa0K 22 237) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 842, 1403]) (Sierksma.FB.xa0K 22 238) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 844, 1403]) (Sierksma.FB.xa0K 22 239) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 845, 1403]) (Sierksma.FB.xa0K 22 240) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 847, 1403]) (Sierksma.FB.xa0K 22 241) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 874, 1403]) (Sierksma.FB.xa0K 22 242) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 875, 1403]) (Sierksma.FB.xa0K 22 243) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 877, 1403]) (Sierksma.FB.xa0K 22 244) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 878, 1403]) (Sierksma.FB.xa0K 22 245) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 879, 1403]) (Sierksma.FB.xa0K 22 246) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 882, 1403]) (Sierksma.FB.xa0K 22 247) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 892, 1403]) (Sierksma.FB.xa0K 22 248) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 893, 1403]) (Sierksma.FB.xa0K 22 249) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 894, 1403]) (Sierksma.FB.xa0K 22 250) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 897, 1403]) (Sierksma.FB.xa0K 22 251) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 901, 1403]) (Sierksma.FB.xa0K 22 252) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 903, 1403]) (Sierksma.FB.xa0K 22 253) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 904, 1403]) (Sierksma.FB.xa0K 22 254) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 906, 1403]) (Sierksma.FB.xa0K 22 255) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1357, 1403]) (Sierksma.FB.xa0K 22 256) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1358, 1403]) (Sierksma.FB.xa0K 22 257) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1359, 1403]) (Sierksma.FB.xa0K 22 258) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1360, 1403]) (Sierksma.FB.xa0K 22 259) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1361, 1403]) (Sierksma.FB.xa0K 22 260) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1362, 1403]) (Sierksma.FB.xa0K 22 261) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1364, 1403]) (Sierksma.FB.xa0K 22 262) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1365, 1403]) (Sierksma.FB.xa0K 22 263) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1366, 1403]) (Sierksma.FB.xa0K 22 264) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1369, 1403]) (Sierksma.FB.xa0K 22 265) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1376, 1403]) (Sierksma.FB.xa0K 22 266) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1377, 1403]) (Sierksma.FB.xa0K 22 267) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1378, 1403]) (Sierksma.FB.xa0K 22 268) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1381, 1403]) (Sierksma.FB.xa0K 22 269) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1384, 1403]) (Sierksma.FB.xa0K 22 270) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1385, 1403]) (Sierksma.FB.xa0K 22 271) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1386, 1403]) (Sierksma.FB.xa0K 22 272) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1388, 1403]) (Sierksma.FB.xa0K 22 273) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1389, 1403]) (Sierksma.FB.xa0K 22 274) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1390, 1403]) (Sierksma.FB.xa0K 22 275) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1410]) (Sierksma.FB.xa0K 22 276) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1411]) (Sierksma.FB.xa0K 22 277) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1412]) (Sierksma.FB.xa0K 22 278) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1413]) (Sierksma.FB.xa0K 22 279) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1414]) (Sierksma.FB.xa0K 22 280) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1415]) (Sierksma.FB.xa0K 22 281) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1422]) (Sierksma.FB.xa0K 22 282) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1424]) (Sierksma.FB.xa0K 22 283) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1425]) (Sierksma.FB.xa0K 22 284) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1427]) (Sierksma.FB.xa0K 22 285) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1429]) (Sierksma.FB.xa0K 22 286) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1430]) (Sierksma.FB.xa0K 22 287) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1431]) (Sierksma.FB.xa0K 22 288) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1434]) (Sierksma.FB.xa0K 22 289) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1447]) (Sierksma.FB.xa0K 22 290) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1450]) (Sierksma.FB.xa0K 22 291) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1451]) (Sierksma.FB.xa0K 22 292) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1452]) (Sierksma.FB.xa0K 22 293) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1472]) (Sierksma.FB.xa0K 22 294) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1473]) (Sierksma.FB.xa0K 22 295) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1474]) (Sierksma.FB.xa0K 22 296) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1477]) (Sierksma.FB.xa0K 22 297) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1481]) (Sierksma.FB.xa0K 22 298) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1483]) (Sierksma.FB.xa0K 22 299) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1484]) (Sierksma.FB.xa0K 22 300) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1486]) (Sierksma.FB.xa0K 22 301) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1496]) (Sierksma.FB.xa0K 22 302) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1497]) (Sierksma.FB.xa0K 22 303) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1498]) (Sierksma.FB.xa0K 22 304) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1500]) (Sierksma.FB.xa0K 22 305) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1501]) (Sierksma.FB.xa0K 22 306) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1502]) (Sierksma.FB.xa0K 22 307) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1505]) (Sierksma.FB.xa0K 22 308) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1508]) (Sierksma.FB.xa0K 22 309) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1509]) (Sierksma.FB.xa0K 22 310) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1510]) (Sierksma.FB.xa0K 22 311) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1519]) (Sierksma.FB.xa0K 22 312) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1520]) (Sierksma.FB.xa0K 22 313) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1521]) (Sierksma.FB.xa0K 22 314) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1522]) (Sierksma.FB.xa0K 22 315) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1523]) (Sierksma.FB.xa0K 22 316) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1524]) (Sierksma.FB.xa0K 22 317) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1526]) (Sierksma.FB.xa0K 22 318) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1527]) (Sierksma.FB.xa0K 22 319) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1528]) (Sierksma.FB.xa0K 22 320) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1531]) (Sierksma.FB.xa0K 22 321) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1562]) (Sierksma.FB.xa0K 22 322) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1564]) (Sierksma.FB.xa0K 22 323) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1565]) (Sierksma.FB.xa0K 22 324) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1567]) (Sierksma.FB.xa0K 22 325) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1571]) (Sierksma.FB.xa0K 22 326) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1574]) (Sierksma.FB.xa0K 22 327) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1575]) (Sierksma.FB.xa0K 22 328) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1576]) (Sierksma.FB.xa0K 22 329) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1577]) (Sierksma.FB.xa0K 22 330) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1578]) (Sierksma.FB.xa0K 22 331) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1579]) (Sierksma.FB.xa0K 22 332) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1580]) (Sierksma.FB.xa0K 22 333) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1581]) (Sierksma.FB.xa0K 22 334) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1582]) (Sierksma.FB.xa0K 22 335) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1589]) (Sierksma.FB.xa0K 22 336) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1591]) (Sierksma.FB.xa0K 22 337) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1592]) (Sierksma.FB.xa0K 22 338) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1594]) (Sierksma.FB.xa0K 22 339) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1605]) (Sierksma.FB.xa0K 22 340) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1607]) (Sierksma.FB.xa0K 22 341) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1608]) (Sierksma.FB.xa0K 22 342) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1610]) (Sierksma.FB.xa0K 22 343) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1617]) (Sierksma.FB.xa0K 22 344) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1618]) (Sierksma.FB.xa0K 22 345) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1619]) (Sierksma.FB.xa0K 22 346) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1620]) (Sierksma.FB.xa0K 22 347) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1621]) (Sierksma.FB.xa0K 22 348) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1622]) (Sierksma.FB.xa0K 22 349) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1623]) (Sierksma.FB.xa0K 22 350) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1624]) (Sierksma.FB.xa0K 22 351) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1625]) (Sierksma.FB.xa0K 22 352) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1628]) (Sierksma.FB.xa0K 22 353) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1632]) (Sierksma.FB.xa0K 22 354) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1634]) (Sierksma.FB.xa0K 22 355) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1635]) (Sierksma.FB.xa0K 22 356) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1637]) (Sierksma.FB.xa0K 22 357) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1668]) (Sierksma.FB.xa0K 22 358) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1671]) (Sierksma.FB.xa0K 22 359) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1672]) (Sierksma.FB.xa0K 22 360) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1673]) (Sierksma.FB.xa0K 22 361) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1675]) (Sierksma.FB.xa0K 22 362) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1676]) (Sierksma.FB.xa0K 22 363) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1677]) (Sierksma.FB.xa0K 22 364) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1678]) (Sierksma.FB.xa0K 22 365) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1679]) (Sierksma.FB.xa0K 22 366) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1680]) (Sierksma.FB.xa0K 22 367) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1689]) (Sierksma.FB.xa0K 22 368) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1690]) (Sierksma.FB.xa0K 22 369) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1691]) (Sierksma.FB.xa0K 22 370) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1694]) (Sierksma.FB.xa0K 22 371) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1697]) (Sierksma.FB.xa0K 22 372) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1698]) (Sierksma.FB.xa0K 22 373) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1699]) (Sierksma.FB.xa0K 22 374) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1701]) (Sierksma.FB.xa0K 22 375) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1702]) (Sierksma.FB.xa0K 22 376) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1703]) (Sierksma.FB.xa0K 22 377) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1713]) (Sierksma.FB.xa0K 22 378) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1715]) (Sierksma.FB.xa0K 22 379) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1716]) (Sierksma.FB.xa0K 22 380) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1718]) (Sierksma.FB.xa0K 22 381) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1722]) (Sierksma.FB.xa0K 22 382) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1725]) (Sierksma.FB.xa0K 22 383) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1726]) (Sierksma.FB.xa0K 22 384) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1727]) (Sierksma.FB.xa0K 22 385) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1747]) (Sierksma.FB.xa0K 22 386) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1748]) (Sierksma.FB.xa0K 22 387) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1749]) (Sierksma.FB.xa0K 22 388) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1752]) (Sierksma.FB.xa0K 22 389) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1765]) (Sierksma.FB.xa0K 22 390) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1768]) (Sierksma.FB.xa0K 22 391) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1769]) (Sierksma.FB.xa0K 22 392) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1770]) (Sierksma.FB.xa0K 22 393) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1772]) (Sierksma.FB.xa0K 22 394) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1774]) (Sierksma.FB.xa0K 22 395) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1775]) (Sierksma.FB.xa0K 22 396) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1777]) (Sierksma.FB.xa0K 22 397) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1784]) (Sierksma.FB.xa0K 22 398) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1785]) (Sierksma.FB.xa0K 22 399) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1786]) (Sierksma.FB.xa0K 22 400) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1787]) (Sierksma.FB.xa0K 22 401) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1788]) (Sierksma.FB.xa0K 22 402) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1789]) (Sierksma.FB.xa0K 22 403) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1809]) (Sierksma.FB.xa0K 22 404) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1810]) (Sierksma.FB.xa0K 22 405) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1811]) (Sierksma.FB.xa0K 22 406) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1813]) (Sierksma.FB.xa0K 22 407) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1814]) (Sierksma.FB.xa0K 22 408) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1815]) (Sierksma.FB.xa0K 22 409) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1818]) (Sierksma.FB.xa0K 22 410) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1821]) (Sierksma.FB.xa0K 22 411) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1822]) (Sierksma.FB.xa0K 22 412) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1823]) (Sierksma.FB.xa0K 22 413) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1830]) (Sierksma.FB.xa0K 22 414) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1833]) (Sierksma.FB.xa0K 22 415) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1834]) (Sierksma.FB.xa0K 22 416) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1835]) (Sierksma.FB.xa0K 22 417) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1837]) (Sierksma.FB.xa0K 22 418) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1838]) (Sierksma.FB.xa0K 22 419) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1839]) (Sierksma.FB.xa0K 22 420) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1840]) (Sierksma.FB.xa0K 22 421) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1841]) (Sierksma.FB.xa0K 22 422) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 1403, 1842]) (Sierksma.FB.xa0K 22 423) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits (Sierksma.FB.pairSort (Sierksma.FB.R1.getD 1 0) 28)) (Sierksma.FB.KS 1 28) 5 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits (Sierksma.FB.pairSort (Sierksma.FB.R1.getD 1 0) 41)) (Sierksma.FB.KS 1 41) 5 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits (Sierksma.FB.pairSort (Sierksma.FB.R1.getD 3 0) 52)) (Sierksma.FB.KS 3 52) 5 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits (Sierksma.FB.pairSort (Sierksma.FB.R1.getD 4 0) 81)) (Sierksma.FB.KS 4 81) 5 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits (Sierksma.FB.pairSort (Sierksma.FB.R1.getD 3 0) 197)) (Sierksma.FB.KS 3 197) 5 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits (Sierksma.FB.pairSort (Sierksma.FB.R1.getD 4 0) 262)) (Sierksma.FB.KS 4 262) 5 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 130, 1402]) (Sierksma.FB.xa0K 29 0) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 131, 1402]) (Sierksma.FB.xa0K 29 1) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 134, 1402]) (Sierksma.FB.xa0K 29 2) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 135, 1402]) (Sierksma.FB.xa0K 29 3) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 137, 1402]) (Sierksma.FB.xa0K 29 4) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 138, 1402]) (Sierksma.FB.xa0K 29 5) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 143, 1402]) (Sierksma.FB.xa0K 29 6) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 144, 1402]) (Sierksma.FB.xa0K 29 7) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 145, 1402]) (Sierksma.FB.xa0K 29 8) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 146, 1402]) (Sierksma.FB.xa0K 29 9) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 147, 1402]) (Sierksma.FB.xa0K 29 10) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 148, 1402]) (Sierksma.FB.xa0K 29 11) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 151, 1402]) (Sierksma.FB.xa0K 29 12) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 152, 1402]) (Sierksma.FB.xa0K 29 13) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 154, 1402]) (Sierksma.FB.xa0K 29 14) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 155, 1402]) (Sierksma.FB.xa0K 29 15) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 156, 1402]) (Sierksma.FB.xa0K 29 16) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 157, 1402]) (Sierksma.FB.xa0K 29 17) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 158, 1402]) (Sierksma.FB.xa0K 29 18) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 159, 1402]) (Sierksma.FB.xa0K 29 19) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 170, 1402]) (Sierksma.FB.xa0K 29 20) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 171, 1402]) (Sierksma.FB.xa0K 29 21) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 174, 1402]) (Sierksma.FB.xa0K 29 22) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 175, 1402]) (Sierksma.FB.xa0K 29 23) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 178, 1402]) (Sierksma.FB.xa0K 29 24) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 179, 1402]) (Sierksma.FB.xa0K 29 25) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 188, 1402]) (Sierksma.FB.xa0K 29 26) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 189, 1402]) (Sierksma.FB.xa0K 29 27) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 190, 1402]) (Sierksma.FB.xa0K 29 28) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 192, 1402]) (Sierksma.FB.xa0K 29 29) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 193, 1402]) (Sierksma.FB.xa0K 29 30) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 194, 1402]) (Sierksma.FB.xa0K 29 31) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 197, 1402]) (Sierksma.FB.xa0K 29 32) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 198, 1402]) (Sierksma.FB.xa0K 29 33) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 200, 1402]) (Sierksma.FB.xa0K 29 34) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 201, 1402]) (Sierksma.FB.xa0K 29 35) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 202, 1402]) (Sierksma.FB.xa0K 29 36) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 204, 1402]) (Sierksma.FB.xa0K 29 37) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 205, 1402]) (Sierksma.FB.xa0K 29 38) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 206, 1402]) (Sierksma.FB.xa0K 29 39) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 257, 1402]) (Sierksma.FB.xa0K 29 40) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 258, 1402]) (Sierksma.FB.xa0K 29 41) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 260, 1402]) (Sierksma.FB.xa0K 29 42) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 261, 1402]) (Sierksma.FB.xa0K 29 43) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 262, 1402]) (Sierksma.FB.xa0K 29 44) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 263, 1402]) (Sierksma.FB.xa0K 29 45) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 264, 1402]) (Sierksma.FB.xa0K 29 46) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 265, 1402]) (Sierksma.FB.xa0K 29 47) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 267, 1402]) (Sierksma.FB.xa0K 29 48) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 268, 1402]) (Sierksma.FB.xa0K 29 49) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 271, 1402]) (Sierksma.FB.xa0K 29 50) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 272, 1402]) (Sierksma.FB.xa0K 29 51) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 274, 1402]) (Sierksma.FB.xa0K 29 52) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 275, 1402]) (Sierksma.FB.xa0K 29 53) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 276, 1402]) (Sierksma.FB.xa0K 29 54) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 277, 1402]) (Sierksma.FB.xa0K 29 55) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 278, 1402]) (Sierksma.FB.xa0K 29 56) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 279, 1402]) (Sierksma.FB.xa0K 29 57) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 282, 1402]) (Sierksma.FB.xa0K 29 58) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 283, 1402]) (Sierksma.FB.xa0K 29 59) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 297, 1402]) (Sierksma.FB.xa0K 29 60) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 298, 1402]) (Sierksma.FB.xa0K 29 61) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 299, 1402]) (Sierksma.FB.xa0K 29 62) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 300, 1402]) (Sierksma.FB.xa0K 29 63) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 301, 1402]) (Sierksma.FB.xa0K 29 64) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 302, 1402]) (Sierksma.FB.xa0K 29 65) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 304, 1402]) (Sierksma.FB.xa0K 29 66) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 305, 1402]) (Sierksma.FB.xa0K 29 67) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 306, 1402]) (Sierksma.FB.xa0K 29 68) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 308, 1402]) (Sierksma.FB.xa0K 29 69) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 309, 1402]) (Sierksma.FB.xa0K 29 70) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 310, 1402]) (Sierksma.FB.xa0K 29 71) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 312, 1402]) (Sierksma.FB.xa0K 29 72) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 313, 1402]) (Sierksma.FB.xa0K 29 73) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 314, 1402]) (Sierksma.FB.xa0K 29 74) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 315, 1402]) (Sierksma.FB.xa0K 29 75) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 316, 1402]) (Sierksma.FB.xa0K 29 76) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 317, 1402]) (Sierksma.FB.xa0K 29 77) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 324, 1402]) (Sierksma.FB.xa0K 29 78) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 325, 1402]) (Sierksma.FB.xa0K 29 79) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 326, 1402]) (Sierksma.FB.xa0K 29 80) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 327, 1402]) (Sierksma.FB.xa0K 29 81) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 328, 1402]) (Sierksma.FB.xa0K 29 82) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 329, 1402]) (Sierksma.FB.xa0K 29 83) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 331, 1402]) (Sierksma.FB.xa0K 29 84) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 332, 1402]) (Sierksma.FB.xa0K 29 85) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 333, 1402]) (Sierksma.FB.xa0K 29 86) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 335, 1402]) (Sierksma.FB.xa0K 29 87) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 336, 1402]) (Sierksma.FB.xa0K 29 88) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 337, 1402]) (Sierksma.FB.xa0K 29 89) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 340, 1402]) (Sierksma.FB.xa0K 29 90) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 341, 1402]) (Sierksma.FB.xa0K 29 91) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 342, 1402]) (Sierksma.FB.xa0K 29 92) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 343, 1402]) (Sierksma.FB.xa0K 29 93) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 344, 1402]) (Sierksma.FB.xa0K 29 94) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 345, 1402]) (Sierksma.FB.xa0K 29 95) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 405, 1402]) (Sierksma.FB.xa0K 29 96) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 406, 1402]) (Sierksma.FB.xa0K 29 97) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 407, 1402]) (Sierksma.FB.xa0K 29 98) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 408, 1402]) (Sierksma.FB.xa0K 29 99) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 409, 1402]) (Sierksma.FB.xa0K 29 100) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 410, 1402]) (Sierksma.FB.xa0K 29 101) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 412, 1402]) (Sierksma.FB.xa0K 29 102) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 413, 1402]) (Sierksma.FB.xa0K 29 103) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 414, 1402]) (Sierksma.FB.xa0K 29 104) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 416, 1402]) (Sierksma.FB.xa0K 29 105) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 417, 1402]) (Sierksma.FB.xa0K 29 106) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 418, 1402]) (Sierksma.FB.xa0K 29 107) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 420, 1402]) (Sierksma.FB.xa0K 29 108) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 421, 1402]) (Sierksma.FB.xa0K 29 109) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 422, 1402]) (Sierksma.FB.xa0K 29 110) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 423, 1402]) (Sierksma.FB.xa0K 29 111) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 424, 1402]) (Sierksma.FB.xa0K 29 112) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 425, 1402]) (Sierksma.FB.xa0K 29 113) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 432, 1402]) (Sierksma.FB.xa0K 29 114) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 433, 1402]) (Sierksma.FB.xa0K 29 115) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 434, 1402]) (Sierksma.FB.xa0K 29 116) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 435, 1402]) (Sierksma.FB.xa0K 29 117) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 436, 1402]) (Sierksma.FB.xa0K 29 118) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 437, 1402]) (Sierksma.FB.xa0K 29 119) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 439, 1402]) (Sierksma.FB.xa0K 29 120) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 440, 1402]) (Sierksma.FB.xa0K 29 121) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 441, 1402]) (Sierksma.FB.xa0K 29 122) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 443, 1402]) (Sierksma.FB.xa0K 29 123) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 444, 1402]) (Sierksma.FB.xa0K 29 124) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 445, 1402]) (Sierksma.FB.xa0K 29 125) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 448, 1402]) (Sierksma.FB.xa0K 29 126) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 449, 1402]) (Sierksma.FB.xa0K 29 127) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 450, 1402]) (Sierksma.FB.xa0K 29 128) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 451, 1402]) (Sierksma.FB.xa0K 29 129) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 452, 1402]) (Sierksma.FB.xa0K 29 130) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 453, 1402]) (Sierksma.FB.xa0K 29 131) 4 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 140, 467, 1402]) (Sierksma.FB.xa0K 30 0) 3 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 141, 467, 1402]) (Sierksma.FB.xa0K 30 1) 3 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 161, 467, 1402]) (Sierksma.FB.xa0K 30 2) 3 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 162, 467, 1402]) (Sierksma.FB.xa0K 30 3) 3 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 163, 467, 1402]) (Sierksma.FB.xa0K 30 4) 3 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 165, 467, 1402]) (Sierksma.FB.xa0K 30 5) 3 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 166, 467, 1402]) (Sierksma.FB.xa0K 30 6) 3 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 167, 467, 1402]) (Sierksma.FB.xa0K 30 7) 3 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 181, 467, 1402]) (Sierksma.FB.xa0K 30 8) 3 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 182, 467, 1402]) (Sierksma.FB.xa0K 30 9) 3 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 183, 467, 1402]) (Sierksma.FB.xa0K 30 10) 3 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 184, 467, 1402]) (Sierksma.FB.xa0K 30 11) 3 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 185, 467, 1402]) (Sierksma.FB.xa0K 30 12) 3 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 186, 467, 1402]) (Sierksma.FB.xa0K 30 13) 3 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 208, 467, 1402]) (Sierksma.FB.xa0K 30 14) 3 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 209, 467, 1402]) (Sierksma.FB.xa0K 30 15) 3 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 210, 467, 1402]) (Sierksma.FB.xa0K 30 16) 3 (Sierksma.FB.capsOf 3 4)) := by
  have r_AS_61_1403_x174 : Sierksma.FB.runR [0x726112fc1499091116104a22] [61, 654, 1403] (Sierksma.FB.xa0K 22 173) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x174 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x174 (by simp)
  have r_AS_61_1403_x175 : Sierksma.FB.runR [0x82107239473111116104a2200033] [61, 656, 1403] (Sierksma.FB.xa0K 22 174) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x175 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x175 (by simp)
  have r_AS_61_1403_x176 : Sierksma.FB.runR [0x82107239473111116104a2200033] [61, 657, 1403] (Sierksma.FB.xa0K 22 175) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x176 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x176 (by simp)
  have r_AS_61_1403_x177 : Sierksma.FB.runR [0x82107239473111116104a22] [61, 658, 1403] (Sierksma.FB.xa0K 22 176) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x177 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x177 (by simp)
  have r_AS_61_1403_x178 : Sierksma.FB.runR [0x82107239473111116104a22] [61, 661, 1403] (Sierksma.FB.xa0K 22 177) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x178 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x178 (by simp)
  have r_AS_61_1403_x179 : Sierksma.FB.runR [0x72710725138fc138f4104a22] [61, 664, 1403] (Sierksma.FB.xa0K 22 178) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x179 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x179 (by simp)
  have r_AS_61_1403_x180 : Sierksma.FB.runR [0x72710725138fc138f4104a22] [61, 665, 1403] (Sierksma.FB.xa0K 22 179) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x180 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x180 (by simp)
  have r_AS_61_1403_x181 : Sierksma.FB.runR [0x81990811945c4938f4104a2200033] [61, 670, 1403] (Sierksma.FB.xa0K 22 180) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x181 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x181 (by simp)
  have r_AS_61_1403_x182 : Sierksma.FB.runR [0x81990811945c4938f4104a2200033] [61, 671, 1403] (Sierksma.FB.xa0K 22 181) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x182 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x182 (by simp)
  have r_AS_61_1403_x183 : Sierksma.FB.runR [0x21bb12398945c4938f4104a22] [61, 672, 1403] (Sierksma.FB.xa0K 22 182) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x183 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x183 (by simp)
  have r_AS_61_1403_x184 : Sierksma.FB.runR [0x21bb12398945c4938f4104a22] [61, 673, 1403] (Sierksma.FB.xa0K 22 183) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x184 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x184 (by simp)
  have r_AS_61_1403_x185 : Sierksma.FB.runR [0x21bb12398945c4938f4104a22] [61, 674, 1403] (Sierksma.FB.xa0K 22 184) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x185 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x185 (by simp)
  have r_AS_61_1403_x186 : Sierksma.FB.runR [0x21bb12398945c4938f4104a22] [61, 675, 1403] (Sierksma.FB.xa0K 22 185) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x186 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x186 (by simp)
  have r_AS_61_1403_x187 : Sierksma.FB.runR [0x358145c494bf694bf0104a2200033] [61, 684, 1403] (Sierksma.FB.xa0K 22 186) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x187 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x187 (by simp)
  have r_AS_61_1403_x188 : Sierksma.FB.runR [0x358145c494bf694bf0104a2200033] [61, 685, 1403] (Sierksma.FB.xa0K 22 187) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x188 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x188 (by simp)
  have r_AS_61_1403_x189 : Sierksma.FB.runR [0x358145c494bf694bf0104a22] [61, 686, 1403] (Sierksma.FB.xa0K 22 188) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x189 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x189 (by simp)
  have r_AS_61_1403_x190 : Sierksma.FB.runR [0x358145c494bf694bf0104a22] [61, 687, 1403] (Sierksma.FB.xa0K 22 189) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x190 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x190 (by simp)
  have r_AS_61_1403_x191 : Sierksma.FB.runR [0x358145c494bf694bf0104a22] [61, 688, 1403] (Sierksma.FB.xa0K 22 190) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x191 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x191 (by simp)
  have r_AS_61_1403_x192 : Sierksma.FB.runR [0x358145c494bf694bf0104a22] [61, 689, 1403] (Sierksma.FB.xa0K 22 191) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x192 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x192 (by simp)
  have r_AS_61_1403_x193 : Sierksma.FB.runR [0x811912fc1111e11116104a2200033] [61, 696, 1403] (Sierksma.FB.xa0K 22 192) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x193 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x193 (by simp)
  have r_AS_61_1403_x194 : Sierksma.FB.runR [0x1563918ae1473111116104a22] [61, 698, 1403] (Sierksma.FB.xa0K 22 193) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x194 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x194 (by simp)
  have r_AS_61_1403_x195 : Sierksma.FB.runR [0x1563918ae1473111116104a22] [61, 699, 1403] (Sierksma.FB.xa0K 22 194) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x195 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x195 (by simp)
  have r_AS_61_1403_x196 : Sierksma.FB.runR [0x1563918ae1473111116104a22] [61, 701, 1403] (Sierksma.FB.xa0K 22 195) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x196 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x196 (by simp)
  have r_AS_61_1403_x197 : Sierksma.FB.runR [0x21bb12398945c4938f4104a22] [61, 704, 1403] (Sierksma.FB.xa0K 22 196) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x197 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x197 (by simp)
  have r_AS_61_1403_x198 : Sierksma.FB.runR [0x21bb12398945c4938f4104a22] [61, 705, 1403] (Sierksma.FB.xa0K 22 197) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x198 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x198 (by simp)
  have r_AS_61_1403_x199 : Sierksma.FB.runR [0x72710725138fc138f4104a2200033] [61, 707, 1403] (Sierksma.FB.xa0K 22 198) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x199 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x199 (by simp)
  have r_AS_61_1403_x200 : Sierksma.FB.runR [0x72710725138fc138f4104a2200033] [61, 708, 1403] (Sierksma.FB.xa0K 22 199) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x200 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x200 (by simp)
  have r_AS_61_1403_x201 : Sierksma.FB.runR [0x72710725138fc138f4104a22] [61, 709, 1403] (Sierksma.FB.xa0K 22 200) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x201 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x201 (by simp)
  have r_AS_61_1403_x202 : Sierksma.FB.runR [0x72710725138fc138f4104a22] [61, 710, 1403] (Sierksma.FB.xa0K 22 201) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x202 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x202 (by simp)
  have r_AS_61_1403_x203 : Sierksma.FB.runR [0x72710725138fc138f4104a22] [61, 711, 1403] (Sierksma.FB.xa0K 22 202) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x203 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x203 (by simp)
  have r_AS_61_1403_x204 : Sierksma.FB.runR [0x72710725138fc138f4104a22] [61, 712, 1403] (Sierksma.FB.xa0K 22 203) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x204 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x204 (by simp)
  have r_AS_61_1403_x205 : Sierksma.FB.runR [0x358145c494bf694bf0104a2200033] [61, 741, 1403] (Sierksma.FB.xa0K 22 204) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x205 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x205 (by simp)
  have r_AS_61_1403_x206 : Sierksma.FB.runR [0x358145c494bf694bf0104a2200033] [61, 742, 1403] (Sierksma.FB.xa0K 22 205) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x206 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x206 (by simp)
  have r_AS_61_1403_x207 : Sierksma.FB.runR [0x358145c494bf694bf0104a22] [61, 743, 1403] (Sierksma.FB.xa0K 22 206) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x207 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x207 (by simp)
  have r_AS_61_1403_x208 : Sierksma.FB.runR [0x358145c494bf694bf0104a22] [61, 746, 1403] (Sierksma.FB.xa0K 22 207) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x208 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x208 (by simp)
  have r_AS_61_1403_x209 : Sierksma.FB.runR [0x725100821499091116104a2200033] [61, 750, 1403] (Sierksma.FB.xa0K 22 208) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x209 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x209 (by simp)
  have r_AS_61_1403_x210 : Sierksma.FB.runR [0x725100821499091116104a22] [61, 752, 1403] (Sierksma.FB.xa0K 22 209) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x210 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x210 (by simp)
  have r_AS_61_1403_x211 : Sierksma.FB.runR [0x725100821499091116104a22] [61, 753, 1403] (Sierksma.FB.xa0K 22 210) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x211 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x211 (by simp)
  have r_AS_61_1403_x212 : Sierksma.FB.runR [0x725100821499091116104a22] [61, 755, 1403] (Sierksma.FB.xa0K 22 211) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x212 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x212 (by simp)
  have r_AS_61_1403_x213 : Sierksma.FB.runR [0x1562932c8945c4938f4104a22] [61, 766, 1403] (Sierksma.FB.xa0K 22 212) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x213 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x213 (by simp)
  have r_AS_61_1403_x214 : Sierksma.FB.runR [0x1562932c8945c4938f4104a22] [61, 767, 1403] (Sierksma.FB.xa0K 22 213) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x214 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x214 (by simp)
  have r_AS_61_1403_x215 : Sierksma.FB.runR [0x17c3938fc138f4104a1a] [61, 770, 1403] (Sierksma.FB.xa0K 22 214) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x215 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x215 (by simp)
  have r_AS_61_1403_x216 : Sierksma.FB.runR [0x17c3938fc138f4104a1a] [61, 771, 1403] (Sierksma.FB.xa0K 22 215) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x216 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x216 (by simp)
  have r_AS_61_1403_x217 : Sierksma.FB.runR [0x29294a9239896ac9904a2200033] [61, 777, 1403] (Sierksma.FB.xa0K 22 216) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x217 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x217 (by simp)
  have r_AS_61_1403_x218 : Sierksma.FB.runR [0x29294a9239896ac9904a2200033] [61, 778, 1403] (Sierksma.FB.xa0K 22 217) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x218 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x218 (by simp)
  have r_AS_61_1403_x219 : Sierksma.FB.runR [0x29294a9239896ac9904a22] [61, 779, 1403] (Sierksma.FB.xa0K 22 218) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x219 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x219 (by simp)
  have r_AS_61_1403_x220 : Sierksma.FB.runR [0x29294a9239896ac9904a22] [61, 780, 1403] (Sierksma.FB.xa0K 22 219) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x220 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x220 (by simp)
  have r_AS_61_1403_x221 : Sierksma.FB.runR [0x29294a9239896ac9904a22] [61, 781, 1403] (Sierksma.FB.xa0K 22 220) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x221 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x221 (by simp)
  have r_AS_61_1403_x222 : Sierksma.FB.runR [0x29294a9239896ac9904a22] [61, 782, 1403] (Sierksma.FB.xa0K 22 221) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x222 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x222 (by simp)
  have r_AS_61_1403_x223 : Sierksma.FB.runR [0x358155e7926f216ac9904a2200033] [61, 784, 1403] (Sierksma.FB.xa0K 22 222) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x223 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x223 (by simp)
  have r_AS_61_1403_x224 : Sierksma.FB.runR [0x358155e7926f216ac9904a2200033] [61, 785, 1403] (Sierksma.FB.xa0K 22 223) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x224 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x224 (by simp)
  have r_AS_61_1403_x225 : Sierksma.FB.runR [0x358155e7926f216ac9904a22] [61, 786, 1403] (Sierksma.FB.xa0K 22 224) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x225 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x225 (by simp)
  have r_AS_61_1403_x226 : Sierksma.FB.runR [0x358155e7926f216ac9904a22] [61, 789, 1403] (Sierksma.FB.xa0K 22 225) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x226 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x226 (by simp)
  have r_AS_61_1403_x227 : Sierksma.FB.runR [0x358132cf14bf694bf0104a22] [61, 812, 1403] (Sierksma.FB.xa0K 22 226) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x227 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x227 (by simp)
  have r_AS_61_1403_x228 : Sierksma.FB.runR [0x358132cf14bf694bf0104a22] [61, 813, 1403] (Sierksma.FB.xa0K 22 227) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x228 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x228 (by simp)
  have r_AS_61_1403_x229 : Sierksma.FB.runR [0x8212398945c4938f4104a2200033] [61, 822, 1403] (Sierksma.FB.xa0K 22 228) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x229 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x229 (by simp)
  have r_AS_61_1403_x230 : Sierksma.FB.runR [0x8212398945c4938f4104a2200033] [61, 823, 1403] (Sierksma.FB.xa0K 22 229) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x230 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x230 (by simp)
  have r_AS_61_1403_x231 : Sierksma.FB.runR [0x8212398945c4938f4104a22] [61, 824, 1403] (Sierksma.FB.xa0K 22 230) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x231 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x231 (by simp)
  have r_AS_61_1403_x232 : Sierksma.FB.runR [0x8212398945c4938f4104a22] [61, 827, 1403] (Sierksma.FB.xa0K 22 231) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x232 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x232 (by simp)
  have r_AS_61_1403_x233 : Sierksma.FB.runR [0x821686a118ae14bf0104a2200033] [61, 830, 1403] (Sierksma.FB.xa0K 22 232) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x233 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x233 (by simp)
  have r_AS_61_1403_x234 : Sierksma.FB.runR [0x821686a118ae14bf0104a2200033] [61, 831, 1403] (Sierksma.FB.xa0K 22 233) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x234 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x234 (by simp)
  have r_AS_61_1403_x235 : Sierksma.FB.runR [0x821686a118ae14bf0104a22] [61, 832, 1403] (Sierksma.FB.xa0K 22 234) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x235 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x235 (by simp)
  have r_AS_61_1403_x236 : Sierksma.FB.runR [0x821686a118ae14bf0104a22] [61, 833, 1403] (Sierksma.FB.xa0K 22 235) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x236 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x236 (by simp)
  have r_AS_61_1403_x237 : Sierksma.FB.runR [0x821686a118ae14bf0104a22] [61, 834, 1403] (Sierksma.FB.xa0K 22 236) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x237 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x237 (by simp)
  have r_AS_61_1403_x238 : Sierksma.FB.runR [0x821686a118ae14bf0104a22] [61, 835, 1403] (Sierksma.FB.xa0K 22 237) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x238 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x238 (by simp)
  have r_AS_61_1403_x239 : Sierksma.FB.runR [0x72514990921bb11116104a2200033] [61, 842, 1403] (Sierksma.FB.xa0K 22 238) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x239 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x239 (by simp)
  have r_AS_61_1403_x240 : Sierksma.FB.runR [0x4c6108119499091116104a22] [61, 844, 1403] (Sierksma.FB.xa0K 22 239) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x240 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x240 (by simp)
  have r_AS_61_1403_x241 : Sierksma.FB.runR [0x4c6108119499091116104a22] [61, 845, 1403] (Sierksma.FB.xa0K 22 240) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x241 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x241 (by simp)
  have r_AS_61_1403_x242 : Sierksma.FB.runR [0x4c6108119499091116104a22] [61, 847, 1403] (Sierksma.FB.xa0K 22 241) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x242 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x242 (by simp)
  have r_AS_61_1403_x243 : Sierksma.FB.runR [0x8212398945c4938f4104a22] [61, 874, 1403] (Sierksma.FB.xa0K 22 242) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x243 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x243 (by simp)
  have r_AS_61_1403_x244 : Sierksma.FB.runR [0x8212398945c4938f4104a22] [61, 875, 1403] (Sierksma.FB.xa0K 22 243) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x244 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x244 (by simp)
  have r_AS_61_1403_x245 : Sierksma.FB.runR [0x17c3938fc138f4104a1a00033] [61, 877, 1403] (Sierksma.FB.xa0K 22 244) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x245 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x245 (by simp)
  have r_AS_61_1403_x246 : Sierksma.FB.runR [0x17c3938fc138f4104a1a00033] [61, 878, 1403] (Sierksma.FB.xa0K 22 245) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x246 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x246 (by simp)
  have r_AS_61_1403_x247 : Sierksma.FB.runR [0x17c3938fc138f4104a1a] [61, 879, 1403] (Sierksma.FB.xa0K 22 246) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x247 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x247 (by simp)
  have r_AS_61_1403_x248 : Sierksma.FB.runR [0x17c3938fc138f4104a1a] [61, 882, 1403] (Sierksma.FB.xa0K 22 247) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x248 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x248 (by simp)
  have r_AS_61_1403_x249 : Sierksma.FB.runR [0x1116105b791a9c14bf0104a2200033] [61, 892, 1403] (Sierksma.FB.xa0K 22 248) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x249 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x249 (by simp)
  have r_AS_61_1403_x250 : Sierksma.FB.runR [0x1116105b791a9c14bf0104a2200033] [61, 893, 1403] (Sierksma.FB.xa0K 22 249) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x250 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x250 (by simp)
  have r_AS_61_1403_x251 : Sierksma.FB.runR [0x79f94997118ae14bf0104a22] [61, 894, 1403] (Sierksma.FB.xa0K 22 250) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x251 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x251 (by simp)
  have r_AS_61_1403_x252 : Sierksma.FB.runR [0x79f94997118ae14bf0104a22] [61, 897, 1403] (Sierksma.FB.xa0K 22 251) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x252 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x252 (by simp)
  have r_AS_61_1403_x253 : Sierksma.FB.runR [0x811912fc1111e11116104a2200033] [61, 901, 1403] (Sierksma.FB.xa0K 22 252) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x253 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x253 (by simp)
  have r_AS_61_1403_x254 : Sierksma.FB.runR [0x1563918ae1111614731104a22] [61, 903, 1403] (Sierksma.FB.xa0K 22 253) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x254 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x254 (by simp)
  have r_AS_61_1403_x255 : Sierksma.FB.runR [0x1563918ae1111614731104a22] [61, 904, 1403] (Sierksma.FB.xa0K 22 254) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x255 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x255 (by simp)
  have r_AS_61_1403_x256 : Sierksma.FB.runR [0x1563918ae1111614731104a22] [61, 906, 1403] (Sierksma.FB.xa0K 22 255) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x256 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x256 (by simp)
  have r_AS_61_1403_x257 : Sierksma.FB.runR [0x17c3157d6157cd904a1a00033] [61, 1357, 1403] (Sierksma.FB.xa0K 22 256) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x257 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x257 (by simp)
  have r_AS_61_1403_x258 : Sierksma.FB.runR [0x17c3157d6157cd904a1a00033] [61, 1358, 1403] (Sierksma.FB.xa0K 22 257) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x258 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x258 (by simp)
  have r_AS_61_1403_x259 : Sierksma.FB.runR [0x17c3157d6157cd904a1a] [61, 1359, 1403] (Sierksma.FB.xa0K 22 258) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x259 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x259 (by simp)
  have r_AS_61_1403_x260 : Sierksma.FB.runR [0x17c3157d6157cd904a1a] [61, 1360, 1403] (Sierksma.FB.xa0K 22 259) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x260 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x260 (by simp)
  have r_AS_61_1403_x261 : Sierksma.FB.runR [0x17c3157d6157cd904a1a] [61, 1361, 1403] (Sierksma.FB.xa0K 22 260) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x261 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x261 (by simp)
  have r_AS_61_1403_x262 : Sierksma.FB.runR [0x17c3157d6157cd904a1a] [61, 1362, 1403] (Sierksma.FB.xa0K 22 261) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x262 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x262 (by simp)
  have r_AS_61_1403_x263 : Sierksma.FB.runR [0x2e195316938fc157cd904a2200033] [61, 1364, 1403] (Sierksma.FB.xa0K 22 262) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x263 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x263 (by simp)
  have r_AS_61_1403_x264 : Sierksma.FB.runR [0x2e195316938fc157cd904a2200033] [61, 1365, 1403] (Sierksma.FB.xa0K 22 263) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x264 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x264 (by simp)
  have r_AS_61_1403_x265 : Sierksma.FB.runR [0x2e195316938fc157cd904a22] [61, 1366, 1403] (Sierksma.FB.xa0K 22 264) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x265 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x265 (by simp)
  have r_AS_61_1403_x266 : Sierksma.FB.runR [0x2e195316938fc157cd904a22] [61, 1369, 1403] (Sierksma.FB.xa0K 22 265) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x266 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x266 (by simp)
  have r_AS_61_1403_x267 : Sierksma.FB.runR [0x17c3157d6157cd904a1a00033] [61, 1376, 1403] (Sierksma.FB.xa0K 22 266) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x267 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x267 (by simp)
  have r_AS_61_1403_x268 : Sierksma.FB.runR [0x17c3157d6157cd904a1a00033] [61, 1377, 1403] (Sierksma.FB.xa0K 22 267) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x268 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x268 (by simp)
  have r_AS_61_1403_x269 : Sierksma.FB.runR [0x17c3157d6157cd904a1a] [61, 1378, 1403] (Sierksma.FB.xa0K 22 268) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x269 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x269 (by simp)
  have r_AS_61_1403_x270 : Sierksma.FB.runR [0x17c3157d6157cd904a1a] [61, 1381, 1403] (Sierksma.FB.xa0K 22 269) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x270 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x270 (by simp)
  have r_AS_61_1403_x271 : Sierksma.FB.runR [0x241892419157cd904a1a00033] [61, 1384, 1403] (Sierksma.FB.xa0K 22 270) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x271 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x271 (by simp)
  have r_AS_61_1403_x272 : Sierksma.FB.runR [0x241892419157cd904a1a00033] [61, 1385, 1403] (Sierksma.FB.xa0K 22 271) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x272 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x272 (by simp)
  have r_AS_61_1403_x273 : Sierksma.FB.runR [0x241892419157cd904a1a] [61, 1386, 1403] (Sierksma.FB.xa0K 22 272) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x273 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x273 (by simp)
  have r_AS_61_1403_x274 : Sierksma.FB.runR [0x241892419157cd904a1a] [61, 1388, 1403] (Sierksma.FB.xa0K 22 273) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x274 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x274 (by simp)
  have r_AS_61_1403_x275 : Sierksma.FB.runR [0x241892419157cd904a1a] [61, 1389, 1403] (Sierksma.FB.xa0K 22 274) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x275 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x275 (by simp)
  have r_AS_61_1403_x276 : Sierksma.FB.runR [0x241892419157cd904a1a] [61, 1390, 1403] (Sierksma.FB.xa0K 22 275) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x276 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x276 (by simp)
  have r_AS_61_1403_x277 : Sierksma.FB.runR [0x4bf145cb16ad094bf0104a2200033] [61, 1403, 1410] (Sierksma.FB.xa0K 22 276) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x277 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x277 (by simp)
  have r_AS_61_1403_x278 : Sierksma.FB.runR [0x4bf145cb16ad094bf0104a2200033] [61, 1403, 1411] (Sierksma.FB.xa0K 22 277) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x278 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x278 (by simp)
  have r_AS_61_1403_x279 : Sierksma.FB.runR [0x4bf145cb16ad094bf0104a22] [61, 1403, 1412] (Sierksma.FB.xa0K 22 278) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x279 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x279 (by simp)
  have r_AS_61_1403_x280 : Sierksma.FB.runR [0x4bf145cb16ad094bf0104a22] [61, 1403, 1413] (Sierksma.FB.xa0K 22 279) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x280 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x280 (by simp)
  have r_AS_61_1403_x281 : Sierksma.FB.runR [0x4bf145cb16ad094bf0104a22] [61, 1403, 1414] (Sierksma.FB.xa0K 22 280) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x281 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x281 (by simp)
  have r_AS_61_1403_x282 : Sierksma.FB.runR [0x4bf145cb16ad094bf0104a22] [61, 1403, 1415] (Sierksma.FB.xa0K 22 281) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x282 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x282 (by simp)
  have r_AS_61_1403_x283 : Sierksma.FB.runR [0x17c3157d6157cd904a1a00033] [61, 1403, 1422] (Sierksma.FB.xa0K 22 282) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x283 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x283 (by simp)
  have r_AS_61_1403_x284 : Sierksma.FB.runR [0x17c3157d6157cd904a1a] [61, 1403, 1424] (Sierksma.FB.xa0K 22 283) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x284 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x284 (by simp)
  have r_AS_61_1403_x285 : Sierksma.FB.runR [0x17c3157d6157cd904a1a] [61, 1403, 1425] (Sierksma.FB.xa0K 22 284) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x285 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x285 (by simp)
  have r_AS_61_1403_x286 : Sierksma.FB.runR [0x17c3157d6157cd904a1a] [61, 1403, 1427] (Sierksma.FB.xa0K 22 285) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x286 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x286 (by simp)
  have r_AS_61_1403_x287 : Sierksma.FB.runR [0xa001642d14bf694bf0104a2200033] [61, 1403, 1429] (Sierksma.FB.xa0K 22 286) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x287 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x287 (by simp)
  have r_AS_61_1403_x288 : Sierksma.FB.runR [0xa001642d14bf694bf0104a2200033] [61, 1403, 1430] (Sierksma.FB.xa0K 22 287) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x288 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x288 (by simp)
  have r_AS_61_1403_x289 : Sierksma.FB.runR [0xa001642d14bf694bf0104a22] [61, 1403, 1431] (Sierksma.FB.xa0K 22 288) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x289 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x289 (by simp)
  have r_AS_61_1403_x290 : Sierksma.FB.runR [0xa001642d14bf694bf0104a22] [61, 1403, 1434] (Sierksma.FB.xa0K 22 289) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x290 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x290 (by simp)
  have r_AS_61_1403_x291 : Sierksma.FB.runR [0x17c3157d6157cd904a1a00033] [61, 1403, 1447] (Sierksma.FB.xa0K 22 290) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x291 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x291 (by simp)
  have r_AS_61_1403_x292 : Sierksma.FB.runR [0x17c3157d6157cd904a1a] [61, 1403, 1450] (Sierksma.FB.xa0K 22 291) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x292 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x292 (by simp)
  have r_AS_61_1403_x293 : Sierksma.FB.runR [0x17c3157d6157cd904a1a] [61, 1403, 1451] (Sierksma.FB.xa0K 22 292) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x293 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x293 (by simp)
  have r_AS_61_1403_x294 : Sierksma.FB.runR [0x17c3157d6157cd904a1a] [61, 1403, 1452] (Sierksma.FB.xa0K 22 293) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x294 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x294 (by simp)
  have r_AS_61_1403_x295 : Sierksma.FB.runR [0x358132cf13b5a14bf0104a2200033] [61, 1403, 1472] (Sierksma.FB.xa0K 22 294) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x295 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x295 (by simp)
  have r_AS_61_1403_x296 : Sierksma.FB.runR [0x358132cf13b5a14bf0104a2200033] [61, 1403, 1473] (Sierksma.FB.xa0K 22 295) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x296 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x296 (by simp)
  have r_AS_61_1403_x297 : Sierksma.FB.runR [0x358132cf13b5a14bf0104a22] [61, 1403, 1474] (Sierksma.FB.xa0K 22 296) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x297 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x297 (by simp)
  have r_AS_61_1403_x298 : Sierksma.FB.runR [0x358132cf13b5a14bf0104a22] [61, 1403, 1477] (Sierksma.FB.xa0K 22 297) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x298 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x298 (by simp)
  have r_AS_61_1403_x299 : Sierksma.FB.runR [0x2e195316938fc157cd904a2200033] [61, 1403, 1481] (Sierksma.FB.xa0K 22 298) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x299 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x299 (by simp)
  have r_AS_61_1403_x300 : Sierksma.FB.runR [0x2e195316938fc157cd904a22] [61, 1403, 1483] (Sierksma.FB.xa0K 22 299) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x300 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x300 (by simp)
  have r_AS_61_1403_x301 : Sierksma.FB.runR [0x2e195316938fc157cd904a22] [61, 1403, 1484] (Sierksma.FB.xa0K 22 300) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x301 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x301 (by simp)
  have r_AS_61_1403_x302 : Sierksma.FB.runR [0x2e195316938fc157cd904a22] [61, 1403, 1486] (Sierksma.FB.xa0K 22 301) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x302 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x302 (by simp)
  have r_AS_61_1403_x303 : Sierksma.FB.runR [0x12fc1499094bf694bf0104a2200033] [61, 1403, 1496] (Sierksma.FB.xa0K 22 302) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x303 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x303 (by simp)
  have r_AS_61_1403_x304 : Sierksma.FB.runR [0x12fc1499094bf694bf0104a2200033] [61, 1403, 1497] (Sierksma.FB.xa0K 22 303) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x304 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x304 (by simp)
  have r_AS_61_1403_x305 : Sierksma.FB.runR [0x12fc1499094bf694bf0104a22] [61, 1403, 1498] (Sierksma.FB.xa0K 22 304) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x305 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x305 (by simp)
  have r_AS_61_1403_x306 : Sierksma.FB.runR [0x12fc1499094bf694bf0104a22] [61, 1403, 1500] (Sierksma.FB.xa0K 22 305) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x306 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x306 (by simp)
  have r_AS_61_1403_x307 : Sierksma.FB.runR [0x12fc1499094bf694bf0104a22] [61, 1403, 1501] (Sierksma.FB.xa0K 22 306) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x307 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x307 (by simp)
  have r_AS_61_1403_x308 : Sierksma.FB.runR [0x12fc1499094bf694bf0104a22] [61, 1403, 1502] (Sierksma.FB.xa0K 22 307) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x308 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x308 (by simp)
  have r_AS_61_1403_x309 : Sierksma.FB.runR [0x241892419157cd904a1a00033] [61, 1403, 1505] (Sierksma.FB.xa0K 22 308) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x309 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x309 (by simp)
  have r_AS_61_1403_x310 : Sierksma.FB.runR [0x241892419157cd904a1a] [61, 1403, 1508] (Sierksma.FB.xa0K 22 309) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x310 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x310 (by simp)
  have r_AS_61_1403_x311 : Sierksma.FB.runR [0x241892419157cd904a1a] [61, 1403, 1509] (Sierksma.FB.xa0K 22 310) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x311 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x311 (by simp)
  have r_AS_61_1403_x312 : Sierksma.FB.runR [0x241892419157cd904a1a] [61, 1403, 1510] (Sierksma.FB.xa0K 22 311) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x312 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x312 (by simp)
  have r_AS_61_1403_x313 : Sierksma.FB.runR [0x4c610082145c4938f4104a2200033] [61, 1403, 1519] (Sierksma.FB.xa0K 22 312) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x313 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x313 (by simp)
  have r_AS_61_1403_x314 : Sierksma.FB.runR [0x4c610082145c4938f4104a2200033] [61, 1403, 1520] (Sierksma.FB.xa0K 22 313) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x314 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x314 (by simp)
  have r_AS_61_1403_x315 : Sierksma.FB.runR [0x4c610082145c4938f4104a22] [61, 1403, 1521] (Sierksma.FB.xa0K 22 314) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x315 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x315 (by simp)
  have r_AS_61_1403_x316 : Sierksma.FB.runR [0x4c610082145c4938f4104a22] [61, 1403, 1522] (Sierksma.FB.xa0K 22 315) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x316 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x316 (by simp)
  have r_AS_61_1403_x317 : Sierksma.FB.runR [0x4c610082145c4938f4104a22] [61, 1403, 1523] (Sierksma.FB.xa0K 22 316) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x317 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x317 (by simp)
  have r_AS_61_1403_x318 : Sierksma.FB.runR [0x4c610082145c4938f4104a22] [61, 1403, 1524] (Sierksma.FB.xa0K 22 317) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x318 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x318 (by simp)
  have r_AS_61_1403_x319 : Sierksma.FB.runR [0x821000514365138f4104a2200033] [61, 1403, 1526] (Sierksma.FB.xa0K 22 318) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x319 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x319 (by simp)
  have r_AS_61_1403_x320 : Sierksma.FB.runR [0x821000514365138f4104a2200033] [61, 1403, 1527] (Sierksma.FB.xa0K 22 319) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x320 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x320 (by simp)
  have r_AS_61_1403_x321 : Sierksma.FB.runR [0x821000514365138f4104a22] [61, 1403, 1528] (Sierksma.FB.xa0K 22 320) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x321 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x321 (by simp)
  have r_AS_61_1403_x322 : Sierksma.FB.runR [0x821000514365138f4104a22] [61, 1403, 1531] (Sierksma.FB.xa0K 22 321) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x322 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x322 (by simp)
  have r_AS_61_1403_x323 : Sierksma.FB.runR [0x5b8100821072096ac9904a2200033] [61, 1403, 1562] (Sierksma.FB.xa0K 22 322) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x323 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x323 (by simp)
  have r_AS_61_1403_x324 : Sierksma.FB.runR [0x5b8100821072096ac9904a22] [61, 1403, 1564] (Sierksma.FB.xa0K 22 323) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x324 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x324 (by simp)
  have r_AS_61_1403_x325 : Sierksma.FB.runR [0x5b8100821072096ac9904a22] [61, 1403, 1565] (Sierksma.FB.xa0K 22 324) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x325 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x325 (by simp)
  have r_AS_61_1403_x326 : Sierksma.FB.runR [0x5b8100821072096ac9904a22] [61, 1403, 1567] (Sierksma.FB.xa0K 22 325) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x326 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x326 (by simp)
  have r_AS_61_1403_x327 : Sierksma.FB.runR [0x2904bf1072096ac9904a2200033] [61, 1403, 1571] (Sierksma.FB.xa0K 22 326) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x327 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x327 (by simp)
  have r_AS_61_1403_x328 : Sierksma.FB.runR [0x2904bf1072096ac9904a22] [61, 1403, 1574] (Sierksma.FB.xa0K 22 327) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x328 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x328 (by simp)
  have r_AS_61_1403_x329 : Sierksma.FB.runR [0x2904bf1072096ac9904a22] [61, 1403, 1575] (Sierksma.FB.xa0K 22 328) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x329 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x329 (by simp)
  have r_AS_61_1403_x330 : Sierksma.FB.runR [0x2904bf1072096ac9904a22] [61, 1403, 1576] (Sierksma.FB.xa0K 22 329) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x330 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x330 (by simp)
  have r_AS_61_1403_x331 : Sierksma.FB.runR [0x6bbe96684138f4104a1a00033] [61, 1403, 1577] (Sierksma.FB.xa0K 22 330) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x331 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x331 (by simp)
  have r_AS_61_1403_x332 : Sierksma.FB.runR [0x6bbe96684138f4104a1a00033] [61, 1403, 1578] (Sierksma.FB.xa0K 22 331) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x332 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x332 (by simp)
  have r_AS_61_1403_x333 : Sierksma.FB.runR [0x6bbe96684138f4104a1a] [61, 1403, 1579] (Sierksma.FB.xa0K 22 332) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x333 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x333 (by simp)
  have r_AS_61_1403_x334 : Sierksma.FB.runR [0x6bbe96684138f4104a1a] [61, 1403, 1580] (Sierksma.FB.xa0K 22 333) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x334 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x334 (by simp)
  have r_AS_61_1403_x335 : Sierksma.FB.runR [0x6bbe96684138f4104a1a] [61, 1403, 1581] (Sierksma.FB.xa0K 22 334) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x335 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x335 (by simp)
  have r_AS_61_1403_x336 : Sierksma.FB.runR [0x6bbe96684138f4104a1a] [61, 1403, 1582] (Sierksma.FB.xa0K 22 335) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x336 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x336 (by simp)
  have r_AS_61_1403_x337 : Sierksma.FB.runR [0x6bbe96684138f4104a1a00033] [61, 1403, 1589] (Sierksma.FB.xa0K 22 336) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x337 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x337 (by simp)
  have r_AS_61_1403_x338 : Sierksma.FB.runR [0x6bbe96684138f4104a1a] [61, 1403, 1591] (Sierksma.FB.xa0K 22 337) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x338 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x338 (by simp)
  have r_AS_61_1403_x339 : Sierksma.FB.runR [0x6bbe96684138f4104a1a] [61, 1403, 1592] (Sierksma.FB.xa0K 22 338) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x339 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x339 (by simp)
  have r_AS_61_1403_x340 : Sierksma.FB.runR [0x6bbe96684138f4104a1a] [61, 1403, 1594] (Sierksma.FB.xa0K 22 339) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x340 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x340 (by simp)
  have r_AS_61_1403_x341 : Sierksma.FB.runR [0xfb904bf1072094bf0104a2200033] [61, 1403, 1605] (Sierksma.FB.xa0K 22 340) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x341 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x341 (by simp)
  have r_AS_61_1403_x342 : Sierksma.FB.runR [0xfb904bf1072094bf0104a22] [61, 1403, 1607] (Sierksma.FB.xa0K 22 341) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x342 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x342 (by simp)
  have r_AS_61_1403_x343 : Sierksma.FB.runR [0xfb904bf1072094bf0104a22] [61, 1403, 1608] (Sierksma.FB.xa0K 22 342) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x343 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x343 (by simp)
  have r_AS_61_1403_x344 : Sierksma.FB.runR [0xfb904bf1072094bf0104a22] [61, 1403, 1610] (Sierksma.FB.xa0K 22 343) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x344 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x344 (by simp)
  have r_AS_61_1403_x345 : Sierksma.FB.runR [0x82107209436516d29104a2200033] [61, 1403, 1617] (Sierksma.FB.xa0K 22 344) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x345 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x345 (by simp)
  have r_AS_61_1403_x346 : Sierksma.FB.runR [0x82107209436516d29104a2200033] [61, 1403, 1618] (Sierksma.FB.xa0K 22 345) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x346 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x346 (by simp)
  have r_AS_61_1403_x347 : Sierksma.FB.runR [0x82107209436516d29104a22] [61, 1403, 1619] (Sierksma.FB.xa0K 22 346) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x347 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x347 (by simp)
  have r_AS_61_1403_x348 : Sierksma.FB.runR [0x82107209436516d29104a22] [61, 1403, 1620] (Sierksma.FB.xa0K 22 347) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x348 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x348 (by simp)
  have r_AS_61_1403_x349 : Sierksma.FB.runR [0x82107209436516d29104a22] [61, 1403, 1621] (Sierksma.FB.xa0K 22 348) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x349 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x349 (by simp)
  have r_AS_61_1403_x350 : Sierksma.FB.runR [0x82107209436516d29104a22] [61, 1403, 1622] (Sierksma.FB.xa0K 22 349) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x350 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x350 (by simp)
  have r_AS_61_1403_x351 : Sierksma.FB.runR [0x8216424938f4104a1a00033] [61, 1403, 1623] (Sierksma.FB.xa0K 22 350) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x351 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x351 (by simp)
  have r_AS_61_1403_x352 : Sierksma.FB.runR [0x8216424938f4104a1a00033] [61, 1403, 1624] (Sierksma.FB.xa0K 22 351) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x352 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x352 (by simp)
  have r_AS_61_1403_x353 : Sierksma.FB.runR [0x8216424938f4104a1a] [61, 1403, 1625] (Sierksma.FB.xa0K 22 352) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x353 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x353 (by simp)
  have r_AS_61_1403_x354 : Sierksma.FB.runR [0x8216424938f4104a1a] [61, 1403, 1628] (Sierksma.FB.xa0K 22 353) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x354 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x354 (by simp)
  have r_AS_61_1403_x355 : Sierksma.FB.runR [0x8216424938f4104a1a00033] [61, 1403, 1632] (Sierksma.FB.xa0K 22 354) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x355 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x355 (by simp)
  have r_AS_61_1403_x356 : Sierksma.FB.runR [0x8216424938f4104a1a] [61, 1403, 1634] (Sierksma.FB.xa0K 22 355) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x356 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x356 (by simp)
  have r_AS_61_1403_x357 : Sierksma.FB.runR [0x8216424938f4104a1a] [61, 1403, 1635] (Sierksma.FB.xa0K 22 356) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x357 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x357 (by simp)
  have r_AS_61_1403_x358 : Sierksma.FB.runR [0x8216424938f4104a1a] [61, 1403, 1637] (Sierksma.FB.xa0K 22 357) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x358 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x358 (by simp)
  have r_AS_61_1403_x359 : Sierksma.FB.runR [0x57d61072094bf0104a1a00033] [61, 1403, 1668] (Sierksma.FB.xa0K 22 358) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x359 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x359 (by simp)
  have r_AS_61_1403_x360 : Sierksma.FB.runR [0x57d61072094bf0104a1a] [61, 1403, 1671] (Sierksma.FB.xa0K 22 359) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x360 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x360 (by simp)
  have r_AS_61_1403_x361 : Sierksma.FB.runR [0x57d61072094bf0104a1a] [61, 1403, 1672] (Sierksma.FB.xa0K 22 360) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x361 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x361 (by simp)
  have r_AS_61_1403_x362 : Sierksma.FB.runR [0x57d61072094bf0104a1a] [61, 1403, 1673] (Sierksma.FB.xa0K 22 361) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x362 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x362 (by simp)
  have r_AS_61_1403_x363 : Sierksma.FB.runR [0x510720945c494990904a2200033] [61, 1403, 1675] (Sierksma.FB.xa0K 22 362) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x363 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x363 (by simp)
  have r_AS_61_1403_x364 : Sierksma.FB.runR [0x510720945c494990904a2200033] [61, 1403, 1676] (Sierksma.FB.xa0K 22 363) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x364 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x364 (by simp)
  have r_AS_61_1403_x365 : Sierksma.FB.runR [0x510720945c494990904a22] [61, 1403, 1677] (Sierksma.FB.xa0K 22 364) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x365 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x365 (by simp)
  have r_AS_61_1403_x366 : Sierksma.FB.runR [0x510720945c494990904a22] [61, 1403, 1678] (Sierksma.FB.xa0K 22 365) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x366 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x366 (by simp)
  have r_AS_61_1403_x367 : Sierksma.FB.runR [0x510720945c494990904a22] [61, 1403, 1679] (Sierksma.FB.xa0K 22 366) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x367 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x367 (by simp)
  have r_AS_61_1403_x368 : Sierksma.FB.runR [0x510720945c494990904a22] [61, 1403, 1680] (Sierksma.FB.xa0K 22 367) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x368 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x368 (by simp)
  have r_AS_61_1403_x369 : Sierksma.FB.runR [0x82145c4938f4104a1a00033] [61, 1403, 1689] (Sierksma.FB.xa0K 22 368) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x369 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x369 (by simp)
  have r_AS_61_1403_x370 : Sierksma.FB.runR [0x82145c4938f4104a1a00033] [61, 1403, 1690] (Sierksma.FB.xa0K 22 369) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x370 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x370 (by simp)
  have r_AS_61_1403_x371 : Sierksma.FB.runR [0x82145c4938f4104a1a] [61, 1403, 1691] (Sierksma.FB.xa0K 22 370) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x371 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x371 (by simp)
  have r_AS_61_1403_x372 : Sierksma.FB.runR [0x82145c4938f4104a1a] [61, 1403, 1694] (Sierksma.FB.xa0K 22 371) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x372 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x372 (by simp)
  have r_AS_61_1403_x373 : Sierksma.FB.runR [0x2df94365138f4104a1a00033] [61, 1403, 1697] (Sierksma.FB.xa0K 22 372) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x373 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x373 (by simp)
  have r_AS_61_1403_x374 : Sierksma.FB.runR [0x2df94365138f4104a1a00033] [61, 1403, 1698] (Sierksma.FB.xa0K 22 373) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x374 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x374 (by simp)
  have r_AS_61_1403_x375 : Sierksma.FB.runR [0x2df94365138f4104a1a] [61, 1403, 1699] (Sierksma.FB.xa0K 22 374) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x375 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x375 (by simp)
  have r_AS_61_1403_x376 : Sierksma.FB.runR [0x2df94365138f4104a1a] [61, 1403, 1701] (Sierksma.FB.xa0K 22 375) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x376 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x376 (by simp)
  have r_AS_61_1403_x377 : Sierksma.FB.runR [0x2df94365138f4104a1a] [61, 1403, 1702] (Sierksma.FB.xa0K 22 376) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x377 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x377 (by simp)
  have r_AS_61_1403_x378 : Sierksma.FB.runR [0x2df94365138f4104a1a] [61, 1403, 1703] (Sierksma.FB.xa0K 22 377) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x378 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x378 (by simp)
  have r_AS_61_1403_x379 : Sierksma.FB.runR [0x4bf102db16ac9904a1a00033] [61, 1403, 1713] (Sierksma.FB.xa0K 22 378) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x379 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x379 (by simp)
  have r_AS_61_1403_x380 : Sierksma.FB.runR [0x4bf102db16ac9904a1a] [61, 1403, 1715] (Sierksma.FB.xa0K 22 379) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x380 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x380 (by simp)
  have r_AS_61_1403_x381 : Sierksma.FB.runR [0x4bf102db16ac9904a1a] [61, 1403, 1716] (Sierksma.FB.xa0K 22 380) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x381 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x381 (by simp)
  have r_AS_61_1403_x382 : Sierksma.FB.runR [0x4bf102db16ac9904a1a] [61, 1403, 1718] (Sierksma.FB.xa0K 22 381) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x382 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x382 (by simp)
  have r_AS_61_1403_x383 : Sierksma.FB.runR [0x4bf102db16ac9904a1a00033] [61, 1403, 1722] (Sierksma.FB.xa0K 22 382) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x383 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x383 (by simp)
  have r_AS_61_1403_x384 : Sierksma.FB.runR [0x4bf102db16ac9904a1a] [61, 1403, 1725] (Sierksma.FB.xa0K 22 383) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x384 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x384 (by simp)
  have r_AS_61_1403_x385 : Sierksma.FB.runR [0x4bf102db16ac9904a1a] [61, 1403, 1726] (Sierksma.FB.xa0K 22 384) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x385 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x385 (by simp)
  have r_AS_61_1403_x386 : Sierksma.FB.runR [0x4bf102db16ac9904a1a] [61, 1403, 1727] (Sierksma.FB.xa0K 22 385) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x386 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x386 (by simp)
  have r_AS_61_1403_x387 : Sierksma.FB.runR [0xfb16684138f4104a1a00033] [61, 1403, 1747] (Sierksma.FB.xa0K 22 386) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x387 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x387 (by simp)
  have r_AS_61_1403_x388 : Sierksma.FB.runR [0xfb16684138f4104a1a00033] [61, 1403, 1748] (Sierksma.FB.xa0K 22 387) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x388 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x388 (by simp)
  have r_AS_61_1403_x389 : Sierksma.FB.runR [0xfb16684138f4104a1a] [61, 1403, 1749] (Sierksma.FB.xa0K 22 388) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x389 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x389 (by simp)
  have r_AS_61_1403_x390 : Sierksma.FB.runR [0xfb16684138f4104a1a] [61, 1403, 1752] (Sierksma.FB.xa0K 22 389) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x390 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x390 (by simp)
  have r_AS_61_1403_x391 : Sierksma.FB.runR [0x516684138f4104a1a00033] [61, 1403, 1765] (Sierksma.FB.xa0K 22 390) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x391 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x391 (by simp)
  have r_AS_61_1403_x392 : Sierksma.FB.runR [0x516684138f4104a1a] [61, 1403, 1768] (Sierksma.FB.xa0K 22 391) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x392 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x392 (by simp)
  have r_AS_61_1403_x393 : Sierksma.FB.runR [0x516684138f4104a1a] [61, 1403, 1769] (Sierksma.FB.xa0K 22 392) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x393 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x393 (by simp)
  have r_AS_61_1403_x394 : Sierksma.FB.runR [0x516684138f4104a1a] [61, 1403, 1770] (Sierksma.FB.xa0K 22 393) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x394 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x394 (by simp)
  have r_AS_61_1403_x395 : Sierksma.FB.runR [0x5102db14bf0104a1a00033] [61, 1403, 1772] (Sierksma.FB.xa0K 22 394) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x395 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x395 (by simp)
  have r_AS_61_1403_x396 : Sierksma.FB.runR [0x5102db14bf0104a1a] [61, 1403, 1774] (Sierksma.FB.xa0K 22 395) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x396 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x396 (by simp)
  have r_AS_61_1403_x397 : Sierksma.FB.runR [0x5102db14bf0104a1a] [61, 1403, 1775] (Sierksma.FB.xa0K 22 396) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x397 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x397 (by simp)
  have r_AS_61_1403_x398 : Sierksma.FB.runR [0x5102db14bf0104a1a] [61, 1403, 1777] (Sierksma.FB.xa0K 22 397) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x398 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x398 (by simp)
  have r_AS_61_1403_x399 : Sierksma.FB.runR [0x2db1436514990904a1a00033] [61, 1403, 1784] (Sierksma.FB.xa0K 22 398) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x399 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x399 (by simp)
  have r_AS_61_1403_x400 : Sierksma.FB.runR [0x2db1436514990904a1a00033] [61, 1403, 1785] (Sierksma.FB.xa0K 22 399) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x400 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x400 (by simp)
  have r_AS_61_1403_x401 : Sierksma.FB.runR [0x2db1436514990904a1a] [61, 1403, 1786] (Sierksma.FB.xa0K 22 400) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x401 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x401 (by simp)
  have r_AS_61_1403_x402 : Sierksma.FB.runR [0x2db1436514990904a1a] [61, 1403, 1787] (Sierksma.FB.xa0K 22 401) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x402 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x402 (by simp)
  have r_AS_61_1403_x403 : Sierksma.FB.runR [0x2db1436514990904a1a] [61, 1403, 1788] (Sierksma.FB.xa0K 22 402) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x403 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x403 (by simp)
  have r_AS_61_1403_x404 : Sierksma.FB.runR [0x2db1436514990904a1a] [61, 1403, 1789] (Sierksma.FB.xa0K 22 403) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x404 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x404 (by simp)
  have r_AS_61_1403_x405 : Sierksma.FB.runR [0x6424938f4104a1200033] [61, 1403, 1809] (Sierksma.FB.xa0K 22 404) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x405 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x405 (by simp)
  have r_AS_61_1403_x406 : Sierksma.FB.runR [0x6424938f4104a1200033] [61, 1403, 1810] (Sierksma.FB.xa0K 22 405) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x406 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x406 (by simp)
  have r_AS_61_1403_x407 : Sierksma.FB.runR [0x6424938f4104a12] [61, 1403, 1811] (Sierksma.FB.xa0K 22 406) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x407 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x407 (by simp)
  have r_AS_61_1403_x408 : Sierksma.FB.runR [0x6424938f4104a12] [61, 1403, 1813] (Sierksma.FB.xa0K 22 407) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x408 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x408 (by simp)
  have r_AS_61_1403_x409 : Sierksma.FB.runR [0x6424938f4104a12] [61, 1403, 1814] (Sierksma.FB.xa0K 22 408) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x409 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x409 (by simp)
  have r_AS_61_1403_x410 : Sierksma.FB.runR [0x6424938f4104a12] [61, 1403, 1815] (Sierksma.FB.xa0K 22 409) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x410 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x410 (by simp)
  have r_AS_61_1403_x411 : Sierksma.FB.runR [0x6424938f4104a1200033] [61, 1403, 1818] (Sierksma.FB.xa0K 22 410) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x411 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x411 (by simp)
  have r_AS_61_1403_x412 : Sierksma.FB.runR [0x6424938f4104a12] [61, 1403, 1821] (Sierksma.FB.xa0K 22 411) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x412 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x412 (by simp)
  have r_AS_61_1403_x413 : Sierksma.FB.runR [0x6424938f4104a12] [61, 1403, 1822] (Sierksma.FB.xa0K 22 412) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x413 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x413 (by simp)
  have r_AS_61_1403_x414 : Sierksma.FB.runR [0x6424938f4104a12] [61, 1403, 1823] (Sierksma.FB.xa0K 22 413) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x414 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x414 (by simp)
  have r_AS_61_1403_x415 : Sierksma.FB.runR [0x2db14bf0104a1200033] [61, 1403, 1830] (Sierksma.FB.xa0K 22 414) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x415 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x415 (by simp)
  have r_AS_61_1403_x416 : Sierksma.FB.runR [0x2db14bf0104a12] [61, 1403, 1833] (Sierksma.FB.xa0K 22 415) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x416 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x416 (by simp)
  have r_AS_61_1403_x417 : Sierksma.FB.runR [0x2db14bf0104a12] [61, 1403, 1834] (Sierksma.FB.xa0K 22 416) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x417 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x417 (by simp)
  have r_AS_61_1403_x418 : Sierksma.FB.runR [0x2db14bf0104a12] [61, 1403, 1835] (Sierksma.FB.xa0K 22 417) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x418 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x418 (by simp)
  have r_AS_61_1403_x419 : Sierksma.FB.runR [0x2db14731145c4904a1a00033] [61, 1403, 1837] (Sierksma.FB.xa0K 22 418) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x419 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x419 (by simp)
  have r_AS_61_1403_x420 : Sierksma.FB.runR [0x2db14731145c4904a1a00033] [61, 1403, 1838] (Sierksma.FB.xa0K 22 419) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x420 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x420 (by simp)
  have r_AS_61_1403_x421 : Sierksma.FB.runR [0x2db14731145c4904a1a] [61, 1403, 1839] (Sierksma.FB.xa0K 22 420) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x421 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x421 (by simp)
  have r_AS_61_1403_x422 : Sierksma.FB.runR [0x2db14731145c4904a1a] [61, 1403, 1840] (Sierksma.FB.xa0K 22 421) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x422 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x422 (by simp)
  have r_AS_61_1403_x423 : Sierksma.FB.runR [0x2db14731145c4904a1a] [61, 1403, 1841] (Sierksma.FB.xa0K 22 422) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x423 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x423 (by simp)
  have r_AS_61_1403_x424 : Sierksma.FB.runR [0x2db14731145c4904a1a] [61, 1403, 1842] (Sierksma.FB.xa0K 22 423) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_1403_x424 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_1403_x424 (by simp)
  have r_AS_4_28 : Sierksma.FB.runR [0x63ab1] (Sierksma.FB.pairSort (Sierksma.FB.R1.getD 1 0) 28) (Sierksma.FB.KS 1 28) 5 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_4_28 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_4_28 (by simp)
  have r_AS_4_41 : Sierksma.FB.runR [0xf31] (Sierksma.FB.pairSort (Sierksma.FB.R1.getD 1 0) 41) (Sierksma.FB.KS 1 41) 5 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_4_41 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_4_41 (by simp)
  have r_AS_44_52 : Sierksma.FB.runR [0x1] (Sierksma.FB.pairSort (Sierksma.FB.R1.getD 3 0) 52) (Sierksma.FB.KS 3 52) 5 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_44_52 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_44_52 (by simp)
  have r_AS_61_81 : Sierksma.FB.runR [0x1] (Sierksma.FB.pairSort (Sierksma.FB.R1.getD 4 0) 81) (Sierksma.FB.KS 4 81) 5 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_81 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_81 (by simp)
  have r_AS_44_197 : Sierksma.FB.runR [0xeb000030071600f3100123000030070e02679001230006300003006fe02679001230009b0006300003006f6686a401d960000500059001230009b000630000300e8600059001230009b000630000300bfe00f31001230000300a0600059001230003300003008d600059001230000300816000590012300033000030080e00059001230006300003007fe00059001230009b0006300003007f600f3100123000030071600f3100123000030070e02679001230006300003006fe02679001230009b0006300003006f6686a401d8e0000500059001230009b0002b0000300e860005900123001030009b0002b0000300bfe00f31001230000300a06000590012300103000bb00003008d6000590012300103000bb00003008160005900123000bb000030080e00059001230002b00003007fe00059001230009b0002b00003007f600f3100123000030071600f3100123000030070e0267100123001030002b00003006fe02671001230009b0002b00003006f6686a401d7e0000500f31001230006b0000300a060005900123000bb0006b00003008d60005900123000bb00003008160005900123000bb0006b000030080e00059001230002b00003007fe00f3100123000030071600f31001230006b000030070e02671001230002b00003006fe686a40009b01d7613ef1649e104a1201b5613ef16424904a12018ce473116424904a120009b016d657cd9649e104a120009b015a60268100f31649e104a1a014e657cd9649e104a120009b014de007f113ef1649e104a1a014ce007f113ef1649e104a1a014c60352900f316424904a1a013e600f31035296424904a1a0009b013de00059035296424904a1a013ce00059035296424904a1a013c663ab4, 0x7f100123000330000300a0600f310012300003008d600f3100123000030081600f3100123000030080e02e11001230006300003007fe02e11001230009b0006300003007f6007f1001230000300716007f10012300033000030070e007f1001230006300003006fe007f1001230009b0006300003006f6686a401e8e00005007f100123000eb0009b0002b0000300e86007f1001230009b0002b0000300bfe007f100123000eb000bb0000300a0600f310012300003008d600f3100123000030081600f3100123000030080e02e0900123000eb0002b00003007fe02e09001230009b0002b00003007f6007f100123000eb000bb0000300716007f100123000bb000030070e007f1001230002b00003006fe007f1001230009b0002b00003006f6686a401e7e00005007f100123000bb0006b0000300a0600f31001230006b00003008d600f3100123000030081600f31001230006b000030080e02e09001230002b00003007fe007f100123000bb0000300716007f100123000bb0006b000030070e007f1001230002b00003006fe686a40009b01e760000500f31001230006b0000300a06000590012300103000bb0006b00003008d6000590012300103000bb00003008160005900123000bb0006b000030080e00059001230002b00003007fe00f3100123000030071600f31001230006b000030070e0267900123001030002b00003006fe686a40009b01de6000050005900123000eb0009b000630000300e8600059001230009b000630000300bfe00f3100123000eb0000300a06000590012300003008d6000590012300003008160005900123000030080e0005900123000eb0006300003007fe00059001230009b0006300003007f600f3100123, 0x542721649e10361202926097e1686a100212027ce00005007f100123000eb000bb0006b0000300a0600f31001230006b00003008d600f3100123000030081600f31001230006b000030080e02e1100123000eb0002b00003007fe007f100123000eb000bb0000300716007f100123000bb0006b000030070e007f1001230002b00003006fe686a40009b01fb600005007f1001230009b000630000300e86007f100123001030009b000630000300bfe007f1001230000300a0600f31001230010300003008d600f310012300103000030081600f3100123000030080e02e11001230006300003007fe02e11001230009b0006300003007f6007f1001230000300716007f100123000030070e007f100123001030006300003006fe007f1001230009b0006300003006f6686a401e9600005007f1001230009b000630000300e86007f1001230009b000630000300bfe] (Sierksma.FB.pairSort (Sierksma.FB.R1.getD 3 0) 197) (Sierksma.FB.KS 3 197) 5 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_44_197 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_44_197 (by simp)
  have r_AS_61_262 : Sierksma.FB.runR [0x1] (Sierksma.FB.pairSort (Sierksma.FB.R1.getD 4 0) 262) (Sierksma.FB.KS 4 262) 5 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_61_262 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_61_262 (by simp)
  have r_AS_65_1402_x1 : Sierksma.FB.runR [0xfb104c61294a9436514731104a2a] [65, 130, 1402] (Sierksma.FB.xa0K 29 0) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x1 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x1 (by simp)
  have r_AS_65_1402_x2 : Sierksma.FB.runR [0xfb104c61294a9436514731104a2a] [65, 131, 1402] (Sierksma.FB.xa0K 29 1) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x2 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x2 (by simp)
  have r_AS_65_1402_x3 : Sierksma.FB.runR [0x482c9294a9436514731104a22] [65, 134, 1402] (Sierksma.FB.xa0K 29 2) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x3 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x3 (by simp)
  have r_AS_65_1402_x4 : Sierksma.FB.runR [0x482c9294a9436514731104a22] [65, 135, 1402] (Sierksma.FB.xa0K 29 3) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x4 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x4 (by simp)
  have r_AS_65_1402_x5 : Sierksma.FB.runR [0x292abe9294a9436514731104a2a] [65, 137, 1402] (Sierksma.FB.xa0K 29 4) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x5 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x5 (by simp)
  have r_AS_65_1402_x6 : Sierksma.FB.runR [0x292abe9294a9436514731104a2a] [65, 138, 1402] (Sierksma.FB.xa0K 29 5) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x6 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x6 (by simp)
  have r_AS_65_1402_x7 : Sierksma.FB.runR [0x1a1c90819915629436514731104a2a000c3] [65, 143, 1402] (Sierksma.FB.xa0K 29 6) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x7 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x7 (by simp)
  have r_AS_65_1402_x8 : Sierksma.FB.runR [0x1a1c90819915629436514731104a2a000c3] [65, 144, 1402] (Sierksma.FB.xa0K 29 7) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x8 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x8 (by simp)
  have r_AS_65_1402_x9 : Sierksma.FB.runR [0xfb957d6115629436514731104a2a] [65, 145, 1402] (Sierksma.FB.xa0K 29 8) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x9 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x9 (by simp)
  have r_AS_65_1402_x10 : Sierksma.FB.runR [0xfb957d6115629436514731104a2a] [65, 146, 1402] (Sierksma.FB.xa0K 29 9) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x10 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x10 (by simp)
  have r_AS_65_1402_x11 : Sierksma.FB.runR [0xfb957d6115629436514731104a2a] [65, 147, 1402] (Sierksma.FB.xa0K 29 10) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x11 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x11 (by simp)
  have r_AS_65_1402_x12 : Sierksma.FB.runR [0xfb957d6115629436514731104a2a] [65, 148, 1402] (Sierksma.FB.xa0K 29 11) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x12 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x12 (by simp)
  have r_AS_65_1402_x13 : Sierksma.FB.runR [0x352f143651053f955e7904a22] [65, 151, 1402] (Sierksma.FB.xa0K 29 12) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x13 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x13 (by simp)
  have r_AS_65_1402_x14 : Sierksma.FB.runR [0x352f143651053f955e7904a22] [65, 152, 1402] (Sierksma.FB.xa0K 29 13) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x14 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x14 (by simp)
  have r_AS_65_1402_x15 : Sierksma.FB.runR [0x2908119008210079904a22000c3] [65, 154, 1402] (Sierksma.FB.xa0K 29 14) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x15 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x15 (by simp)
  have r_AS_65_1402_x16 : Sierksma.FB.runR [0x2908119008210079904a22000c3] [65, 155, 1402] (Sierksma.FB.xa0K 29 15) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x16 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x16 (by simp)
  have r_AS_65_1402_x17 : Sierksma.FB.runR [0x2908119008210079904a22] [65, 156, 1402] (Sierksma.FB.xa0K 29 16) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x17 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x17 (by simp)
  have r_AS_65_1402_x18 : Sierksma.FB.runR [0x2908119008210079904a22] [65, 157, 1402] (Sierksma.FB.xa0K 29 17) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x18 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x18 (by simp)
  have r_AS_65_1402_x19 : Sierksma.FB.runR [0x2908119008210079904a22] [65, 158, 1402] (Sierksma.FB.xa0K 29 18) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x19 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x19 (by simp)
  have r_AS_65_1402_x20 : Sierksma.FB.runR [0x2908119008210079904a22] [65, 159, 1402] (Sierksma.FB.xa0K 29 19) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x20 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x20 (by simp)
  have r_AS_65_1402_x21 : Sierksma.FB.runR [0xfb10267912fc1668416d29104a2a] [65, 170, 1402] (Sierksma.FB.xa0K 29 20) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x21 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x21 (by simp)
  have r_AS_65_1402_x22 : Sierksma.FB.runR [0xfb10267912fc1668416d29104a2a] [65, 171, 1402] (Sierksma.FB.xa0K 29 21) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x22 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x22 (by simp)
  have r_AS_65_1402_x23 : Sierksma.FB.runR [0x7990266912fc1668416d29104a2a] [65, 174, 1402] (Sierksma.FB.xa0K 29 22) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x23 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x23 (by simp)
  have r_AS_65_1402_x24 : Sierksma.FB.runR [0x7990266912fc1668416d29104a2a] [65, 175, 1402] (Sierksma.FB.xa0K 29 23) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x24 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x24 (by simp)
  have r_AS_65_1402_x25 : Sierksma.FB.runR [0x32c8957cd955f0155e7904a22] [65, 178, 1402] (Sierksma.FB.xa0K 29 24) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x25 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x25 (by simp)
  have r_AS_65_1402_x26 : Sierksma.FB.runR [0x32c8957cd955f0155e7904a22] [65, 179, 1402] (Sierksma.FB.xa0K 29 25) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x26 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x26 (by simp)
  have r_AS_65_1402_x27 : Sierksma.FB.runR [0x28d894997138fc10079904a22000c3] [65, 188, 1402] (Sierksma.FB.xa0K 29 26) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x27 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x27 (by simp)
  have r_AS_65_1402_x28 : Sierksma.FB.runR [0x28d894997138fc10079904a22000c3] [65, 189, 1402] (Sierksma.FB.xa0K 29 27) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x28 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x28 (by simp)
  have r_AS_65_1402_x29 : Sierksma.FB.runR [0x6100fb9687114bf690079904a2a] [65, 190, 1402] (Sierksma.FB.xa0K 29 28) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x29 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x29 (by simp)
  have r_AS_65_1402_x30 : Sierksma.FB.runR [0x6100fb9687114bf690079904a2a] [65, 192, 1402] (Sierksma.FB.xa0K 29 29) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x30 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x30 (by simp)
  have r_AS_65_1402_x31 : Sierksma.FB.runR [0x6100fb9687114bf690079904a2a] [65, 193, 1402] (Sierksma.FB.xa0K 29 30) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x31 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x31 (by simp)
  have r_AS_65_1402_x32 : Sierksma.FB.runR [0x6100fb9687114bf690079904a2a] [65, 194, 1402] (Sierksma.FB.xa0K 29 31) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x32 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x32 (by simp)
  have r_AS_65_1402_x33 : Sierksma.FB.runR [0x53f155f0155e7904a1a] [65, 197, 1402] (Sierksma.FB.xa0K 29 32) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x33 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x33 (by simp)
  have r_AS_65_1402_x34 : Sierksma.FB.runR [0x53f155f0155e7904a1a] [65, 198, 1402] (Sierksma.FB.xa0K 29 33) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x34 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x34 (by simp)
  have r_AS_65_1402_x35 : Sierksma.FB.runR [0x51213f1109e92bb210811904a2a000c3] [65, 200, 1402] (Sierksma.FB.xa0K 29 34) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x35 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x35 (by simp)
  have r_AS_65_1402_x36 : Sierksma.FB.runR [0x51213f1109e92bb210811904a2a000c3] [65, 201, 1402] (Sierksma.FB.xa0K 29 35) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x36 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x36 (by simp)
  have r_AS_65_1402_x37 : Sierksma.FB.runR [0x51213f1109e92bb210811904a2a] [65, 202, 1402] (Sierksma.FB.xa0K 29 36) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x37 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x37 (by simp)
  have r_AS_65_1402_x38 : Sierksma.FB.runR [0x51213f1109e92bb210811904a2a] [65, 204, 1402] (Sierksma.FB.xa0K 29 37) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x38 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x38 (by simp)
  have r_AS_65_1402_x39 : Sierksma.FB.runR [0x51213f1109e92bb210811904a2a] [65, 205, 1402] (Sierksma.FB.xa0K 29 38) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x39 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x39 (by simp)
  have r_AS_65_1402_x40 : Sierksma.FB.runR [0x51213f1109e92bb210811904a2a] [65, 206, 1402] (Sierksma.FB.xa0K 29 39) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x40 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x40 (by simp)
  have r_AS_65_1402_x41 : Sierksma.FB.runR [0x516d29104c6104bf104a22] [65, 257, 1402] (Sierksma.FB.xa0K 29 40) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x41 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x41 (by simp)
  have r_AS_65_1402_x42 : Sierksma.FB.runR [0x516d29104c6104bf104a22] [65, 258, 1402] (Sierksma.FB.xa0K 29 41) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x42 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x42 (by simp)
  have r_AS_65_1402_x43 : Sierksma.FB.runR [0x55f01499090811904bf104a22] [65, 260, 1402] (Sierksma.FB.xa0K 29 42) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x43 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x43 (by simp)
  have r_AS_65_1402_x44 : Sierksma.FB.runR [0x55f01499090811904bf104a22] [65, 261, 1402] (Sierksma.FB.xa0K 29 43) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x44 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x44 (by simp)
  have r_AS_65_1402_x45 : Sierksma.FB.runR [0x55f01499090811904bf104a22000c3] [65, 262, 1402] (Sierksma.FB.xa0K 29 44) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x45 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x45 (by simp)
  have r_AS_65_1402_x46 : Sierksma.FB.runR [0x55f01499090811904bf104a22000c3] [65, 263, 1402] (Sierksma.FB.xa0K 29 45) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x46 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x46 (by simp)
  have r_AS_65_1402_x47 : Sierksma.FB.runR [0x55f01499090811904bf104a22] [65, 264, 1402] (Sierksma.FB.xa0K 29 46) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x47 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x47 (by simp)
  have r_AS_65_1402_x48 : Sierksma.FB.runR [0x55f01499090811904bf104a22] [65, 265, 1402] (Sierksma.FB.xa0K 29 47) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x48 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x48 (by simp)
  have r_AS_65_1402_x49 : Sierksma.FB.runR [0x17c31294a96ac9904bf104a22] [65, 267, 1402] (Sierksma.FB.xa0K 29 48) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x49 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x49 (by simp)
  have r_AS_65_1402_x50 : Sierksma.FB.runR [0x17c31294a96ac9904bf104a22] [65, 268, 1402] (Sierksma.FB.xa0K 29 49) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x50 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x50 (by simp)
  have r_AS_65_1402_x51 : Sierksma.FB.runR [0x5d86104c6104bf104a1a] [65, 271, 1402] (Sierksma.FB.xa0K 29 50) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x51 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x51 (by simp)
  have r_AS_65_1402_x52 : Sierksma.FB.runR [0x5d86104c6104bf104a1a] [65, 272, 1402] (Sierksma.FB.xa0K 29 51) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x52 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x52 (by simp)
  have r_AS_65_1402_x53 : Sierksma.FB.runR [0x516d29104c6104bf104a22] [65, 274, 1402] (Sierksma.FB.xa0K 29 52) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x53 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x53 (by simp)
  have r_AS_65_1402_x54 : Sierksma.FB.runR [0x516d29104c6104bf104a22] [65, 275, 1402] (Sierksma.FB.xa0K 29 53) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x54 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x54 (by simp)
  have r_AS_65_1402_x55 : Sierksma.FB.runR [0x516d29104c6104bf104a22000c3] [65, 276, 1402] (Sierksma.FB.xa0K 29 54) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x55 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x55 (by simp)
  have r_AS_65_1402_x56 : Sierksma.FB.runR [0x516d29104c6104bf104a22000c3] [65, 277, 1402] (Sierksma.FB.xa0K 29 55) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x56 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x56 (by simp)
  have r_AS_65_1402_x57 : Sierksma.FB.runR [0x516d29104c6104bf104a22] [65, 278, 1402] (Sierksma.FB.xa0K 29 56) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x57 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x57 (by simp)
  have r_AS_65_1402_x58 : Sierksma.FB.runR [0x516d29104c6104bf104a22] [65, 279, 1402] (Sierksma.FB.xa0K 29 57) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x58 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x58 (by simp)
  have r_AS_65_1402_x59 : Sierksma.FB.runR [0xa791294a957cd955e7904a22] [65, 282, 1402] (Sierksma.FB.xa0K 29 58) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x59 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x59 (by simp)
  have r_AS_65_1402_x60 : Sierksma.FB.runR [0xa791294a957cd955e7904a22] [65, 283, 1402] (Sierksma.FB.xa0K 29 59) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x60 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x60 (by simp)
  have r_AS_65_1402_x61 : Sierksma.FB.runR [0x1198155f0155e7904a1a] [65, 297, 1402] (Sierksma.FB.xa0K 29 60) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x61 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x61 (by simp)
  have r_AS_65_1402_x62 : Sierksma.FB.runR [0x1198155f0155e7904a1a] [65, 298, 1402] (Sierksma.FB.xa0K 29 61) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x62 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x62 (by simp)
  have r_AS_65_1402_x63 : Sierksma.FB.runR [0x1198155f0155e7904a1a000c3] [65, 299, 1402] (Sierksma.FB.xa0K 29 62) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x63 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x63 (by simp)
  have r_AS_65_1402_x64 : Sierksma.FB.runR [0x1198155f0155e7904a1a000c3] [65, 300, 1402] (Sierksma.FB.xa0K 29 63) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x64 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x64 (by simp)
  have r_AS_65_1402_x65 : Sierksma.FB.runR [0x1198155f0155e7904a1a] [65, 301, 1402] (Sierksma.FB.xa0K 29 64) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x65 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x65 (by simp)
  have r_AS_65_1402_x66 : Sierksma.FB.runR [0x1198155f0155e7904a1a] [65, 302, 1402] (Sierksma.FB.xa0K 29 65) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x66 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x66 (by simp)
  have r_AS_65_1402_x67 : Sierksma.FB.runR [0x296d29104c6104bf104a22] [65, 304, 1402] (Sierksma.FB.xa0K 29 66) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x67 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x67 (by simp)
  have r_AS_65_1402_x68 : Sierksma.FB.runR [0x296d29104c6104bf104a22] [65, 305, 1402] (Sierksma.FB.xa0K 29 67) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x68 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x68 (by simp)
  have r_AS_65_1402_x69 : Sierksma.FB.runR [0x296d29104c6104bf104a22000c3] [65, 306, 1402] (Sierksma.FB.xa0K 29 68) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x69 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x69 (by simp)
  have r_AS_65_1402_x70 : Sierksma.FB.runR [0x296d29104c6104bf104a22000c3] [65, 308, 1402] (Sierksma.FB.xa0K 29 69) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x70 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x70 (by simp)
  have r_AS_65_1402_x71 : Sierksma.FB.runR [0x296d29104c6104bf104a22] [65, 309, 1402] (Sierksma.FB.xa0K 29 70) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x71 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x71 (by simp)
  have r_AS_65_1402_x72 : Sierksma.FB.runR [0x296d29104c6104bf104a22] [65, 310, 1402] (Sierksma.FB.xa0K 29 71) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x72 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x72 (by simp)
  have r_AS_65_1402_x73 : Sierksma.FB.runR [0x213f16ac9955f016684104a22] [65, 312, 1402] (Sierksma.FB.xa0K 29 72) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x73 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x73 (by simp)
  have r_AS_65_1402_x74 : Sierksma.FB.runR [0x213f16ac9955f016684104a22] [65, 313, 1402] (Sierksma.FB.xa0K 29 73) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x74 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x74 (by simp)
  have r_AS_65_1402_x75 : Sierksma.FB.runR [0x6144d4139ee1294a96684104a2a000c3] [65, 314, 1402] (Sierksma.FB.xa0K 29 74) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x75 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x75 (by simp)
  have r_AS_65_1402_x76 : Sierksma.FB.runR [0x6144d4139ee1294a96684104a2a000c3] [65, 315, 1402] (Sierksma.FB.xa0K 29 75) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x76 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x76 (by simp)
  have r_AS_65_1402_x77 : Sierksma.FB.runR [0x213f16ac9955f016684104a22] [65, 316, 1402] (Sierksma.FB.xa0K 29 76) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x77 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x77 (by simp)
  have r_AS_65_1402_x78 : Sierksma.FB.runR [0x213f16ac9955f016684104a22] [65, 317, 1402] (Sierksma.FB.xa0K 29 77) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x78 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x78 (by simp)
  have r_AS_65_1402_x79 : Sierksma.FB.runR [0x213f15390155f016684104a22] [65, 324, 1402] (Sierksma.FB.xa0K 29 78) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x79 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x79 (by simp)
  have r_AS_65_1402_x80 : Sierksma.FB.runR [0x213f15390155f016684104a22] [65, 325, 1402] (Sierksma.FB.xa0K 29 79) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x80 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x80 (by simp)
  have r_AS_65_1402_x81 : Sierksma.FB.runR [0x723938fc138f416684104a22000c3] [65, 326, 1402] (Sierksma.FB.xa0K 29 80) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x81 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x81 (by simp)
  have r_AS_65_1402_x82 : Sierksma.FB.runR [0x723938fc138f416684104a22000c3] [65, 327, 1402] (Sierksma.FB.xa0K 29 81) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x82 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x82 (by simp)
  have r_AS_65_1402_x83 : Sierksma.FB.runR [0x213f15390155f016684104a22] [65, 328, 1402] (Sierksma.FB.xa0K 29 82) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x83 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x83 (by simp)
  have r_AS_65_1402_x84 : Sierksma.FB.runR [0x213f15390155f016684104a22] [65, 329, 1402] (Sierksma.FB.xa0K 29 83) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x84 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x84 (by simp)
  have r_AS_65_1402_x85 : Sierksma.FB.runR [0x262121bb104bf10a00145c4904a2a] [65, 331, 1402] (Sierksma.FB.xa0K 29 84) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x85 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x85 (by simp)
  have r_AS_65_1402_x86 : Sierksma.FB.runR [0x262121bb104bf10a00145c4904a2a] [65, 332, 1402] (Sierksma.FB.xa0K 29 85) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x86 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x86 (by simp)
  have r_AS_65_1402_x87 : Sierksma.FB.runR [0x35b14bf01294a904bf104a22000c3] [65, 333, 1402] (Sierksma.FB.xa0K 29 86) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x87 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x87 (by simp)
  have r_AS_65_1402_x88 : Sierksma.FB.runR [0x35b14bf01294a904bf104a22000c3] [65, 335, 1402] (Sierksma.FB.xa0K 29 87) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x88 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x88 (by simp)
  have r_AS_65_1402_x89 : Sierksma.FB.runR [0x262121bb104bf10a00145c4904a2a] [65, 336, 1402] (Sierksma.FB.xa0K 29 88) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x89 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x89 (by simp)
  have r_AS_65_1402_x90 : Sierksma.FB.runR [0x262121bb104bf10a00145c4904a2a] [65, 337, 1402] (Sierksma.FB.xa0K 29 89) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x90 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x90 (by simp)
  have r_AS_65_1402_x91 : Sierksma.FB.runR [0x53f155f0155e7904a1a] [65, 340, 1402] (Sierksma.FB.xa0K 29 90) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x91 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x91 (by simp)
  have r_AS_65_1402_x92 : Sierksma.FB.runR [0x53f155f0155e7904a1a] [65, 341, 1402] (Sierksma.FB.xa0K 29 91) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x92 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x92 (by simp)
  have r_AS_65_1402_x93 : Sierksma.FB.runR [0x53f155f0155e7904a1a000c3] [65, 342, 1402] (Sierksma.FB.xa0K 29 92) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x93 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x93 (by simp)
  have r_AS_65_1402_x94 : Sierksma.FB.runR [0x53f155f0155e7904a1a000c3] [65, 343, 1402] (Sierksma.FB.xa0K 29 93) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x94 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x94 (by simp)
  have r_AS_65_1402_x95 : Sierksma.FB.runR [0x53f155f0155e7904a1a] [65, 344, 1402] (Sierksma.FB.xa0K 29 94) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x95 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x95 (by simp)
  have r_AS_65_1402_x96 : Sierksma.FB.runR [0x53f155f0155e7904a1a] [65, 345, 1402] (Sierksma.FB.xa0K 29 95) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x96 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x96 (by simp)
  have r_AS_65_1402_x97 : Sierksma.FB.runR [0x35b132c89111616d29104a22] [65, 405, 1402] (Sierksma.FB.xa0K 29 96) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x97 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x97 (by simp)
  have r_AS_65_1402_x98 : Sierksma.FB.runR [0x35b132c89111616d29104a22] [65, 406, 1402] (Sierksma.FB.xa0K 29 97) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x98 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x98 (by simp)
  have r_AS_65_1402_x99 : Sierksma.FB.runR [0x35b132c89111616d29104a22] [65, 407, 1402] (Sierksma.FB.xa0K 29 98) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x99 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x99 (by simp)
  have r_AS_65_1402_x100 : Sierksma.FB.runR [0x35b132c89111616d29104a22] [65, 408, 1402] (Sierksma.FB.xa0K 29 99) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x100 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x100 (by simp)
  have r_AS_65_1402_x101 : Sierksma.FB.runR [0x35b132c89111616d29104a22000c3] [65, 409, 1402] (Sierksma.FB.xa0K 29 100) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x101 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x101 (by simp)
  have r_AS_65_1402_x102 : Sierksma.FB.runR [0x35b132c89111616d29104a22000c3] [65, 410, 1402] (Sierksma.FB.xa0K 29 101) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x102 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x102 (by simp)
  have r_AS_65_1402_x103 : Sierksma.FB.runR [0x378f1642496d29155e7904a22] [65, 412, 1402] (Sierksma.FB.xa0K 29 102) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x103 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x103 (by simp)
  have r_AS_65_1402_x104 : Sierksma.FB.runR [0x378f1642496d29155e7904a22] [65, 413, 1402] (Sierksma.FB.xa0K 29 103) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x104 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x104 (by simp)
  have r_AS_65_1402_x105 : Sierksma.FB.runR [0x378f1642496d29155e7904a22] [65, 414, 1402] (Sierksma.FB.xa0K 29 104) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x105 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x105 (by simp)
  have r_AS_65_1402_x106 : Sierksma.FB.runR [0x378f1642496d29155e7904a22] [65, 416, 1402] (Sierksma.FB.xa0K 29 105) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x106 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x106 (by simp)
  have r_AS_65_1402_x107 : Sierksma.FB.runR [0x378f1642496d29155e7904a22000c3] [65, 417, 1402] (Sierksma.FB.xa0K 29 106) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x107 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x107 (by simp)
  have r_AS_65_1402_x108 : Sierksma.FB.runR [0x378f1642496d29155e7904a22000c3] [65, 418, 1402] (Sierksma.FB.xa0K 29 107) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x108 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x108 (by simp)
  have r_AS_65_1402_x109 : Sierksma.FB.runR [0x111e145cb145c4904a1a] [65, 420, 1402] (Sierksma.FB.xa0K 29 108) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x109 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x109 (by simp)
  have r_AS_65_1402_x110 : Sierksma.FB.runR [0x111e145cb145c4904a1a] [65, 421, 1402] (Sierksma.FB.xa0K 29 109) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x110 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x110 (by simp)
  have r_AS_65_1402_x111 : Sierksma.FB.runR [0x111e145cb145c4904a1a] [65, 422, 1402] (Sierksma.FB.xa0K 29 110) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x111 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x111 (by simp)
  have r_AS_65_1402_x112 : Sierksma.FB.runR [0x111e145cb145c4904a1a] [65, 423, 1402] (Sierksma.FB.xa0K 29 111) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x112 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x112 (by simp)
  have r_AS_65_1402_x113 : Sierksma.FB.runR [0x111e145cb145c4904a1a000c3] [65, 424, 1402] (Sierksma.FB.xa0K 29 112) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x113 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x113 (by simp)
  have r_AS_65_1402_x114 : Sierksma.FB.runR [0x111e145cb145c4904a1a000c3] [65, 425, 1402] (Sierksma.FB.xa0K 29 113) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x114 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x114 (by simp)
  have r_AS_65_1402_x115 : Sierksma.FB.runR [0x6613164249686a155e7904a22] [65, 432, 1402] (Sierksma.FB.xa0K 29 114) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x115 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x115 (by simp)
  have r_AS_65_1402_x116 : Sierksma.FB.runR [0x6613164249686a155e7904a22] [65, 433, 1402] (Sierksma.FB.xa0K 29 115) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x116 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x116 (by simp)
  have r_AS_65_1402_x117 : Sierksma.FB.runR [0x6613164249686a155e7904a22] [65, 434, 1402] (Sierksma.FB.xa0K 29 116) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x117 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x117 (by simp)
  have r_AS_65_1402_x118 : Sierksma.FB.runR [0x6613164249686a155e7904a22] [65, 435, 1402] (Sierksma.FB.xa0K 29 117) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x118 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x118 (by simp)
  have r_AS_65_1402_x119 : Sierksma.FB.runR [0x6613164249686a155e7904a22000c3] [65, 436, 1402] (Sierksma.FB.xa0K 29 118) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x119 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x119 (by simp)
  have r_AS_65_1402_x120 : Sierksma.FB.runR [0x6613164249686a155e7904a22000c3] [65, 437, 1402] (Sierksma.FB.xa0K 29 119) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x120 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x120 (by simp)
  have r_AS_65_1402_x121 : Sierksma.FB.runR [0xfb96ac9955f016684104a22] [65, 439, 1402] (Sierksma.FB.xa0K 29 120) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x121 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x121 (by simp)
  have r_AS_65_1402_x122 : Sierksma.FB.runR [0xfb96ac9955f016684104a22] [65, 440, 1402] (Sierksma.FB.xa0K 29 121) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x122 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x122 (by simp)
  have r_AS_65_1402_x123 : Sierksma.FB.runR [0xfb96ac9955f016684104a22] [65, 441, 1402] (Sierksma.FB.xa0K 29 122) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x123 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x123 (by simp)
  have r_AS_65_1402_x124 : Sierksma.FB.runR [0xfb96ac9955f016684104a22] [65, 443, 1402] (Sierksma.FB.xa0K 29 123) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x124 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x124 (by simp)
  have r_AS_65_1402_x125 : Sierksma.FB.runR [0xfb96ac9955f016684104a22000c3] [65, 444, 1402] (Sierksma.FB.xa0K 29 124) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x125 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x125 (by simp)
  have r_AS_65_1402_x126 : Sierksma.FB.runR [0xfb96ac9955f016684104a22000c3] [65, 445, 1402] (Sierksma.FB.xa0K 29 125) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x126 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x126 (by simp)
  have r_AS_65_1402_x127 : Sierksma.FB.runR [0x266912fc138f416684104a22] [65, 448, 1402] (Sierksma.FB.xa0K 29 126) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x127 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x127 (by simp)
  have r_AS_65_1402_x128 : Sierksma.FB.runR [0x266912fc138f416684104a22] [65, 449, 1402] (Sierksma.FB.xa0K 29 127) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x128 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x128 (by simp)
  have r_AS_65_1402_x129 : Sierksma.FB.runR [0x266912fc138f416684104a22] [65, 450, 1402] (Sierksma.FB.xa0K 29 128) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x129 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x129 (by simp)
  have r_AS_65_1402_x130 : Sierksma.FB.runR [0x266912fc138f416684104a22] [65, 451, 1402] (Sierksma.FB.xa0K 29 129) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x130 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x130 (by simp)
  have r_AS_65_1402_x131 : Sierksma.FB.runR [0x34b5118ae157cd96684104a22000c3] [65, 452, 1402] (Sierksma.FB.xa0K 29 130) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x131 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x131 (by simp)
  have r_AS_65_1402_x132 : Sierksma.FB.runR [0x34b5118ae157cd96684104a22000c3] [65, 453, 1402] (Sierksma.FB.xa0K 29 131) 4 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x132 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x132 (by simp)
  have r_AS_65_1402_x133_x1 : Sierksma.FB.runR [0x358100123000c30003300003] [65, 140, 467, 1402] (Sierksma.FB.xa0K 30 0) 3 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x133_x1 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x133_x1 (by simp)
  have r_AS_65_1402_x133_x2 : Sierksma.FB.runR [0x35810012300003] [65, 141, 467, 1402] (Sierksma.FB.xa0K 30 1) 3 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x133_x2 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x133_x2 (by simp)
  have r_AS_65_1402_x133_x3 : Sierksma.FB.runR [0xfb900123000c30003300003] [65, 161, 467, 1402] (Sierksma.FB.xa0K 30 2) 3 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x133_x3 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x133_x3 (by simp)
  have r_AS_65_1402_x133_x4 : Sierksma.FB.runR [0xfb90012300113000c30003300003] [65, 162, 467, 1402] (Sierksma.FB.xa0K 30 3) 3 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x133_x4 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x133_x4 (by simp)
  have r_AS_65_1402_x133_x5 : Sierksma.FB.runR [0xfb90012300003] [65, 163, 467, 1402] (Sierksma.FB.xa0K 30 4) 3 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x133_x5 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x133_x5 (by simp)
  have r_AS_65_1402_x133_x6 : Sierksma.FB.runR [0xfb9001230011300003] [65, 165, 467, 1402] (Sierksma.FB.xa0K 30 5) 3 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x133_x6 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x133_x6 (by simp)
  have r_AS_65_1402_x133_x7 : Sierksma.FB.runR [0xfb900123000fb00003] [65, 166, 467, 1402] (Sierksma.FB.xa0K 30 6) 3 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x133_x7 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x133_x7 (by simp)
  have r_AS_65_1402_x133_x8 : Sierksma.FB.runR [0xfb900123000fb00003] [65, 167, 467, 1402] (Sierksma.FB.xa0K 30 7) 3 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x133_x8 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x133_x8 (by simp)
  have r_AS_65_1402_x133_x9 : Sierksma.FB.runR [0x35810012300113000c30003300003] [65, 181, 467, 1402] (Sierksma.FB.xa0K 30 8) 3 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x133_x9 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x133_x9 (by simp)
  have r_AS_65_1402_x133_x10 : Sierksma.FB.runR [0x358100123000c30003300003] [65, 182, 467, 1402] (Sierksma.FB.xa0K 30 9) 3 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x133_x10 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x133_x10 (by simp)
  have r_AS_65_1402_x133_x11 : Sierksma.FB.runR [0x358100123000fb00003] [65, 183, 467, 1402] (Sierksma.FB.xa0K 30 10) 3 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x133_x11 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x133_x11 (by simp)
  have r_AS_65_1402_x133_x12 : Sierksma.FB.runR [0x358100123000fb00003] [65, 184, 467, 1402] (Sierksma.FB.xa0K 30 11) 3 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x133_x12 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x133_x12 (by simp)
  have r_AS_65_1402_x133_x13 : Sierksma.FB.runR [0x35810012300003] [65, 185, 467, 1402] (Sierksma.FB.xa0K 30 12) 3 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x133_x13 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x133_x13 (by simp)
  have r_AS_65_1402_x133_x14 : Sierksma.FB.runR [0x3581001230011300003] [65, 186, 467, 1402] (Sierksma.FB.xa0K 30 13) 3 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x133_x14 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x133_x14 (by simp)
  have r_AS_65_1402_x133_x15 : Sierksma.FB.runR [0xfb900123000c30003300003] [65, 208, 467, 1402] (Sierksma.FB.xa0K 30 14) 3 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x133_x15 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x133_x15 (by simp)
  have r_AS_65_1402_x133_x16 : Sierksma.FB.runR [0xfb90012300113000c30003300003] [65, 209, 467, 1402] (Sierksma.FB.xa0K 30 15) 3 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x133_x16 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x133_x16 (by simp)
  have r_AS_65_1402_x133_x17 : Sierksma.FB.runR [0xfb90012300003] [65, 210, 467, 1402] (Sierksma.FB.xa0K 30 16) 3 (Sierksma.FB.capsOf 3 4) [] = true := by decide +kernel
  have g_AS_65_1402_x133_x17 := Sierksma.FB.run_sound _ _ _ _ _ _ r_AS_65_1402_x133_x17 (by simp)
  exact ⟨g_AS_61_1403_x174, g_AS_61_1403_x175, g_AS_61_1403_x176, g_AS_61_1403_x177, g_AS_61_1403_x178, g_AS_61_1403_x179, g_AS_61_1403_x180, g_AS_61_1403_x181, g_AS_61_1403_x182, g_AS_61_1403_x183, g_AS_61_1403_x184, g_AS_61_1403_x185, g_AS_61_1403_x186, g_AS_61_1403_x187, g_AS_61_1403_x188, g_AS_61_1403_x189, g_AS_61_1403_x190, g_AS_61_1403_x191, g_AS_61_1403_x192, g_AS_61_1403_x193, g_AS_61_1403_x194, g_AS_61_1403_x195, g_AS_61_1403_x196, g_AS_61_1403_x197, g_AS_61_1403_x198, g_AS_61_1403_x199, g_AS_61_1403_x200, g_AS_61_1403_x201, g_AS_61_1403_x202, g_AS_61_1403_x203, g_AS_61_1403_x204, g_AS_61_1403_x205, g_AS_61_1403_x206, g_AS_61_1403_x207, g_AS_61_1403_x208, g_AS_61_1403_x209, g_AS_61_1403_x210, g_AS_61_1403_x211, g_AS_61_1403_x212, g_AS_61_1403_x213, g_AS_61_1403_x214, g_AS_61_1403_x215, g_AS_61_1403_x216, g_AS_61_1403_x217, g_AS_61_1403_x218, g_AS_61_1403_x219, g_AS_61_1403_x220, g_AS_61_1403_x221, g_AS_61_1403_x222, g_AS_61_1403_x223, g_AS_61_1403_x224, g_AS_61_1403_x225, g_AS_61_1403_x226, g_AS_61_1403_x227, g_AS_61_1403_x228, g_AS_61_1403_x229, g_AS_61_1403_x230, g_AS_61_1403_x231, g_AS_61_1403_x232, g_AS_61_1403_x233, g_AS_61_1403_x234, g_AS_61_1403_x235, g_AS_61_1403_x236, g_AS_61_1403_x237, g_AS_61_1403_x238, g_AS_61_1403_x239, g_AS_61_1403_x240, g_AS_61_1403_x241, g_AS_61_1403_x242, g_AS_61_1403_x243, g_AS_61_1403_x244, g_AS_61_1403_x245, g_AS_61_1403_x246, g_AS_61_1403_x247, g_AS_61_1403_x248, g_AS_61_1403_x249, g_AS_61_1403_x250, g_AS_61_1403_x251, g_AS_61_1403_x252, g_AS_61_1403_x253, g_AS_61_1403_x254, g_AS_61_1403_x255, g_AS_61_1403_x256, g_AS_61_1403_x257, g_AS_61_1403_x258, g_AS_61_1403_x259, g_AS_61_1403_x260, g_AS_61_1403_x261, g_AS_61_1403_x262, g_AS_61_1403_x263, g_AS_61_1403_x264, g_AS_61_1403_x265, g_AS_61_1403_x266, g_AS_61_1403_x267, g_AS_61_1403_x268, g_AS_61_1403_x269, g_AS_61_1403_x270, g_AS_61_1403_x271, g_AS_61_1403_x272, g_AS_61_1403_x273, g_AS_61_1403_x274, g_AS_61_1403_x275, g_AS_61_1403_x276, g_AS_61_1403_x277, g_AS_61_1403_x278, g_AS_61_1403_x279, g_AS_61_1403_x280, g_AS_61_1403_x281, g_AS_61_1403_x282, g_AS_61_1403_x283, g_AS_61_1403_x284, g_AS_61_1403_x285, g_AS_61_1403_x286, g_AS_61_1403_x287, g_AS_61_1403_x288, g_AS_61_1403_x289, g_AS_61_1403_x290, g_AS_61_1403_x291, g_AS_61_1403_x292, g_AS_61_1403_x293, g_AS_61_1403_x294, g_AS_61_1403_x295, g_AS_61_1403_x296, g_AS_61_1403_x297, g_AS_61_1403_x298, g_AS_61_1403_x299, g_AS_61_1403_x300, g_AS_61_1403_x301, g_AS_61_1403_x302, g_AS_61_1403_x303, g_AS_61_1403_x304, g_AS_61_1403_x305, g_AS_61_1403_x306, g_AS_61_1403_x307, g_AS_61_1403_x308, g_AS_61_1403_x309, g_AS_61_1403_x310, g_AS_61_1403_x311, g_AS_61_1403_x312, g_AS_61_1403_x313, g_AS_61_1403_x314, g_AS_61_1403_x315, g_AS_61_1403_x316, g_AS_61_1403_x317, g_AS_61_1403_x318, g_AS_61_1403_x319, g_AS_61_1403_x320, g_AS_61_1403_x321, g_AS_61_1403_x322, g_AS_61_1403_x323, g_AS_61_1403_x324, g_AS_61_1403_x325, g_AS_61_1403_x326, g_AS_61_1403_x327, g_AS_61_1403_x328, g_AS_61_1403_x329, g_AS_61_1403_x330, g_AS_61_1403_x331, g_AS_61_1403_x332, g_AS_61_1403_x333, g_AS_61_1403_x334, g_AS_61_1403_x335, g_AS_61_1403_x336, g_AS_61_1403_x337, g_AS_61_1403_x338, g_AS_61_1403_x339, g_AS_61_1403_x340, g_AS_61_1403_x341, g_AS_61_1403_x342, g_AS_61_1403_x343, g_AS_61_1403_x344, g_AS_61_1403_x345, g_AS_61_1403_x346, g_AS_61_1403_x347, g_AS_61_1403_x348, g_AS_61_1403_x349, g_AS_61_1403_x350, g_AS_61_1403_x351, g_AS_61_1403_x352, g_AS_61_1403_x353, g_AS_61_1403_x354, g_AS_61_1403_x355, g_AS_61_1403_x356, g_AS_61_1403_x357, g_AS_61_1403_x358, g_AS_61_1403_x359, g_AS_61_1403_x360, g_AS_61_1403_x361, g_AS_61_1403_x362, g_AS_61_1403_x363, g_AS_61_1403_x364, g_AS_61_1403_x365, g_AS_61_1403_x366, g_AS_61_1403_x367, g_AS_61_1403_x368, g_AS_61_1403_x369, g_AS_61_1403_x370, g_AS_61_1403_x371, g_AS_61_1403_x372, g_AS_61_1403_x373, g_AS_61_1403_x374, g_AS_61_1403_x375, g_AS_61_1403_x376, g_AS_61_1403_x377, g_AS_61_1403_x378, g_AS_61_1403_x379, g_AS_61_1403_x380, g_AS_61_1403_x381, g_AS_61_1403_x382, g_AS_61_1403_x383, g_AS_61_1403_x384, g_AS_61_1403_x385, g_AS_61_1403_x386, g_AS_61_1403_x387, g_AS_61_1403_x388, g_AS_61_1403_x389, g_AS_61_1403_x390, g_AS_61_1403_x391, g_AS_61_1403_x392, g_AS_61_1403_x393, g_AS_61_1403_x394, g_AS_61_1403_x395, g_AS_61_1403_x396, g_AS_61_1403_x397, g_AS_61_1403_x398, g_AS_61_1403_x399, g_AS_61_1403_x400, g_AS_61_1403_x401, g_AS_61_1403_x402, g_AS_61_1403_x403, g_AS_61_1403_x404, g_AS_61_1403_x405, g_AS_61_1403_x406, g_AS_61_1403_x407, g_AS_61_1403_x408, g_AS_61_1403_x409, g_AS_61_1403_x410, g_AS_61_1403_x411, g_AS_61_1403_x412, g_AS_61_1403_x413, g_AS_61_1403_x414, g_AS_61_1403_x415, g_AS_61_1403_x416, g_AS_61_1403_x417, g_AS_61_1403_x418, g_AS_61_1403_x419, g_AS_61_1403_x420, g_AS_61_1403_x421, g_AS_61_1403_x422, g_AS_61_1403_x423, g_AS_61_1403_x424, g_AS_4_28, g_AS_4_41, g_AS_44_52, g_AS_61_81, g_AS_44_197, g_AS_61_262, g_AS_65_1402_x1, g_AS_65_1402_x2, g_AS_65_1402_x3, g_AS_65_1402_x4, g_AS_65_1402_x5, g_AS_65_1402_x6, g_AS_65_1402_x7, g_AS_65_1402_x8, g_AS_65_1402_x9, g_AS_65_1402_x10, g_AS_65_1402_x11, g_AS_65_1402_x12, g_AS_65_1402_x13, g_AS_65_1402_x14, g_AS_65_1402_x15, g_AS_65_1402_x16, g_AS_65_1402_x17, g_AS_65_1402_x18, g_AS_65_1402_x19, g_AS_65_1402_x20, g_AS_65_1402_x21, g_AS_65_1402_x22, g_AS_65_1402_x23, g_AS_65_1402_x24, g_AS_65_1402_x25, g_AS_65_1402_x26, g_AS_65_1402_x27, g_AS_65_1402_x28, g_AS_65_1402_x29, g_AS_65_1402_x30, g_AS_65_1402_x31, g_AS_65_1402_x32, g_AS_65_1402_x33, g_AS_65_1402_x34, g_AS_65_1402_x35, g_AS_65_1402_x36, g_AS_65_1402_x37, g_AS_65_1402_x38, g_AS_65_1402_x39, g_AS_65_1402_x40, g_AS_65_1402_x41, g_AS_65_1402_x42, g_AS_65_1402_x43, g_AS_65_1402_x44, g_AS_65_1402_x45, g_AS_65_1402_x46, g_AS_65_1402_x47, g_AS_65_1402_x48, g_AS_65_1402_x49, g_AS_65_1402_x50, g_AS_65_1402_x51, g_AS_65_1402_x52, g_AS_65_1402_x53, g_AS_65_1402_x54, g_AS_65_1402_x55, g_AS_65_1402_x56, g_AS_65_1402_x57, g_AS_65_1402_x58, g_AS_65_1402_x59, g_AS_65_1402_x60, g_AS_65_1402_x61, g_AS_65_1402_x62, g_AS_65_1402_x63, g_AS_65_1402_x64, g_AS_65_1402_x65, g_AS_65_1402_x66, g_AS_65_1402_x67, g_AS_65_1402_x68, g_AS_65_1402_x69, g_AS_65_1402_x70, g_AS_65_1402_x71, g_AS_65_1402_x72, g_AS_65_1402_x73, g_AS_65_1402_x74, g_AS_65_1402_x75, g_AS_65_1402_x76, g_AS_65_1402_x77, g_AS_65_1402_x78, g_AS_65_1402_x79, g_AS_65_1402_x80, g_AS_65_1402_x81, g_AS_65_1402_x82, g_AS_65_1402_x83, g_AS_65_1402_x84, g_AS_65_1402_x85, g_AS_65_1402_x86, g_AS_65_1402_x87, g_AS_65_1402_x88, g_AS_65_1402_x89, g_AS_65_1402_x90, g_AS_65_1402_x91, g_AS_65_1402_x92, g_AS_65_1402_x93, g_AS_65_1402_x94, g_AS_65_1402_x95, g_AS_65_1402_x96, g_AS_65_1402_x97, g_AS_65_1402_x98, g_AS_65_1402_x99, g_AS_65_1402_x100, g_AS_65_1402_x101, g_AS_65_1402_x102, g_AS_65_1402_x103, g_AS_65_1402_x104, g_AS_65_1402_x105, g_AS_65_1402_x106, g_AS_65_1402_x107, g_AS_65_1402_x108, g_AS_65_1402_x109, g_AS_65_1402_x110, g_AS_65_1402_x111, g_AS_65_1402_x112, g_AS_65_1402_x113, g_AS_65_1402_x114, g_AS_65_1402_x115, g_AS_65_1402_x116, g_AS_65_1402_x117, g_AS_65_1402_x118, g_AS_65_1402_x119, g_AS_65_1402_x120, g_AS_65_1402_x121, g_AS_65_1402_x122, g_AS_65_1402_x123, g_AS_65_1402_x124, g_AS_65_1402_x125, g_AS_65_1402_x126, g_AS_65_1402_x127, g_AS_65_1402_x128, g_AS_65_1402_x129, g_AS_65_1402_x130, g_AS_65_1402_x131, g_AS_65_1402_x132, g_AS_65_1402_x133_x1, g_AS_65_1402_x133_x2, g_AS_65_1402_x133_x3, g_AS_65_1402_x133_x4, g_AS_65_1402_x133_x5, g_AS_65_1402_x133_x6, g_AS_65_1402_x133_x7, g_AS_65_1402_x133_x8, g_AS_65_1402_x133_x9, g_AS_65_1402_x133_x10, g_AS_65_1402_x133_x11, g_AS_65_1402_x133_x12, g_AS_65_1402_x133_x13, g_AS_65_1402_x133_x14, g_AS_65_1402_x133_x15, g_AS_65_1402_x133_x16, g_AS_65_1402_x133_x17⟩

import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_0
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_1
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_2
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_3
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_5
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_8
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_9
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_11
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_12
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_14
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_15
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_37
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_38
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_39
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_40
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_41
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_42
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_43
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_44
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_45
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem proof_Sierksma_FB_famB : ∀ k < 6, ∀ r2 ∈ Sierksma.FB.rootList k,
    Sierksma.FB.Good (Sierksma.FB.memBits (Sierksma.FB.pairSort (Sierksma.FB.R1.getD k 0) r2)) (Sierksma.FB.KS k r2) 5 (Sierksma.FB.capsOf 2 5) := by
  obtain ⟨g_BS_0_1, g_BS_0_15, g_BS_0_16, g_BS_0_40, g_BS_0_41, g_BS_0_215, g_BS_0_216, g_BS_4_0, g_BS_4_1, g_BS_4_5, g_BS_4_8, g_BS_4_9, g_BS_4_15, g_BS_4_16, g_BS_4_19, g_BS_4_20, g_BS_4_23, g_BS_4_24, g_BS_4_27, g_BS_4_28, g_BS_4_37, g_BS_4_38, g_BS_4_40, g_BS_4_41, g_BS_4_51, g_BS_4_52, g_BS_4_97, g_BS_4_98, g_BS_4_215, g_BS_4_216, g_BS_4_219, g_BS_4_220, g_BS_4_222, g_BS_4_223, g_BS_4_236, g_BS_4_237, g_BS_4_356, g_BS_4_357, g_BS_4_364, g_BS_4_365, g_BS_4_428, g_BS_4_429, g_BS_43_0, g_BS_43_1, g_BS_43_4, g_BS_43_5, g_BS_43_8, g_BS_43_9, g_BS_43_37, g_BS_43_38, g_BS_43_45, g_BS_43_51, g_BS_43_52, g_BS_43_54, g_BS_43_56, g_BS_43_115, g_BS_43_119, g_BS_43_123, g_BS_43_124, g_BS_43_137, g_BS_43_138, g_BS_43_143, g_BS_43_145, g_BS_43_151, g_BS_43_152, g_BS_43_154, g_BS_43_156, g_BS_43_197, g_BS_43_198, g_BS_43_209, g_BS_43_213, g_BS_44_0, g_BS_44_1, g_BS_44_4, g_BS_44_5, g_BS_44_8, g_BS_44_9, g_BS_44_37, g_BS_44_38, g_BS_44_40, g_BS_44_41, g_BS_44_43, g_BS_44_45, g_BS_44_46, g_BS_44_47, g_BS_44_48, g_BS_44_51, g_BS_44_52, g_BS_44_54, g_BS_44_55, g_BS_44_56, g_BS_44_57, g_BS_44_58, g_BS_44_59, g_BS_44_115, g_BS_44_116, g_BS_44_119, g_BS_44_120, g_BS_44_123, g_BS_44_124, g_BS_44_127, g_BS_44_128, g_BS_44_137, g_BS_44_138, g_BS_44_140, g_BS_44_141, g_BS_44_143, g_BS_44_144, g_BS_44_145, g_BS_44_146, g_BS_44_147, g_BS_44_148, g_BS_44_151, g_BS_44_152, g_BS_44_154, g_BS_44_155, g_BS_44_156, g_BS_44_157, g_BS_44_158, g_BS_44_159, g_BS_44_197, g_BS_44_198, g_BS_44_208, g_BS_44_209, g_BS_44_210, g_BS_44_212, g_BS_44_213, g_BS_44_214, g_BS_44_267, g_BS_44_268, g_BS_44_271, g_BS_44_272, g_BS_44_274, g_BS_44_275, g_BS_44_276, g_BS_44_277, g_BS_44_278, g_BS_44_279, g_BS_44_282, g_BS_44_283, g_BS_44_506, g_BS_44_507, g_BS_44_508, g_BS_44_510, g_BS_44_511, g_BS_44_512, g_BS_44_522, g_BS_44_523, g_BS_44_1346, g_BS_44_1347, g_BS_44_1354, g_BS_44_1355, g_BS_44_1357, g_BS_44_1358, g_BS_44_1359⟩ := Sierksma.FB.cBS_0
  obtain ⟨g_BS_44_1358, g_BS_44_1359, g_BS_44_1360, g_BS_44_1361, g_BS_44_1362, g_BS_61_0, g_BS_61_1, g_BS_61_4, g_BS_61_5, g_BS_61_12, g_BS_61_13, g_BS_61_30, g_BS_61_31, g_BS_61_34, g_BS_61_35, g_BS_61_40, g_BS_61_41, g_BS_61_43, g_BS_61_44, g_BS_61_45, g_BS_61_46, g_BS_61_47, g_BS_61_48, g_BS_61_62, g_BS_61_63, g_BS_61_66, g_BS_61_70, g_BS_61_71, g_BS_61_81, g_BS_61_82, g_BS_61_83, g_BS_61_84, g_BS_61_85, g_BS_61_86, g_BS_61_88, g_BS_61_90, g_BS_61_115, g_BS_61_116, g_BS_61_119, g_BS_61_120, g_BS_61_127, g_BS_61_128, g_BS_61_130, g_BS_61_131, g_BS_61_134, g_BS_61_135, g_BS_61_140, g_BS_61_141, g_BS_61_143, g_BS_61_144, g_BS_61_145, g_BS_61_146, g_BS_61_147, g_BS_61_148, g_BS_61_161, g_BS_61_162, g_BS_61_163, g_BS_61_166, g_BS_61_170, g_BS_61_171, g_BS_61_174, g_BS_61_175, g_BS_61_181, g_BS_61_182, g_BS_61_183, g_BS_61_184, g_BS_61_185, g_BS_61_186, g_BS_61_188, g_BS_61_189, g_BS_61_190⟩ := Sierksma.FB.cBS_1
  obtain ⟨g_BS_61_193, g_BS_61_208, g_BS_61_209, g_BS_61_210, g_BS_61_212, g_BS_61_213, g_BS_61_214, g_BS_61_254, g_BS_61_255, g_BS_61_257, g_BS_61_258, g_BS_61_260, g_BS_61_261, g_BS_61_262, g_BS_61_263, g_BS_61_264, g_BS_61_265, g_BS_61_271, g_BS_61_272, g_BS_61_286, g_BS_61_288, g_BS_61_289, g_BS_61_291, g_BS_61_294, g_BS_61_295, g_BS_61_297, g_BS_61_298, g_BS_61_299, g_BS_61_300, g_BS_61_301, g_BS_61_302, g_BS_61_304, g_BS_61_305, g_BS_61_306, g_BS_61_309, g_BS_61_320, g_BS_61_321, g_BS_61_324, g_BS_61_326⟩ := Sierksma.FB.cBS_2
  obtain ⟨g_BS_61_327, g_BS_61_329, g_BS_61_349, g_BS_61_352, g_BS_61_353, g_BS_61_354, g_BS_61_464, g_BS_61_465, g_BS_61_467, g_BS_61_468, g_BS_61_469, g_BS_61_472, g_BS_61_475, g_BS_61_476, g_BS_61_477, g_BS_61_479, g_BS_61_480, g_BS_61_481, g_BS_61_491, g_BS_61_493, g_BS_61_494, g_BS_61_496, g_BS_61_500, g_BS_61_503, g_BS_61_504, g_BS_61_505, g_BS_61_522, g_BS_61_523, g_BS_61_1346, g_BS_61_1347, g_BS_61_1357, g_BS_61_1358, g_BS_61_1359, g_BS_61_1360, g_BS_61_1361, g_BS_61_1362, g_BS_61_1364, g_BS_61_1366, g_BS_61_1392, g_BS_61_1393, g_BS_61_1395, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := Sierksma.FB.cBS_3
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, g_BS_61_1399, g_BS_61_1402, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := Sierksma.FB.cBS_5
  obtain ⟨g_BS_61_1404, g_BS_61_1407⟩ := Sierksma.FB.cBS_8
  obtain ⟨g_BS_61_1447, g_BS_61_1451, g_BS_65_0, g_BS_65_1, g_BS_65_4, g_BS_65_5, g_BS_65_12, g_BS_65_13, g_BS_65_40, g_BS_65_43, g_BS_65_44, g_BS_65_45, g_BS_65_46, g_BS_65_47, g_BS_65_48, g_BS_65_61, g_BS_65_62, g_BS_65_67, g_BS_65_88, g_BS_65_92, g_BS_65_115, g_BS_65_116, g_BS_65_119, g_BS_65_120, g_BS_65_127, g_BS_65_128, g_BS_65_130, g_BS_65_134, g_BS_65_135, g_BS_65_140, g_BS_65_141, g_BS_65_143, g_BS_65_144, g_BS_65_145, g_BS_65_146, g_BS_65_147, g_BS_65_148, g_BS_65_161, g_BS_65_162, g_BS_65_163, g_BS_65_165, g_BS_65_166, g_BS_65_167, g_BS_65_174, g_BS_65_181, g_BS_65_182, g_BS_65_183, g_BS_65_184, g_BS_65_185, g_BS_65_186, g_BS_65_188, g_BS_65_189, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := Sierksma.FB.cBS_9
  obtain ⟨_, _, _, _, _, _, _, _, _, g_BS_65_192, g_BS_65_193, g_BS_65_194, g_BS_65_208, g_BS_65_209, g_BS_65_210, g_BS_65_212, g_BS_65_213, g_BS_65_214, g_BS_65_271, g_BS_65_272, g_BS_65_286, g_BS_65_287, g_BS_65_288, g_BS_65_289, g_BS_65_290, g_BS_65_291, g_BS_65_324⟩ := Sierksma.FB.cBS_11
  obtain ⟨g_BS_65_325, g_BS_65_327, g_BS_65_348, g_BS_65_349, g_BS_65_350, g_BS_65_352, g_BS_65_353, g_BS_65_354, g_BS_65_522, g_BS_65_1346, g_BS_65_1347, g_BS_65_1357, g_BS_65_1358, g_BS_65_1359, g_BS_65_1360, g_BS_65_1364, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := Sierksma.FB.cBS_12
  obtain ⟨_, _, _, _, _, g_BS_65_1368⟩ := Sierksma.FB.cBS_14
  obtain ⟨g_BS_65_1395, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := Sierksma.FB.cBS_15
  have g_BS_65_1408 := Sierksma.FB.cBS_37
  have g_BS_65_1406 := Sierksma.FB.cBS_38
  have g_BS_65_1403 := Sierksma.FB.cBS_39
  have g_BS_65_1402 := Sierksma.FB.cBS_40
  have g_BS_65_1396 := Sierksma.FB.cBS_41
  have g_BS_65_1366 := Sierksma.FB.cBS_42
  have g_BS_65_190 := Sierksma.FB.cBS_43
  have g_BS_61_1403 := Sierksma.FB.cBS_44
  have g_BS_61_1396 := Sierksma.FB.cBS_45
  intro k hk r2 hr2
  interval_cases k
  · have e : Sierksma.FB.rootList 0 = [1, 15, 16, 40, 41, 215, 216] := rfl
    rw [e] at hr2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr2
    rcases hr2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact g_BS_0_1
    · exact g_BS_0_15
    · exact g_BS_0_16
    · exact g_BS_0_40
    · exact g_BS_0_41
    · exact g_BS_0_215
    · exact g_BS_0_216
  · have e : Sierksma.FB.rootList 1 = [0, 1, 5, 8, 9, 15, 16, 19, 20, 23, 24, 27, 28, 37, 38, 40, 41, 51, 52, 97, 98, 215, 216, 219, 220, 222, 223, 236, 237, 356, 357, 364, 365, 428, 429] := rfl
    rw [e] at hr2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr2
    rcases hr2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact g_BS_4_0
    · exact g_BS_4_1
    · exact g_BS_4_5
    · exact g_BS_4_8
    · exact g_BS_4_9
    · exact g_BS_4_15
    · exact g_BS_4_16
    · exact g_BS_4_19
    · exact g_BS_4_20
    · exact g_BS_4_23
    · exact g_BS_4_24
    · exact g_BS_4_27
    · exact g_BS_4_28
    · exact g_BS_4_37
    · exact g_BS_4_38
    · exact g_BS_4_40
    · exact g_BS_4_41
    · exact g_BS_4_51
    · exact g_BS_4_52
    · exact g_BS_4_97
    · exact g_BS_4_98
    · exact g_BS_4_215
    · exact g_BS_4_216
    · exact g_BS_4_219
    · exact g_BS_4_220
    · exact g_BS_4_222
    · exact g_BS_4_223
    · exact g_BS_4_236
    · exact g_BS_4_237
    · exact g_BS_4_356
    · exact g_BS_4_357
    · exact g_BS_4_364
    · exact g_BS_4_365
    · exact g_BS_4_428
    · exact g_BS_4_429
  · have e : Sierksma.FB.rootList 2 = [0, 1, 4, 5, 8, 9, 37, 38, 45, 51, 52, 54, 56, 115, 119, 123, 124, 137, 138, 143, 145, 151, 152, 154, 156, 197, 198, 209, 213] := rfl
    rw [e] at hr2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr2
    rcases hr2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact g_BS_43_0
    · exact g_BS_43_1
    · exact g_BS_43_4
    · exact g_BS_43_5
    · exact g_BS_43_8
    · exact g_BS_43_9
    · exact g_BS_43_37
    · exact g_BS_43_38
    · exact g_BS_43_45
    · exact g_BS_43_51
    · exact g_BS_43_52
    · exact g_BS_43_54
    · exact g_BS_43_56
    · exact g_BS_43_115
    · exact g_BS_43_119
    · exact g_BS_43_123
    · exact g_BS_43_124
    · exact g_BS_43_137
    · exact g_BS_43_138
    · exact g_BS_43_143
    · exact g_BS_43_145
    · exact g_BS_43_151
    · exact g_BS_43_152
    · exact g_BS_43_154
    · exact g_BS_43_156
    · exact g_BS_43_197
    · exact g_BS_43_198
    · exact g_BS_43_209
    · exact g_BS_43_213
  · have e : Sierksma.FB.rootList 3 = [0, 1, 4, 5, 8, 9, 37, 38, 40, 41, 43, 45, 46, 47, 48, 51, 52, 54, 55, 56, 57, 58, 59, 115, 116, 119, 120, 123, 124, 127, 128, 137, 138, 140, 141, 143, 144, 145, 146, 147, 148, 151, 152, 154, 155, 156, 157, 158, 159, 197, 198, 208, 209, 210, 212, 213, 214, 267, 268, 271, 272, 274, 275, 276, 277, 278, 279, 282, 283, 506, 507, 508, 510, 511, 512, 522, 523, 1346, 1347, 1354, 1355, 1357, 1358, 1359, 1360, 1361, 1362] := rfl
    rw [e] at hr2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr2
    rcases hr2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact g_BS_44_0
    · exact g_BS_44_1
    · exact g_BS_44_4
    · exact g_BS_44_5
    · exact g_BS_44_8
    · exact g_BS_44_9
    · exact g_BS_44_37
    · exact g_BS_44_38
    · exact g_BS_44_40
    · exact g_BS_44_41
    · exact g_BS_44_43
    · exact g_BS_44_45
    · exact g_BS_44_46
    · exact g_BS_44_47
    · exact g_BS_44_48
    · exact g_BS_44_51
    · exact g_BS_44_52
    · exact g_BS_44_54
    · exact g_BS_44_55
    · exact g_BS_44_56
    · exact g_BS_44_57
    · exact g_BS_44_58
    · exact g_BS_44_59
    · exact g_BS_44_115
    · exact g_BS_44_116
    · exact g_BS_44_119
    · exact g_BS_44_120
    · exact g_BS_44_123
    · exact g_BS_44_124
    · exact g_BS_44_127
    · exact g_BS_44_128
    · exact g_BS_44_137
    · exact g_BS_44_138
    · exact g_BS_44_140
    · exact g_BS_44_141
    · exact g_BS_44_143
    · exact g_BS_44_144
    · exact g_BS_44_145
    · exact g_BS_44_146
    · exact g_BS_44_147
    · exact g_BS_44_148
    · exact g_BS_44_151
    · exact g_BS_44_152
    · exact g_BS_44_154
    · exact g_BS_44_155
    · exact g_BS_44_156
    · exact g_BS_44_157
    · exact g_BS_44_158
    · exact g_BS_44_159
    · exact g_BS_44_197
    · exact g_BS_44_198
    · exact g_BS_44_208
    · exact g_BS_44_209
    · exact g_BS_44_210
    · exact g_BS_44_212
    · exact g_BS_44_213
    · exact g_BS_44_214
    · exact g_BS_44_267
    · exact g_BS_44_268
    · exact g_BS_44_271
    · exact g_BS_44_272
    · exact g_BS_44_274
    · exact g_BS_44_275
    · exact g_BS_44_276
    · exact g_BS_44_277
    · exact g_BS_44_278
    · exact g_BS_44_279
    · exact g_BS_44_282
    · exact g_BS_44_283
    · exact g_BS_44_506
    · exact g_BS_44_507
    · exact g_BS_44_508
    · exact g_BS_44_510
    · exact g_BS_44_511
    · exact g_BS_44_512
    · exact g_BS_44_522
    · exact g_BS_44_523
    · exact g_BS_44_1346
    · exact g_BS_44_1347
    · exact g_BS_44_1354
    · exact g_BS_44_1355
    · exact g_BS_44_1357
    · exact g_BS_44_1358
    · exact g_BS_44_1359
    · exact g_BS_44_1360
    · exact g_BS_44_1361
    · exact g_BS_44_1362
  · have e : Sierksma.FB.rootList 4 = [0, 1, 4, 5, 12, 13, 30, 31, 34, 35, 40, 41, 43, 44, 45, 46, 47, 48, 62, 63, 66, 70, 71, 81, 82, 83, 84, 85, 86, 88, 90, 115, 116, 119, 120, 127, 128, 130, 131, 134, 135, 140, 141, 143, 144, 145, 146, 147, 148, 161, 162, 163, 166, 170, 171, 174, 175, 181, 182, 183, 184, 185, 186, 188, 189, 190, 193, 208, 209, 210, 212, 213, 214, 254, 255, 257, 258, 260, 261, 262, 263, 264, 265, 271, 272, 286, 288, 289, 291, 294, 295, 297, 298, 299, 300, 301, 302, 304, 305, 306, 309, 320, 321, 324, 326, 327, 329, 349, 352, 353, 354, 464, 465, 467, 468, 469, 472, 475, 476, 477, 479, 480, 481, 491, 493, 494, 496, 500, 503, 504, 505, 522, 523, 1346, 1347, 1357, 1358, 1359, 1360, 1361, 1362, 1364, 1366, 1392, 1393, 1395, 1396, 1399, 1402, 1403, 1404, 1407, 1447, 1451] := rfl
    rw [e] at hr2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr2
    rcases hr2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact g_BS_61_0
    · exact g_BS_61_1
    · exact g_BS_61_4
    · exact g_BS_61_5
    · exact g_BS_61_12
    · exact g_BS_61_13
    · exact g_BS_61_30
    · exact g_BS_61_31
    · exact g_BS_61_34
    · exact g_BS_61_35
    · exact g_BS_61_40
    · exact g_BS_61_41
    · exact g_BS_61_43
    · exact g_BS_61_44
    · exact g_BS_61_45
    · exact g_BS_61_46
    · exact g_BS_61_47
    · exact g_BS_61_48
    · exact g_BS_61_62
    · exact g_BS_61_63
    · exact g_BS_61_66
    · exact g_BS_61_70
    · exact g_BS_61_71
    · exact g_BS_61_81
    · exact g_BS_61_82
    · exact g_BS_61_83
    · exact g_BS_61_84
    · exact g_BS_61_85
    · exact g_BS_61_86
    · exact g_BS_61_88
    · exact g_BS_61_90
    · exact g_BS_61_115
    · exact g_BS_61_116
    · exact g_BS_61_119
    · exact g_BS_61_120
    · exact g_BS_61_127
    · exact g_BS_61_128
    · exact g_BS_61_130
    · exact g_BS_61_131
    · exact g_BS_61_134
    · exact g_BS_61_135
    · exact g_BS_61_140
    · exact g_BS_61_141
    · exact g_BS_61_143
    · exact g_BS_61_144
    · exact g_BS_61_145
    · exact g_BS_61_146
    · exact g_BS_61_147
    · exact g_BS_61_148
    · exact g_BS_61_161
    · exact g_BS_61_162
    · exact g_BS_61_163
    · exact g_BS_61_166
    · exact g_BS_61_170
    · exact g_BS_61_171
    · exact g_BS_61_174
    · exact g_BS_61_175
    · exact g_BS_61_181
    · exact g_BS_61_182
    · exact g_BS_61_183
    · exact g_BS_61_184
    · exact g_BS_61_185
    · exact g_BS_61_186
    · exact g_BS_61_188
    · exact g_BS_61_189
    · exact g_BS_61_190
    · exact g_BS_61_193
    · exact g_BS_61_208
    · exact g_BS_61_209
    · exact g_BS_61_210
    · exact g_BS_61_212
    · exact g_BS_61_213
    · exact g_BS_61_214
    · exact g_BS_61_254
    · exact g_BS_61_255
    · exact g_BS_61_257
    · exact g_BS_61_258
    · exact g_BS_61_260
    · exact g_BS_61_261
    · exact g_BS_61_262
    · exact g_BS_61_263
    · exact g_BS_61_264
    · exact g_BS_61_265
    · exact g_BS_61_271
    · exact g_BS_61_272
    · exact g_BS_61_286
    · exact g_BS_61_288
    · exact g_BS_61_289
    · exact g_BS_61_291
    · exact g_BS_61_294
    · exact g_BS_61_295
    · exact g_BS_61_297
    · exact g_BS_61_298
    · exact g_BS_61_299
    · exact g_BS_61_300
    · exact g_BS_61_301
    · exact g_BS_61_302
    · exact g_BS_61_304
    · exact g_BS_61_305
    · exact g_BS_61_306
    · exact g_BS_61_309
    · exact g_BS_61_320
    · exact g_BS_61_321
    · exact g_BS_61_324
    · exact g_BS_61_326
    · exact g_BS_61_327
    · exact g_BS_61_329
    · exact g_BS_61_349
    · exact g_BS_61_352
    · exact g_BS_61_353
    · exact g_BS_61_354
    · exact g_BS_61_464
    · exact g_BS_61_465
    · exact g_BS_61_467
    · exact g_BS_61_468
    · exact g_BS_61_469
    · exact g_BS_61_472
    · exact g_BS_61_475
    · exact g_BS_61_476
    · exact g_BS_61_477
    · exact g_BS_61_479
    · exact g_BS_61_480
    · exact g_BS_61_481
    · exact g_BS_61_491
    · exact g_BS_61_493
    · exact g_BS_61_494
    · exact g_BS_61_496
    · exact g_BS_61_500
    · exact g_BS_61_503
    · exact g_BS_61_504
    · exact g_BS_61_505
    · exact g_BS_61_522
    · exact g_BS_61_523
    · exact g_BS_61_1346
    · exact g_BS_61_1347
    · exact g_BS_61_1357
    · exact g_BS_61_1358
    · exact g_BS_61_1359
    · exact g_BS_61_1360
    · exact g_BS_61_1361
    · exact g_BS_61_1362
    · exact g_BS_61_1364
    · exact g_BS_61_1366
    · exact g_BS_61_1392
    · exact g_BS_61_1393
    · exact g_BS_61_1395
    · exact g_BS_61_1396
    · exact g_BS_61_1399
    · exact g_BS_61_1402
    · exact g_BS_61_1403
    · exact g_BS_61_1404
    · exact g_BS_61_1407
    · exact g_BS_61_1447
    · exact g_BS_61_1451
  · have e : Sierksma.FB.rootList 5 = [0, 1, 4, 5, 12, 13, 40, 43, 44, 45, 46, 47, 48, 61, 62, 67, 88, 92, 115, 116, 119, 120, 127, 128, 130, 134, 135, 140, 141, 143, 144, 145, 146, 147, 148, 161, 162, 163, 165, 166, 167, 174, 181, 182, 183, 184, 185, 186, 188, 189, 190, 192, 193, 194, 208, 209, 210, 212, 213, 214, 271, 272, 286, 287, 288, 289, 290, 291, 324, 325, 327, 348, 349, 350, 352, 353, 354, 522, 1346, 1347, 1357, 1358, 1359, 1360, 1364, 1366, 1368, 1395, 1396, 1402, 1403, 1406, 1408] := rfl
    rw [e] at hr2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr2
    rcases hr2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact g_BS_65_0
    · exact g_BS_65_1
    · exact g_BS_65_4
    · exact g_BS_65_5
    · exact g_BS_65_12
    · exact g_BS_65_13
    · exact g_BS_65_40
    · exact g_BS_65_43
    · exact g_BS_65_44
    · exact g_BS_65_45
    · exact g_BS_65_46
    · exact g_BS_65_47
    · exact g_BS_65_48
    · exact g_BS_65_61
    · exact g_BS_65_62
    · exact g_BS_65_67
    · exact g_BS_65_88
    · exact g_BS_65_92
    · exact g_BS_65_115
    · exact g_BS_65_116
    · exact g_BS_65_119
    · exact g_BS_65_120
    · exact g_BS_65_127
    · exact g_BS_65_128
    · exact g_BS_65_130
    · exact g_BS_65_134
    · exact g_BS_65_135
    · exact g_BS_65_140
    · exact g_BS_65_141
    · exact g_BS_65_143
    · exact g_BS_65_144
    · exact g_BS_65_145
    · exact g_BS_65_146
    · exact g_BS_65_147
    · exact g_BS_65_148
    · exact g_BS_65_161
    · exact g_BS_65_162
    · exact g_BS_65_163
    · exact g_BS_65_165
    · exact g_BS_65_166
    · exact g_BS_65_167
    · exact g_BS_65_174
    · exact g_BS_65_181
    · exact g_BS_65_182
    · exact g_BS_65_183
    · exact g_BS_65_184
    · exact g_BS_65_185
    · exact g_BS_65_186
    · exact g_BS_65_188
    · exact g_BS_65_189
    · exact g_BS_65_190
    · exact g_BS_65_192
    · exact g_BS_65_193
    · exact g_BS_65_194
    · exact g_BS_65_208
    · exact g_BS_65_209
    · exact g_BS_65_210
    · exact g_BS_65_212
    · exact g_BS_65_213
    · exact g_BS_65_214
    · exact g_BS_65_271
    · exact g_BS_65_272
    · exact g_BS_65_286
    · exact g_BS_65_287
    · exact g_BS_65_288
    · exact g_BS_65_289
    · exact g_BS_65_290
    · exact g_BS_65_291
    · exact g_BS_65_324
    · exact g_BS_65_325
    · exact g_BS_65_327
    · exact g_BS_65_348
    · exact g_BS_65_349
    · exact g_BS_65_350
    · exact g_BS_65_352
    · exact g_BS_65_353
    · exact g_BS_65_354
    · exact g_BS_65_522
    · exact g_BS_65_1346
    · exact g_BS_65_1347
    · exact g_BS_65_1357
    · exact g_BS_65_1358
    · exact g_BS_65_1359
    · exact g_BS_65_1360
    · exact g_BS_65_1364
    · exact g_BS_65_1366
    · exact g_BS_65_1368
    · exact g_BS_65_1395
    · exact g_BS_65_1396
    · exact g_BS_65_1402
    · exact g_BS_65_1403
    · exact g_BS_65_1406
    · exact g_BS_65_1408

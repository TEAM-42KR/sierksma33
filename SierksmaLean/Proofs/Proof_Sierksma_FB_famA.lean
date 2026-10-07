import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_0
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_21
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_22
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_34
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_54
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_61
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_97
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_105
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_109
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_126
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_133
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_140
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_169
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_170
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_200
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_202
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_223
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_251
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_254
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_301
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_316
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_331
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_336
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_361
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_376
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_377
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_378
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_379
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_380
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_381
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_382
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_395
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_408
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_411
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_426
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_436
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_475
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_476
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_495
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_516
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_517
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_544
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_565
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_568
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_571
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_583
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_586
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_593
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_606
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_620
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_627
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_641
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_648
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_651
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_672
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_673
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem proof_Sierksma_FB_famA : ∀ k < 6, ∀ r2 ∈ Sierksma.FB.rootList k,
    Sierksma.FB.Good (Sierksma.FB.memBits (Sierksma.FB.pairSort (Sierksma.FB.R1.getD k 0) r2)) (Sierksma.FB.KS k r2) 5 (Sierksma.FB.capsOf 3 4) := by
  obtain ⟨g_AS_2_213, g_AS_5_287, g_AS_3_120, g_AS_1_37, g_AS_5_116, _⟩ := Sierksma.FB.cAS_0
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, g_AS_0_15, g_AS_5_188, g_AS_3_151, g_AS_5_1359, g_AS_5_352, g_AS_3_48, g_AS_4_255, g_AS_4_48, g_AS_3_51, g_AS_4_166, g_AS_1_428, g_AS_5_327, g_AS_4_464, g_AS_3_123, g_AS_5_194, g_AS_4_190⟩ := Sierksma.FB.cAS_21
  obtain ⟨g_AS_3_157, g_AS_4_306, g_AS_3_140, g_AS_3_1362, g_AS_2_198, g_AS_5_140, g_AS_1_23, g_AS_5_1366, g_AS_2_138, g_AS_4_34, g_AS_5_174, g_AS_3_508, g_AS_5_43, g_AS_3_119, _⟩ := Sierksma.FB.cAS_22
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, g_AS_1_28, g_AS_1_41, g_AS_3_52, g_AS_4_81, g_AS_3_197, g_AS_4_262, _⟩ := Sierksma.FB.cAS_34
  obtain ⟨_, g_AS_1_5, g_AS_4_1357, g_AS_2_156, g_AS_4_44, g_AS_3_1, g_AS_4_505, g_AS_3_57, g_AS_4_188, _⟩ := Sierksma.FB.cAS_54
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, g_AS_3_214, g_AS_4_1393, g_AS_3_1355, g_AS_1_24, g_AS_5_324, g_AS_5_183, g_AS_1_16, g_AS_4_181, g_AS_1_97, g_AS_1_223, g_AS_1_38, g_AS_1_236, g_AS_4_210, g_AS_4_475, g_AS_4_170, g_AS_1_0, g_AS_4_12, g_AS_2_123, g_AS_4_82, g_AS_5_1358, g_AS_2_54, g_AS_5_163, _⟩ := Sierksma.FB.cAS_61
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, g_AS_3_137, g_AS_3_272, g_AS_2_151, g_AS_5_210, g_AS_4_175, g_AS_5_44, g_AS_3_127, _⟩ := Sierksma.FB.cAS_97
  obtain ⟨_, _, _, _, _, _, g_AS_2_56, g_AS_5_127, g_AS_4_493, g_AS_4_291, g_AS_5_350, g_AS_4_189, g_AS_5_120, g_AS_3_146, g_AS_4_1347, g_AS_2_45, g_AS_1_27, g_AS_3_38, g_AS_5_135, g_AS_3_510, _⟩ := Sierksma.FB.cAS_105
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, g_AS_4_472, g_AS_4_354, g_AS_2_38, g_AS_4_465, g_AS_5_45, g_AS_4_1396, g_AS_4_320, g_AS_3_1357, g_AS_3_511, g_AS_5_212, g_AS_4_128, g_AS_4_131, g_AS_3_282, g_AS_3_54, g_AS_5_522, g_AS_4_1366, g_AS_5_208, g_AS_2_0, g_AS_4_83, g_AS_5_1, g_AS_4_329, g_AS_1_8, g_AS_5_4, g_AS_5_290, g_AS_3_56, g_AS_4_116, g_AS_5_165, g_AS_4_1, g_AS_3_152, g_AS_5_354, g_AS_3_144, g_AS_3_507, g_AS_4_70, g_AS_5_130, g_AS_5_141, g_AS_3_55, g_AS_5_1364, g_AS_4_41, g_AS_1_215, g_AS_4_476, g_AS_4_263, _⟩ := Sierksma.FB.cAS_109
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, g_AS_3_271, g_AS_3_198, g_AS_5_271, g_AS_4_5, g_AS_5_0, g_AS_3_268, g_AS_5_162, g_AS_4_141, g_AS_4_183, g_AS_4_261, g_AS_3_1359, _⟩ := Sierksma.FB.cAS_126
  obtain ⟨_, _, _, _, _, _, _, _, _, _, g_AS_4_40, g_AS_5_286, g_AS_4_272, g_AS_4_353, g_AS_4_88, g_AS_0_40, g_AS_5_61, g_AS_4_186, g_AS_3_213, g_AS_4_309, g_AS_2_143, g_AS_3_276, g_AS_5_128, g_AS_4_286, g_AS_5_1357, g_AS_2_119, g_AS_0_16, g_AS_3_0, _⟩ := Sierksma.FB.cAS_133
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, g_AS_4_294, g_AS_4_161, g_AS_4_522, g_AS_5_40, g_AS_2_8, g_AS_3_37, g_AS_5_88, g_AS_4_115, g_AS_4_1361, g_AS_5_119, g_AS_1_20, g_AS_0_216, g_AS_2_37, g_AS_2_197, _⟩ := Sierksma.FB.cAS_140
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, g_AS_4_288, g_AS_3_523, g_AS_5_1396, g_AS_5_289, g_AS_3_267, g_AS_5_1395, g_AS_5_166, g_AS_4_265, g_AS_4_523, g_AS_4_295, g_AS_3_138, g_AS_4_352, g_AS_4_264, g_AS_5_67, g_AS_4_71, g_AS_4_297, g_AS_5_47, g_AS_4_254⟩ := Sierksma.FB.cAS_169
  obtain ⟨g_AS_4_1447, g_AS_4_271, g_AS_5_288, g_AS_4_119, g_AS_3_522, g_AS_1_356, g_AS_4_13, g_AS_5_5, g_AS_5_62, g_AS_4_134, _⟩ := Sierksma.FB.cAS_170
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, g_AS_2_154, g_AS_3_279, g_AS_5_272, g_AS_1_365, g_AS_3_209, g_AS_4_496, g_AS_5_13, g_AS_4_260, g_AS_4_349, g_AS_4_63, g_AS_4_4, g_AS_4_182, _⟩ := Sierksma.FB.cAS_200
  obtain ⟨_, _, _, _, _, _, _, _, g_AS_4_30, g_AS_4_304, _⟩ := Sierksma.FB.cAS_202
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, g_AS_4_491, g_AS_1_222, g_AS_4_298, g_AS_4_209, g_AS_3_47, g_AS_4_31, g_AS_4_43, g_AS_5_1368, g_AS_4_163, g_AS_5_1360, g_AS_4_479, g_AS_2_51, g_AS_4_213, g_AS_5_1347, g_AS_2_152, g_AS_4_504, g_AS_2_137, g_AS_4_185, g_AS_3_278, g_AS_4_135, g_AS_5_349, g_AS_5_46, g_AS_5_209, _⟩ := Sierksma.FB.cAS_223
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, g_AS_1_98, g_AS_3_43, g_AS_1_9, g_AS_4_1358, g_AS_0_41, g_AS_5_12, g_AS_4_321, g_AS_4_90, g_AS_4_0, g_AS_5_48, g_AS_5_193, g_AS_4_503, g_AS_5_348, g_AS_4_1362, g_AS_3_45, g_AS_3_210, g_AS_1_19, g_AS_3_116, g_AS_4_86, g_AS_4_1346, g_AS_4_327, _⟩ := Sierksma.FB.cAS_251
  obtain ⟨_, _, _, _, _, _, _, _, g_AS_4_1451, g_AS_0_215, g_AS_4_35, g_AS_1_216, _⟩ := Sierksma.FB.cAS_254
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, g_AS_2_9, g_AS_5_189, g_AS_3_128, g_AS_4_467, g_AS_1_15, g_AS_4_45, g_AS_2_124, g_AS_4_289, g_AS_5_186, g_AS_3_41, g_AS_4_47, g_AS_4_326, g_AS_0_1, g_AS_3_9, g_AS_5_190, g_AS_3_5, g_AS_4_477, g_AS_5_1346, g_AS_3_1361, g_AS_1_237, g_AS_4_143, g_AS_2_52, g_AS_4_1392, g_AS_4_193, g_AS_5_353, g_AS_5_325, g_AS_4_62, g_AS_3_274, g_AS_5_192, _⟩ := Sierksma.FB.cAS_301
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, g_AS_5_92, g_AS_4_46, g_AS_4_1359, g_AS_4_174, g_AS_3_155, _⟩ := Sierksma.FB.cAS_316
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, g_AS_3_506, g_AS_1_429, g_AS_5_182, g_AS_3_208, g_AS_3_277, g_AS_4_468, g_AS_4_481, g_AS_2_115, g_AS_1_52, g_AS_5_184, g_AS_3_1358, g_AS_4_480, g_AS_5_214, g_AS_4_85, g_AS_3_1347, _⟩ := Sierksma.FB.cAS_331
  obtain ⟨_, g_AS_3_156, g_AS_3_158, g_AS_3_283, g_AS_1_364, g_AS_3_4, g_AS_3_512, g_AS_5_115, _⟩ := Sierksma.FB.cAS_336
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, g_AS_4_305, g_AS_3_154, _⟩ := Sierksma.FB.cAS_361
  obtain ⟨_, _, _, _, _, _, g_AS_4_120, g_AS_4_494, g_AS_4_1360, g_AS_3_1354, g_AS_5_181, g_AS_5_185, g_AS_1_1, g_AS_4_257, g_AS_3_58, g_AS_4_212, g_AS_3_40, _⟩ := Sierksma.FB.cAS_376
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, g_AS_4_171, g_AS_3_124, g_AS_3_212, g_AS_4_258, g_AS_1_220, g_AS_4_127, g_AS_4_140, g_AS_3_46, g_AS_4_1364, g_AS_3_59, g_AS_4_469, g_AS_3_159, g_AS_3_1346, g_AS_1_51, g_AS_2_209⟩ := Sierksma.FB.cAS_377
  obtain ⟨g_AS_4_1399, g_AS_5_134, g_AS_3_275, g_AS_2_5, g_AS_4_130, _⟩ := Sierksma.FB.cAS_378
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, g_AS_3_8, g_AS_5_167, g_AS_2_4, g_AS_3_141, g_AS_1_219, g_AS_4_66, g_AS_4_1395, g_AS_4_324, g_AS_5_291, g_AS_4_214, g_AS_4_500, g_AS_4_84⟩ := Sierksma.FB.cAS_379
  obtain ⟨g_AS_3_1360, g_AS_4_184, g_AS_1_357, g_AS_5_161, g_AS_2_1, g_AS_4_162, g_AS_3_115, g_AS_4_208, g_AS_3_143, g_AS_5_213, g_AS_1_40⟩ := Sierksma.FB.cAS_380
  have g_AS_4_144 := Sierksma.FB.cAS_381
  have g_AS_5_143 := Sierksma.FB.cAS_382
  have g_AS_5_145 := Sierksma.FB.cAS_395
  have g_AS_3_147 := Sierksma.FB.cAS_408
  have g_AS_3_145 := Sierksma.FB.cAS_411
  have g_AS_4_148 := Sierksma.FB.cAS_426
  have g_AS_5_1403 := Sierksma.FB.cAS_436
  have g_AS_5_147 := Sierksma.FB.cAS_475
  have g_AS_4_300 := Sierksma.FB.cAS_476
  have g_AS_5_148 := Sierksma.FB.cAS_495
  have g_AS_4_146 := Sierksma.FB.cAS_516
  have g_AS_2_145 := Sierksma.FB.cAS_517
  have g_AS_4_301 := Sierksma.FB.cAS_544
  have g_AS_5_1408 := Sierksma.FB.cAS_565
  have g_AS_5_144 := Sierksma.FB.cAS_568
  have g_AS_4_302 := Sierksma.FB.cAS_571
  have g_AS_5_1406 := Sierksma.FB.cAS_583
  have g_AS_4_1404 := Sierksma.FB.cAS_586
  have g_AS_4_145 := Sierksma.FB.cAS_593
  have g_AS_4_299 := Sierksma.FB.cAS_606
  have g_AS_3_148 := Sierksma.FB.cAS_620
  have g_AS_4_1402 := Sierksma.FB.cAS_627
  have g_AS_5_1402 := Sierksma.FB.cAS_641
  have g_AS_4_1403 := Sierksma.FB.cAS_648
  have g_AS_5_146 := Sierksma.FB.cAS_651
  have g_AS_4_147 := Sierksma.FB.cAS_672
  have g_AS_4_1407 := Sierksma.FB.cAS_673
  intro k hk r2 hr2
  interval_cases k
  · have e : Sierksma.FB.rootList 0 = [1, 15, 16, 40, 41, 215, 216] := rfl
    rw [e] at hr2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr2
    rcases hr2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact g_AS_0_1
    · exact g_AS_0_15
    · exact g_AS_0_16
    · exact g_AS_0_40
    · exact g_AS_0_41
    · exact g_AS_0_215
    · exact g_AS_0_216
  · have e : Sierksma.FB.rootList 1 = [0, 1, 5, 8, 9, 15, 16, 19, 20, 23, 24, 27, 28, 37, 38, 40, 41, 51, 52, 97, 98, 215, 216, 219, 220, 222, 223, 236, 237, 356, 357, 364, 365, 428, 429] := rfl
    rw [e] at hr2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr2
    rcases hr2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact g_AS_1_0
    · exact g_AS_1_1
    · exact g_AS_1_5
    · exact g_AS_1_8
    · exact g_AS_1_9
    · exact g_AS_1_15
    · exact g_AS_1_16
    · exact g_AS_1_19
    · exact g_AS_1_20
    · exact g_AS_1_23
    · exact g_AS_1_24
    · exact g_AS_1_27
    · exact g_AS_1_28
    · exact g_AS_1_37
    · exact g_AS_1_38
    · exact g_AS_1_40
    · exact g_AS_1_41
    · exact g_AS_1_51
    · exact g_AS_1_52
    · exact g_AS_1_97
    · exact g_AS_1_98
    · exact g_AS_1_215
    · exact g_AS_1_216
    · exact g_AS_1_219
    · exact g_AS_1_220
    · exact g_AS_1_222
    · exact g_AS_1_223
    · exact g_AS_1_236
    · exact g_AS_1_237
    · exact g_AS_1_356
    · exact g_AS_1_357
    · exact g_AS_1_364
    · exact g_AS_1_365
    · exact g_AS_1_428
    · exact g_AS_1_429
  · have e : Sierksma.FB.rootList 2 = [0, 1, 4, 5, 8, 9, 37, 38, 45, 51, 52, 54, 56, 115, 119, 123, 124, 137, 138, 143, 145, 151, 152, 154, 156, 197, 198, 209, 213] := rfl
    rw [e] at hr2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr2
    rcases hr2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact g_AS_2_0
    · exact g_AS_2_1
    · exact g_AS_2_4
    · exact g_AS_2_5
    · exact g_AS_2_8
    · exact g_AS_2_9
    · exact g_AS_2_37
    · exact g_AS_2_38
    · exact g_AS_2_45
    · exact g_AS_2_51
    · exact g_AS_2_52
    · exact g_AS_2_54
    · exact g_AS_2_56
    · exact g_AS_2_115
    · exact g_AS_2_119
    · exact g_AS_2_123
    · exact g_AS_2_124
    · exact g_AS_2_137
    · exact g_AS_2_138
    · exact g_AS_2_143
    · exact g_AS_2_145
    · exact g_AS_2_151
    · exact g_AS_2_152
    · exact g_AS_2_154
    · exact g_AS_2_156
    · exact g_AS_2_197
    · exact g_AS_2_198
    · exact g_AS_2_209
    · exact g_AS_2_213
  · have e : Sierksma.FB.rootList 3 = [0, 1, 4, 5, 8, 9, 37, 38, 40, 41, 43, 45, 46, 47, 48, 51, 52, 54, 55, 56, 57, 58, 59, 115, 116, 119, 120, 123, 124, 127, 128, 137, 138, 140, 141, 143, 144, 145, 146, 147, 148, 151, 152, 154, 155, 156, 157, 158, 159, 197, 198, 208, 209, 210, 212, 213, 214, 267, 268, 271, 272, 274, 275, 276, 277, 278, 279, 282, 283, 506, 507, 508, 510, 511, 512, 522, 523, 1346, 1347, 1354, 1355, 1357, 1358, 1359, 1360, 1361, 1362] := rfl
    rw [e] at hr2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr2
    rcases hr2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact g_AS_3_0
    · exact g_AS_3_1
    · exact g_AS_3_4
    · exact g_AS_3_5
    · exact g_AS_3_8
    · exact g_AS_3_9
    · exact g_AS_3_37
    · exact g_AS_3_38
    · exact g_AS_3_40
    · exact g_AS_3_41
    · exact g_AS_3_43
    · exact g_AS_3_45
    · exact g_AS_3_46
    · exact g_AS_3_47
    · exact g_AS_3_48
    · exact g_AS_3_51
    · exact g_AS_3_52
    · exact g_AS_3_54
    · exact g_AS_3_55
    · exact g_AS_3_56
    · exact g_AS_3_57
    · exact g_AS_3_58
    · exact g_AS_3_59
    · exact g_AS_3_115
    · exact g_AS_3_116
    · exact g_AS_3_119
    · exact g_AS_3_120
    · exact g_AS_3_123
    · exact g_AS_3_124
    · exact g_AS_3_127
    · exact g_AS_3_128
    · exact g_AS_3_137
    · exact g_AS_3_138
    · exact g_AS_3_140
    · exact g_AS_3_141
    · exact g_AS_3_143
    · exact g_AS_3_144
    · exact g_AS_3_145
    · exact g_AS_3_146
    · exact g_AS_3_147
    · exact g_AS_3_148
    · exact g_AS_3_151
    · exact g_AS_3_152
    · exact g_AS_3_154
    · exact g_AS_3_155
    · exact g_AS_3_156
    · exact g_AS_3_157
    · exact g_AS_3_158
    · exact g_AS_3_159
    · exact g_AS_3_197
    · exact g_AS_3_198
    · exact g_AS_3_208
    · exact g_AS_3_209
    · exact g_AS_3_210
    · exact g_AS_3_212
    · exact g_AS_3_213
    · exact g_AS_3_214
    · exact g_AS_3_267
    · exact g_AS_3_268
    · exact g_AS_3_271
    · exact g_AS_3_272
    · exact g_AS_3_274
    · exact g_AS_3_275
    · exact g_AS_3_276
    · exact g_AS_3_277
    · exact g_AS_3_278
    · exact g_AS_3_279
    · exact g_AS_3_282
    · exact g_AS_3_283
    · exact g_AS_3_506
    · exact g_AS_3_507
    · exact g_AS_3_508
    · exact g_AS_3_510
    · exact g_AS_3_511
    · exact g_AS_3_512
    · exact g_AS_3_522
    · exact g_AS_3_523
    · exact g_AS_3_1346
    · exact g_AS_3_1347
    · exact g_AS_3_1354
    · exact g_AS_3_1355
    · exact g_AS_3_1357
    · exact g_AS_3_1358
    · exact g_AS_3_1359
    · exact g_AS_3_1360
    · exact g_AS_3_1361
    · exact g_AS_3_1362
  · have e : Sierksma.FB.rootList 4 = [0, 1, 4, 5, 12, 13, 30, 31, 34, 35, 40, 41, 43, 44, 45, 46, 47, 48, 62, 63, 66, 70, 71, 81, 82, 83, 84, 85, 86, 88, 90, 115, 116, 119, 120, 127, 128, 130, 131, 134, 135, 140, 141, 143, 144, 145, 146, 147, 148, 161, 162, 163, 166, 170, 171, 174, 175, 181, 182, 183, 184, 185, 186, 188, 189, 190, 193, 208, 209, 210, 212, 213, 214, 254, 255, 257, 258, 260, 261, 262, 263, 264, 265, 271, 272, 286, 288, 289, 291, 294, 295, 297, 298, 299, 300, 301, 302, 304, 305, 306, 309, 320, 321, 324, 326, 327, 329, 349, 352, 353, 354, 464, 465, 467, 468, 469, 472, 475, 476, 477, 479, 480, 481, 491, 493, 494, 496, 500, 503, 504, 505, 522, 523, 1346, 1347, 1357, 1358, 1359, 1360, 1361, 1362, 1364, 1366, 1392, 1393, 1395, 1396, 1399, 1402, 1403, 1404, 1407, 1447, 1451] := rfl
    rw [e] at hr2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr2
    rcases hr2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact g_AS_4_0
    · exact g_AS_4_1
    · exact g_AS_4_4
    · exact g_AS_4_5
    · exact g_AS_4_12
    · exact g_AS_4_13
    · exact g_AS_4_30
    · exact g_AS_4_31
    · exact g_AS_4_34
    · exact g_AS_4_35
    · exact g_AS_4_40
    · exact g_AS_4_41
    · exact g_AS_4_43
    · exact g_AS_4_44
    · exact g_AS_4_45
    · exact g_AS_4_46
    · exact g_AS_4_47
    · exact g_AS_4_48
    · exact g_AS_4_62
    · exact g_AS_4_63
    · exact g_AS_4_66
    · exact g_AS_4_70
    · exact g_AS_4_71
    · exact g_AS_4_81
    · exact g_AS_4_82
    · exact g_AS_4_83
    · exact g_AS_4_84
    · exact g_AS_4_85
    · exact g_AS_4_86
    · exact g_AS_4_88
    · exact g_AS_4_90
    · exact g_AS_4_115
    · exact g_AS_4_116
    · exact g_AS_4_119
    · exact g_AS_4_120
    · exact g_AS_4_127
    · exact g_AS_4_128
    · exact g_AS_4_130
    · exact g_AS_4_131
    · exact g_AS_4_134
    · exact g_AS_4_135
    · exact g_AS_4_140
    · exact g_AS_4_141
    · exact g_AS_4_143
    · exact g_AS_4_144
    · exact g_AS_4_145
    · exact g_AS_4_146
    · exact g_AS_4_147
    · exact g_AS_4_148
    · exact g_AS_4_161
    · exact g_AS_4_162
    · exact g_AS_4_163
    · exact g_AS_4_166
    · exact g_AS_4_170
    · exact g_AS_4_171
    · exact g_AS_4_174
    · exact g_AS_4_175
    · exact g_AS_4_181
    · exact g_AS_4_182
    · exact g_AS_4_183
    · exact g_AS_4_184
    · exact g_AS_4_185
    · exact g_AS_4_186
    · exact g_AS_4_188
    · exact g_AS_4_189
    · exact g_AS_4_190
    · exact g_AS_4_193
    · exact g_AS_4_208
    · exact g_AS_4_209
    · exact g_AS_4_210
    · exact g_AS_4_212
    · exact g_AS_4_213
    · exact g_AS_4_214
    · exact g_AS_4_254
    · exact g_AS_4_255
    · exact g_AS_4_257
    · exact g_AS_4_258
    · exact g_AS_4_260
    · exact g_AS_4_261
    · exact g_AS_4_262
    · exact g_AS_4_263
    · exact g_AS_4_264
    · exact g_AS_4_265
    · exact g_AS_4_271
    · exact g_AS_4_272
    · exact g_AS_4_286
    · exact g_AS_4_288
    · exact g_AS_4_289
    · exact g_AS_4_291
    · exact g_AS_4_294
    · exact g_AS_4_295
    · exact g_AS_4_297
    · exact g_AS_4_298
    · exact g_AS_4_299
    · exact g_AS_4_300
    · exact g_AS_4_301
    · exact g_AS_4_302
    · exact g_AS_4_304
    · exact g_AS_4_305
    · exact g_AS_4_306
    · exact g_AS_4_309
    · exact g_AS_4_320
    · exact g_AS_4_321
    · exact g_AS_4_324
    · exact g_AS_4_326
    · exact g_AS_4_327
    · exact g_AS_4_329
    · exact g_AS_4_349
    · exact g_AS_4_352
    · exact g_AS_4_353
    · exact g_AS_4_354
    · exact g_AS_4_464
    · exact g_AS_4_465
    · exact g_AS_4_467
    · exact g_AS_4_468
    · exact g_AS_4_469
    · exact g_AS_4_472
    · exact g_AS_4_475
    · exact g_AS_4_476
    · exact g_AS_4_477
    · exact g_AS_4_479
    · exact g_AS_4_480
    · exact g_AS_4_481
    · exact g_AS_4_491
    · exact g_AS_4_493
    · exact g_AS_4_494
    · exact g_AS_4_496
    · exact g_AS_4_500
    · exact g_AS_4_503
    · exact g_AS_4_504
    · exact g_AS_4_505
    · exact g_AS_4_522
    · exact g_AS_4_523
    · exact g_AS_4_1346
    · exact g_AS_4_1347
    · exact g_AS_4_1357
    · exact g_AS_4_1358
    · exact g_AS_4_1359
    · exact g_AS_4_1360
    · exact g_AS_4_1361
    · exact g_AS_4_1362
    · exact g_AS_4_1364
    · exact g_AS_4_1366
    · exact g_AS_4_1392
    · exact g_AS_4_1393
    · exact g_AS_4_1395
    · exact g_AS_4_1396
    · exact g_AS_4_1399
    · exact g_AS_4_1402
    · exact g_AS_4_1403
    · exact g_AS_4_1404
    · exact g_AS_4_1407
    · exact g_AS_4_1447
    · exact g_AS_4_1451
  · have e : Sierksma.FB.rootList 5 = [0, 1, 4, 5, 12, 13, 40, 43, 44, 45, 46, 47, 48, 61, 62, 67, 88, 92, 115, 116, 119, 120, 127, 128, 130, 134, 135, 140, 141, 143, 144, 145, 146, 147, 148, 161, 162, 163, 165, 166, 167, 174, 181, 182, 183, 184, 185, 186, 188, 189, 190, 192, 193, 194, 208, 209, 210, 212, 213, 214, 271, 272, 286, 287, 288, 289, 290, 291, 324, 325, 327, 348, 349, 350, 352, 353, 354, 522, 1346, 1347, 1357, 1358, 1359, 1360, 1364, 1366, 1368, 1395, 1396, 1402, 1403, 1406, 1408] := rfl
    rw [e] at hr2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr2
    rcases hr2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact g_AS_5_0
    · exact g_AS_5_1
    · exact g_AS_5_4
    · exact g_AS_5_5
    · exact g_AS_5_12
    · exact g_AS_5_13
    · exact g_AS_5_40
    · exact g_AS_5_43
    · exact g_AS_5_44
    · exact g_AS_5_45
    · exact g_AS_5_46
    · exact g_AS_5_47
    · exact g_AS_5_48
    · exact g_AS_5_61
    · exact g_AS_5_62
    · exact g_AS_5_67
    · exact g_AS_5_88
    · exact g_AS_5_92
    · exact g_AS_5_115
    · exact g_AS_5_116
    · exact g_AS_5_119
    · exact g_AS_5_120
    · exact g_AS_5_127
    · exact g_AS_5_128
    · exact g_AS_5_130
    · exact g_AS_5_134
    · exact g_AS_5_135
    · exact g_AS_5_140
    · exact g_AS_5_141
    · exact g_AS_5_143
    · exact g_AS_5_144
    · exact g_AS_5_145
    · exact g_AS_5_146
    · exact g_AS_5_147
    · exact g_AS_5_148
    · exact g_AS_5_161
    · exact g_AS_5_162
    · exact g_AS_5_163
    · exact g_AS_5_165
    · exact g_AS_5_166
    · exact g_AS_5_167
    · exact g_AS_5_174
    · exact g_AS_5_181
    · exact g_AS_5_182
    · exact g_AS_5_183
    · exact g_AS_5_184
    · exact g_AS_5_185
    · exact g_AS_5_186
    · exact g_AS_5_188
    · exact g_AS_5_189
    · exact g_AS_5_190
    · exact g_AS_5_192
    · exact g_AS_5_193
    · exact g_AS_5_194
    · exact g_AS_5_208
    · exact g_AS_5_209
    · exact g_AS_5_210
    · exact g_AS_5_212
    · exact g_AS_5_213
    · exact g_AS_5_214
    · exact g_AS_5_271
    · exact g_AS_5_272
    · exact g_AS_5_286
    · exact g_AS_5_287
    · exact g_AS_5_288
    · exact g_AS_5_289
    · exact g_AS_5_290
    · exact g_AS_5_291
    · exact g_AS_5_324
    · exact g_AS_5_325
    · exact g_AS_5_327
    · exact g_AS_5_348
    · exact g_AS_5_349
    · exact g_AS_5_350
    · exact g_AS_5_352
    · exact g_AS_5_353
    · exact g_AS_5_354
    · exact g_AS_5_522
    · exact g_AS_5_1346
    · exact g_AS_5_1347
    · exact g_AS_5_1357
    · exact g_AS_5_1358
    · exact g_AS_5_1359
    · exact g_AS_5_1360
    · exact g_AS_5_1364
    · exact g_AS_5_1366
    · exact g_AS_5_1368
    · exact g_AS_5_1395
    · exact g_AS_5_1396
    · exact g_AS_5_1402
    · exact g_AS_5_1403
    · exact g_AS_5_1406
    · exact g_AS_5_1408

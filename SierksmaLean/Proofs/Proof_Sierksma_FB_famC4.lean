import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cC4S_0
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem proof_Sierksma_FB_famC4 : ∀ k < 6, ∀ r2 ∈ Sierksma.FB.rootList k,
    Sierksma.FB.Good (Sierksma.FB.memBits (Sierksma.FB.pairSort (Sierksma.FB.R1.getD k 0) r2)) (Sierksma.FB.KS k r2) 5 (Sierksma.FB.capsOf 15 3) := by
  have hg0 := Sierksma.FB.cC4S_0
  simp only [Bool.and_eq_true] at hg0
  obtain ⟨h_C4S_0_1, h_C4S_0_15, h_C4S_0_16, h_C4S_0_40, h_C4S_0_41, h_C4S_0_215, h_C4S_0_216, h_C4S_4_0, h_C4S_4_1, h_C4S_4_5, h_C4S_4_8, h_C4S_4_9, h_C4S_4_15, h_C4S_4_16, h_C4S_4_19, h_C4S_4_20, h_C4S_4_23, h_C4S_4_24, h_C4S_4_27, h_C4S_4_28, h_C4S_4_37, h_C4S_4_38, h_C4S_4_40, h_C4S_4_41, h_C4S_4_51, h_C4S_4_52, h_C4S_4_97, h_C4S_4_98, h_C4S_4_215, h_C4S_4_216, h_C4S_4_219, h_C4S_4_220, h_C4S_4_222, h_C4S_4_223, h_C4S_4_236, h_C4S_4_237, h_C4S_4_356, h_C4S_4_357, h_C4S_4_364, h_C4S_4_365, h_C4S_4_428, h_C4S_4_429, h_C4S_43_0, h_C4S_43_1, h_C4S_43_4, h_C4S_43_5, h_C4S_43_8, h_C4S_43_9, h_C4S_43_37, h_C4S_43_38, h_C4S_43_45, h_C4S_43_51, h_C4S_43_52, h_C4S_43_54, h_C4S_43_56, h_C4S_43_115, h_C4S_43_119, h_C4S_43_123, h_C4S_43_124, h_C4S_43_137, h_C4S_43_138, h_C4S_43_143, h_C4S_43_145, h_C4S_43_151, h_C4S_43_152, h_C4S_43_154, h_C4S_43_156, h_C4S_43_197, h_C4S_43_198, h_C4S_43_209, h_C4S_43_213, h_C4S_44_0, h_C4S_44_1, h_C4S_44_4, h_C4S_44_5, h_C4S_44_8, h_C4S_44_9, h_C4S_44_37, h_C4S_44_38, h_C4S_44_40, h_C4S_44_41, h_C4S_44_43, h_C4S_44_45, h_C4S_44_46, h_C4S_44_47, h_C4S_44_48, h_C4S_44_51, h_C4S_44_52, h_C4S_44_54, h_C4S_44_55, h_C4S_44_56, h_C4S_44_57, h_C4S_44_58, h_C4S_44_59, h_C4S_44_115, h_C4S_44_116, h_C4S_44_119, h_C4S_44_120, h_C4S_44_123, h_C4S_44_124, h_C4S_44_127, h_C4S_44_128, h_C4S_44_137, h_C4S_44_138, h_C4S_44_140, h_C4S_44_141, h_C4S_44_143, h_C4S_44_144, h_C4S_44_145, h_C4S_44_146, h_C4S_44_147, h_C4S_44_148, h_C4S_44_151, h_C4S_44_152, h_C4S_44_154, h_C4S_44_155, h_C4S_44_156, h_C4S_44_157, h_C4S_44_158, h_C4S_44_159, h_C4S_44_197, h_C4S_44_198, h_C4S_44_208, h_C4S_44_209, h_C4S_44_210, h_C4S_44_212, h_C4S_44_213, h_C4S_44_214, h_C4S_44_267, h_C4S_44_268, h_C4S_44_271, h_C4S_44_272, h_C4S_44_274, h_C4S_44_275, h_C4S_44_276, h_C4S_44_277, h_C4S_44_278, h_C4S_44_279, h_C4S_44_282, h_C4S_44_283, h_C4S_44_506, h_C4S_44_507, h_C4S_44_508, h_C4S_44_510, h_C4S_44_511, h_C4S_44_512, h_C4S_44_522, h_C4S_44_523, h_C4S_44_1346, h_C4S_44_1347, h_C4S_44_1354, h_C4S_44_1355, h_C4S_44_1357, h_C4S_44_1358, h_C4S_44_1359, h_C4S_44_1360, h_C4S_44_1361, h_C4S_44_1362, h_C4S_61_0, h_C4S_61_1, h_C4S_61_4, h_C4S_61_5, h_C4S_61_12, h_C4S_61_13, h_C4S_61_30, h_C4S_61_31, h_C4S_61_34, h_C4S_61_35, h_C4S_61_40, h_C4S_61_41, h_C4S_61_43, h_C4S_61_44, h_C4S_61_45, h_C4S_61_46, h_C4S_61_47, h_C4S_61_48, h_C4S_61_62, h_C4S_61_63, h_C4S_61_66, h_C4S_61_70, h_C4S_61_71, h_C4S_61_81, h_C4S_61_82, h_C4S_61_83, h_C4S_61_84, h_C4S_61_85, h_C4S_61_86, h_C4S_61_88, h_C4S_61_90, h_C4S_61_115, h_C4S_61_116, h_C4S_61_119, h_C4S_61_120, h_C4S_61_127, h_C4S_61_128, h_C4S_61_130, h_C4S_61_131, h_C4S_61_134, h_C4S_61_135, h_C4S_61_140, h_C4S_61_141, h_C4S_61_143, h_C4S_61_144, h_C4S_61_145, h_C4S_61_146, h_C4S_61_147, h_C4S_61_148, h_C4S_61_161, h_C4S_61_162, h_C4S_61_163, h_C4S_61_166, h_C4S_61_170, h_C4S_61_171, h_C4S_61_174, h_C4S_61_175, h_C4S_61_181, h_C4S_61_182, h_C4S_61_183, h_C4S_61_184, h_C4S_61_185, h_C4S_61_186, h_C4S_61_188, h_C4S_61_189, h_C4S_61_190, h_C4S_61_193, h_C4S_61_208, h_C4S_61_209, h_C4S_61_210, h_C4S_61_212, h_C4S_61_213, h_C4S_61_214, h_C4S_61_254, h_C4S_61_255, h_C4S_61_257, h_C4S_61_258, h_C4S_61_260, h_C4S_61_261, h_C4S_61_262, h_C4S_61_263, h_C4S_61_264, h_C4S_61_265, h_C4S_61_271, h_C4S_61_272, h_C4S_61_286, h_C4S_61_288, h_C4S_61_289, h_C4S_61_291, h_C4S_61_294, h_C4S_61_295, h_C4S_61_297, h_C4S_61_298, h_C4S_61_299, h_C4S_61_300, h_C4S_61_301, h_C4S_61_302, h_C4S_61_304, h_C4S_61_305, h_C4S_61_306, h_C4S_61_309, h_C4S_61_320, h_C4S_61_321, h_C4S_61_324, h_C4S_61_326, h_C4S_61_327, h_C4S_61_329, h_C4S_61_349, h_C4S_61_352, h_C4S_61_353, h_C4S_61_354, h_C4S_61_464, h_C4S_61_465, h_C4S_61_467, h_C4S_61_468, h_C4S_61_469, h_C4S_61_472, h_C4S_61_475, h_C4S_61_476, h_C4S_61_477, h_C4S_61_479, h_C4S_61_480, h_C4S_61_481, h_C4S_61_491, h_C4S_61_493, h_C4S_61_494, h_C4S_61_496, h_C4S_61_500, h_C4S_61_503, h_C4S_61_504, h_C4S_61_505, h_C4S_61_522, h_C4S_61_523, h_C4S_61_1346, h_C4S_61_1347, h_C4S_61_1357, h_C4S_61_1358, h_C4S_61_1359, h_C4S_61_1360, h_C4S_61_1361, h_C4S_61_1362, h_C4S_61_1364, h_C4S_61_1366, h_C4S_61_1392, h_C4S_61_1393, h_C4S_61_1395, h_C4S_61_1396, h_C4S_61_1399, h_C4S_61_1402, h_C4S_61_1403, h_C4S_61_1404, h_C4S_61_1407, h_C4S_61_1447, h_C4S_61_1451, h_C4S_65_0, h_C4S_65_1, h_C4S_65_4, h_C4S_65_5, h_C4S_65_12, h_C4S_65_13, h_C4S_65_40, h_C4S_65_43, h_C4S_65_44, h_C4S_65_45, h_C4S_65_46, h_C4S_65_47, h_C4S_65_48, h_C4S_65_61, h_C4S_65_62, h_C4S_65_67, h_C4S_65_88, h_C4S_65_92, h_C4S_65_115, h_C4S_65_116, h_C4S_65_119, h_C4S_65_120, h_C4S_65_127, h_C4S_65_128, h_C4S_65_130, h_C4S_65_134, h_C4S_65_135, h_C4S_65_140, h_C4S_65_141, h_C4S_65_143, h_C4S_65_144, h_C4S_65_145, h_C4S_65_146, h_C4S_65_147, h_C4S_65_148, h_C4S_65_161, h_C4S_65_162, h_C4S_65_163, h_C4S_65_165, h_C4S_65_166, h_C4S_65_167, h_C4S_65_174, h_C4S_65_181, h_C4S_65_182, h_C4S_65_183, h_C4S_65_184, h_C4S_65_185, h_C4S_65_186, h_C4S_65_188, h_C4S_65_189, h_C4S_65_190, h_C4S_65_192, h_C4S_65_193, h_C4S_65_194, h_C4S_65_208, h_C4S_65_209, h_C4S_65_210, h_C4S_65_212, h_C4S_65_213, h_C4S_65_214, h_C4S_65_271, h_C4S_65_272, h_C4S_65_286, h_C4S_65_287, h_C4S_65_288, h_C4S_65_289, h_C4S_65_290, h_C4S_65_291, h_C4S_65_324, h_C4S_65_325, h_C4S_65_327, h_C4S_65_348, h_C4S_65_349, h_C4S_65_350, h_C4S_65_352, h_C4S_65_353, h_C4S_65_354, h_C4S_65_522, h_C4S_65_1346, h_C4S_65_1347, h_C4S_65_1357, h_C4S_65_1358, h_C4S_65_1359, h_C4S_65_1360, h_C4S_65_1364, h_C4S_65_1366, h_C4S_65_1368, h_C4S_65_1395, h_C4S_65_1396, h_C4S_65_1402, h_C4S_65_1403, h_C4S_65_1406, h_C4S_65_1408⟩ := hg0
  have g_C4S_0_1 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_0_1 (by simp)
  have g_C4S_0_15 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_0_15 (by simp)
  have g_C4S_0_16 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_0_16 (by simp)
  have g_C4S_0_40 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_0_40 (by simp)
  have g_C4S_0_41 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_0_41 (by simp)
  have g_C4S_0_215 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_0_215 (by simp)
  have g_C4S_0_216 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_0_216 (by simp)
  have g_C4S_4_0 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_4_0 (by simp)
  have g_C4S_4_1 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_4_1 (by simp)
  have g_C4S_4_5 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_4_5 (by simp)
  have g_C4S_4_8 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_4_8 (by simp)
  have g_C4S_4_9 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_4_9 (by simp)
  have g_C4S_4_15 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_4_15 (by simp)
  have g_C4S_4_16 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_4_16 (by simp)
  have g_C4S_4_19 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_4_19 (by simp)
  have g_C4S_4_20 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_4_20 (by simp)
  have g_C4S_4_23 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_4_23 (by simp)
  have g_C4S_4_24 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_4_24 (by simp)
  have g_C4S_4_27 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_4_27 (by simp)
  have g_C4S_4_28 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_4_28 (by simp)
  have g_C4S_4_37 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_4_37 (by simp)
  have g_C4S_4_38 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_4_38 (by simp)
  have g_C4S_4_40 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_4_40 (by simp)
  have g_C4S_4_41 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_4_41 (by simp)
  have g_C4S_4_51 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_4_51 (by simp)
  have g_C4S_4_52 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_4_52 (by simp)
  have g_C4S_4_97 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_4_97 (by simp)
  have g_C4S_4_98 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_4_98 (by simp)
  have g_C4S_4_215 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_4_215 (by simp)
  have g_C4S_4_216 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_4_216 (by simp)
  have g_C4S_4_219 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_4_219 (by simp)
  have g_C4S_4_220 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_4_220 (by simp)
  have g_C4S_4_222 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_4_222 (by simp)
  have g_C4S_4_223 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_4_223 (by simp)
  have g_C4S_4_236 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_4_236 (by simp)
  have g_C4S_4_237 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_4_237 (by simp)
  have g_C4S_4_356 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_4_356 (by simp)
  have g_C4S_4_357 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_4_357 (by simp)
  have g_C4S_4_364 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_4_364 (by simp)
  have g_C4S_4_365 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_4_365 (by simp)
  have g_C4S_4_428 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_4_428 (by simp)
  have g_C4S_4_429 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_4_429 (by simp)
  have g_C4S_43_0 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_43_0 (by simp)
  have g_C4S_43_1 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_43_1 (by simp)
  have g_C4S_43_4 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_43_4 (by simp)
  have g_C4S_43_5 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_43_5 (by simp)
  have g_C4S_43_8 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_43_8 (by simp)
  have g_C4S_43_9 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_43_9 (by simp)
  have g_C4S_43_37 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_43_37 (by simp)
  have g_C4S_43_38 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_43_38 (by simp)
  have g_C4S_43_45 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_43_45 (by simp)
  have g_C4S_43_51 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_43_51 (by simp)
  have g_C4S_43_52 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_43_52 (by simp)
  have g_C4S_43_54 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_43_54 (by simp)
  have g_C4S_43_56 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_43_56 (by simp)
  have g_C4S_43_115 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_43_115 (by simp)
  have g_C4S_43_119 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_43_119 (by simp)
  have g_C4S_43_123 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_43_123 (by simp)
  have g_C4S_43_124 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_43_124 (by simp)
  have g_C4S_43_137 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_43_137 (by simp)
  have g_C4S_43_138 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_43_138 (by simp)
  have g_C4S_43_143 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_43_143 (by simp)
  have g_C4S_43_145 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_43_145 (by simp)
  have g_C4S_43_151 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_43_151 (by simp)
  have g_C4S_43_152 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_43_152 (by simp)
  have g_C4S_43_154 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_43_154 (by simp)
  have g_C4S_43_156 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_43_156 (by simp)
  have g_C4S_43_197 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_43_197 (by simp)
  have g_C4S_43_198 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_43_198 (by simp)
  have g_C4S_43_209 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_43_209 (by simp)
  have g_C4S_43_213 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_43_213 (by simp)
  have g_C4S_44_0 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_0 (by simp)
  have g_C4S_44_1 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_1 (by simp)
  have g_C4S_44_4 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_4 (by simp)
  have g_C4S_44_5 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_5 (by simp)
  have g_C4S_44_8 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_8 (by simp)
  have g_C4S_44_9 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_9 (by simp)
  have g_C4S_44_37 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_37 (by simp)
  have g_C4S_44_38 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_38 (by simp)
  have g_C4S_44_40 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_40 (by simp)
  have g_C4S_44_41 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_41 (by simp)
  have g_C4S_44_43 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_43 (by simp)
  have g_C4S_44_45 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_45 (by simp)
  have g_C4S_44_46 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_46 (by simp)
  have g_C4S_44_47 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_47 (by simp)
  have g_C4S_44_48 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_48 (by simp)
  have g_C4S_44_51 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_51 (by simp)
  have g_C4S_44_52 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_52 (by simp)
  have g_C4S_44_54 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_54 (by simp)
  have g_C4S_44_55 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_55 (by simp)
  have g_C4S_44_56 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_56 (by simp)
  have g_C4S_44_57 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_57 (by simp)
  have g_C4S_44_58 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_58 (by simp)
  have g_C4S_44_59 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_59 (by simp)
  have g_C4S_44_115 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_115 (by simp)
  have g_C4S_44_116 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_116 (by simp)
  have g_C4S_44_119 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_119 (by simp)
  have g_C4S_44_120 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_120 (by simp)
  have g_C4S_44_123 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_123 (by simp)
  have g_C4S_44_124 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_124 (by simp)
  have g_C4S_44_127 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_127 (by simp)
  have g_C4S_44_128 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_128 (by simp)
  have g_C4S_44_137 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_137 (by simp)
  have g_C4S_44_138 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_138 (by simp)
  have g_C4S_44_140 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_140 (by simp)
  have g_C4S_44_141 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_141 (by simp)
  have g_C4S_44_143 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_143 (by simp)
  have g_C4S_44_144 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_144 (by simp)
  have g_C4S_44_145 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_145 (by simp)
  have g_C4S_44_146 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_146 (by simp)
  have g_C4S_44_147 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_147 (by simp)
  have g_C4S_44_148 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_148 (by simp)
  have g_C4S_44_151 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_151 (by simp)
  have g_C4S_44_152 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_152 (by simp)
  have g_C4S_44_154 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_154 (by simp)
  have g_C4S_44_155 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_155 (by simp)
  have g_C4S_44_156 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_156 (by simp)
  have g_C4S_44_157 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_157 (by simp)
  have g_C4S_44_158 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_158 (by simp)
  have g_C4S_44_159 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_159 (by simp)
  have g_C4S_44_197 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_197 (by simp)
  have g_C4S_44_198 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_198 (by simp)
  have g_C4S_44_208 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_208 (by simp)
  have g_C4S_44_209 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_209 (by simp)
  have g_C4S_44_210 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_210 (by simp)
  have g_C4S_44_212 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_212 (by simp)
  have g_C4S_44_213 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_213 (by simp)
  have g_C4S_44_214 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_214 (by simp)
  have g_C4S_44_267 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_267 (by simp)
  have g_C4S_44_268 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_268 (by simp)
  have g_C4S_44_271 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_271 (by simp)
  have g_C4S_44_272 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_272 (by simp)
  have g_C4S_44_274 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_274 (by simp)
  have g_C4S_44_275 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_275 (by simp)
  have g_C4S_44_276 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_276 (by simp)
  have g_C4S_44_277 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_277 (by simp)
  have g_C4S_44_278 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_278 (by simp)
  have g_C4S_44_279 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_279 (by simp)
  have g_C4S_44_282 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_282 (by simp)
  have g_C4S_44_283 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_283 (by simp)
  have g_C4S_44_506 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_506 (by simp)
  have g_C4S_44_507 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_507 (by simp)
  have g_C4S_44_508 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_508 (by simp)
  have g_C4S_44_510 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_510 (by simp)
  have g_C4S_44_511 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_511 (by simp)
  have g_C4S_44_512 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_512 (by simp)
  have g_C4S_44_522 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_522 (by simp)
  have g_C4S_44_523 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_523 (by simp)
  have g_C4S_44_1346 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_1346 (by simp)
  have g_C4S_44_1347 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_1347 (by simp)
  have g_C4S_44_1354 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_1354 (by simp)
  have g_C4S_44_1355 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_1355 (by simp)
  have g_C4S_44_1357 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_1357 (by simp)
  have g_C4S_44_1358 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_1358 (by simp)
  have g_C4S_44_1359 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_1359 (by simp)
  have g_C4S_44_1360 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_1360 (by simp)
  have g_C4S_44_1361 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_1361 (by simp)
  have g_C4S_44_1362 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_44_1362 (by simp)
  have g_C4S_61_0 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_0 (by simp)
  have g_C4S_61_1 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_1 (by simp)
  have g_C4S_61_4 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_4 (by simp)
  have g_C4S_61_5 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_5 (by simp)
  have g_C4S_61_12 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_12 (by simp)
  have g_C4S_61_13 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_13 (by simp)
  have g_C4S_61_30 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_30 (by simp)
  have g_C4S_61_31 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_31 (by simp)
  have g_C4S_61_34 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_34 (by simp)
  have g_C4S_61_35 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_35 (by simp)
  have g_C4S_61_40 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_40 (by simp)
  have g_C4S_61_41 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_41 (by simp)
  have g_C4S_61_43 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_43 (by simp)
  have g_C4S_61_44 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_44 (by simp)
  have g_C4S_61_45 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_45 (by simp)
  have g_C4S_61_46 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_46 (by simp)
  have g_C4S_61_47 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_47 (by simp)
  have g_C4S_61_48 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_48 (by simp)
  have g_C4S_61_62 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_62 (by simp)
  have g_C4S_61_63 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_63 (by simp)
  have g_C4S_61_66 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_66 (by simp)
  have g_C4S_61_70 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_70 (by simp)
  have g_C4S_61_71 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_71 (by simp)
  have g_C4S_61_81 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_81 (by simp)
  have g_C4S_61_82 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_82 (by simp)
  have g_C4S_61_83 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_83 (by simp)
  have g_C4S_61_84 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_84 (by simp)
  have g_C4S_61_85 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_85 (by simp)
  have g_C4S_61_86 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_86 (by simp)
  have g_C4S_61_88 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_88 (by simp)
  have g_C4S_61_90 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_90 (by simp)
  have g_C4S_61_115 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_115 (by simp)
  have g_C4S_61_116 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_116 (by simp)
  have g_C4S_61_119 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_119 (by simp)
  have g_C4S_61_120 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_120 (by simp)
  have g_C4S_61_127 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_127 (by simp)
  have g_C4S_61_128 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_128 (by simp)
  have g_C4S_61_130 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_130 (by simp)
  have g_C4S_61_131 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_131 (by simp)
  have g_C4S_61_134 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_134 (by simp)
  have g_C4S_61_135 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_135 (by simp)
  have g_C4S_61_140 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_140 (by simp)
  have g_C4S_61_141 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_141 (by simp)
  have g_C4S_61_143 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_143 (by simp)
  have g_C4S_61_144 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_144 (by simp)
  have g_C4S_61_145 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_145 (by simp)
  have g_C4S_61_146 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_146 (by simp)
  have g_C4S_61_147 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_147 (by simp)
  have g_C4S_61_148 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_148 (by simp)
  have g_C4S_61_161 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_161 (by simp)
  have g_C4S_61_162 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_162 (by simp)
  have g_C4S_61_163 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_163 (by simp)
  have g_C4S_61_166 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_166 (by simp)
  have g_C4S_61_170 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_170 (by simp)
  have g_C4S_61_171 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_171 (by simp)
  have g_C4S_61_174 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_174 (by simp)
  have g_C4S_61_175 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_175 (by simp)
  have g_C4S_61_181 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_181 (by simp)
  have g_C4S_61_182 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_182 (by simp)
  have g_C4S_61_183 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_183 (by simp)
  have g_C4S_61_184 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_184 (by simp)
  have g_C4S_61_185 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_185 (by simp)
  have g_C4S_61_186 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_186 (by simp)
  have g_C4S_61_188 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_188 (by simp)
  have g_C4S_61_189 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_189 (by simp)
  have g_C4S_61_190 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_190 (by simp)
  have g_C4S_61_193 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_193 (by simp)
  have g_C4S_61_208 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_208 (by simp)
  have g_C4S_61_209 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_209 (by simp)
  have g_C4S_61_210 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_210 (by simp)
  have g_C4S_61_212 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_212 (by simp)
  have g_C4S_61_213 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_213 (by simp)
  have g_C4S_61_214 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_214 (by simp)
  have g_C4S_61_254 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_254 (by simp)
  have g_C4S_61_255 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_255 (by simp)
  have g_C4S_61_257 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_257 (by simp)
  have g_C4S_61_258 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_258 (by simp)
  have g_C4S_61_260 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_260 (by simp)
  have g_C4S_61_261 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_261 (by simp)
  have g_C4S_61_262 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_262 (by simp)
  have g_C4S_61_263 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_263 (by simp)
  have g_C4S_61_264 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_264 (by simp)
  have g_C4S_61_265 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_265 (by simp)
  have g_C4S_61_271 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_271 (by simp)
  have g_C4S_61_272 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_272 (by simp)
  have g_C4S_61_286 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_286 (by simp)
  have g_C4S_61_288 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_288 (by simp)
  have g_C4S_61_289 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_289 (by simp)
  have g_C4S_61_291 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_291 (by simp)
  have g_C4S_61_294 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_294 (by simp)
  have g_C4S_61_295 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_295 (by simp)
  have g_C4S_61_297 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_297 (by simp)
  have g_C4S_61_298 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_298 (by simp)
  have g_C4S_61_299 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_299 (by simp)
  have g_C4S_61_300 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_300 (by simp)
  have g_C4S_61_301 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_301 (by simp)
  have g_C4S_61_302 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_302 (by simp)
  have g_C4S_61_304 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_304 (by simp)
  have g_C4S_61_305 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_305 (by simp)
  have g_C4S_61_306 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_306 (by simp)
  have g_C4S_61_309 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_309 (by simp)
  have g_C4S_61_320 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_320 (by simp)
  have g_C4S_61_321 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_321 (by simp)
  have g_C4S_61_324 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_324 (by simp)
  have g_C4S_61_326 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_326 (by simp)
  have g_C4S_61_327 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_327 (by simp)
  have g_C4S_61_329 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_329 (by simp)
  have g_C4S_61_349 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_349 (by simp)
  have g_C4S_61_352 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_352 (by simp)
  have g_C4S_61_353 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_353 (by simp)
  have g_C4S_61_354 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_354 (by simp)
  have g_C4S_61_464 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_464 (by simp)
  have g_C4S_61_465 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_465 (by simp)
  have g_C4S_61_467 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_467 (by simp)
  have g_C4S_61_468 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_468 (by simp)
  have g_C4S_61_469 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_469 (by simp)
  have g_C4S_61_472 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_472 (by simp)
  have g_C4S_61_475 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_475 (by simp)
  have g_C4S_61_476 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_476 (by simp)
  have g_C4S_61_477 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_477 (by simp)
  have g_C4S_61_479 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_479 (by simp)
  have g_C4S_61_480 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_480 (by simp)
  have g_C4S_61_481 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_481 (by simp)
  have g_C4S_61_491 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_491 (by simp)
  have g_C4S_61_493 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_493 (by simp)
  have g_C4S_61_494 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_494 (by simp)
  have g_C4S_61_496 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_496 (by simp)
  have g_C4S_61_500 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_500 (by simp)
  have g_C4S_61_503 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_503 (by simp)
  have g_C4S_61_504 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_504 (by simp)
  have g_C4S_61_505 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_505 (by simp)
  have g_C4S_61_522 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_522 (by simp)
  have g_C4S_61_523 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_523 (by simp)
  have g_C4S_61_1346 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_1346 (by simp)
  have g_C4S_61_1347 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_1347 (by simp)
  have g_C4S_61_1357 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_1357 (by simp)
  have g_C4S_61_1358 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_1358 (by simp)
  have g_C4S_61_1359 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_1359 (by simp)
  have g_C4S_61_1360 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_1360 (by simp)
  have g_C4S_61_1361 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_1361 (by simp)
  have g_C4S_61_1362 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_1362 (by simp)
  have g_C4S_61_1364 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_1364 (by simp)
  have g_C4S_61_1366 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_1366 (by simp)
  have g_C4S_61_1392 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_1392 (by simp)
  have g_C4S_61_1393 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_1393 (by simp)
  have g_C4S_61_1395 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_1395 (by simp)
  have g_C4S_61_1396 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_1396 (by simp)
  have g_C4S_61_1399 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_1399 (by simp)
  have g_C4S_61_1402 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_1402 (by simp)
  have g_C4S_61_1403 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_1403 (by simp)
  have g_C4S_61_1404 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_1404 (by simp)
  have g_C4S_61_1407 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_1407 (by simp)
  have g_C4S_61_1447 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_1447 (by simp)
  have g_C4S_61_1451 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_61_1451 (by simp)
  have g_C4S_65_0 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_0 (by simp)
  have g_C4S_65_1 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_1 (by simp)
  have g_C4S_65_4 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_4 (by simp)
  have g_C4S_65_5 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_5 (by simp)
  have g_C4S_65_12 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_12 (by simp)
  have g_C4S_65_13 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_13 (by simp)
  have g_C4S_65_40 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_40 (by simp)
  have g_C4S_65_43 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_43 (by simp)
  have g_C4S_65_44 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_44 (by simp)
  have g_C4S_65_45 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_45 (by simp)
  have g_C4S_65_46 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_46 (by simp)
  have g_C4S_65_47 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_47 (by simp)
  have g_C4S_65_48 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_48 (by simp)
  have g_C4S_65_61 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_61 (by simp)
  have g_C4S_65_62 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_62 (by simp)
  have g_C4S_65_67 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_67 (by simp)
  have g_C4S_65_88 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_88 (by simp)
  have g_C4S_65_92 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_92 (by simp)
  have g_C4S_65_115 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_115 (by simp)
  have g_C4S_65_116 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_116 (by simp)
  have g_C4S_65_119 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_119 (by simp)
  have g_C4S_65_120 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_120 (by simp)
  have g_C4S_65_127 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_127 (by simp)
  have g_C4S_65_128 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_128 (by simp)
  have g_C4S_65_130 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_130 (by simp)
  have g_C4S_65_134 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_134 (by simp)
  have g_C4S_65_135 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_135 (by simp)
  have g_C4S_65_140 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_140 (by simp)
  have g_C4S_65_141 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_141 (by simp)
  have g_C4S_65_143 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_143 (by simp)
  have g_C4S_65_144 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_144 (by simp)
  have g_C4S_65_145 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_145 (by simp)
  have g_C4S_65_146 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_146 (by simp)
  have g_C4S_65_147 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_147 (by simp)
  have g_C4S_65_148 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_148 (by simp)
  have g_C4S_65_161 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_161 (by simp)
  have g_C4S_65_162 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_162 (by simp)
  have g_C4S_65_163 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_163 (by simp)
  have g_C4S_65_165 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_165 (by simp)
  have g_C4S_65_166 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_166 (by simp)
  have g_C4S_65_167 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_167 (by simp)
  have g_C4S_65_174 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_174 (by simp)
  have g_C4S_65_181 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_181 (by simp)
  have g_C4S_65_182 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_182 (by simp)
  have g_C4S_65_183 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_183 (by simp)
  have g_C4S_65_184 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_184 (by simp)
  have g_C4S_65_185 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_185 (by simp)
  have g_C4S_65_186 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_186 (by simp)
  have g_C4S_65_188 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_188 (by simp)
  have g_C4S_65_189 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_189 (by simp)
  have g_C4S_65_190 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_190 (by simp)
  have g_C4S_65_192 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_192 (by simp)
  have g_C4S_65_193 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_193 (by simp)
  have g_C4S_65_194 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_194 (by simp)
  have g_C4S_65_208 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_208 (by simp)
  have g_C4S_65_209 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_209 (by simp)
  have g_C4S_65_210 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_210 (by simp)
  have g_C4S_65_212 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_212 (by simp)
  have g_C4S_65_213 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_213 (by simp)
  have g_C4S_65_214 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_214 (by simp)
  have g_C4S_65_271 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_271 (by simp)
  have g_C4S_65_272 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_272 (by simp)
  have g_C4S_65_286 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_286 (by simp)
  have g_C4S_65_287 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_287 (by simp)
  have g_C4S_65_288 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_288 (by simp)
  have g_C4S_65_289 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_289 (by simp)
  have g_C4S_65_290 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_290 (by simp)
  have g_C4S_65_291 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_291 (by simp)
  have g_C4S_65_324 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_324 (by simp)
  have g_C4S_65_325 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_325 (by simp)
  have g_C4S_65_327 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_327 (by simp)
  have g_C4S_65_348 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_348 (by simp)
  have g_C4S_65_349 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_349 (by simp)
  have g_C4S_65_350 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_350 (by simp)
  have g_C4S_65_352 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_352 (by simp)
  have g_C4S_65_353 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_353 (by simp)
  have g_C4S_65_354 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_354 (by simp)
  have g_C4S_65_522 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_522 (by simp)
  have g_C4S_65_1346 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_1346 (by simp)
  have g_C4S_65_1347 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_1347 (by simp)
  have g_C4S_65_1357 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_1357 (by simp)
  have g_C4S_65_1358 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_1358 (by simp)
  have g_C4S_65_1359 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_1359 (by simp)
  have g_C4S_65_1360 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_1360 (by simp)
  have g_C4S_65_1364 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_1364 (by simp)
  have g_C4S_65_1366 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_1366 (by simp)
  have g_C4S_65_1368 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_1368 (by simp)
  have g_C4S_65_1395 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_1395 (by simp)
  have g_C4S_65_1396 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_1396 (by simp)
  have g_C4S_65_1402 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_1402 (by simp)
  have g_C4S_65_1403 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_1403 (by simp)
  have g_C4S_65_1406 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_1406 (by simp)
  have g_C4S_65_1408 := Sierksma.FB.run_sound _ _ _ _ _ _ h_C4S_65_1408 (by simp)
  intro k hk r2 hr2
  interval_cases k
  · have e : Sierksma.FB.rootList 0 = [1, 15, 16, 40, 41, 215, 216] := rfl
    rw [e] at hr2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr2
    rcases hr2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact g_C4S_0_1
    · exact g_C4S_0_15
    · exact g_C4S_0_16
    · exact g_C4S_0_40
    · exact g_C4S_0_41
    · exact g_C4S_0_215
    · exact g_C4S_0_216
  · have e : Sierksma.FB.rootList 1 = [0, 1, 5, 8, 9, 15, 16, 19, 20, 23, 24, 27, 28, 37, 38, 40, 41, 51, 52, 97, 98, 215, 216, 219, 220, 222, 223, 236, 237, 356, 357, 364, 365, 428, 429] := rfl
    rw [e] at hr2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr2
    rcases hr2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact g_C4S_4_0
    · exact g_C4S_4_1
    · exact g_C4S_4_5
    · exact g_C4S_4_8
    · exact g_C4S_4_9
    · exact g_C4S_4_15
    · exact g_C4S_4_16
    · exact g_C4S_4_19
    · exact g_C4S_4_20
    · exact g_C4S_4_23
    · exact g_C4S_4_24
    · exact g_C4S_4_27
    · exact g_C4S_4_28
    · exact g_C4S_4_37
    · exact g_C4S_4_38
    · exact g_C4S_4_40
    · exact g_C4S_4_41
    · exact g_C4S_4_51
    · exact g_C4S_4_52
    · exact g_C4S_4_97
    · exact g_C4S_4_98
    · exact g_C4S_4_215
    · exact g_C4S_4_216
    · exact g_C4S_4_219
    · exact g_C4S_4_220
    · exact g_C4S_4_222
    · exact g_C4S_4_223
    · exact g_C4S_4_236
    · exact g_C4S_4_237
    · exact g_C4S_4_356
    · exact g_C4S_4_357
    · exact g_C4S_4_364
    · exact g_C4S_4_365
    · exact g_C4S_4_428
    · exact g_C4S_4_429
  · have e : Sierksma.FB.rootList 2 = [0, 1, 4, 5, 8, 9, 37, 38, 45, 51, 52, 54, 56, 115, 119, 123, 124, 137, 138, 143, 145, 151, 152, 154, 156, 197, 198, 209, 213] := rfl
    rw [e] at hr2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr2
    rcases hr2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact g_C4S_43_0
    · exact g_C4S_43_1
    · exact g_C4S_43_4
    · exact g_C4S_43_5
    · exact g_C4S_43_8
    · exact g_C4S_43_9
    · exact g_C4S_43_37
    · exact g_C4S_43_38
    · exact g_C4S_43_45
    · exact g_C4S_43_51
    · exact g_C4S_43_52
    · exact g_C4S_43_54
    · exact g_C4S_43_56
    · exact g_C4S_43_115
    · exact g_C4S_43_119
    · exact g_C4S_43_123
    · exact g_C4S_43_124
    · exact g_C4S_43_137
    · exact g_C4S_43_138
    · exact g_C4S_43_143
    · exact g_C4S_43_145
    · exact g_C4S_43_151
    · exact g_C4S_43_152
    · exact g_C4S_43_154
    · exact g_C4S_43_156
    · exact g_C4S_43_197
    · exact g_C4S_43_198
    · exact g_C4S_43_209
    · exact g_C4S_43_213
  · have e : Sierksma.FB.rootList 3 = [0, 1, 4, 5, 8, 9, 37, 38, 40, 41, 43, 45, 46, 47, 48, 51, 52, 54, 55, 56, 57, 58, 59, 115, 116, 119, 120, 123, 124, 127, 128, 137, 138, 140, 141, 143, 144, 145, 146, 147, 148, 151, 152, 154, 155, 156, 157, 158, 159, 197, 198, 208, 209, 210, 212, 213, 214, 267, 268, 271, 272, 274, 275, 276, 277, 278, 279, 282, 283, 506, 507, 508, 510, 511, 512, 522, 523, 1346, 1347, 1354, 1355, 1357, 1358, 1359, 1360, 1361, 1362] := rfl
    rw [e] at hr2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr2
    rcases hr2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact g_C4S_44_0
    · exact g_C4S_44_1
    · exact g_C4S_44_4
    · exact g_C4S_44_5
    · exact g_C4S_44_8
    · exact g_C4S_44_9
    · exact g_C4S_44_37
    · exact g_C4S_44_38
    · exact g_C4S_44_40
    · exact g_C4S_44_41
    · exact g_C4S_44_43
    · exact g_C4S_44_45
    · exact g_C4S_44_46
    · exact g_C4S_44_47
    · exact g_C4S_44_48
    · exact g_C4S_44_51
    · exact g_C4S_44_52
    · exact g_C4S_44_54
    · exact g_C4S_44_55
    · exact g_C4S_44_56
    · exact g_C4S_44_57
    · exact g_C4S_44_58
    · exact g_C4S_44_59
    · exact g_C4S_44_115
    · exact g_C4S_44_116
    · exact g_C4S_44_119
    · exact g_C4S_44_120
    · exact g_C4S_44_123
    · exact g_C4S_44_124
    · exact g_C4S_44_127
    · exact g_C4S_44_128
    · exact g_C4S_44_137
    · exact g_C4S_44_138
    · exact g_C4S_44_140
    · exact g_C4S_44_141
    · exact g_C4S_44_143
    · exact g_C4S_44_144
    · exact g_C4S_44_145
    · exact g_C4S_44_146
    · exact g_C4S_44_147
    · exact g_C4S_44_148
    · exact g_C4S_44_151
    · exact g_C4S_44_152
    · exact g_C4S_44_154
    · exact g_C4S_44_155
    · exact g_C4S_44_156
    · exact g_C4S_44_157
    · exact g_C4S_44_158
    · exact g_C4S_44_159
    · exact g_C4S_44_197
    · exact g_C4S_44_198
    · exact g_C4S_44_208
    · exact g_C4S_44_209
    · exact g_C4S_44_210
    · exact g_C4S_44_212
    · exact g_C4S_44_213
    · exact g_C4S_44_214
    · exact g_C4S_44_267
    · exact g_C4S_44_268
    · exact g_C4S_44_271
    · exact g_C4S_44_272
    · exact g_C4S_44_274
    · exact g_C4S_44_275
    · exact g_C4S_44_276
    · exact g_C4S_44_277
    · exact g_C4S_44_278
    · exact g_C4S_44_279
    · exact g_C4S_44_282
    · exact g_C4S_44_283
    · exact g_C4S_44_506
    · exact g_C4S_44_507
    · exact g_C4S_44_508
    · exact g_C4S_44_510
    · exact g_C4S_44_511
    · exact g_C4S_44_512
    · exact g_C4S_44_522
    · exact g_C4S_44_523
    · exact g_C4S_44_1346
    · exact g_C4S_44_1347
    · exact g_C4S_44_1354
    · exact g_C4S_44_1355
    · exact g_C4S_44_1357
    · exact g_C4S_44_1358
    · exact g_C4S_44_1359
    · exact g_C4S_44_1360
    · exact g_C4S_44_1361
    · exact g_C4S_44_1362
  · have e : Sierksma.FB.rootList 4 = [0, 1, 4, 5, 12, 13, 30, 31, 34, 35, 40, 41, 43, 44, 45, 46, 47, 48, 62, 63, 66, 70, 71, 81, 82, 83, 84, 85, 86, 88, 90, 115, 116, 119, 120, 127, 128, 130, 131, 134, 135, 140, 141, 143, 144, 145, 146, 147, 148, 161, 162, 163, 166, 170, 171, 174, 175, 181, 182, 183, 184, 185, 186, 188, 189, 190, 193, 208, 209, 210, 212, 213, 214, 254, 255, 257, 258, 260, 261, 262, 263, 264, 265, 271, 272, 286, 288, 289, 291, 294, 295, 297, 298, 299, 300, 301, 302, 304, 305, 306, 309, 320, 321, 324, 326, 327, 329, 349, 352, 353, 354, 464, 465, 467, 468, 469, 472, 475, 476, 477, 479, 480, 481, 491, 493, 494, 496, 500, 503, 504, 505, 522, 523, 1346, 1347, 1357, 1358, 1359, 1360, 1361, 1362, 1364, 1366, 1392, 1393, 1395, 1396, 1399, 1402, 1403, 1404, 1407, 1447, 1451] := rfl
    rw [e] at hr2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr2
    rcases hr2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact g_C4S_61_0
    · exact g_C4S_61_1
    · exact g_C4S_61_4
    · exact g_C4S_61_5
    · exact g_C4S_61_12
    · exact g_C4S_61_13
    · exact g_C4S_61_30
    · exact g_C4S_61_31
    · exact g_C4S_61_34
    · exact g_C4S_61_35
    · exact g_C4S_61_40
    · exact g_C4S_61_41
    · exact g_C4S_61_43
    · exact g_C4S_61_44
    · exact g_C4S_61_45
    · exact g_C4S_61_46
    · exact g_C4S_61_47
    · exact g_C4S_61_48
    · exact g_C4S_61_62
    · exact g_C4S_61_63
    · exact g_C4S_61_66
    · exact g_C4S_61_70
    · exact g_C4S_61_71
    · exact g_C4S_61_81
    · exact g_C4S_61_82
    · exact g_C4S_61_83
    · exact g_C4S_61_84
    · exact g_C4S_61_85
    · exact g_C4S_61_86
    · exact g_C4S_61_88
    · exact g_C4S_61_90
    · exact g_C4S_61_115
    · exact g_C4S_61_116
    · exact g_C4S_61_119
    · exact g_C4S_61_120
    · exact g_C4S_61_127
    · exact g_C4S_61_128
    · exact g_C4S_61_130
    · exact g_C4S_61_131
    · exact g_C4S_61_134
    · exact g_C4S_61_135
    · exact g_C4S_61_140
    · exact g_C4S_61_141
    · exact g_C4S_61_143
    · exact g_C4S_61_144
    · exact g_C4S_61_145
    · exact g_C4S_61_146
    · exact g_C4S_61_147
    · exact g_C4S_61_148
    · exact g_C4S_61_161
    · exact g_C4S_61_162
    · exact g_C4S_61_163
    · exact g_C4S_61_166
    · exact g_C4S_61_170
    · exact g_C4S_61_171
    · exact g_C4S_61_174
    · exact g_C4S_61_175
    · exact g_C4S_61_181
    · exact g_C4S_61_182
    · exact g_C4S_61_183
    · exact g_C4S_61_184
    · exact g_C4S_61_185
    · exact g_C4S_61_186
    · exact g_C4S_61_188
    · exact g_C4S_61_189
    · exact g_C4S_61_190
    · exact g_C4S_61_193
    · exact g_C4S_61_208
    · exact g_C4S_61_209
    · exact g_C4S_61_210
    · exact g_C4S_61_212
    · exact g_C4S_61_213
    · exact g_C4S_61_214
    · exact g_C4S_61_254
    · exact g_C4S_61_255
    · exact g_C4S_61_257
    · exact g_C4S_61_258
    · exact g_C4S_61_260
    · exact g_C4S_61_261
    · exact g_C4S_61_262
    · exact g_C4S_61_263
    · exact g_C4S_61_264
    · exact g_C4S_61_265
    · exact g_C4S_61_271
    · exact g_C4S_61_272
    · exact g_C4S_61_286
    · exact g_C4S_61_288
    · exact g_C4S_61_289
    · exact g_C4S_61_291
    · exact g_C4S_61_294
    · exact g_C4S_61_295
    · exact g_C4S_61_297
    · exact g_C4S_61_298
    · exact g_C4S_61_299
    · exact g_C4S_61_300
    · exact g_C4S_61_301
    · exact g_C4S_61_302
    · exact g_C4S_61_304
    · exact g_C4S_61_305
    · exact g_C4S_61_306
    · exact g_C4S_61_309
    · exact g_C4S_61_320
    · exact g_C4S_61_321
    · exact g_C4S_61_324
    · exact g_C4S_61_326
    · exact g_C4S_61_327
    · exact g_C4S_61_329
    · exact g_C4S_61_349
    · exact g_C4S_61_352
    · exact g_C4S_61_353
    · exact g_C4S_61_354
    · exact g_C4S_61_464
    · exact g_C4S_61_465
    · exact g_C4S_61_467
    · exact g_C4S_61_468
    · exact g_C4S_61_469
    · exact g_C4S_61_472
    · exact g_C4S_61_475
    · exact g_C4S_61_476
    · exact g_C4S_61_477
    · exact g_C4S_61_479
    · exact g_C4S_61_480
    · exact g_C4S_61_481
    · exact g_C4S_61_491
    · exact g_C4S_61_493
    · exact g_C4S_61_494
    · exact g_C4S_61_496
    · exact g_C4S_61_500
    · exact g_C4S_61_503
    · exact g_C4S_61_504
    · exact g_C4S_61_505
    · exact g_C4S_61_522
    · exact g_C4S_61_523
    · exact g_C4S_61_1346
    · exact g_C4S_61_1347
    · exact g_C4S_61_1357
    · exact g_C4S_61_1358
    · exact g_C4S_61_1359
    · exact g_C4S_61_1360
    · exact g_C4S_61_1361
    · exact g_C4S_61_1362
    · exact g_C4S_61_1364
    · exact g_C4S_61_1366
    · exact g_C4S_61_1392
    · exact g_C4S_61_1393
    · exact g_C4S_61_1395
    · exact g_C4S_61_1396
    · exact g_C4S_61_1399
    · exact g_C4S_61_1402
    · exact g_C4S_61_1403
    · exact g_C4S_61_1404
    · exact g_C4S_61_1407
    · exact g_C4S_61_1447
    · exact g_C4S_61_1451
  · have e : Sierksma.FB.rootList 5 = [0, 1, 4, 5, 12, 13, 40, 43, 44, 45, 46, 47, 48, 61, 62, 67, 88, 92, 115, 116, 119, 120, 127, 128, 130, 134, 135, 140, 141, 143, 144, 145, 146, 147, 148, 161, 162, 163, 165, 166, 167, 174, 181, 182, 183, 184, 185, 186, 188, 189, 190, 192, 193, 194, 208, 209, 210, 212, 213, 214, 271, 272, 286, 287, 288, 289, 290, 291, 324, 325, 327, 348, 349, 350, 352, 353, 354, 522, 1346, 1347, 1357, 1358, 1359, 1360, 1364, 1366, 1368, 1395, 1396, 1402, 1403, 1406, 1408] := rfl
    rw [e] at hr2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr2
    rcases hr2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact g_C4S_65_0
    · exact g_C4S_65_1
    · exact g_C4S_65_4
    · exact g_C4S_65_5
    · exact g_C4S_65_12
    · exact g_C4S_65_13
    · exact g_C4S_65_40
    · exact g_C4S_65_43
    · exact g_C4S_65_44
    · exact g_C4S_65_45
    · exact g_C4S_65_46
    · exact g_C4S_65_47
    · exact g_C4S_65_48
    · exact g_C4S_65_61
    · exact g_C4S_65_62
    · exact g_C4S_65_67
    · exact g_C4S_65_88
    · exact g_C4S_65_92
    · exact g_C4S_65_115
    · exact g_C4S_65_116
    · exact g_C4S_65_119
    · exact g_C4S_65_120
    · exact g_C4S_65_127
    · exact g_C4S_65_128
    · exact g_C4S_65_130
    · exact g_C4S_65_134
    · exact g_C4S_65_135
    · exact g_C4S_65_140
    · exact g_C4S_65_141
    · exact g_C4S_65_143
    · exact g_C4S_65_144
    · exact g_C4S_65_145
    · exact g_C4S_65_146
    · exact g_C4S_65_147
    · exact g_C4S_65_148
    · exact g_C4S_65_161
    · exact g_C4S_65_162
    · exact g_C4S_65_163
    · exact g_C4S_65_165
    · exact g_C4S_65_166
    · exact g_C4S_65_167
    · exact g_C4S_65_174
    · exact g_C4S_65_181
    · exact g_C4S_65_182
    · exact g_C4S_65_183
    · exact g_C4S_65_184
    · exact g_C4S_65_185
    · exact g_C4S_65_186
    · exact g_C4S_65_188
    · exact g_C4S_65_189
    · exact g_C4S_65_190
    · exact g_C4S_65_192
    · exact g_C4S_65_193
    · exact g_C4S_65_194
    · exact g_C4S_65_208
    · exact g_C4S_65_209
    · exact g_C4S_65_210
    · exact g_C4S_65_212
    · exact g_C4S_65_213
    · exact g_C4S_65_214
    · exact g_C4S_65_271
    · exact g_C4S_65_272
    · exact g_C4S_65_286
    · exact g_C4S_65_287
    · exact g_C4S_65_288
    · exact g_C4S_65_289
    · exact g_C4S_65_290
    · exact g_C4S_65_291
    · exact g_C4S_65_324
    · exact g_C4S_65_325
    · exact g_C4S_65_327
    · exact g_C4S_65_348
    · exact g_C4S_65_349
    · exact g_C4S_65_350
    · exact g_C4S_65_352
    · exact g_C4S_65_353
    · exact g_C4S_65_354
    · exact g_C4S_65_522
    · exact g_C4S_65_1346
    · exact g_C4S_65_1347
    · exact g_C4S_65_1357
    · exact g_C4S_65_1358
    · exact g_C4S_65_1359
    · exact g_C4S_65_1360
    · exact g_C4S_65_1364
    · exact g_C4S_65_1366
    · exact g_C4S_65_1368
    · exact g_C4S_65_1395
    · exact g_C4S_65_1396
    · exact g_C4S_65_1402
    · exact g_C4S_65_1403
    · exact g_C4S_65_1406
    · exact g_C4S_65_1408

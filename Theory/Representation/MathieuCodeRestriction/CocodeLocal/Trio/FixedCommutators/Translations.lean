module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.Affine

/-!
# Paired translations of the standard Golay trio

Translating two octads by the same binary vector, while fixing the third
pointwise, preserves the native Golay code. This is certified on its twelve
rows. The resulting elements lie in the intrinsic two-core by the proved
affine kernel criterion. They supply point-moving elements with a fixed
anchor in another octad.

Source: Aschbacher–Smith, H.14.1(3) and H.15.6, printed pp.396 and 401;
Aschbacher, *Sporadic Groups*, Lemma 20.2. The finite certificates below use
the native Golay rows and the checked standard affine point coordinates.
-/

public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
open scoped Pointwise
namespace MathieuCode.TrioCalculation
noncomputable section

/-- An explicit inverse to the native affine point labelling. -/
@[expose] def coordinates : Fin 24 ≃ Fin 3 × Vector where
  toFun := ![(0, ![0, 0, 0]), (0, ![1, 0, 1]), (0, ![1, 1, 0]), (0, ![0, 1, 1]), (2, ![0, 0, 0]), (2, ![1, 0, 1]), (1, ![0, 1, 0]), (1, ![0, 0, 0]), (2, ![1, 1, 1]), (1, ![1, 1, 1]), (0, ![1, 1, 1]), (2, ![1, 1, 0]), (1, ![0, 1, 1]), (2, ![1, 0, 0]), (1, ![0, 0, 1]), (1, ![1, 0, 1]), (0, ![1, 0, 0]), (2, ![0, 1, 1]), (2, ![0, 0, 1]), (1, ![1, 0, 0]), (1, ![1, 1, 0]), (2, ![0, 1, 0]), (0, ![0, 1, 0]), (0, ![0, 0, 1])]
  invFun := point
  left_inv := by decide +kernel
  right_inv := by decide +kernel

lemma coordinates_point (i : Fin 3) (v : Vector) : coordinates (point (i,v)) = (i,v) :=
  coordinates.apply_symm_apply (i,v)

lemma point_coordinates (x : Fin 24) : point (coordinates x) = x :=
  coordinates.symm_apply_apply x

private def pairedCoordinatePerm (j : Fin 3) (v : Vector) : Equiv.Perm (Fin 3 × Vector) where
  toFun p := (p.1, p.2 + if p.1 = j then 0 else v)
  invFun p := (p.1, p.2 + if p.1 = j then 0 else v)
  left_inv p := by
    apply Prod.ext
    · rfl
    · funext k
      simp [Pi.add_apply, add_assoc, CharTwo.add_self_eq_zero]
  right_inv p := by
    apply Prod.ext
    · rfl
    · funext k
      simp [Pi.add_apply, add_assoc, CharTwo.add_self_eq_zero]

/-- Fix octad `j`, and translate the other two octads by `v`. -/
def pairedTranslationPerm (j : Fin 3) (v : Vector) : Equiv.Perm (Fin 24) :=
  (coordinates.trans (pairedCoordinatePerm j v)).trans coordinates.symm

lemma pairedTranslationPerm_point (j i : Fin 3) (v w : Vector) :
    pairedTranslationPerm j v (point (i,w)) =
      point (i, w + if i = j then 0 else v) := by
  simp only [pairedTranslationPerm, Equiv.trans_apply, coordinates_point]
  rfl

private def translationMessages : Fin 3 → Fin 8 → Fin 12 → Fin 4096 :=
  ![![![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048], ![1857, 1410, 804, 488, 2944, 1440, 1760, 576, 224, 1632, 1824, 1232], ![529, 530, 4, 8, 512, 272, 144, 576, 544, 16, 2576, 1552], ![2721, 2146, 804, 488, 1632, 2912, 2496, 128, 960, 2944, 2352, 2752], ![705, 2, 212, 536, 192, 2192, 592, 576, 1680, 720, 336, 672], ![1409, 1410, 3076, 3080, 1184, 3344, 2816, 128, 2176, 2368, 3456, 384], ![209, 530, 212, 536, 720, 1616, 640, 128, 2624, 192, 176, 832], ![2145, 2146, 3076, 3080, 2368, 3104, 1056, 576, 1104, 1184, 3168, 96]], ![![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048], ![1282, 1294, 302, 301, 2313, 1315, 1126, 143, 42, 1577, 1317, 1045], ![24, 27, 11, 7, 6, 284, 89, 143, 42, 534, 2069, 1045], ![2084, 2088, 289, 290, 1056, 2336, 2368, 128, 256, 2816, 2352, 2048], ![1, 13, 29, 30, 6, 2067, 89, 143, 1045, 534, 282, 42], ![1282, 1281, 3080, 3076, 1056, 3344, 2368, 128, 2048, 2816, 3328, 256], ![24, 20, 18, 17, 16, 1040, 64, 128, 2048, 512, 48, 256], ![2084, 2087, 3079, 3083, 2313, 3116, 1126, 143, 1045, 1577, 3114, 42]], ![![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048], ![578, 142, 526, 205, 665, 163, 710, 591, 458, 585, 1541, 2245], ![520, 523, 11, 7, 534, 44, 137, 591, 778, 6, 1541, 2565], ![644, 72, 513, 194, 592, 608, 192, 128, 960, 640, 1024, 2752], ![705, 13, 205, 526, 214, 163, 585, 591, 901, 710, 1098, 2698], ![130, 129, 8, 4, 144, 32, 512, 128, 384, 64, 1152, 2176], ![200, 516, 194, 513, 720, 608, 640, 128, 832, 192, 1152, 2624], ![68, 71, 7, 11, 89, 44, 6, 591, 325, 137, 1098, 2122]]]

private lemma pairedTranslationPerm_rows (j : Fin 3) (v : Vector) (k : Fin 12) :
    m24PermuteMask (pairedTranslationPerm j v) (m24GolayRow k) =
      m24GolayCode (translationMessages j (vectorIndex v) k) := by
  revert v k
  fin_cases j <;> decide +kernel

/-- The translations are elements of the actual native M24 trio stabilizer. -/
def pairedTranslation (j : Fin 3) (v : Vector) : trioStabilizer standardTrio :=
  ⟨⟨pairedTranslationPerm j v,
    AffineLiftConstruction.mem_M24_of_rows _
      (fun k => ⟨translationMessages j (vectorIndex v) k, pairedTranslationPerm_rows j v k⟩)⟩, by
    apply (mem_trioStabilizer_iff _ _).mpr
    intro B hB
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hB
    change pairedTranslationPerm j v • standardTrioOctad i ∈ standardTrio.parts
    have he : pairedTranslationPerm j v • standardTrioOctad i = standardTrioOctad i := by
      revert j v i
      decide +kernel
    rw [he]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩

lemma pairedTranslation_point (j i : Fin 3) (v w : Vector) :
    (pairedTranslation j v).val.val (point (i,w)) =
      point (i, w + if i = j then 0 else v) :=
  pairedTranslationPerm_point j i v w

lemma pairedTranslation_mem_twoCore (j : Fin 3) (v : Vector) :
    pairedTranslation j v ∈ pCore 2 (trioStabilizer standardTrio) :=
  (mem_standardTwoCore_iff _).mpr
    ⟨fun i => if i = j then 0 else v, fun i w => pairedTranslation_point j i v w⟩

end
end MathieuCode.TrioCalculation

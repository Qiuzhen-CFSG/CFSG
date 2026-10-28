module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.CaseFourExclusion.CentralizerSylow.Local
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# The faithful Case IV normalizer action

Transport conjugation on the actual embedded F through its ordered basis
z₀,z₂,a,d. Its kernel is exactly F, giving an isomorphism of N_G(F)/F with
the image in Aut(binary four-space). The coordinate Sylow subgroup has
image exactly `localAutomizer`: the three source conjugators give its
specified generators, and eight words cover the model modulo F.

Fixing the first vector means centralizing the original involution D.z.
The local normalizer calculation therefore identifies its stabilizer with
`localAutomizer`, which is the precise premise consumed by finite rigidity.

Source: Janko, J. Algebra 9 (1968), Section 1, printed p.3.
-/

namespace Theory.GroupTheory.HeldM22A10.LocalModelDichotomy.CaseFour
open Subgroup
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (K : Subgroup D.centralizer) (hK : D.kernel.IsComplement' K)
  (R : JankoCoordinates (D.binaryAction K hK) .four)

public noncomputable def FgBasis : BinaryFour ≃* Fg D K hK R :=
  fBasis.trans (F.equivMapOfInjective (into D K hK R) (into_injective D K hK R))

public theorem FgBasis_coe (v : BinaryFour) :
    (FgBasis D K hK R v : G) = into D K hK R (fWord v) := by
  change into D K hK R (fBasis v : Model) = _
  rw [fBasis_apply]

public theorem FgBasis_point : (FgBasis D K hK R automizerPoint : G) = D.z := by
  change into D K hK R (fBasis automizerPoint : Model) = _
  rw [fBasis_point, into_z_zero]

public noncomputable def normalizerAction : normalizer (Fg D K hK R : Set G) →* MulAut BinaryFour :=
  (MulAut.congr (FgBasis D K hK R).symm).toMonoidHom.comp
    (Fg D K hK R).normalizerMonoidHom

public theorem normalizerAction_apply (n : normalizer (Fg D K hK R : Set G)) (v : BinaryFour) :
    (FgBasis D K hK R (normalizerAction D K hK R n v) : G) =
      (n : G) * (FgBasis D K hK R v : G) * (n : G)⁻¹ := by
  change ((FgBasis D K hK R) ((FgBasis D K hK R).symm
    ((Fg D K hK R).normalizerMonoidHom n (FgBasis D K hK R v))) : G) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

public theorem normalizerAction_ker : (normalizerAction D K hK R).ker =
    (Fg D K hK R).subgroupOf (normalizer (Fg D K hK R : Set G)) := by
  have he : (normalizerAction D K hK R).ker = (Fg D K hK R).normalizerMonoidHom.ker := by
    ext n
    change MulAut.congr (FgBasis D K hK R).symm
      ((Fg D K hK R).normalizerMonoidHom n) = 1 ↔
        (Fg D K hK R).normalizerMonoidHom n = 1
    rw [← (MulAut.congr (FgBasis D K hK R).symm).map_one,
      (MulAut.congr (FgBasis D K hK R).symm).injective.eq_iff]
  rw [he, normalizerMonoidHom_ker, centralizer_Fg]

public noncomputable def normalizerQuotientEquivAction :
    (normalizer (Fg D K hK R : Set G) ⧸
      (Fg D K hK R).subgroupOf (normalizer (Fg D K hK R : Set G))) ≃*
        (normalizerAction D K hK R).range :=
  (QuotientGroup.quotientMulEquivOfEq (normalizerAction_ker D K hK R)).symm.trans
    (QuotientGroup.quotientKerEquivRange _)

private noncomputable def modelNormalizerMap : Model →* normalizer (Fg D K hK R : Set G) :=
  (into D K hK R).codRestrict _ (fun x => T_le_normalizer_Fg D K hK R ⟨x, rfl⟩)

private noncomputable def modelAutomizer : Model →* MulAut BinaryFour :=
  (normalizerAction D K hK R).comp (modelNormalizerMap D K hK R)

private theorem modelAutomizer_apply (x : Model) (v : BinaryFour) :
    fWord (modelAutomizer D K hK R x v) = x * fWord v * x⁻¹ := by
  apply into_injective D K hK R
  have h := normalizerAction_apply D K hK R (modelNormalizerMap D K hK R x) v
  simpa only [FgBasis_coe, map_mul, map_inv, modelAutomizer, MonoidHom.comp_apply,
    modelNormalizerMap, MonoidHom.codRestrict_apply] using h

private theorem modelAutomizer_F (x : Model) (hx : x ∈ F) :
    modelAutomizer D K hK R x = 1 := by
  change modelNormalizerMap D K hK R x ∈ (normalizerAction D K hK R).ker
  rw [normalizerAction_ker]
  exact ⟨x, hx, rfl⟩

private theorem modelAutomizer_generator (i : Fin 3) :
    modelAutomizer D K hK R (fConjugator i) = automizerGenerator i := by
  apply MulEquiv.ext
  intro v
  apply fBasis.injective
  apply Subtype.ext
  rw [fBasis_apply, fBasis_apply, modelAutomizer_apply]
  have hi : ∀ i, (fConjugator i)⁻¹ = fConjugator i := by decide +kernel
  rw [← hi i]
  simpa only [inv_inv] using f_conjugation i v

private def word (i j k : Fin 2) : Model :=
  fConjugator 0 ^ i.val * fConjugator 1 ^ j.val * fConjugator 2 ^ k.val

private theorem word_covers : ∀ x : Model, ∃ i j k : Fin 2, x * (word i j k)⁻¹ ∈ F := by
  decide +kernel

private theorem modelAutomizer_range : (modelAutomizer D K hK R).range = localAutomizer := by
  apply le_antisymm
  · rintro f ⟨x, rfl⟩
    obtain ⟨i, j, k, hx⟩ := word_covers x
    have he := modelAutomizer_F D K hK R _ hx
    rw [map_mul, map_inv, mul_inv_eq_one] at he
    rw [he]
    have hg (i : Fin 3) : automizerGenerator i ∈ localAutomizer := subset_closure ⟨i, rfl⟩
    simpa only [word, map_mul, map_pow, modelAutomizer_generator] using
      mul_mem (mul_mem (pow_mem (hg 0) i.val) (pow_mem (hg 1) j.val)) (pow_mem (hg 2) k.val)
  · apply (closure_le _).mpr
    rintro f ⟨i, rfl⟩
    exact ⟨fConjugator i, modelAutomizer_generator D K hK R i⟩

public theorem localAutomizer_le_normalizerAction_range :
    localAutomizer ≤ (normalizerAction D K hK R).range := by
  rw [← modelAutomizer_range D K hK R]
  rintro f ⟨x, rfl⟩
  exact ⟨modelNormalizerMap D K hK R x, rfl⟩

public theorem normalizerAction_mem_local_iff (n : normalizer (Fg D K hK R : Set G)) :
    normalizerAction D K hK R n ∈ localAutomizer ↔ (n : G) ∈ T D K hK R := by
  constructor
  · intro hn
    rw [← modelAutomizer_range D K hK R] at hn
    obtain ⟨x, hx⟩ := hn
    have he : n * (modelNormalizerMap D K hK R x)⁻¹ ∈ (normalizerAction D K hK R).ker := by
      change normalizerAction D K hK R (n * (modelNormalizerMap D K hK R x)⁻¹) = 1
      rw [map_mul, map_inv]
      exact mul_inv_eq_one.mpr hx.symm
    rw [normalizerAction_ker] at he
    have hm : (n : G) * (into D K hK R x)⁻¹ ∈ T D K hK R :=
      Fg_le_T D K hK R he
    simpa only [inv_mul_cancel_right] using (T D K hK R).mul_mem hm
      (show into D K hK R x ∈ T D K hK R from ⟨x, rfl⟩)
  · rintro ⟨x, hx⟩
    have he : modelNormalizerMap D K hK R x = n := Subtype.ext hx
    rw [← he]
    exact (modelAutomizer_range D K hK R) ▸ (show modelAutomizer D K hK R x ∈
      (modelAutomizer D K hK R).range from ⟨x, rfl⟩)

public theorem normalizerAction_stabilizer (f : MulAut BinaryFour)
    (hf : f ∈ (normalizerAction D K hK R).range)
    (hfix : f automizerPoint = automizerPoint) : f ∈ localAutomizer := by
  obtain ⟨n, rfl⟩ := hf
  apply (normalizerAction_mem_local_iff D K hK R n).mpr
  apply normalizer_Fg_inter_centralizer_le D K hK R
  refine ⟨n.property, mem_centralizer_singleton_iff.mpr ?_⟩
  have hh := normalizerAction_apply D K hK R n automizerPoint
  rw [hfix, FgBasis_point] at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh.symm)

end Theory.GroupTheory.HeldM22A10.LocalModelDichotomy.CaseFour

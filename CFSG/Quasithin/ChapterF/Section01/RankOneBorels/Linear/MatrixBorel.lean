module

public import BenderSuzuki.Converse.PSL2
public import Theory.SpecificGroups.SL2.UpperUnipotent
public import Mathlib.GroupTheory.Solvable

/-!
# Elementary matrix geometry for the linear branch of F.1.3(1)

Over any field, the normalizer of the upper unipotents in SL₂ is the upper
triangular Borel, and every proper subgroup containing those unipotents lies
in that Borel. For the latter assertion, multiply a matrix outside the Borel
by an upper unipotent to make its upper-left entry zero. Conjugating upper
unipotents by this matrix gives every lower unipotent; the upper and lower
transvections generate SL₂. This proves uniqueness of the proper Sylow
overgroup, including over the field of order two.

The diagonal homomorphism exhibits the Borel as an extension of two abelian
groups. These matrix lemmas supply the linear case of Aschbacher–Smith,
`refs/quasithin.pdf`, printed pp.259–260, Remark F.1.2 and Lemma F.1.3(1).
-/

@[expose] public section

open BenderSuzuki.Converse Matrix

namespace CFSG.Quasithin.ChapterF.Source.Linear

variable {F : Type*} [Field F]

theorem unip_eq_upper : Unip F = SpecialLinearGroup.upperUnipotent F := by
  change (uniHom F).range = (SpecialLinearGroup.upperUnipotentHom F).range
  congr 1
  apply MonoidHom.ext
  intro b
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uniHom, SpecialLinearGroup.upperUnipotentHom,
      SpecialLinearGroup.transvection_coe]

theorem unip_normalizer : Subgroup.normalizer (Unip F : Set (SL2 F)) = Borel F := by
  apply le_antisymm
  · intro g hg
    have hu : g * uni (1 : F) * g⁻¹ ∈ Unip F :=
      (Subgroup.mem_normalizer_iff.mp hg _).mp
        ((mem_Unip_iff _).mpr ⟨1, rfl⟩)
    obtain ⟨b, hb⟩ := (mem_Unip_iff _).mp hu
    have he := congrArg (fun A : SL2 F => A.val 1 0) hb
    simp [adjugate_fin_two, mul_apply, Fin.sum_univ_two] at he
    apply (mem_Borel_iff _).mpr
    have hz : g.val 1 0 * g.val 1 0 = 0 := by linear_combination -he
    exact (mul_self_eq_zero.mp hz)
  · intro g hg
    apply Subgroup.mem_normalizer_iff.mpr
    intro u
    constructor
    · exact Unip_conj_mem hg
    · intro hu
      have := Unip_conj_mem ((Borel F).inv_mem hg) hu
      simpa [mul_assoc] using this

theorem lower_of_zero_entry (g : SL2 F) (h00 : g.val 0 0 = 0) (t : F) :
    g * uni t * g⁻¹ =
      SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) one_ne_zero
        (-(g.val 1 0 ^ 2 * t)) := by
  have hd := g.property
  simp only [det_fin_two, h00, zero_mul, zero_sub] at hd
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adjugate_fin_two, mul_apply, Fin.sum_univ_two,
      SpecialLinearGroup.transvection_coe, h00] <;>
    first | exact hd | simpa only [mul_comm] using hd | ring

theorem eq_top_of_unip_le_of_not_le_borel (M : Subgroup (SL2 F))
    (hU : Unip F ≤ M) (hB : ¬ M ≤ Borel F) : M = ⊤ := by
  obtain ⟨g, hg, hgb⟩ := SetLike.not_le_iff_exists.mp hB
  have hc : g.val 1 0 ≠ 0 := by simpa [mem_Borel_iff] using hgb
  let a : SL2 F := uni (-(g.val 0 0 / g.val 1 0)) * g
  have ha : a ∈ M := M.mul_mem (hU ((mem_Unip_iff _).mpr ⟨_, rfl⟩)) hg
  have ha00 : a.val 0 0 = 0 := by
    simp [a, mul_apply, Fin.sum_univ_two, hc]
  have ha10 : a.val 1 0 = g.val 1 0 := by
    simp [a, mul_apply, Fin.sum_univ_two]
  have hlower (c : F) :
      SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) one_ne_zero c ∈ M := by
    have hmem := M.mul_mem (M.mul_mem ha
      (hU ((mem_Unip_iff _).mpr ⟨-(c / g.val 1 0 ^ 2), rfl⟩))) (M.inv_mem ha)
    rw [lower_of_zero_entry a ha00, ha10] at hmem
    simpa [mul_div_cancel₀ _ (pow_ne_zero 2 hc)] using hmem
  apply top_unique
  intro x _
  refine Matrix.SL2.transvection_induction (fun x => x ∈ M) ?_ ?_ x
  · intro i j hij c
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · apply hU
      apply (mem_Unip_iff _).mpr
      refine ⟨c, ?_⟩
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [SpecialLinearGroup.transvection_coe]
    · exact hlower c
    · exact (hij rfl).elim
  · exact fun _ _ => M.mul_mem

theorem proper_overgroup_le_borel (M : Subgroup (SL2 F))
    (hU : Unip F ≤ M) (hM : M < ⊤) : M ≤ Borel F := by
  by_contra h
  exact hM.ne (eq_top_of_unip_le_of_not_le_borel M hU h)

def diagonalHom : Borel F →* Fˣ where
  toFun g := Units.mk0 (g.val.val 0 0) (Borel_diag_ne_zero g.property)
  map_one' := by ext; rfl
  map_mul' g h := by
    ext
    simp [mul_apply, Fin.sum_univ_two,
      (mem_Borel_iff _).mp h.property]

theorem borel_solvable : Group.IsSolvable (Borel F) := by
  let f : Multiplicative F →* Borel F :=
    (uniHom F).codRestrict (Borel F) (fun b => Unip_le_Borel ⟨b, rfl⟩)
  apply Group.isSolvable_of_ker_le_range f diagonalHom
  intro g hg
  have h00 : g.val.val 0 0 = 1 := congrArg Units.val hg
  have h10 := (mem_Borel_iff _).mp g.property
  have h11 : g.val.val 1 1 = 1 := by
    simpa [h00] using Borel_lower_right g.property
  refine ⟨Multiplicative.ofAdd (g.val.val 0 1), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [f, uniHom, h00, h10, h11]

end CFSG.Quasithin.ChapterF.Source.Linear

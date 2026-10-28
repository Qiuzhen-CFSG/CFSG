module

public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ReadyCoverCases
public import CFSG.Quasithin.ChapterI.Section01.LieMultipliers.PSL2
public import Theory.SpecificGroups.Suzuki.SchurCoverReduction
public import Theory.SpecificGroups.SU3.TernaryPerfectCover
public import Theory.GroupTheory.PerfectCentralCoverCentralQuotient
public import Theory.GroupTheory.CoveringPGroupDescent
public import GorensteinWalter.PSL2ProjectiveLine

/-!
# Remaining ready ordinary-component cover cases in A.3.6

The actual universal PSL₂ covers have two-primary kernels, including
the exceptional four-element field. Suzuki perfect covers likewise have
two-group kernels, including Sz(8). For PSU₃(3) and the literal G₂(2)′
carrier, the local ternary-kernel exclusion together with cyclic-Sylow
transfer gives the same assertion. The component's own trivial two-core
therefore makes its specified central-quotient projection injective.

Each theorem constructs the actual model isomorphism from that projection
and concludes all of `A36Conclusion`, including the common Fitting and
radical clauses. Odd PSL₂(9) remains with the A₆ cover case. No exact
Suzuki multiplier, general unitary universality, or full multiplier table
is used. These case theorems do not assert the separate orbit restrictions
of A.3.8 or remove its merely-quasithin SU₃(8) exception.

Source: Aschbacher–Smith A.3.6–A.3.8, printed pp.43–46, and the
covering convention and multiplier deductions I.1.1–I.1.3, printed p.407.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory PerfectCentralCovering GorensteinWalter
open BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.SQTKStructure.RankOneCoverCases
open Chapter1.Section02 Chapter1.Section02.LocalModels
universe u

private theorem injective_of_two_kernel {E S : Type*}
    [Group E] [Finite E] [Group S] (f : PerfectCentralCovering.Cover E S)
    (hker : IsPGroup 2 f.toMonoidHom.ker) (hcore : pCore 2 E = ⊥) :
    Function.Injective f.toMonoidHom := by
  apply f.toMonoidHom.ker_eq_bot_iff.mp
  apply bot_unique
  rw [← hcore]
  exact le_sSup ⟨inferInstance, hker⟩

private theorem simple_conclusion {X S : Type*} [Group X] [Finite X]
    [Group S] [Finite S] [IsSimpleGroup S]
    (L : Subgroup X) (hL : IsComponent X L)
    (j : L ≃* S) (hmodel : TheoremCModel L) (heven : 2 ∣ Nat.card S) :
    A36Conclusion L := by
  let : Theory.GroupTheory.IsQuasisimple L := hL.2
  let : IsSimpleGroup L := j.isSimpleGroup
  have hz : center L = ⊥ := by
    rcases (inferInstance : (center L).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (Group.IsPerfect.not_isMulCommutative L (center_eq_top_iff.mp ht)).elim
  exact ⟨.simple hL inferInstance hmodel,
    ReadyCoverCases.common_of_quasisimple
      ((Nat.card_congr j.toEquiv).symm ▸ heven)
      (Or.inl (by rw [hz]; simp))⟩

private theorem even_psl2 {F : Type*} [Field F] [Finite F]
    (hF : Even (Nat.card F)) : 2 ∣ Nat.card PSL(2,F) := by
  have h : 2 ∣ Nat.card (psl2UpperUnipotentSubgroup F) := by
    rw [psl2UpperUnipotentSubgroup_card]
    exact even_iff_two_dvd.mp hF
  exact h.trans (psl2UpperUnipotentSubgroup F).card_subgroup_dvd_card

private theorem odd_psl2_even_order {F : Type*} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) : 2 ∣ Nat.card PSL(2,F) := by
  let S : Sylow 2 PSL(2,F) := default
  obtain ⟨m, _, ⟨eS⟩⟩ := psl2_odd_hasDihedralSylowTwo_model F hF S
  have h : 2 ∣ Nat.card S := by
    rw [Nat.card_congr eS.toEquiv, DihedralGroup.nat_card]
    exact dvd_mul_right _ _
  exact h.trans S.card_subgroup_dvd_card

private theorem suzuki_even_order (m : ℕ) (hm : 0 < m) :
    2 ∣ Nat.card (SuzukiMatrixGroup m) := by
  by_contra h
  have ho : Odd (Nat.card (SuzukiMatrixGroup m)) :=
    Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using h)
  let : Group.IsSolvable (⊤ : Subgroup (SuzukiMatrixGroup m)) :=
    suzukiSubgroup_isSolvable_of_odd hm ⊤ (by simpa only [card_top] using ho)
  exact BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable m hm
    (Group.isSolvable_of_surjective
      (f := (topEquiv : (⊤ : Subgroup (SuzukiMatrixGroup m)) ≃* _).toMonoidHom)
      topEquiv.surjective)

/-- A.3.6 for an ordinary component with actual PSL₂(2ⁿ) central quotient,
including n = 2 and its nontrivial universal two-kernel. -/
theorem a36_psl2_even {X : Type u} [Group X] [Finite X]
    (L : Subgroup X) (hL : IsComponent X L) (hcore : pCore 2 L = ⊥)
    (n : ℕ) (hn : 2 ≤ n) (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) (e : L ⧸ center L ≃* PSL(2,F)) :
    A36Conclusion L := by
  let : Theory.GroupTheory.IsQuasisimple L := hL.2
  let : IsSimpleGroup (L ⧸ center L) := Theory.GroupTheory.IsQuasisimple.simple
  let : IsSimpleGroup PSL(2,F) := e.symm.isSimpleGroup
  have hsize : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.le_of_dvd (by positivity) (pow_dvd_pow 2 hn)
  let : Fact (3 < Nat.card F) := ⟨by omega⟩
  have heven : Even (Nat.card F) := by
    rw [hF]
    exact Nat.even_pow.mpr ⟨by decide, by omega⟩
  let g : Covering L PSL(2,F) := (centralQuotientCover e).toCovering
  have hi : Function.Injective g.toMonoidHom := by
    by_cases hn2 : n = 2
    · let : Fact (Nat.Prime 5) := ⟨by decide⟩
      let : Fact (3 < Nat.card (ZMod 5)) := ⟨by norm_num⟩
      have hfour : Nat.card F = 4 := by simpa [hn2] using hF
      obtain ⟨hc, ⟨ek⟩⟩ := ChapterI.LieMultipliers.PSL2.four_universalCover.{0,u} F hfour
      have hk : IsPGroup 2 (PSL2Cover.fourCover F hfour).toMonoidHom.ker := by
        apply IsPGroup.of_card (n := 1)
        exact (Nat.card_congr ek.toEquiv).trans (by simp)
      exact hc.injective_of_pGroup_kernel hk g hcore
    · have height : 8 ≤ Nat.card F := by
        rw [hF]
        exact Nat.le_of_dvd (by positivity) (pow_dvd_pow 2 (by omega : 3 ≤ n))
      obtain ⟨hc, ⟨ek⟩⟩ := ChapterI.LieMultipliers.PSL2.even_universalCover.{0,u,0} F height heven
      have hk : IsPGroup 2 (Covering.id : Covering PSL(2,F) PSL(2,F)).toMonoidHom.ker := by
        apply IsPGroup.of_card (n := 0)
        exact (Nat.card_congr ek.toEquiv).trans (by simp)
      exact hc.injective_of_pGroup_kernel hk g hcore
  let j := MulEquiv.ofBijective g.toMonoidHom ⟨hi, g.surjective⟩
  exact simple_conclusion L hL j
    (.rank_one (.linear n hn ⟨F, inferInstance, inferInstance, hF, ⟨j⟩⟩))
    (even_psl2 heven)

/-- A.3.6 for the source odd PSL₂ prime/prime-square cases other than
order nine. The A₆ alias and its triple cover remain separate. -/
theorem a36_psl2_odd {X : Type u} [Group X] [Finite X]
    (L : Subgroup X) (hL : IsComponent X L) (hcore : pCore 2 L = ⊥)
    (p r : ℕ) (hp : p.Prime) (ho : Odd p) (hr : r = 1 ∨ r = 2)
    (hsize : 4 ≤ p ^ r) (h9 : p ^ r ≠ 9)
    (F : Type) [Field F] [Finite F] (hF : Nat.card F = p ^ r)
    (e : L ⧸ center L ≃* PSL(2,F)) : A36Conclusion L := by
  let : Theory.GroupTheory.IsQuasisimple L := hL.2
  let : IsSimpleGroup (L ⧸ center L) := Theory.GroupTheory.IsQuasisimple.simple
  let : IsSimpleGroup PSL(2,F) := e.symm.isSimpleGroup
  let : Fact (3 < Nat.card F) := ⟨by omega⟩
  have hodd : Odd (Nat.card F) := hF.symm ▸ ho.pow
  let g : Covering L PSL(2,F) := (centralQuotientCover e).toCovering
  obtain ⟨hc, ⟨ek⟩⟩ := ChapterI.LieMultipliers.PSL2.odd_universalCover.{0,u}
    F (by omega) hodd (by omega)
  have hk : IsPGroup 2 (PSL2Cover.cover F).toMonoidHom.ker := by
    apply IsPGroup.of_card (n := 1)
    exact (Nat.card_congr ek.toEquiv).trans (by simp)
  have hi := hc.injective_of_pGroup_kernel hk g hcore
  let j := MulEquiv.ofBijective g.toMonoidHom ⟨hi, g.surjective⟩
  exact simple_conclusion L hL j
    (.linear_odd p r hp ho hr hsize ⟨F, inferInstance, inferInstance, hF, ⟨j⟩⟩)
    (odd_psl2_even_order ⟨p, r, hp, ho, by omega, hF⟩)

/-- A.3.6 for every nondegenerate Suzuki quotient, including Sz(8).
Only the proved two-primary nature of every perfect central kernel is used. -/
theorem a36_suzuki {X : Type u} [Group X] [Finite X]
    (L : Subgroup X) (hL : IsComponent X L) (hcore : pCore 2 L = ⊥)
    (m : ℕ) (hm : 1 ≤ m)
    (e : L ⧸ center L ≃* SuzukiMatrixGroup m) : A36Conclusion L := by
  let : Theory.GroupTheory.IsQuasisimple L := hL.2
  let : IsSimpleGroup (L ⧸ center L) := Theory.GroupTheory.IsQuasisimple.simple
  let : IsSimpleGroup (SuzukiMatrixGroup m) := e.symm.isSimpleGroup
  let f := centralQuotientCover e
  have hi := injective_of_two_kernel f (SchurCover.kernel_isTwoGroup (by omega) f) hcore
  let j := MulEquiv.ofBijective f.toMonoidHom ⟨hi, f.surjective⟩
  exact simple_conclusion L hL j (.rank_one (.suzuki m hm ⟨j⟩))
    (suzuki_even_order m (by omega))

/-- A.3.6 for the actual ternary projective unitary model, retaining every
field-nine Hermitian form with cube conjugation. -/
theorem a36_psu3_three {X : Type u} [Group X] [Finite X]
    (L : Subgroup X) (hL : IsComponent X L) (hcore : pCore 2 L = ⊥)
    (F : Type) [Field F] [Finite F] (J : HermitianForm 3 F)
    (hcard : Nat.card F = 3 ^ 2) (hconj : ∀ x, J.conj x = x ^ 3)
    (e : L ⧸ center L ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    A36Conclusion L := by
  let : Theory.GroupTheory.IsQuasisimple L := hL.2
  let : IsSimpleGroup (L ⧸ center L) := Theory.GroupTheory.IsQuasisimple.simple
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) := e.symm.isSimpleGroup
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_surjective e e.surjective
  let f := centralQuotientCover e
  have hi := injective_of_two_kernel f
    (HermitianForm.TernaryPerfectCover.kernel_isTwoGroup J hcard hconj f) hcore
  let j := MulEquiv.ofBijective f.toMonoidHom ⟨hi, f.surjective⟩
  exact simple_conclusion L hL j
    (.three_odd 3 (by decide) (by decide) true
      ⟨F, inferInstance, inferInstance, J, hcard, hconj, ⟨j⟩⟩)
    (by rw [HermitianForm.TernaryPerfectCover.card_projective J hcard hconj]; norm_num)

/-- A.3.6 for the literal commutator subgroup of the binary octonion
automorphism group. Its given source projection becomes an isomorphism. -/
theorem a36_binary_g2_derived {X : Type u} [Group X] [Finite X]
    (L : Subgroup X) (hL : IsComponent X L) (hcore : pCore 2 L = ⊥)
    (e : L ⧸ center L ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    A36Conclusion L := by
  let : Theory.GroupTheory.IsQuasisimple L := hL.2
  let : IsSimpleGroup (L ⧸ center L) := Theory.GroupTheory.IsQuasisimple.simple
  let : IsSimpleGroup (commutator (Atlas.G2.Model (ZMod 2))) := e.symm.isSimpleGroup
  let f := centralQuotientCover e
  have hi := injective_of_two_kernel f
    (HermitianForm.TernaryPerfectCover.binaryDerived_kernel_isTwoGroup f) hcore
  let j := MulEquiv.ofBijective f.toMonoidHom ⟨hi, f.surjective⟩
  exact simple_conclusion L hL j (.rank_two (.g2_derived ⟨j⟩))
    (by rw [Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)]; norm_num)

end CFSG.Quasithin.ChapterA.SQTKStructure.RankOneCoverCases

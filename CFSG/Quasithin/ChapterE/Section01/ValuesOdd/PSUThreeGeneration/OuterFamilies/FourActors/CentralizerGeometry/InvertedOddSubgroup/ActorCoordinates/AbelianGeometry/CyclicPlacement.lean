module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianGeometry.CyclicSetup
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianGeometry.CyclicPlacement.Setup
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianGeometry.CyclicPlacement.FixedCyclicRoot
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianGeometry.CyclicPlacement.FixedInvolution
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianGeometry.InnerPreimage
import all CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianGeometry.InnerPreimage
public import Theory.SpecificGroups.SU3.CyclicNormalOuter.PrimeTwoActors
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# Cyclic inner placement from fixed-field matrix geometry

The diagonal outer contribution has exponent three. Thus every actor in
the given two-group is inner, possibly followed by entrywise conjugation.
Commutativity and centerlessness make the literal inner preimage pointwise
fixed. Choose a generator of that cyclic preimage.

If its order exceeds two, fixed cyclic root coordinates describe the whole
actor. Otherwise the marked involution generates the preimage, and a
second commuting fixed involution generates an actual pointwise fixed
four-group. This includes the order-two preimage without requiring the
four-group to lie inside it.

The internal import reuses the noncyclic proof's private inner-preimage
fixation lemma, preserving that module's public boundary.

The conditional reduction is retained. The final theorem discharges both
matrix existence inputs when p is one modulo four: fixed torus placement
supplies the larger cyclic case, and the orthogonal reflection construction
supplies the order-two case. The independent standard-four fixer input of
the full abelian-coordinate theorem is not needed for this placement result.
Source: Aschbacher--Smith E.1.14(7), printed p.214, and A.3.21(a)--(b),
printed p.55; Aschbacher (1982), Lemma 4.11.
-/

public section
open Matrix Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianGeometry.CyclicPlacement
variable {F : Type} [Field F]

private theorem fixed_four_of_extension {K : Type*} [Group K]
    (U : Subgroup (MulAut K)) (γ : MulAut K) (w v : K)
    (hU : U = (zpowers w).map MulAut.conj ⊔ zpowers γ)
    (hw : orderOf w = 2) (hv : orderOf v = 2) (hne : v ≠ w)
    (hγw : γ w = w) (hγv : γ v = v) (hcomm : Commute w v) :
    ∃ B : Subgroup K, IsElementaryAbelian 2 B ∧ Nat.card B = 4 ∧ w ∈ B ∧
      ∀ a ∈ U, ∀ x ∈ B, a x = x := by
  let B : Subgroup K := closure ({w, v} : Set K)
  let : IsKleinFour B := isKleinFour_closure_pair_of_orderOf w v hw hv hne.symm hcomm
  have hBe : IsElementaryAbelian 2 B :=
    { toIsMulCommutative := IsKleinFour.isMulCommutative
      exponent_dvd_p := by simp only [IsKleinFour.exponent_two, dvd_refl] }
  have hBγ : B ≤ γ.fixedSubgroup := by
    apply (closure_le _).mpr
    intro x hx
    rcases hx with rfl | rfl
    · exact (MulAut.mem_fixedSubgroup _ _).mpr hγw
    · exact (MulAut.mem_fixedSubgroup _ _).mpr hγv
  have hBw : B ≤ (MulAut.conj w).fixedSubgroup := by
    apply (closure_le _).mpr
    intro x hx
    rcases hx with hx | hx
    · have he : x = w := hx
      subst x
      apply (MulAut.mem_fixedSubgroup _ _).mpr
      change w * w * w⁻¹ = w
      exact mul_inv_cancel_right w w
    · have he : x = v := hx
      subst x
      apply (MulAut.mem_fixedSubgroup _ _).mpr
      change w * v * w⁻¹ = v
      rw [hcomm.eq, mul_inv_cancel_right]
  have hfix : U ≤ fixingSubgroup (MulAut K) (B : Set K) := by
    rw [hU, MonoidHom.map_zpowers]
    apply sup_le
    · apply zpowers_le.mpr
      exact (mem_fixingSubgroup_iff _).mpr
        (fun x hx => (MulAut.mem_fixedSubgroup _ _).mp (hBw hx))
    · apply zpowers_le.mpr
      exact (mem_fixingSubgroup_iff _).mpr
        (fun x hx => (MulAut.mem_fixedSubgroup _ _).mp (hBγ hx))
  exact ⟨B, hBe, IsKleinFour.card_four, subset_closure (by simp),
    fun a ha x hx => (mem_fixingSubgroup_iff _).mp (hfix ha) x hx⟩

/-- All abelian actor and inner-preimage hypotheses reduce to the two fixed
matrix problems, including the order-two inner preimage. -/
theorem cyclicInnerPlacement_of_fixed_geometry [Finite F]
    (J : HermitianForm 3 F) [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hext : FixedInvolutionExtension J) (hroot : FixedCyclicRootCoordinates J) :
    CyclicInnerPlacement J := by
  intro U hU hcomm hC γ hγ hγU w hw hwU
  let : IsMulCommutative U := hcomm
  let : Finite (ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    obtain ⟨k, hk⟩ := ho
    omega
  have h2 : (2 : F) ≠ 0 :=
    HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage.two_ne_zero_of_prime_square
      hp hp3 hcard
  have hZ := projective_center_eq_bot J hJ h2
  have hC2 : IsPGroup 2 (U.comap MulAut.conj) :=
    hU.comap_of_injective MulAut.conj (MulAut.conj_injective_of_center_eq_bot hZ)
  obtain ⟨x, hx⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top _).mp hC
  have hxC : x ∈ U.comap MulAut.conj := hx ▸ mem_zpowers x
  have hxfix : γ x = x := fixes_innerPreimage hZ U γ hγU x hxC
  have hUeq := HermitianForm.PrimeTwoActors.actor_eq_inner_sup_entrywise
    J hJ hp ho hcard hc U hU γ hγ hγU
  by_cases hlarge : 2 < orderOf x
  · left
    have hx2 : IsPGroup 2 (zpowers x) := hx.symm ▸ hC2
    have hwx : w ∈ zpowers x := hx.symm ▸ hwU
    have hr := hroot γ hγ x hxfix hx2 hlarge w hw hwx
    rw [hx, ← hUeq] at hr
    exact hr
  · right
    have hcardC : Nat.card (U.comap MulAut.conj) ≤ 2 := by
      rw [← hx, Nat.card_zpowers]
      omega
    have hCw : U.comap MulAut.conj = zpowers w := by
      apply (eq_of_le_of_card_ge (zpowers_le.mpr (show w ∈ U.comap MulAut.conj from hwU)) ?_).symm
      rw [Nat.card_zpowers, hw]
      exact hcardC
    have hwfix := fixes_innerPreimage hZ U γ hγU w hwU
    obtain ⟨v, hv, hne, hvfix, hcommv⟩ := hext γ hγ w hw hwfix
    rw [hCw] at hUeq
    exact fixed_four_of_extension U γ w v hUeq hw hv hne hwfix hvfix hcommv

/-- An abelian automorphism two-group with cyclic inner preimage has literal
root coordinates or a pointwise fixed marked four-group when p is one modulo
four. Both fixed-field geometry inputs are discharged, including the case
where the inner preimage has order two. -/
theorem cyclicInnerPlacement [Finite F]
    (J : HermitianForm 3 F) [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hmod : p % 4 = 1)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) :
    CyclicInnerPlacement J := by
  exact cyclicInnerPlacement_of_fixed_geometry J hp ho hcard hc hJ
    (fixedInvolutionExtension J hp ho hcard hJ)
    (fixedCyclicRootCoordinates J hp ho hmod hcard hc hJ)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianGeometry.CyclicPlacement

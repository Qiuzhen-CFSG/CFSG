module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.ResidualCoordinates.SourceSeed
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Decomposition

/-!
# The canonical fixed factor of the original paired supports

The fixed factor is the literal preimage C = C_U(H mod Z). The original
Gaschütz decomposition writes every element as a component-commutator lift
times a member of C. If [U,H] lies in A join B, this gives the required
three-factor decomposition. A vector in A intersect (B join C) is fixed
by the full natural action modulo A intersect B, hence belongs to Z.
Thus separation from the fixed factor is proved, rather than assumed.

The same full natural/dual sections and the component-commutator containment
are the genuine 14.6.22--23 inputs, owned by qt-e-suitable-component-supports.
Single-component placement and final suitable marking remain with
qt-e-suitable-component-marking, with qt-e-suitable-existence assembling
suitable choice. The next residual consumer uses this exact C and seed.

Source: Aschbacher--Smith, 14.6.23(3) and printed p.1042.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open scoped commutatorElement IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Matrix.PSL3Two.NaturalDualMarking
variable {G : Type*} [Group G] [Finite G]

/-- Construct the original fixed-factor supplement and its separation from
the natural support using the full paired action and component commutator. -/
theorem source_fixed_factor_of_pair_commutator
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (A B : Subgroup G)
    (hAU : A ≤ conjugateSpanBy (localModule T M) Mc)
    (hBU : B ≤ conjugateSpanBy (localModule T M) Mc)
    (hsep : A ⊓ B ≤ centralInvolutions T)
    (q : (Mc ⊓ normalizer (A : Set G) : Subgroup G) →* BinaryLinear.GL Space)
    (hq : Function.Surjective q)
    (n : BinaryConjugationSection (Mc ⊓ normalizer (A : Set G)) A (centralInvolutions T)
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp q))
    (d : BinaryConjugationSection (Mc ⊓ normalizer (A : Set G)) B (centralInvolutions T)
      (Representation.dual (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp q)))
    (hmove : ⁅conjugateSpanBy (localModule T M) Mc,Mc⁆ ≤ A ⊔ B) :
    let U := conjugateSpanBy (localModule T M) Mc
    let Z := centralInvolutions T
    let C := commutatorPreimage U Mc Z
    C ≤ U ∧ Z ≤ C ∧ A ⊓ (B ⊔ C) ≤ Z ∧
      (∀ x ∈ Mc, ∀ c ∈ C, ⁅c,x⁆ ∈ Z) ∧
      (∀ v ∈ U, ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, v = a*b*c) := by
  dsimp only
  let U := conjugateSpanBy (localModule T M) Mc
  let Z := centralInvolutions T
  let C := commutatorPreimage U Mc Z
  let L := Mc ⊓ normalizer (A : Set G)
  let h := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  let : IsElementaryAbelian 2 U :=
    h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  have hUZ : U ≤ normalizer (Z : Set G) :=
    h.UH_le_H.trans (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
  have hCU : C ≤ U := commutatorPreimage_le U Mc Z
  have hZC : Z ≤ C := le_commutatorPreimage
    (h.point_lt.le.trans (le_conjugateSpanBy _ _)) (by
      apply commutator_le.mpr
      intro z hz x hx
      have hh : Commute z x := h.H_centralizes hx z hz
      rw [hh.commutator_eq]
      exact Z.one_mem)
  have hfixed : ∀ x ∈ Mc, ∀ c ∈ C, ⁅c,x⁆ ∈ Z := by
    intro x hx c hc
    exact commutator_commutatorPreimage_le U Mc Z hUZ (commutator_mem_commutator hc hx)
  have hn (S : Subgroup G) (hS : S ≤ U) : U ≤ normalizer (S : Set G) :=
    (le_centralizer_iff_isMulCommutative.mpr hab).trans
      ((centralizer_le hS).trans (Subgroup.centralizer_le_normalizer _))
  have hsepC : A ⊓ (B ⊔ C) ≤ Z := by
    have hBC : B ⊔ C ≤ commutatorPreimage U L B := by
      apply sup_le
      · exact le_commutatorPreimage hBU (le_normalizer_iff_commutator_le_left.mp d.normalized)
      · apply le_commutatorPreimage hCU
        apply commutator_le.mpr
        intro c hc x hx
        exact d.kernel_le (hfixed x hx.1 c hc)
    intro a ha
    apply (n.coordinates_eq_one_iff ⟨a,ha.1⟩).mp
    apply natural_common_fixed_eq_zero
    intro g
    obtain ⟨x,rfl⟩ := hq g
    apply (n.fixed_coordinate_iff_commutator_mem x ⟨a,ha.1⟩).mpr
    apply hsep
    refine ⟨(le_normalizer_iff_commutator_le_left.mp n.normalized)
      (commutator_mem_commutator ha.1 x.property),?_⟩
    exact commutator_commutatorPreimage_le U L B (hn B hBU)
      (commutator_mem_commutator (hBC ha.2) x.property)
  refine ⟨hCU,hZC,hsepC,hfixed,?_⟩
  obtain ⟨ρ,sec,hspan⟩ := ComponentSupports.source_canonical_commutator_decomposition
    hG T hempty hM hunique hmany hcard e hab
  intro v hv
  have hvspan : (sec.coordinates ⟨v,hv⟩).toAdd ∈ sec.imageSpace ⁅U,Mc⁆ ⊔ fixed ρ := by
    rw [hspan]
    trivial
  obtain ⟨x,hx,y,hy,hxy⟩ := Submodule.mem_sup.mp hvspan
  obtain ⟨z,hz,hzx⟩ := (sec.mem_imageSpace_iff _ _).mp hx
  obtain ⟨w,hw⟩ := sec.onto (Multiplicative.ofAdd y)
  have hwC : (w : G) ∈ C := by
    apply (Subgroup.mem_commutatorPreimage_iff U Mc Z hUZ w).mpr
    refine ⟨w.property,?_⟩
    intro k hk
    apply (sec.fixed_coordinate_iff_commutator_mem ⟨k,hk⟩ w).mp
    rw [hw]
    exact hy ⟨k,hk⟩
  have hzw : sec.coordinates (z*w) = sec.coordinates ⟨v,hv⟩ := by
    rw [map_mul]
    apply Multiplicative.toAdd.injective
    change (sec.coordinates z).toAdd + (sec.coordinates w).toAdd = _
    rw [hzx,hw]
    exact hxy
  have herror : v*((z : G)*(w : G))⁻¹ ∈ Z := by
    apply (sec.coordinates_eq_one_iff (⟨v,hv⟩*(z*w)⁻¹)).mp
    rw [map_mul,map_inv,hzw,mul_inv_cancel]
  have hvjoin : v ∈ (A ⊔ B) ⊔ C := by
    have hzjoin : (z : G)*(w : G) ∈ (A ⊔ B) ⊔ C := mul_mem_sup (hmove hz) hwC
    have herr : v*((z : G)*(w : G))⁻¹ ∈ (A ⊔ B) ⊔ C :=
      (show C ≤ (A ⊔ B) ⊔ C from le_sup_right) (hZC herror)
    simpa only [inv_mul_cancel_right] using ((A ⊔ B) ⊔ C).mul_mem herr hzjoin
  have hnormC : C ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) :=
    hCU.trans (hn (A ⊔ B) (sup_le hAU hBU))
  have hp : v ∈ ((A ⊔ B : Subgroup G) : Set G) * (C : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left (A ⊔ B) C hnormC]
    exact hvjoin
  obtain ⟨ab,hab,c,hc,rfl⟩ := hp
  have hp' : ab ∈ (A : Set G) * (B : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left A B (hBU.trans (hn A hAU))]
    exact hab
  obtain ⟨a,ha,b,hb,rfl⟩ := hp'
  exact ⟨a,ha,b,hb,c,hc,rfl⟩

end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair

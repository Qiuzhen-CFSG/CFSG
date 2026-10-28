module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.Sporadic.Reduction
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoFour
public import Theory.GroupTheory.GeneralizedFitting.PGroupCentralizer
public import Theory.Quasithin.EvenCharacteristic

/-!
# The J₄ whole-two-action inspection

Full innerness identifies an automorphism two-subgroup with an actual
subgroup Q of J₄. A central involution of the actor places Q and its common
fixed subgroup inside one involution centralizer T. Both genuine centralizer
classes have a self-centralizing normal two-subgroup: the intrinsic two-core
in the first class and the actual elementary kernel in the second.

The common fixed subgroup is explicitly identified with C_T(Q). The general
component-exclusion theorem applies Thompson's A × B lemma to the normal
kernel, so this entire common fixed subgroup has no components. In particular
it has no A₇ or triple-cover A₇ component. No transfer of component membership
from a subgroup to an overgroup is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.18,
printed p.252; Theorem C, printed p.33; 16.1.5(9), printed p.1172;
GLS3 Table 5.3i. Full innerness and the exact marked centralizer comparisons
are supplied by the completed Chapter 16 J₄ preliminary development.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
namespace SporadicInspection
open Chapter16.OtherPreliminaries.JankoFour
open Janko4 Janko4.InvolutionCentralizers
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares

attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private theorem first_core_selfCentralizing :
    centralizer (pCore 2 First.centralizer : Set First.centralizer) ≤
      pCore 2 First.centralizer := by
  apply (@Theory.Quasithin.centralizer_pCore_le_iff
    First.centralizer involutionCentralizer inferInstance inferInstance
    2 First.centralizerEquiv).mpr
  exact localTwoCoreCentralizerControl.1

private theorem involution_fixed_kernel [IsSimpleGroup Model] [Group.IsPerfect Model]
    (r : MulAut Model) (hr : orderOf r = 2) :
    ∃ K : Subgroup r.fixedSubgroup, K.Normal ∧ IsPGroup 2 K ∧
      centralizer (K : Set r.fixedSubgroup) ≤ K := by
  classical
  obtain ⟨g, hg, rfl, _⟩ := involution_representative r hr
  by_cases hc : SylowCentral g
  · obtain ⟨eC⟩ := central_fixed_equiv hg hc
    exact ⟨pCore 2 _, inferInstance, pCore_isPGroup,
      (Theory.Quasithin.centralizer_pCore_le_iff 2 eC).mpr first_core_selfCentralizing⟩
  · obtain ⟨eC⟩ := noncentral_fixed_equiv hg hc
    let K := Second.ambientKernel.comap eC.toMonoidHom
    refine ⟨K, inferInstance,
      Second.ambientKernel_elementary.isPGroup.comap_of_injective eC.toMonoidHom eC.injective, ?_⟩
    intro x hx
    have he : eC x ∈ centralizer (Second.ambientKernel : Set Second.ambientCentralizer) := by
      intro y hy
      obtain ⟨z, rfl⟩ := eC.surjective y
      exact (eC.map_mul z x).symm.trans ((congrArg eC (hx z hy)).trans (eC.map_mul x z))
    rw [Second.ambientKernel_selfCentralizing] at he
    exact he

private theorem no_component_common_fixed_of_kernel {G : Type*} [Group G] [Finite G]
    (T Q : Subgroup G) (hQT : Q ≤ T) (hQ : IsPGroup 2 Q)
    (hFT : FixedPoints.subgroup (Q.map (MulAut.conj : G →* MulAut G)) G ≤ T)
    (K : Subgroup T) [K.Normal] (hK : IsPGroup 2 K)
    (hC : centralizer (K : Set T) ≤ K)
    (D : Subgroup (FixedPoints.subgroup (Q.map (MulAut.conj : G →* MulAut G)) G)) :
    ¬ IsComponent (FixedPoints.subgroup (Q.map (MulAut.conj : G →* MulAut G)) G) D := by
  let F := FixedPoints.subgroup (Q.map (MulAut.conj : G →* MulAut G)) G
  let B := Q.subgroupOf T
  let e : F ≃* centralizer (B : Set T) := {
    toFun := fun x => ⟨⟨x, hFT x.property⟩, by
      intro q hq
      apply Subtype.ext
      have hx := x.property ⟨MulAut.conj (q : G), mem_map_of_mem _ hq⟩
      exact mul_inv_eq_iff_eq_mul.mp hx⟩
    invFun := fun x => ⟨(x : T), by
      intro a
      obtain ⟨q, hq, hqa⟩ := a.property
      change (a : MulAut G) (x : G) = (x : G)
      rw [← hqa]
      exact mul_inv_eq_iff_eq_mul.mpr
        (congrArg Subtype.val (x.property (⟨q, hQT hq⟩ : T) hq))⟩
    left_inv := fun x => rfl
    right_inv := fun x => rfl
    map_mul' := fun x y => rfl }
  exact fun hD => not_isComponent_centralizer_of_normal_pGroup K B hK
    (hQ.comap_of_injective T.subtype T.subtype_injective) hC _ (hD.map_equiv e)

/-- The J₄ case of the whole-two-action inspection in E.6.18. -/
theorem janko_four {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ¬ IsMulCommutative S) (_hqt : IsStronglyQuasithin S)
    (e : S ≃* Janko4.Model) : SevenActionInspection S := by
  let : Group.IsPerfect S := by
    constructor
    rcases (inferInstance : (commutator S).Normal).eq_bot_or_eq_top with hb | ht
    · exact (hna ((commutator_eq_bot_iff S).mp hb)).elim
    · exact ht
  let : IsSimpleGroup Janko4.Model := (MulEquiv.isSimpleGroup_congr e).mp inferInstance
  let : Group.IsPerfect Janko4.Model :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  apply of_equiv e
  intro P hp L _hLF hcomp _hseven
  by_contra hP
  let c : Janko4.Model →* MulAut Janko4.Model := MulAut.conj
  have hPin : P ≤ c.range := by
    intro a _ha
    obtain ⟨g, hg⟩ := automorphism_inner a
    exact ⟨g, hg.symm⟩
  let Q : Subgroup Janko4.Model := P.comap c
  have hQc : Q.map c = P := Subgroup.map_comap_eq_self hPin
  have hc_inj : Function.Injective c := MulAut.conj_injective_of_center_eq_bot center_eq_bot
  have hQp : IsPGroup 2 Q := hp.comap_of_injective c hc_inj
  let : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hP
  let : Nontrivial (center P) := hp.center_nontrivial
  obtain ⟨n, hn, hc⟩ := (hp.to_subgroup (center P)).nontrivial_iff_card.mp inferInstance
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center P) 2
    (hc.symm ▸ dvd_pow_self 2 (Nat.ne_of_gt hn))
  let t : P := z.1
  have ht : orderOf (t : MulAut Janko4.Model) = 2 :=
    (Subgroup.orderOf_coe z.1).trans ((Subgroup.orderOf_coe z).trans hz)
  obtain ⟨g, _hg, hconj, _⟩ := involution_representative (t : MulAut Janko4.Model) ht
  let T : Subgroup Janko4.Model := (t : MulAut Janko4.Model).fixedSubgroup
  have hgQ : g ∈ Q := by
    change c g ∈ P
    exact hconj ▸ t.property
  have hQT : Q ≤ T := by
    intro q hq
    apply (MulAut.mem_fixedSubgroup (t : MulAut Janko4.Model) q).mpr
    have hcent := congrArg Subtype.val
      (mem_center_iff.mp z.property ⟨c q, hq⟩)
    change c q * (t : MulAut Model) = (t : MulAut Model) * c q at hcent
    rw [hconj] at hcent
    have hcomm : q * g = g * q := by
      apply hc_inj
      simpa only [map_mul] using hcent
    rw [hconj]
    exact mul_inv_eq_iff_eq_mul.mpr hcomm.symm
  have hFT : FixedPoints.subgroup (Q.map c) Janko4.Model ≤ T := by
    intro x hx
    apply (MulAut.mem_fixedSubgroup (t : MulAut Janko4.Model) x).mpr
    have hxg := hx ⟨c g, mem_map_of_mem c hgQ⟩
    change c g x = x at hxg
    rw [hconj]
    exact hxg
  obtain ⟨K, hKn, hKp, hKc⟩ := involution_fixed_kernel (t : MulAut Janko4.Model) ht
  let := hKn
  have hcompQ : IsComponent (FixedPoints.subgroup (Q.map c) Janko4.Model)
      (L.subgroupOf (FixedPoints.subgroup (Q.map c) Janko4.Model)) := by
    rw [hQc]
    exact hcomp
  exact no_component_common_fixed_of_kernel T Q hQT hQp hFT K hKp hKc _ hcompQ

end SporadicInspection
end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance

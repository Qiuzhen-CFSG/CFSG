module
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.PointRigidity
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.RadicalOrientation.Basic
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoBlocks
public import Theory.GroupTheory.PCoreQuotientJoinAction
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.GroupTheory.PCoreImage

/-!
# Extending a marked binary five-space quotient

An automorphism preserving a point parabolic preserves its two-core,
which is the corresponding point radical. Binary point-radical rigidity
therefore makes it inner on the entire linear group. If a two-group S
normalizes X and its marked point parabolic, the conjugation action of XS
on X/O₂(X) consequently lifts to a surjection XS → GL₅(2). Its restriction
is the original marked quotient map and its kernel is a two-group.

Source: Aschbacher--Smith, 15.2.23(a), printed p.1117, the assertion that
S acts trivially on the Dynkin diagram. The original-subgroup consumer is
TerminalLinear.RepeatedNatural.MinimalParabolic.
-/

public noncomputable section
open Subgroup
namespace BinaryLinear
open OuterCyclic
private instance : Finite (LinearGroup 5) :=
  Finite.of_injective (fun g : LinearGroup 5 => (g : Space 5 → Space 5)) DFunLike.coe_injective

/-- An automorphism preserving an actual point parabolic is inner on all of GL₅(2). -/
theorem inner_of_preserves_pointParabolic (v : Space 5) (hv : v ≠ 0)
    (a : MulAut (LinearGroup 5))
    (ha : (parabolic (Submodule.span (ZMod 2) {v})).map a.toMonoidHom =
      parabolic (Submodule.span (ZMod 2) {v})) :
    a ∈ MulAut.innerSubgroup (LinearGroup 5) := by
  have hr : (pointRadical 5 v).map a.toMonoidHom = pointRadical 5 v := by
    change (radical (Submodule.span (ZMod 2) {v})).map a.toMonoidHom =
      radical (Submodule.span (ZMod 2) {v})
    rw [← SmallParabolicLevi.map_twoCore_eq_radical]
    change ((parabolic (Submodule.span (ZMod 2) {v})).pCoreIn 2).map a.toMonoidHom = _
    have hk : IsPGroup 2 a.toMonoidHom.ker := by
      rw [(MonoidHom.ker_eq_bot_iff a.toMonoidHom).mpr a.injective]
      exact IsPGroup.of_card (n := 0) (by simp)
    rw [map_pCoreIn_of_ker_isPGroup a.toMonoidHom hk,ha]
    rfl
  obtain ⟨g,hg⟩ := eq_conj_of_preservesPointRadicals (Or.inr rfl) a
    (preservesPointRadicals_of_one a hv hv hr)
  exact ⟨g,hg.symm⟩

private theorem center_transport {D E : Type*} [Group D] [Group E]
    (k : D ≃* E) (h : center E = ⊥) : center D = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have he : k x ∈ center E := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨z,rfl⟩ := k.surjective y
    exact (k.map_mul z x).symm.trans ((congrArg k (mem_center_iff.mp hx z)).trans (k.map_mul x z))
  have hx1 : k x = 1 := h.le he
  exact k.map_eq_one_iff.mp hx1

variable {G : Type*} [Group G]

/-- A two-group supplement preserving an actual point parabolic admits the
same binary-linear quotient as its normal subgroup. The restriction is the
original marked core-quotient map. -/
theorem exists_point_extension (X S A : Subgroup G)
    (hn : S ≤ normalizer (X : Set G)) (hS : IsPGroup 2 S)
    (hAX : A ≤ X) (hSA : S ≤ normalizer (A : Set G))
    (e : (X ⧸ pCore 2 X) ≃* LinearGroup 5)
    (v : Space 5) (hv : v ≠ 0)
    (hm : (A.subgroupOf X).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))) =
      parabolic (Submodule.span (ZMod 2) {v})) :
    ∃ f : (X ⊔ S : Subgroup G) →* LinearGroup 5,
      Function.Surjective f ∧ IsPGroup 2 f.ker ∧
      ∀ x : X, f (inclusion le_sup_left x) = e (QuotientGroup.mk' (pCore 2 X) x) := by
  let J := X ⊔ S
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  let a := (MulAut.congr e).toMonoidHom.comp (pCoreJoinAction 2 hn)
  have hinner (s : S) : a (inclusion le_sup_right s) ∈ MulAut.innerSubgroup (LinearGroup 5) := by
    apply inner_of_preserves_pointParabolic v hv
    rw [←hm]
    let c := X.normalizerMonoidHom ⟨s,hn s.property⟩
    have hc : (A.subgroupOf X).map c.toMonoidHom = A.subgroupOf X := by
      apply map_injective X.subtype_injective
      rw [map_map]
      have hh : X.subtype.comp c.toMonoidHom = (MulAut.conj (s : G)).toMonoidHom.comp X.subtype := rfl
      rw [hh,←map_map,map_subgroupOf_eq_of_le hAX]
      exact mem_normalizer_iff_map_conj_eq.mp (hSA s.property)
    have hqa : (a (inclusion le_sup_right s)).toMonoidHom.comp q = q.comp c.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      change e (pCoreJoinAction 2 hn (inclusion le_sup_right s)
        (e.symm (e (QuotientGroup.mk' (pCore 2 X) x)))) = _
      rw [e.symm_apply_apply,pCoreJoinAction_mk]
      rfl
    rw [map_map,hqa,←map_map,hc]
  have hcomp (x : X) : a (inclusion le_sup_left x) = MulAut.conj (q x) := by
    change MulAut.congr e (pCoreJoinAction 2 hn (inclusion le_sup_left x)) = _
    rw [pCoreJoinAction_on_component]
    apply MulEquiv.ext
    intro z
    change e (_ * e.symm z * _⁻¹) = q x * z * (q x)⁻¹
    simp only [map_mul,map_inv,e.apply_symm_apply]
    rfl
  have hai : ∀ j : J, a j ∈ MulAut.innerSubgroup (LinearGroup 5) := by
    intro j
    have hle : J ≤ ((MulAut.innerSubgroup (LinearGroup 5)).comap a).map J.subtype := by
      apply sup_le
      · intro x hx
        exact ⟨⟨x,mem_sup_left hx⟩,by
          change a (inclusion (show X ≤ J from le_sup_left) ⟨x,hx⟩) ∈ MulAut.innerSubgroup (LinearGroup 5)
          rw [hcomp]
          exact ⟨q ⟨x,hx⟩,rfl⟩,rfl⟩
      · intro s hs
        exact ⟨⟨s,mem_sup_right hs⟩,hinner ⟨s,hs⟩,rfl⟩
    obtain ⟨k,hk,hkj⟩ := hle j.property
    exact (Subtype.ext hkj : k = j) ▸ hk
  have hcL : center (LinearGroup 5) = ⊥ :=
    center_transport (slEquivLinear 5).symm (binary_center_eq_bot (n := 5) (by decide))
  have hc : center (X ⧸ pCore 2 X) = ⊥ := center_transport e hcL
  have hinj := Theory.GroupTheory.conj_injective_of_center_eq_bot hcL
  let ei : LinearGroup 5 ≃* MulAut.innerSubgroup (LinearGroup 5) :=
    MulEquiv.ofBijective MulAut.conj.rangeRestrict
      ⟨fun x y h => hinj (congrArg Subtype.val h),MulAut.conj.rangeRestrict_surjective⟩
  let f := ei.symm.toMonoidHom.comp (a.codRestrict _ hai)
  have hfcomp (x : X) : f (inclusion le_sup_left x) = q x := by
    apply ei.injective
    change ei (ei.symm _) = ei (q x)
    rw [ei.apply_symm_apply]
    apply Subtype.ext
    exact hcomp x
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨x,hx⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective _)) z
    exact ⟨inclusion le_sup_left x,(hfcomp x).trans hx⟩
  have hk : f.ker = (pCoreJoinAction 2 hn).ker := by
    ext j
    change ei.symm _ = 1 ↔ pCoreJoinAction 2 hn j = 1
    rw [ei.symm.map_eq_one_iff]
    rw [Subtype.ext_iff]
    change MulAut.congr e (pCoreJoinAction 2 hn j) = 1 ↔ _
    exact (MulAut.congr e).map_eq_one_iff
  refine ⟨f,hf,?_,hfcomp⟩
  rw [hk]
  exact pCoreJoinAction_kernel_isPGroup 2 hn hS hc

end BinaryLinear

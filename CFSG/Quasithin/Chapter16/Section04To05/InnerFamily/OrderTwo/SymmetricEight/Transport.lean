module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.Cases
public import CFSG.Quasithin.Chapter16.Section01To02.SourceHypothesis
public import Theory.GroupAction.CentralKernelFixedResidual

/-!
# Residual transport through the marked component quotient

The marked map from L to A₈ has kernel Z(L), which is a two-group by
16.1.2(1). The fixed-residual theorem for central two-group kernels lifts
every odd-order element centralizing the marked actor to the actual
O²(C_L(s)). The construction retains the quotient map and ambient
conjugation, and does not identify L with its central quotient.

Source: Aschbacher--Smith, 16.4.9(1), printed p.1189, case (II);
the center/core equality is 16.1.2(1).
-/

@[expose] public section

open Subgroup Theory.GroupTheory Equiv Equiv.Perm
namespace CFSG.Quasithin.Chapter16.Intersections.OrderTwo.SymmetricEight.Transport
open OuterResidual
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g : G} {L R : Subgroup G}
abbrev B (L : Subgroup G) (T : Sylow 2 G) := actionImage L (L ⊔ (T : Subgroup G))
abbrev S := Perm (Fin 8)

def componentMark (f : B L T ≃* S) : L →* S :=
  f.toMonoidHom.comp ((actionMap (le_normalizer (H := L))).codRestrict (B L T)
    (fun x => mem_actionImage (le_normalizer x.property)
      ((le_sup_left : L ≤ L ⊔ (T : Subgroup G)) x.property)))

def elementMark (h : IntersectionSetup T z L g R) (f : B L T ≃* S)
    {s : G} (hs : s ∈ R) : S :=
  f ⟨actionElement L s (h.sylow_normalizes (h.le_sylow hs)),
    mem_actionImage (h.sylow_normalizes (h.le_sylow hs))
      ((le_sup_right : (T : Subgroup G) ≤ L ⊔ (T : Subgroup G)) (h.le_sylow hs))⟩

def residualMark (f : B L T ≃* S) (s : G) : involutionResidual L s →* S :=
  (componentMark f).comp (inclusion ((involutionResidual_le L s).trans inf_le_left))

omit [Finite G] in
theorem componentMark_range (f : B L T ≃* S) :
    (componentMark f).range = ((actionImage L L).subgroupOf (B L T)).map f.toMonoidHom := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨actionMap (le_normalizer (H := L)) x,
      mem_actionImage (le_normalizer x.property)
        ((le_sup_left : L ≤ L ⊔ (T : Subgroup G)) x.property)⟩,
      mem_actionImage (le_normalizer x.property) x.property, rfl⟩
  · rintro ⟨d, hd, hfd⟩
    obtain ⟨x, hx, hxd⟩ := hd
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Eq.trans _ hfd
    apply congrArg f
    exact Subtype.ext hxd

omit [Finite G] in
theorem componentMark_ker (f : B L T ≃* S) :
    (componentMark f).ker = center L := by
  rw [← componentActionMap_ker L]
  ext x
  change f _ = 1 ↔ actionMap (le_normalizer (H := L)) x = 1
  rw [← f.map_one, f.injective.eq_iff, Subtype.ext_iff]
  rfl

theorem componentMark_action (h : IntersectionSetup T z L g R) (f : B L T ≃* S)
    {s : G} (hs : s ∈ R) (x : L) :
    componentMark f (involutionAction h hs x) =
      elementMark h f hs * componentMark f x * (elementMark h f hs)⁻¹ := by
  change f _ = f _ * f _ * (f _)⁻¹
  rw [← map_inv, ← map_mul, ← map_mul]
  apply congrArg f
  apply Subtype.ext
  change quotientMap L _ = quotientMap L _ * quotientMap L _ * (quotientMap L _)⁻¹
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

theorem residualMark_commutes (h : IntersectionSetup T z L g R) (f : B L T ≃* S)
    {s : G} (hs : s ∈ R) (x : involutionResidual L s) :
    residualMark f s x * elementMark h f hs = elementMark h f hs * residualMark f s x := by
  let y : L := ⟨x, ((involutionResidual_le L s) x.property).1⟩
  have hy : involutionAction h hs y = y := by
    apply (MulAut.mem_fixedSubgroup _ _).mp
    exact (ComponentTransfer.Intrinsic.mem_fixed_action _ _).mpr
      ((involutionResidual_le L s) x.property).2
  have he := componentMark_action h f hs y
  rw [hy] at he
  exact eq_mul_inv_iff_mul_eq.mp he

theorem exists_residual_preimage
    {𝒦 : GroupClass} (hG : Hypothesis1611 𝒦 G)
    (h : IntersectionSetup T z L g R) (f : B L T ≃* S)
    (he : ((actionImage L L).subgroupOf (B L T)).map f.toMonoidHom =
      alternatingGroup (Fin 8))
    {s : G} (hs : s ∈ R) (x : S) (hx : x ∈ alternatingGroup (Fin 8))
    (hcomm : x * elementMark h f hs = elementMark h f hs * x)
    (hodd : Nat.Coprime 2 (orderOf x)) :
    ∃ d : involutionResidual L s, residualMark f s d = x := by
  let F := componentMark f
  have hrange : F.range = alternatingGroup (Fin 8) := (componentMark_range f).trans he
  let π : L →* alternatingGroup (Fin 8) := F.codRestrict _
    (fun y => hrange ▸ (show F y ∈ F.range from ⟨y, rfl⟩))
  have hπ : Function.Surjective π := by
    intro y
    have hy : (y : S) ∈ F.range := hrange.symm ▸ y.property
    obtain ⟨w, hw⟩ := hy
    exact ⟨w, Subtype.ext hw⟩
  have hker : π.ker = center L := by
    calc π.ker = F.ker := by
           ext y
           change (⟨F y, _⟩ : alternatingGroup (Fin 8)) = 1 ↔ F y = 1
           exact Subtype.ext_iff
         _ = center L := componentMark_ker f
  have hp : IsPGroup 2 π.ker := by
    rw [hker, hG.evenType.component_center_eq_twoCore h.involution h.component]
    exact pCore_isPGroup
  let a := involutionAction h hs
  let b : MulAut (alternatingGroup (Fin 8)) := MulAut.conjNormal (elementMark h f hs)
  have heq : ∀ y, π (a y) = b (π y) := by
    intro y
    apply Subtype.ext
    exact componentMark_action h f hs y
  let y : b.fixedSubgroup := ⟨⟨x, hx⟩, by
    rw [MulAut.mem_fixedSubgroup]
    apply Subtype.ext
    change elementMark h f hs * x * (elementMark h f hs)⁻¹ = x
    exact mul_inv_eq_iff_eq_mul.mpr hcomm.symm⟩
  have hy : y ∈ pResidual 2 b.fixedSubgroup := by
    apply mem_pResidual_of_orderOf_coprime
    have ho : orderOf y = orderOf x :=
      (Subgroup.orderOf_coe y).symm.trans (Subgroup.orderOf_coe y.val).symm
    rwa [ho]
  obtain ⟨v, hv⟩ := MulAut.fixedResidualMap_surjective 2 a b π hπ hker.le hp heq ⟨y, hy⟩
  let E := ComponentTransfer.Intrinsic.centralizerEquivFixed
    (h.sylow_normalizes (h.le_sylow hs))
  have hvR : E.symm v.val ∈ pResidual 2 (ComponentTransfer.centralizerIn L s) :=
    map_pResidual_le 2 E.symm.toMonoidHom ⟨v.val, v.property, rfl⟩
  let d : involutionResidual L s := ⟨(E.symm v.val : G),
    ⟨E.symm v.val, hvR, rfl⟩⟩
  refine ⟨d, ?_⟩
  exact congrArg (fun w : pResidual 2 b.fixedSubgroup => (((w : b.fixedSubgroup) :
    alternatingGroup (Fin 8)) : S)) hv

end CFSG.Quasithin.Chapter16.Intersections.OrderTwo.SymmetricEight.Transport


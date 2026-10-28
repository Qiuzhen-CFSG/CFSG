module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.ResidualTransport
public import Theory.GroupTheory.GeneralizedFitting.CentralizerQuotient
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PCoreSurjective.OddExtension
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.SylowKernelCore

/-!
# The two-kernel and component structure of the action quotient

Once `Y₊ ≤ L` and relative normality of the component have been established,
minimality gives `I = LS`. Its quotient by `L` is a two-group. Since `Z(L)`
is a two-group, restricting this quotient to `C_I(L)` proves that the actual
action kernel is a two-group as well. The normal quasisimple centralizer
quotient theorem identifies the entire generalized Fitting subgroup.

The resulting two-kernel identifies the image of the original radical with
the actual two-core and transports the original `S₃` quotient through an
isomorphism. These are deductions in 15.3.43(e), conditional on component
placement; neither placement nor local maximality is assumed proved here.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.43, printed pp.1139--1140.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.ComponentAction
variable {G : Type*} [Group G] [Finite G] {I L : Subgroup G}
variable (d : ComponentAction I L)

omit [Finite G] in
/-- The action kernel is exactly the centralizer inside `I`. -/
theorem kernel_eq_centralizer : d.kernel = centralizer (L.subgroupOf I : Set I) := by
  ext x
  constructor
  · intro hx y hy
    exact Subtype.ext (hx y hy)
  · intro hx y hy
    exact congrArg Subtype.val (hx ⟨y, d.component_le hy⟩ hy)

omit [Finite G] in
/-- Generation by the component and a two-subgroup gives a two-group quotient. -/
theorem quotient_component_isTwoGroup {S : Subgroup G}
    (hS : IsPGroup 2 S) (hgen : I = L ⊔ S) :
    let := normal_subgroupOf_of_le_normalizer d.normalizes
    IsPGroup 2 (I ⧸ L.subgroupOf I) := by
  have hSI : S ≤ I := hgen ▸ le_sup_right
  let := normal_subgroupOf_of_le_normalizer d.normalizes
  apply isPGroup_quotient_of_sup_eq_top (L.subgroupOf I) (S.subgroupOf I)
    (hS.comap_subtype)
  rw [← subgroupOf_sup d.component_le hSI, ← hgen, subgroupOf_self]

omit [Finite G] in
/-- The centralizer kernel is an extension of two-groups, using the actual component center. -/
theorem kernel_isTwoGroup {S : Subgroup G}
    (hS : IsPGroup 2 S) (hgen : I = L ⊔ S)
    (hz : (center L).map L.subtype = L.pCoreIn 2) : IsPGroup 2 d.kernel := by
  let := normal_subgroupOf_of_le_normalizer d.normalizes
  let q := QuotientGroup.mk' (L.subgroupOf I)
  let f := q.comp d.kernel.subtype
  let j : d.kernel →* G := I.subtype.comp d.kernel.subtype
  have hj : Function.Injective j := I.subtype_injective.comp d.kernel.subtype_injective
  have hk : f.ker ≤ (L.pCoreIn 2).comap j := by
    intro x hx
    have hxL : ((x : d.kernel) : I).val ∈ L := (QuotientGroup.eq_one_iff (N := L.subgroupOf I) (x : I)).mp hx
    have hxz : (⟨j x, hxL⟩ : L) ∈ center L := by
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext (x.property y y.property)
    change j x ∈ L.pCoreIn 2
    rw [← hz]
    exact mem_map.mpr ⟨⟨j x, hxL⟩, hxz, rfl⟩
  have hfk : IsPGroup 2 f.ker := ((isPGroup_pCoreIn 2 L).comap_of_injective j hj).to_le hk
  have hp := ((d.quotient_component_isTwoGroup hS hgen).to_subgroup ⊤).comap_of_ker_isPGroup f hfk
  rw [comap_top] at hp
  exact hp.of_equiv topEquiv

/-- The component image is all of the generalized Fitting subgroup of the action quotient. -/
theorem image_generalizedFitting {S : Subgroup G}
    (hcomp : Theory.GroupTheory.IsComponent I (L.subgroupOf I))
    (hS : IsPGroup 2 S) (hgen : I = L ⊔ S) :
    Theory.GroupTheory.generalizedFitting d.Quotient = d.image L := by
  let := normal_subgroupOf_of_le_normalizer d.normalizes
  let := hcomp.2
  have h := Theory.GroupTheory.centralizerQuotient_generalizedFitting
    (L.subgroupOf I) (d.quotient_component_isTwoGroup hS hgen)
  have aux (N : Subgroup I) [N.Normal]
      (he : N = centralizer (L.subgroupOf I : Set I)) :
      Theory.GroupTheory.generalizedFitting (I ⧸ N) =
        (L.subgroupOf I).map (QuotientGroup.mk' N) := by
    subst N
    exact h
  exact aux d.kernel d.kernel_eq_centralizer

omit [Finite G] in
/-- Simplicity of the image follows from the genuine component hypothesis. -/
theorem image_simple_of_component
    (hcomp : Theory.GroupTheory.IsComponent I (L.subgroupOf I)) :
    IsSimpleGroup (d.image L) := by
  let := normal_subgroupOf_of_le_normalizer d.normalizes
  let := hcomp.2
  have h := Theory.GroupTheory.centralizerQuotientComponent_simple (L.subgroupOf I)
  have aux (N : Subgroup I) [N.Normal]
      (he : N = centralizer (L.subgroupOf I : Set I)) :
      IsSimpleGroup ((L.subgroupOf I).map (QuotientGroup.mk' N)) := by
    subst N
    exact h
  exact aux d.kernel d.kernel_eq_centralizer

omit [Finite G] in
/-- Joins of subgroups of `I` pass to their actual quotient images. -/
theorem image_sup {X Y : Subgroup G} (hX : X ≤ I) (hY : Y ≤ I) :
    d.image (X ⊔ Y) = d.image X ⊔ d.image Y := by
  simp only [image, subgroupOf_sup hX hY, Subgroup.map_sup]

set_option backward.isDefEq.respectTransparency false in
/-- A two-kernel makes the image of the original radical equal the actual image two-core. -/
theorem image_radical {X : Subgroup G} (hX : X ≤ I)
    (hk : IsPGroup 2 d.kernel) :
    d.image (X.pCoreIn 2) = (d.image X).pCoreIn 2 := by
  have he : (X.pCoreIn 2).subgroupOf I = (X.subgroupOf I).pCoreIn 2 := by
    apply Subgroup.map_injective I.subtype_injective
    rw [map_subgroupOf_eq_of_le ((pCoreIn_le 2 X).trans hX),
      map_pCoreIn_of_injective 2 _ I.subtype I.subtype_injective,
      map_subgroupOf_eq_of_le hX]
  change ((X.pCoreIn 2).subgroupOf I).map d.quotientMap = _
  rw [he]
  exact map_pCoreIn_of_ker_isPGroup d.quotientMap
    ((show d.quotientMap.ker = d.kernel from QuotientGroup.ker_mk' _).symm ▸ hk) _

set_option backward.isDefEq.respectTransparency false in
/-- The two-core quotient is preserved through the actual two-kernel map. -/
theorem image_shadow {Yplus S : Subgroup G} (hY : Yplus ≤ I) (hS : S ≤ I)
    (hk : IsPGroup 2 d.kernel) (hshadow : SymmetricThreeShadow Yplus S) :
    SymmetricThreeShadow (d.image Yplus) (d.image S) := by
  let X := Yplus ⊔ S
  have hXI : X ≤ I := sup_le hY hS
  let f : X →* d.image X := (d.quotientMap.subgroupMap (X.subgroupOf I)).comp
    (subgroupOfEquivOfLe hXI).symm.toMonoidHom
  have hf : Function.Surjective f := (d.quotientMap.subgroupMap_surjective _).comp
    (subgroupOfEquivOfLe hXI).symm.surjective
  have hfk : IsPGroup 2 f.ker := by
    dsimp only [f]
    rw [← MonoidHom.comap_ker]
    apply IsPGroup.comap_of_injective _ _ (subgroupOfEquivOfLe hXI).symm.injective
    change IsPGroup 2 ((QuotientGroup.mk' d.kernel).subgroupMap (X.subgroupOf I)).ker
    rw [ker_subgroupMap, QuotientGroup.ker_mk']
    exact hk.comap_subtype
  obtain ⟨e⟩ := hshadow
  have hh : SymmetricThreeShadow (d.image Yplus) (d.image S) := by
    have hh : Nonempty ((d.image X ⧸ pCore 2 (d.image X)) ≃* Equiv.Perm (Fin 3)) :=
      ⟨(MonoidHom.quotientPCoreEquivOfSurjective f hf hfk).symm.trans e⟩
    have aux (J : Subgroup d.Quotient) (he : d.image X = J) :
        Nonempty ((J ⧸ pCore 2 J) ≃* Equiv.Perm (Fin 3)) := by
      subst J
      exact hh
    exact aux _ (d.image_sup hY hS)
  exact hh
end CFSG.Quasithin.Chapter15.Section03.RankOne.ComponentAction

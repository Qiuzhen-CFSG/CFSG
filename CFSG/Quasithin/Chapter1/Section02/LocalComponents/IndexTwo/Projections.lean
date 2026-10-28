module

public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Mathlib.GroupTheory.NoncommPiCoprod

/-!
# Component projections for the index-two local argument

In the quotient by the solvable radical, distinct C-components commute
and each has trivial center. Their independence identifies their generated
subgroup with the product of the actual component carriers. The coordinate
maps below are constructed from this equivalence, including their values
on each factor. A nonsolvable subgroup of the original layer has a
nontrivial coordinate after passage to the radical quotient.

This is the projection construction in the proof of Aschbacher–Smith,
*The Classification of Quasithin Groups*, Lemma 1.2.5, printed p.505
(combined manuscript, 1 March 2004), using Proposition A.3.3(4)–(6).
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.Section02.IndexTwo
universe v
variable {G : Type*} [Group G] [Finite G]

/-- The actual C-components, with their subgroup carriers. -/
abbrev ComponentIndex (G : Type*) [Group G] := {K : Subgroup G // K.IsCComponent}

/-- The layer of a radical-free finite group is the direct product of its C-components. -/
theorem exists_componentCoordinates (hrad : solvableRadical G = ⊥) :
    ∃ e : cComponentLayer G ≃* (∀ K : ComponentIndex G, K.1),
      (∀ (K : ComponentIndex G) (x : K.1),
        e ⟨x, le_cComponentLayer K.2 x.2⟩ K = x) ∧
      (∀ (K J : ComponentIndex G), K ≠ J → ∀ x : K.1,
        e ⟨x, le_cComponentLayer K.2 x.2⟩ J = 1) := by
  classical
  let D : ComponentIndex G → Subgroup G := Subtype.val
  have hc (i j : ComponentIndex G) (hij : i ≠ j) :
      D i ≤ centralizer (D j : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (i.2.commutator_eq_bot_of_ne_of_solvableRadical_eq_bot hrad j.2
        (fun he => hij (Subtype.ext he)))
  have hcomm : Pairwise fun i j : ComponentIndex G =>
      ∀ x y : G, x ∈ D i → y ∈ D j → Commute x y := by
    intro i j hij x y hx hy
    exact (mem_centralizer_iff.mp (hc i j hij hx) y hy).symm
  have hind : iSupIndep D := by
    rw [iSupIndep_def]
    intro i
    apply Subgroup.disjoint_def.mpr
    intro x hx hi
    have hothers : (⨆ j, ⨆ (_ : j ≠ i), D j) ≤ centralizer (D i : Set G) :=
      iSup_le fun j => iSup_le fun hji => hc j i hji
    have hz : (⟨x, hx⟩ : D i) ∈ center (D i) := by
      apply mem_center_iff.mpr
      intro y
      apply Subtype.ext
      exact mem_centralizer_iff.mp (hothers hi) y y.2
    have hcenter := center_eq_bot_of_isSubnormal_of_solvableRadical_eq_bot
      hrad i.2.subnormal
    change center (D i) = ⊥ at hcenter
    have hx1 : (⟨x, hx⟩ : D i) = 1 := by
      simpa only [hcenter, mem_bot] using hz
    exact congrArg Subtype.val hx1
  let : Fintype (ComponentIndex G) := Fintype.ofFinite _
  let f := Subgroup.noncommPiCoprod hcomm
  have hf : Function.Injective f := Subgroup.injective_noncommPiCoprod_of_iSupIndep hind
  have hr : f.range = cComponentLayer G := by
    rw [Subgroup.noncommPiCoprod_range]
    exact (sSup_eq_iSup' {K : Subgroup G | K.IsCComponent}).symm
  let e : (∀ i, D i) ≃* cComponentLayer G :=
    (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hr)
  have hs (i : ComponentIndex G) (x : D i) :
      e (Pi.mulSingle i x) = ⟨x, le_cComponentLayer i.2 x.2⟩ := by
    apply Subtype.ext
    change f (Pi.mulSingle i x) = x
    exact MonoidHom.noncommPiCoprod_mulSingle (hcomm :=
      Subgroup.commute_subtype_of_commute hcomm) _ _ _
  refine ⟨e.symm, ?_, ?_⟩
  · intro i x
    rw [← hs, e.symm_apply_apply, Pi.mulSingle_eq_same]
  · intro i j hij x
    rw [← hs, e.symm_apply_apply, Pi.mulSingle_eq_of_ne hij.symm]

/-- Coordinates in the product of the actual component carriers. -/
noncomputable def componentCoordinates (hrad : solvableRadical G = ⊥) :
    cComponentLayer G ≃* (∀ K : ComponentIndex G, K.1) :=
  (exists_componentCoordinates hrad).choose

/-- Projection from the layer onto a specified component. -/
noncomputable def componentProjection (hrad : solvableRadical G = ⊥)
    (K : ComponentIndex G) : cComponentLayer G →* K.1 :=
  (Pi.evalMonoidHom (fun J : ComponentIndex G => J.1) K).comp
    (componentCoordinates hrad).toMonoidHom

/-- A component projection restricts to the identity on that component. -/
theorem componentProjection_self (hrad : solvableRadical G = ⊥)
    (K : ComponentIndex G) (x : K.1) :
    componentProjection hrad K ⟨x, le_cComponentLayer K.2 x.2⟩ = x :=
  (exists_componentCoordinates hrad).choose_spec.1 K x

/-- A component projection kills every other component. -/
theorem componentProjection_other (hrad : solvableRadical G = ⊥)
    (K J : ComponentIndex G) (hne : K ≠ J) (x : K.1) :
    componentProjection hrad J ⟨x, le_cComponentLayer K.2 x.2⟩ = 1 :=
  (exists_componentCoordinates hrad).choose_spec.2 K J hne x

/-- The projection of the Sylow intersection with the layer is the Sylow
intersection with the chosen component. -/
theorem componentProjection_map_sylow (hrad : solvableRadical G = ⊥)
    (S : Sylow 2 G) (K : ComponentIndex G) :
    ((S : Subgroup G).subgroupOf (cComponentLayer G)).map (componentProjection hrad K) =
      (S : Subgroup G).subgroupOf K.1 := by
  obtain ⟨T, hT⟩ := S.exists_subgroupOf_eq_of_subnormal K.1 K.2.subnormal
  have hp : IsPGroup 2 (((S : Subgroup G).subgroupOf (cComponentLayer G)).map
      (componentProjection hrad K)) :=
    S.isPGroup'.comap_subtype.map _
  have hle : (T : Subgroup K.1) ≤
      ((S : Subgroup G).subgroupOf (cComponentLayer G)).map (componentProjection hrad K) := by
    intro x hx
    have hxS : (x : G) ∈ (S : Subgroup G) :=
      show x ∈ (S : Subgroup G).subgroupOf K.1 from hT ▸ hx
    exact mem_map.mpr ⟨⟨x, le_cComponentLayer K.2 x.2⟩, hxS,
      componentProjection_self hrad K x⟩
  exact (T.is_maximal' hp hle).trans hT

/-- The component projections jointly separate elements of the layer. -/
theorem eq_one_of_componentProjection_eq_one (hrad : solvableRadical G = ⊥)
    (x : cComponentLayer G) (hx : ∀ K, componentProjection hrad K x = 1) : x = 1 := by
  apply (componentCoordinates hrad).injective
  rw [map_one]
  exact funext hx

/-- The quotient map restricted to the C-component layers. -/
noncomputable def radicalLayerMap :
    cComponentLayer G →* cComponentLayer (G ⧸ solvableRadical G) where
  toFun x := ⟨QuotientGroup.mk' (solvableRadical G) x, by
    rw [← cComponentLayer_map_quotient (solvableRadical G)]
    exact mem_map.mpr ⟨x, x.2, rfl⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul (QuotientGroup.mk' (solvableRadical G))
    (x : G) (y : G))

/-- The coordinate map used in Lemma 1.2.5, defined on the original layer. -/
noncomputable def radicalProjection
    (K : ComponentIndex (G ⧸ solvableRadical G)) : cComponentLayer G →* K.1 :=
  (componentProjection (solvableRadical_quotient_solvableRadical (G := G)) K).comp
    radicalLayerMap

/-- Nonsolvability forces a nontrivial projection modulo the ambient radical. -/
theorem exists_nontrivial_radicalProjection {B : Subgroup G}
    (hB : ¬ Group.IsSolvable B) (hBL : B ≤ cComponentLayer G) :
    ∃ K : ComponentIndex (G ⧸ solvableRadical G),
      (B.subgroupOf (cComponentLayer G)).map (radicalProjection K) ≠ ⊥ := by
  classical
  by_contra hn
  push Not at hn
  have hBR : B ≤ solvableRadical G := by
    intro b hb
    have he : radicalLayerMap (⟨b, hBL hb⟩ : cComponentLayer G) = 1 := by
      apply eq_one_of_componentProjection_eq_one
      intro K
      have hm : radicalProjection K ⟨b, hBL hb⟩ ∈
          (B.subgroupOf (cComponentLayer G)).map (radicalProjection K) :=
        mem_map.mpr ⟨⟨b, hBL hb⟩, hb, rfl⟩
      exact mem_bot.mp (hn K ▸ hm)
    exact (QuotientGroup.eq_one_iff (N := solvableRadical G) b).mp
      (congrArg Subtype.val he)
  exact hB (Group.isSolvable_of_isSolvable_injective (inclusion_injective hBR))

/-- Every homomorphism with nontrivial image from a C-component has solvable kernel. -/
theorem solvable_ker_of_cComponent_nontrivial_image {B : Subgroup G}
    (hB : B.IsCComponent) {X : Type v} [Group X] (f : B →* X) (hf : f.range ≠ ⊥) :
    Group.IsSolvable f.ker := by
  apply hB.isSolvable_of_subnormal_lt_top (inferInstance : f.ker.Normal).isSubnormal
  intro ht
  apply hf
  apply eq_bot_iff.mpr
  rintro x ⟨b, rfl⟩
  have hb : b ∈ f.ker := ht.symm ▸ (mem_top b)
  exact mem_bot.mpr hb

/-- A nontrivial homomorphic image of a C-component is a C-component of itself. -/
theorem cComponent_nontrivial_range {B : Subgroup G} (hB : B.IsCComponent)
    {X : Type v} [Group X] (f : B →* X) (hf : f.range ≠ ⊥) :
    (⊤ : Subgroup f.range).IsCComponent := by
  let : Group.IsSolvable f.ker := solvable_ker_of_cComponent_nontrivial_image hB f hf
  let : Group.IsSolvable f.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    infer_instance
  have ht : (⊤ : Subgroup B).IsCComponent := by
    simpa only [subgroupOf_self] using hB.subgroupOf le_rfl
  simpa only [map_top_of_surjective _ f.rangeRestrict_surjective] using
    cComponent_map_of_solvable_ker ht f.rangeRestrict f.rangeRestrict_surjective

end CFSG.Quasithin.Chapter1.Section02.IndexTwo

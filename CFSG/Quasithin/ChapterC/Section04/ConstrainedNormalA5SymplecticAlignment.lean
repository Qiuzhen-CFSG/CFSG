module

public import CFSG.Quasithin.ChapterC.Section04.ConstrainedNormalSeedPlacement
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.SymplecticParabolic
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.PerfectNormalParabolic
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Theory.AtlasPort.LinearGroups.SL2Order

/-!
# The actual normal A₅ seed in a constrained symplectic component

The original normal seed lies in the selected component by C.4.5. Under
any given symplectic marking of that component's actual star image, the
marked local intersection is a parabolic. The seed image is nonsolvable,
perfect and normal there, hence equals its point or plane local residual.
Its SL₂ quotient factors through the original A₅ quotient, forcing the
field to have four elements.

Both images use the same selected component, star map, and conjugated
marking. No parabolic-residual alignment is assumed.
Source: Aschbacher--Smith C.4.8 and 12.7.5, printed pp.154 and 840.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Theory.SpecificGroups.SymplecticFour

private theorem map_toStarImage_subgroupOf
    {G : Type*} [Group G] (K R A : Subgroup G) :
    (A.subgroupOf K).map (toStarImage K R) =
      (starImage K R (A ⊓ K)).subgroupOf (starImage K R K) := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨⟨x,mem_sup_left x.property⟩,⟨hx,x.property⟩,rfl⟩
  · rintro ⟨x,hx,he⟩
    exact ⟨⟨x,hx.2⟩,hx.1,Subtype.ext he⟩

private theorem field_card_four_of_a5_sl2_image {A F : Type*} [Group A] [Finite A] [Field F] [Finite F] [CharP F 2]
    (hF : 4 ≤ Nat.card F)
    (eA : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 5))
    (q : A →* Matrix.SpecialLinearGroup (Fin 2) F) (hq : Function.Surjective q) :
    Nat.card F = 4 := by
  let : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) := NaturalExtension.model_simple (by omega)
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) := NaturalExtension.model_perfect (by omega)
  let N := (pCore 2 A).map q
  let : N.Normal := (inferInstance : (pCore 2 A).Normal).map q hq
  let : Group.IsNilpotent N := (pCore_isPGroup.map q).isNilpotent
  have hn : N = ⊥ := by
    rcases (inferInstance : N.Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · have hs : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) F) :=
        Group.isSolvable_of_surjective (f := N.subtype) (by
          intro x
          exact ⟨⟨x, ht.symm ▸ mem_top x⟩,rfl⟩)
      exact (Group.IsPerfect.not_isSolvable _ hs).elim
  have hk : pCore 2 A ≤ q.ker := (Subgroup.map_eq_bot_iff _).mp hn
  let qb := QuotientGroup.lift (pCore 2 A) q hk
  have hqb : Function.Surjective qb := by
    intro x
    obtain ⟨a,rfl⟩ := hq x
    exact ⟨QuotientGroup.mk' (pCore 2 A) a,rfl⟩
  have hcard := Nat.card_le_card_of_surjective qb hqb
  rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup,Nat.card_fin] at hcard
  norm_num [Nat.factorial] at hcard
  rw [Atlas.card_sl_two] at hcard
  by_contra he
  have h5 : 5 ≤ Nat.card F := by omega
  have h25 : 25 ≤ Nat.card F ^ 2 := Nat.pow_le_pow_left h5 2
  have h24 : 24 ≤ Nat.card F ^ 2 - 1 := by omega
  have h120 := Nat.mul_le_mul h5 h24
  omega

/-- C.4.8 residual alignment and field restriction for the original normal
A₅ seed, in the same marked star image of the selected constrained component. -/
theorem constrained_normal_a5_symplectic_alignment
    {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
    {H M L R V : Subgroup G}
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (hn : (L.subgroupOf M).Normal)
    (eA5 : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (J : Subgroup H) (hJ : J.IsCComponent)
    (hq : IsQuasisimple (J ⧸ pCore 2 J)) (hout : ¬ J ≤ M.subgroupOf H)
    (hf : generalizedFitting J = pCore 2 J)
    (e : starImage (J.map H.subtype) R (J.map H.subtype) ≃* Sp F)
    {n : ℕ} (hcard : Nat.card F = 2 ^ n) (hnF : 1 < n) :
    Nat.card F = 4 ∧ ∃ g : Sp F,
      let E := e.trans (MulAut.conj g)
      let P := ((starM (J.map H.subtype) R M).subgroupOf
        (starImage (J.map H.subtype) R (J.map H.subtype))).map E.toMonoidHom
      let B := (L.subgroupOf (J.map H.subtype)).map
        (E.toMonoidHom.comp (toStarImage (J.map H.subtype) R))
      (P = pointParabolic ∧ B = pointLocal) ∨
      (P = planeParabolic ∧ B = planeLocal) := by
  let K := J.map H.subtype
  have hLK : L ≤ K := by
    intro l hl
    exact ⟨⟨l,h.local_le (h.component_le hl)⟩,
      h.constrained_normal_seed_le hn J hJ hq hout hf hl,rfl⟩
  have hi := h.constrained_source_input J hJ hq hout hf
  have hF : 4 ≤ Nat.card F := by
    rw [hcard]
    exact (show 4 = 2 ^ 2 from rfl).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  obtain ⟨g,hg⟩ := C27Source.star_symplectic_marked_parabolic_from_source hi e hF
  let E := e.trans (MulAut.conj g)
  let q := E.toMonoidHom.comp (toStarImage K R)
  let A := L.subgroupOf K
  let P := (M.subgroupOf K).map q
  let B := A.map q
  have hP : P = ((starM K R M).subgroupOf (starImage K R K)).map E.toMonoidHom := by
    change (M.subgroupOf K).map (E.toMonoidHom.comp (toStarImage K R)) = _
    rw [←map_map,map_toStarImage_subgroupOf]
    rfl
  have hg' : P = pointParabolic ∨ P = planeParabolic := by
    rw [hP]
    have he : E.toMonoidHom = (MulAut.conj g).toMonoidHom.comp e.toMonoidHom := by
      ext x
      rfl
    simpa only [he,map_map] using hg
  have hML : M ≤ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer h.component_le).mp hn
  have hPA : M.subgroupOf K ≤ normalizer (A : Set K) := by
    intro x hx y
    exact hML hx (y : G)
  have hPB : P ≤ normalizer (B : Set (Sp F)) :=
    (map_mono hPA).trans (A.le_normalizer_map q)
  have hBP : B ≤ P := map_mono (subgroupOf_mono K h.component_le)
  let : Group.IsPerfect (L.subgroupOf M) := h.component.perfect
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe h.component_le).toMonoidHom)
    (subgroupOfEquivOfLe h.component_le).surjective
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hLK).symm.toMonoidHom)
    (subgroupOfEquivOfLe hLK).symm.surjective
  let : Group.IsPerfect B := Group.IsPerfect.map q
  have hker : q.ker = (toStarImage K R).ker := by
    ext x
    change E (toStarImage K R x) = 1 ↔ toStarImage K R x = 1
    exact E.map_eq_one_iff
  let : Group.IsSolvable q.ker := by
    rw [hker]
    exact C27Source.toStarImage_ker_solvable_from_source hi
  have hB : ¬ Group.IsSolvable B := by
    intro hs
    let := hs
    let := isSolvable_comap_of_solvable_ker q B
    have hle : A ≤ B.comap q := le_comap_map q A
    let : Group.IsSolvable A := Group.isSolvable_of_isSolvable_injective (inclusion_injective hle)
    let : Group.IsSolvable L := Group.isSolvable_of_surjective
      (f := (subgroupOfEquivOfLe hLK).toMonoidHom) (subgroupOfEquivOfLe hLK).surjective
    exact h.component.not_isSolvable (Group.isSolvable_of_surjective
      (f := (subgroupOfEquivOfLe h.component_le).symm.toMonoidHom)
      (subgroupOfEquivOfLe h.component_le).symm.surjective)
  let qB : L →* B := (q.subgroupMap A).comp (subgroupOfEquivOfLe hLK).symm.toMonoidHom
  have hqB : Function.Surjective qB :=
    (q.subgroupMap_surjective A).comp (subgroupOfEquivOfLe hLK).symm.surjective
  rcases hg' with hp | hp
  · have hb : B = pointLocal := perfect_normal_pointParabolic_eq_local hcard hnF B hB
      (hBP.trans_eq hp) (hp.symm ▸ hPB)
    let f := pointQuotient.comp ((MulEquiv.subgroupCongr hb).toMonoidHom.comp qB)
    have hsurj : Function.Surjective f := pointQuotient_surjective.comp
      ((MulEquiv.subgroupCongr hb).surjective.comp hqB)
    refine ⟨field_card_four_of_a5_sl2_image hF eA5 f hsurj,g,Or.inl ⟨?_,hb⟩⟩
    exact hP.symm.trans hp
  · have hb : B = planeLocal := perfect_normal_planeParabolic_eq_local hcard hnF B hB
      (hBP.trans_eq hp) (hp.symm ▸ hPB)
    let f := Plane.quotientMap.comp ((MulEquiv.subgroupCongr hb).toMonoidHom.comp qB)
    have hsurj : Function.Surjective f := Plane.quotientMap_surjective.comp
      ((MulEquiv.subgroupCongr hb).surjective.comp hqB)
    refine ⟨field_card_four_of_a5_sl2_image hF eA5 f hsurj,g,Or.inr ⟨?_,hb⟩⟩
    exact hP.symm.trans hp

end CFSG.Quasithin.ChapterC.HypothesisC28

module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.MixedLinearStability
public import Theory.GroupTheory.MaximalRadicalTransport
public import Theory.GroupTheory.PCoreInRestriction

/-!
# Returning to the original plane parabolic

The literal N_LT(V₂) is maximal in LT. Its two-core acts inside a
conjugate of the cube of three disjoint swaps on the augmentation core.
An actor of centralizer index eight fills this image. The faithful
ordinary A₆ action has kernel O₂(LT), so MaximalRadicalTransport returns
any conjugator in LT taking this actor back into the radical to N_LT(V₂).

The proof compares the full normalizer marking with the original LT
marking using the same five-dimensional coordinates. No abstract group
identification replaces either action kernel or the actual conjugator.
MixedLinearReturn applies this to V₀ and its original mixed conjugate.
Source: Aschbacher--Smith 13.4.15, printed p.912, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BinaryPermutation
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 BinaryConjugationCoordinates
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- A returning rank-three actor in the original plane radical has its
literal conjugator in the original plane parabolic. -/
theorem original_plane_radical_return
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (W : Submodule (ZMod 2) (natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hT : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (U : Subgroup G)
    (hU : U ≤ ((L ⊔ (T : Subgroup G)) ⊓ normalizer
      (m.naturalPreimage W : Set G) : Subgroup G).pCoreIn 2)
    (g : G) (hg : g ∈ L ⊔ (T : Subgroup G))
    (hUg : U.conjBy g ≤ ((L ⊔ (T : Subgroup G)) ⊓ normalizer
      (m.naturalPreimage W : Set G) : Subgroup G).pCoreIn 2)
    (hi : (centralizer (V : Set G)).relIndex (U.conjBy g) = 8) :
    g ∈ (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G) := by
  let X := L ⊔ (T : Subgroup G)
  let B := X ⊓ normalizer (m.naturalPreimage W : Set G)
  let R := B.pCoreIn 2
  have hBX : B ≤ X := inf_le_left
  have hRX : R ≤ X := (pCoreIn_le 2 B).trans hBX
  have hUX : U ≤ X := hU.trans hRX
  have hUgX : U.conjBy g ≤ X := hUg.trans hRX
  have hXN : X ≤ normalizer (L : Set G) := sup_le L.le_normalizer D.sylow_normalizes_component
  have hn := normalizer_component_le_module h structural D m
  obtain ⟨q,a,hq,hcore⟩ := original_plane_radical_image h structural D m W hW hT
  let f := q.comp (inclusion hXN)
  obtain ⟨f₀,hf₀,_,_,hk₀⟩ := exists_core_product_permutation D m h structural eL
  have hff : f = f₀ := by
    apply MonoidHom.ext
    intro x
    apply SixCoreNormalizer.action_injective
    apply LinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := m.coordinate.surjective (Multiplicative.ofAdd w)
    exact (hq (inclusion hXN x) v).symm.trans (hf₀ x v)
  have hk : f.ker = pCore 2 X := hff ▸ hk₀
  have hbound : Nat.card ((R.subgroupOf X).map f) ≤ 8 := by
    have hh : (R.subgroupOf X).map f ≤
        Theory.SpecificGroups.SymmetricSix.BinaryFlags.D.map (MulAut.conj a.val).toMonoidHom := by
      rintro y ⟨r,hr,rfl⟩
      obtain ⟨b,hb,he⟩ := hr
      apply hcore
      refine ⟨b,hb,?_⟩
      change q ⟨b.val,_⟩ = q ⟨r.val,_⟩
      congr 1
      exact Subtype.ext he
    have hc := Nat.card_le_card_of_injective (inclusion hh) (inclusion_injective hh)
    simpa only [card_map_of_injective (f := (MulAut.conj a.val).toMonoidHom) (MulAut.conj a.val).injective,D_card] using hc
  have image_card (Y : Subgroup G) (hYX : Y ≤ X) :
      Nat.card ((Y.subgroupOf X).map f) = (centralizer (V : Set G)).relIndex Y := by
    let fY := f.comp (inclusion hYX)
    have he : fY.range = (Y.subgroupOf X).map f := by
      ext y
      constructor
      · rintro ⟨v,rfl⟩
        exact ⟨inclusion hYX v,v.property,rfl⟩
      · rintro ⟨v,hv,rfl⟩
        exact ⟨⟨v.val,hv⟩,rfl⟩
    rw [←he]
    exact (model_card_range Y V (hYX.trans (hXN.trans hn)) (coreRepresentation (Fin 6))
      SixCoreNormalizer.action_injective fY m.coordinate
      (fun y v => hq ⟨y.val,hXN (hYX y.property)⟩ v)).trans (inf_relIndex_left _ _)
  let gx : X := ⟨g,hg⟩
  have hconj : (U.subgroupOf X).conjBy gx = (U.conjBy g).subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [map_conjBy_hom,map_subgroupOf_eq_of_le hUX,map_subgroupOf_eq_of_le hUgX]
    rfl
  have hcard : Nat.card ((U.subgroupOf X).map f) = 8 := by
    have hh : Nat.card (((U.subgroupOf X).conjBy gx).map f) = 8 := by
      rw [hconj,image_card (U.conjBy g) hUgX,hi]
    rw [map_conjBy_hom] at hh
    change Nat.card (((U.subgroupOf X).map f).map (MulAut.conj (f gx)).toMonoidHom) = 8 at hh
    rwa [card_map_of_injective (MulAut.conj (f gx)).injective] at hh
  have hRlocal : (B.subgroupOf X).pCoreIn 2 = R.subgroupOf X :=
    pCoreIn_subgroupOf 2 B X hBX
  have hreturn := mem_of_radical_image_return (T.subtype (show (T : Subgroup G) ≤ X from le_sup_right))
    (B.subgroupOf X) (show ((T.subtype le_sup_right : Sylow 2 X) : Subgroup X) ≤ B.subgroupOf X from
      fun t ht => ⟨t.property,hT ht⟩)
    (Solvable.original_second_flag_coatom D m W hW hT) f hk (U.subgroupOf X)
    (by rw [hRlocal]; exact subgroupOf_mono X hU) 8 (by decide) hcard
    (by rw [hRlocal]; exact hbound) gx (by
      rw [hRlocal,hconj]
      exact subgroupOf_mono X hUg)
  exact hreturn
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable

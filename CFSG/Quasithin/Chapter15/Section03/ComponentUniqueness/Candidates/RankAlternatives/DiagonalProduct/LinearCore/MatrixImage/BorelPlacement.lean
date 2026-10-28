module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.LinearCore.MatrixImage.LocalSetup
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.BorelPreimage

/-!
# Placement of the actual linear Borel

Restrict the supplied Sylow subgroup to the relative component. Its image
under the prescribed projective quotient has full preimage S ∩ L, since
the kernel is the two-core. Thus the preimage of the projective normalizer
is exactly N_L(S ∩ L). Its characteristic two is an intrinsic model fact,
valid also for the central two-cover of PSL₃(4). Source 15.3.33(1) places
this Borel in M once Y₊ preserves S ∩ L.

The theorem below isolates that remaining invariance obligation; it does
not claim that choosing a Sylow establishes invariance. The field, quotient
equivalence and outer actor are retained throughout.

Source: Aschbacher--Smith, 15.3.11--12, 15.3.33 and 15.3.36--38,
printed pp.1123--1125 and 1134--1136.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.LinearCore.MatrixImage

variable {G : Type*} [Group G] [Finite G]
variable {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}

/-- Sylow restriction in the actual component, before taking any quotient. -/
theorem SourceSetup.component_sylow (h : SourceSetup d I L) :
    ∃ Q : Sylow 2 L, (Q : Subgroup L) = d.S.subgroupOf L := by
  obtain ⟨P, hP⟩ := h.sylow
  obtain ⟨Q, hQ⟩ := P.exists_subgroupOf_eq_of_subnormal (L.subgroupOf I) h.component.1
  let eL := subgroupOfEquivOfLe h.component_le
  refine ⟨Q.mapSurjective (f := eL.toMonoidHom) eL.surjective, ?_⟩
  change (Q : Subgroup (L.subgroupOf I)).map eL.toMonoidHom = _
  rw [hQ, ← hP]
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.val, ha, rfl⟩
  · rintro ⟨a, ha, he⟩
    refine ⟨⟨a, ?_⟩, ha, ?_⟩
    · change (a : G) ∈ L
      change (a : G) = (x : G) at he
      exact he.symm ▸ x.property
    · exact Subtype.ext he

/-- The prescribed Sylow image has the entire actual component Sylow as preimage. -/
theorem SourceSetup.sylow_preimage (h : SourceSetup d I L)
    {F : Type*} [Field F] (e : (L ⧸ pCore 2 L) ≃* PSL(3,F))
    (P : Sylow 2 PSL(3,F))
    (hP : (P : Subgroup PSL(3,F)) = (d.S.subgroupOf L).map (quotientMap e)) :
    (P : Subgroup PSL(3,F)).comap (quotientMap e) = d.S.subgroupOf L := by
  obtain ⟨Q, hQ⟩ := h.component_sylow
  rw [hP, comap_map_eq_self]
  rw [quotientMap_ker, ← hQ]
  exact fitting_pCore_le_sylow Q

/-- The Borel preimage is the relative normalizer, with no coordinate change. -/
theorem SourceSetup.borel_preimage (h : SourceSetup d I L)
    {F : Type*} [Field F] (e : (L ⧸ pCore 2 L) ≃* PSL(3,F))
    (P : Sylow 2 PSL(3,F))
    (hP : (P : Subgroup PSL(3,F)) = (d.S.subgroupOf L).map (quotientMap e)) :
    ((normalizer (P : Set PSL(3,F))).comap (quotientMap e)).map L.subtype =
      L ⊓ normalizer (d.S ⊓ L : Subgroup G) := by
  change ((normalizer ((P : Subgroup PSL(3,F)) : Set PSL(3,F))).comap
    (quotientMap e)).map L.subtype = _
  rw [comap_normalizer_eq_of_surjective (P : Subgroup PSL(3,F))
    (quotientMap_surjective e), h.sylow_preimage e P hP]
  have he : normalizer (d.S.subgroupOf L : Set L) =
      (normalizer (d.S ⊓ L : Subgroup G)).subgroupOf L := by
    rw [subgroupOf_normalizer_eq (inf_le_right : d.S ⊓ L ≤ L)]
    congr 1
    ext x
    exact ⟨fun hx => ⟨hx, x.property⟩, fun hx => hx.1⟩
  rw [he, subgroupOf_map_subtype, inf_comm]

omit [Finite G] in
/-- The outer actor itself rules out containment in the component. -/
theorem DiagonalCoordinates.actor_not_mem
    (hn : d.Yplus ≤ normalizer (L : Set G)) (y : d.Yplus)
    {F : Type*} [Field F] (w : DiagonalCoordinates L (y : G) F) : (y : G) ∉ L := by
  intro hyL
  apply w.outer
  rw [← quotientAction_eq_of_compatible hn w.e y w.conjugation _
    w.conjugation_eq w.compatible, quotientAction_on_component hn w.e y hyL]
  exact ⟨_, rfl⟩

/-- Placement via 15.3.33(1), conditional only on preservation of the actual
component Sylow by Y₊. Invariance under S follows from L = L₀. -/
theorem SourceSetup.borelPlacement_of_sylow_invariant (h : SourceSetup d I L)
    (hn : d.Yplus ≤ normalizer (L : Set G))
    {F : Type*} [Field F] [Finite F] (e : (L ⧸ pCore 2 L) ≃* PSL(3,F))
    (hfield : ∃ n : ℕ, 0 < n ∧ Nat.card F = 2 ^ n)
    (hstable : d.Yplus ≤ normalizer (d.S ⊓ L : Subgroup G)) :
    Nonempty (BorelPlacement d.Yplus d.S d.M L hn e) := by
  obtain ⟨n, hnpos, hcard⟩ := hfield
  obtain ⟨P, hP⟩ := h.quotient_sylow e
  have hSL : d.S ≤ normalizer (L : Set G) := by
    simpa only [← h.orbit_eq] using le_normalizer_conjugateSpanBy L d.S
  have hinv : d.Yplus ⊔ d.S ≤ normalizer (d.S ⊓ L : Subgroup G) :=
    sup_le hstable (le_normalizer_inf d.S.le_normalizer hSL)
  have hB := h.borel_preimage e P hP
  have hchar : generalizedFitting (L ⊓ normalizer (d.S ⊓ L : Subgroup G) : Subgroup G) =
      pCore 2 (L ⊓ normalizer (d.S ⊓ L : Subgroup G) : Subgroup G) := by
    rw [← hB]
    apply Matrix.PSL3.LinearThree.BorelStructure.sylowNormalizer_preimage_image_characteristicTwo
      F hnpos hcard (quotientMap e) (quotientMap_surjective e) _ P L.subtype L.subtype_injective
    rw [quotientMap_ker]
    exact pCore_isPGroup
  have hBM : L ⊓ normalizer (d.S ⊓ L : Subgroup G) ≤ d.M ⊓ I :=
    h.characteristic_two_containment _ inf_le_left
      (le_normalizer_inf (sup_le hn hSL)
        (hinv.trans (normalizer ((d.S ⊓ L : Subgroup G) : Set G)).le_normalizer)) hchar
  refine ⟨{ sylow := P, sylow_eq := hP, preimage_le := ?_, invariant := ?_ }⟩
  · intro l hl
    exact (hBM (hB ▸ mem_map_of_mem L.subtype hl)).1
  · intro x
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨a, ha, rfl⟩
      rw [hP] at ha ⊢
      obtain ⟨l, hl, rfl⟩ := ha
      change quotientAction hn e x (e (QuotientGroup.mk' (pCore 2 L) l)) ∈
        (d.S.subgroupOf L).map (quotientMap e)
      rw [quotientAction_apply]
      refine mem_map_of_mem (quotientMap e) ?_
      exact ((mem_normalizer_iff.mp (hstable x.property) (l : G)).mp ⟨hl, l.property⟩).1
    · exact (Subgroup.card_map_of_injective (quotientAction hn e x).injective).ge

end CFSG.Quasithin.Chapter15.Section03.Candidates.LinearCore.MatrixImage

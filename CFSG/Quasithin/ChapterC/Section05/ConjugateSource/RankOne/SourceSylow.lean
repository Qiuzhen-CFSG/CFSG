module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Setup
public import Theory.GroupTheory.SylowNormalRestriction
/-!
# The original Baumann Sylow subgroup from its marked quotient

The parameter map makes the finite field additive group a quotient of the
original two-group S, and therefore proves that the field has characteristic
two. The marked quotient KS → SL₂(F) has two-group kernel contained in S
and sends S onto the full upper-root Sylow subgroup. Its Sylow preimage is
exactly S. Normal restriction to K then gives the literal intersection S∩K.
Both assertions retain the original possibly nonsplit central cover.

Source: Aschbacher–Smith, C.5.4 and C.5.6(7), printed pp.155,159–160.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R K : Subgroup G} {F : Type*} [Field F]

/-- The original quotient identifies the same Baumann subgroup as a Sylow subgroup. -/
theorem Setup.source_sylow_join (h : Setup R K F) (hR : IsPGroup 2 R) :
    ∃ P : Sylow 2 (K ⊔ S R : Subgroup G),
      (P : Subgroup (K ⊔ S R : Subgroup G)).map (K ⊔ S R).subtype = S R := by
  let : Finite F := Finite.of_surjective
    (fun s : S R => (h.coordinates.parameter s).toAdd) h.coordinates.parameter_surjective
  let := Fintype.ofFinite F
  have hpF : IsPGroup 2 (Multiplicative F) :=
    (hR.to_le (show S R ≤ R from inf_le_left)).of_surjective
      h.coordinates.parameter h.coordinates.parameter_surjective
  obtain ⟨n,hn⟩ := hpF.exists_card_eq
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_multiplicative] using hn)
  let N := K ⊔ S R
  let Q' := (Q R K).subgroupOf N
  have hker : IsPGroup 2 h.quotient.ker := h.kernel ▸
    (isPGroup_pCoreIn 2 N).comap_subtype
  have hkerS : h.quotient.ker ≤ (S R).subgroupOf N := by
    rw [h.kernel,h.core]
    exact fun _ hh => hh.1
  let P := (Matrix.SpecialLinearGroup.upperUnipotentSylow F 2).comapOfKerIsPGroup
    h.quotient hker (h.quotient.range_eq_top.mpr h.surjective ▸ le_top)
  refine ⟨P,?_⟩
  have he : (P : Subgroup N) = (S R).subgroupOf N := by
    change (Matrix.SpecialLinearGroup.upperUnipotent F).comap h.quotient = _
    rw [← h.image]
    exact comap_map_eq_self hkerS
  rw [he,map_subgroupOf_eq_of_le (show S R ≤ N from le_sup_right)]

/-- Normal restriction gives precisely the original S∩K, including central covers. -/
theorem Setup.source_sylow_block (h : Setup R K F) (hR : IsPGroup 2 R) :
    ∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype = S R ⊓ K := by
  let N := K ⊔ S R
  have hKN : K ≤ N := le_sup_left
  let KN := K.subgroupOf N
  let : KN.Normal := (normal_subgroupOf_iff_le_normalizer hKN).mpr
    (sup_le K.le_normalizer h.normalizes)
  obtain ⟨P,hP⟩ := h.source_sylow_join hR
  obtain ⟨Q,hQ⟩ := P.exists_sylow_map_eq_inf_of_normal KN
  let e := subgroupOfEquivOfLe hKN
  let Q' := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨Q',?_⟩
  change ((Q : Subgroup KN).map e.toMonoidHom).map K.subtype = _
  calc
    _ = ((Q : Subgroup KN).map KN.subtype).map N.subtype := by
      rw [Subgroup.map_map,Subgroup.map_map]
      rfl
    _ = ((P : Subgroup N) ⊓ KN).map N.subtype := congrArg (fun A => A.map N.subtype) hQ
    _ = S R ⊓ K := by
      rw [Subgroup.map_inf _ _ _ N.subtype_injective,hP,map_subgroupOf_eq_of_le hKN]
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne

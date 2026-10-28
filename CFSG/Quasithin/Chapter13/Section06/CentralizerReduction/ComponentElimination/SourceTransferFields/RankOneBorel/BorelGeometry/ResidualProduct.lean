module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# The residual Borel has the same action on V as Lᵥ

The natural rank-one Borel has zero fixed space on the natural plane and
odd index in SL₂. Averaging through the two central layers of W_K therefore
shows that a subgroup covering the component Borel cannot fix z. The
embedded two-residual R of the constructed Borel still covers that Borel.
The earlier local bound puts its action on V inside the cubic image of Lᵥ;
nontriviality makes these images equal. Thus R C_M(V) = Lᵥ C_M(V).

The equality is for R = O²(B). No equality of the full Borel image is
inferred, and fixation modulo the v-line is not lifted to B itself.
`Assembly.source_geometry` applies the equality to the actual marked source.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.6.18, printed p.931 (PDF p.948).
-/

@[expose] public section

open Subgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups IsMulCommutative
open Matrix.SpecialLinearGroup.RankOneResidual
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry
open ComponentSelection Representation.BinaryOffender Representation.HigherFieldBorelFixedSpaces
variable {G : Type*} [Group G] [Finite G]
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Finite G] in
/-- The full component Borel has the same fixed vectors on W_K as K,
including the central layers of the specified natural section. -/
theorem source_borel_fixed_space
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]
    (s : NaturalSection (F := F) (componentRepresentation K L T z v hL hz)
      (movingSpace K L T z v))
    (hF : 2 < Nat.card F)
    (D : Subgroup (plusImage K L T z v hL hz K))
    (hD : D.map s.actor.toMonoidHom = rankOneBorel F) :
    fixedSpace (componentRepresentation K L T z v hL hz) D =
      (componentRepresentation K L T z v hL hz).invariants := by
  have hi : Odd D.index := by
    rw [← index_map_of_bijective (f := s.actor.toMonoidHom) s.actor.bijective D, hD]
    exact sl2_borel_odd_index
  let f := s.actor.toMonoidHom.comp D.subtype
  have hf : f.range = rankOneBorel F := by
    rw [MonoidHom.range_comp, range_subtype]
    exact hD
  exact odd_index_fixedSpace_extension_of_model_section _ (binaryNatural 2)
    D (rankOneBorel F) _ (movingSpace K L T z v) hi
    (displacement_mem K L T z v hL hz) le_rfl (fun a d => s.invariant a d)
    f hf s.coordinates (fun a d => s.equivariant a d) (sl2_borel_fixedSpace hF)

omit [Finite G] in
/-- Any subgroup covering the component Borel moves the source seed z.
This applies in particular to the embedded two-residual of the constructed Borel. -/
theorem not_centralizes_seed_of_borel_image
    (K L T D : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hK : K ∈ Yz L T z v) (hnorm : Tv T v ≤ normalizer (K : Set G))
    (s : NaturalSection (F := F) (componentRepresentation K L T z v hL hz)
      (movingSpace K L T z v))
    (hF : 2 < Nat.card F)
    (hD : ((D.subgroupOf K).map (componentMap K L T z v hL hz)).map
      s.actor.toMonoidHom = rankOneBorel F) :
    ¬ D ≤ centralizer ({z} : Set G) := by
  intro hfix
  have hw : Additive.ofMul (⟨z, le_conjugateSpanBy _ _ (mem_zpowers z)⟩ :
      WK K L T z v) ∈ fixedSpace (componentRepresentation K L T z v hL hz)
        ((D.subgroupOf K).map (componentMap K L T z v hL hz)) := by
    rintro ⟨b, k, hk, rfl⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    change (k : G) * z * (k : G)⁻¹ = z
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp (hfix hk))
  rw [source_borel_fixed_space K L T z v hL hz s hF _ hD] at hw
  have hzK := (invariants_iff K L T z v hL hz _).mp hw
  apply (invariant_component_consequences K L T z v hK hnorm).1.2
  apply (starPreimage_starImage_centralizes_seed_iff z v K hK.1.1).mpr
  intro k hk
  exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hzK k hk)

omit [Finite G] in
private theorem product_eq_of_cubic_action
    (R D V : Subgroup G) (z : G)
    (hR : R ≤ normalizer (V : Set G)) (hD : D ≤ normalizer (V : Set G))
    (hcard : Nat.card (conjugationAction V D hD).range = 3)
    (hbound : R ≤ D ⊔ centralizer (V : Set G))
    (hz : z ∈ V) (hmove : ¬ R ≤ centralizer ({z} : Set G)) :
    R ⊔ centralizer (V : Set G) = D ⊔ centralizer (V : Set G) := by
  let N := normalizer (V : Set G)
  let f := V.normalizerMonoidHom
  let C := (R.subgroupOf N).map f
  let E := (D.subgroupOf N).map f
  have hE : E = (conjugationAction V D hD).range := by
    ext x
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact ⟨⟨d, hd⟩, rfl⟩
    · rintro ⟨d, rfl⟩
      exact ⟨⟨d, hD d.property⟩, d.property, rfl⟩
  have hCE : C ≤ E := by
    apply map_le_iff_le_comap.mpr
    rw [comap_map_eq]
    intro r hr
    rw [normalizerMonoidHom_ker, ← subgroupOf_sup hD (Subgroup.centralizer_le_normalizer _)]
    exact hbound hr
  have hCne : C ≠ ⊥ := by
    intro he
    have hh : R.subgroupOf N ≤ f.ker := (Subgroup.map_eq_bot_iff _).mp he
    rw [normalizerMonoidHom_ker] at hh
    apply hmove
    intro r hr
    exact (centralizer_le (Set.singleton_subset_iff.mpr hz))
      (hh (show (⟨r, hR hr⟩ : N) ∈ R.subgroupOf N from hr))
  let : Fact (Nat.card E).Prime := ⟨by rw [hE, hcard]; exact Nat.prime_three⟩
  have heq : C = E := by
    rcases (C.subgroupOf E).eq_bot_or_eq_top_of_prime_card with hb | ht
    · have he := congrArg (Subgroup.map E.subtype) hb
      rw [map_subgroupOf_eq_of_le hCE, Subgroup.map_bot] at he
      exact (hCne he).elim
    · have he := congrArg (Subgroup.map E.subtype) ht
      rw [map_subgroupOf_eq_of_le hCE, ← MonoidHom.range_eq_map, range_subtype] at he
      exact he
  have he := map_eq_map_iff.mp heq
  have hm := congrArg (Subgroup.map N.subtype) he
  dsimp only [f, N] at hm
  simpa only [Subgroup.map_sup, map_subgroupOf_eq_of_le hR, map_subgroupOf_eq_of_le hD,
    normalizerMonoidHom_ker, map_subgroupOf_eq_of_le (_root_.centralizer_le_normalizer V)] using hm

/-- The source product equality holds for O²(B). It is obtained from the
literal natural-section Borel image and the cubic action, rather than assumed. -/
theorem residual_product_eq_of_local_source
    (K L T M V B : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hK : K ∈ Yz L T z v) (hnorm : Tv T v ≤ normalizer (K : Set G))
    (s : NaturalSection (F := F) (componentRepresentation K L T z v hL hz)
      (movingSpace K L T z v))
    (hF : 4 ≤ Nat.card F)
    (hB : ((B.subgroupOf K).map (componentMap K L T z v hL hz)).map
      s.actor.toMonoidHom = rankOneBorel F)
    (hBM : B ≤ Mv M v)
    (hBV : Mv M v ≤ normalizer (V : Set G))
    (hLV : Lv L v ≤ normalizer (V : Set G))
    (hMV : normalizer (V : Set G) ≤ M)
    (hcard : Nat.card (conjugationAction V (Lv L v) hLV).range = 3)
    (hzV : z ∈ V)
    (hlocal : (pResidual 2 (Mv M v)).map (Mv M v).subtype ≤
      Lv L v ⊔ (M ⊓ centralizer (V : Set G))) :
    (pResidual 2 B).map B.subtype ⊔ (M ⊓ centralizer (V : Set G)) =
      Lv L v ⊔ (M ⊓ centralizer (V : Set G)) := by
  let R := (pResidual 2 B).map B.subtype
  have hRB : R ≤ B := map_subtype_le _
  have hRC : ((R.subgroupOf K).map (componentMap K L T z v hL hz)).map
      s.actor.toMonoidHom = rankOneBorel F := by
    rw [map_map] at hB ⊢
    exact residual_borel_image B K _ hF hB
  have hm := map_mono (f := (Mv M v).subtype)
    (map_pResidual_le 2 (inclusion hBM))
  rw [map_map, subtype_comp_inclusion] at hm
  have hC : M ⊓ centralizer (V : Set G) = centralizer (V : Set G) :=
    inf_eq_right.mpr ((_root_.centralizer_le_normalizer V).trans hMV)
  rw [hC] at hlocal ⊢
  exact product_eq_of_cubic_action R (Lv L v) V z (hRB.trans (hBM.trans hBV)) hLV
    hcard (hm.trans hlocal) hzV
    (not_centralizes_seed_of_borel_image K L T R z v hL hz hK hnorm s (by omega) hRC)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry

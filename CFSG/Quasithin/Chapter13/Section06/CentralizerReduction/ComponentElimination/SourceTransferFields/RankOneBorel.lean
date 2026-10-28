module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules
public import Theory.SpecificGroups.SL2.EvenBorelResidual.NaturalFixed
public import Theory.Representation.ElementaryAbelianAction

/-!
# The higher-field natural-action calculation in 13.6.18

The representation is the literal plus action on W_K, and its moving space
is [W_K,K]. A single equivariant identification of U_K/C_{U_K}(K) with
the natural plane lets the concrete residual calculation lift through the
central layers. Residual functoriality transports fixation from the ambient
Borel to the Borel in K⁺. The resulting fixed seed contradicts membership
in the actual ComponentSelection.Yz family.

The final local application derives residual centralization from the
order-three action of L_v and the earlier bound on O²(C_M(v)). It leaves
the natural-section identification and construction of the marked Borel
explicit. Minimal block replacement, Borel placement and the field-four
block-centralization argument remain separate obligations. This module
does not assert the full source Lemma 13.6.18.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
printed p.931 (PDF p.948), proof of 13.6.18.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel
open Subgroup ComponentSelection
open scoped IsMulCommutative commutatorElement
open Representation.BinaryOffender
open Matrix.SpecialLinearGroup.RankOneResidual
variable {G : Type*} [Group G]
variable (K L T : Subgroup G) (z v : G)
variable (hL : Tv T v ≤ normalizer (Lv L v : Set G))
variable (hz : Tv T v ≤ centralizer ({z} : Set G))
local notation "Kp" => plusImage K L T z v hL hz K
local notation "W" => WK K L T z v

/-- The literal component map into its plus action image. -/
def componentMap : K →* Kp :=
  ((plusMk K L T z v hL hz).comp (inclusion (K_le_plusActor K L T v))).codRestrict Kp
    (fun k => mem_map.mpr ⟨⟨k, K_le_plusActor K L T v k.property⟩, k.property, rfl⟩)

theorem componentMap_surjective : Function.Surjective (componentMap K L T z v hL hz) := by
  rintro ⟨x, y, hy, rfl⟩
  exact ⟨⟨y, hy⟩, rfl⟩

variable [IsElementaryAbelian 2 (WK K L T z v)]

/-- The binary representation is induced by the actual plus action on W_K. -/
noncomputable def componentRepresentation : Representation (ZMod 2) Kp (Additive W) := by
  let a := (plusAction K L T z v hL hz).comp (Kp).subtype
  let _ := MulDistribMulAction.compHom W a
  exact Representation.ofElementaryAbelianAction

/-- The literal commutator U_K=[W_K,K], as a binary subspace of W_K. -/
noncomputable def movingSpace : Submodule (ZMod 2) (Additive W) :=
  AddSubgroup.toZModSubmodule 2 ((⁅W, K⁆).subgroupOf W).toAddSubgroup

theorem componentRepresentation_mk (k : K) (w : W) :
    (((componentRepresentation K L T z v hL hz
      (componentMap K L T z v hL hz k) (Additive.ofMul w)).toMul : W) : G) =
        (k : G) * (w : G) * (k : G)⁻¹ := rfl

/-- The quotient W_K/U_K is fixed, directly from the commutator definition. -/
theorem displacement_mem (a : Kp) (w : Additive W) :
    componentRepresentation K L T z v hL hz a w - w ∈ movingSpace K L T z v := by
  obtain ⟨k, rfl⟩ := componentMap_surjective K L T z v hL hz a
  change ((k : G) * (w.toMul : G) * (k : G)⁻¹) / (w.toMul : G) ∈ ⁅W, K⁆
  rw [div_eq_mul_inv, commutator_comm]
  exact commutator_mem_commutator k.property w.toMul.property

variable [Finite G]

/-- The higher-field calculation on the source's exact W_K and U_K.
The natural section and the actual Borel image are explicit construction
premises; neither is supplied by this conditional application. -/
theorem source_fixed_space {F : Type*} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] {n : ℕ} (hn : 2 < n) (hF : Nat.card F = 2 ^ n)
    (s : NaturalSection (F := F) (componentRepresentation K L T z v hL hz)
      (movingSpace K L T z v))
    (B : Subgroup Kp) (hB : B.map s.actor.toMonoidHom = Matrix.SpecialLinearGroup.rankOneBorel F) :
    fixedSpace (componentRepresentation K L T z v hL hz)
      ((piResidual twoThreePrimes B).map B.subtype) =
        (componentRepresentation K L T z v hL hz).invariants :=
  fixedSpace_residual_eq_invariants hn hF _ _ s (displacement_mem K L T z v hL hz) B hB

omit [Finite G] in
/-- Fixed vectors in the faithful plus image mean ambient centralization. -/
theorem invariants_iff (w : W) :
    Additive.ofMul w ∈ (componentRepresentation K L T z v hL hz).invariants ↔
      (w : G) ∈ centralizer (K : Set G) := by
  constructor
  · intro hw k hk
    have he := congrArg (fun x : Additive W => (x.toMul : G))
      (hw (componentMap K L T z v hL hz ⟨k, hk⟩))
    exact mul_inv_eq_iff_eq_mul.mp he
  · intro hw a
    obtain ⟨k, rfl⟩ := componentMap_surjective K L T z v hL hz a
    apply Additive.toMul.injective
    apply Subtype.ext
    change (k : G) * (w : G) * (k : G)⁻¹ = (w : G)
    rw [mem_centralizer_iff.mp hw k k.property, mul_inv_cancel_right]

/-- An actual ambient residual bound gives fixation by its plus-image residual. -/
theorem residual_fixes_seed (B : Subgroup G)
    (hfix : (piResidual twoThreePrimes B).map B.subtype ≤ centralizer ({z} : Set G)) :
    Additive.ofMul (⟨z, le_conjugateSpanBy _ _ (mem_zpowers z)⟩ : W) ∈
      fixedSpace (componentRepresentation K L T z v hL hz)
        ((piResidual twoThreePrimes
          ((B.subgroupOf K).map (componentMap K L T z v hL hz))).map
            ((B.subgroupOf K).map (componentMap K L T z v hL hz)).subtype) := by
  let f := componentMap K L T z v hL hz
  let C := B.subgroupOf K
  let r : C →* B := {
    toFun x := ⟨x.val.val, x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hmap := map_embedded_piResidual twoThreePrimes C f
  intro b
  have hb : (b : Kp) ∈ ((piResidual twoThreePrimes C).map C.subtype).map f := by
    rw [hmap]
    exact b.property
  obtain ⟨x, hx, he⟩ := hb
  change componentRepresentation K L T z v hL hz (b : Kp) _ = _
  rw [← he]
  obtain ⟨y, hy, rfl⟩ := hx
  have hyr : r y ∈ piResidual twoThreePrimes B :=
    map_piResidual_le twoThreePrimes r (mem_map_of_mem r hy)
  have hyc := hfix (mem_map_of_mem B.subtype hyr)
  apply Additive.toMul.injective
  apply Subtype.ext
  change (y.val.val : G) * z * (y.val.val : G)⁻¹ = z
  have he := mem_centralizer_singleton_iff.mp hyc
  change (y.val.val : G) * z = z * (y.val.val : G) at he
  rw [he, mul_inv_cancel_right]

/-- The large-field branch of 13.6.18 once its natural section and Borel
have been constructed. The moving condition is the actual Y_z condition. -/
theorem degree_le_two_of_source_action {F : Type*} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hK : K ∈ Yz L T z v) (hnorm : Tv T v ≤ normalizer (K : Set G))
    (s : NaturalSection (F := F) (componentRepresentation K L T z v hL hz)
      (movingSpace K L T z v))
    (B : Subgroup G)
    (hB : ((B.subgroupOf K).map (componentMap K L T z v hL hz)).map
      s.actor.toMonoidHom = Matrix.SpecialLinearGroup.rankOneBorel F)
    (hfix : (piResidual twoThreePrimes B).map B.subtype ≤ centralizer ({z} : Set G)) :
    n ≤ 2 := by
  by_contra hn
  have hfixed := residual_fixes_seed K L T z v hL hz B hfix
  rw [source_fixed_space K L T z v hL hz (by omega) hF s _ hB] at hfixed
  have hzK := (invariants_iff K L T z v hL hz _).mp hfixed
  have hmove := (invariant_component_consequences K L T z v hK hnorm).1.2
  apply hmove
  apply (starPreimage_starImage_centralizes_seed_iff z v K hK.1.1).mpr
  intro k hk
  exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hzK k hk)
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel
open Subgroup ComponentSelection
variable {G : Type*} [Group G] [Finite G]

/-- The local cubic action and the two-residual bound kill the actual
{2,3}-residual on V. All centralizers are the kernels of conjugation on V. -/
theorem residual_centralizes_of_cubic_action
    (B D V : Subgroup G)
    (hB : B ≤ normalizer (V : Set G)) (hD : D ≤ normalizer (V : Set G))
    (hcard : Nat.card (conjugationAction V D hD).range = 3)
    (hbound : (pResidual 2 B).map B.subtype ≤ D ⊔ centralizer (V : Set G)) :
    (piResidual twoThreePrimes B).map B.subtype ≤ centralizer (V : Set G) := by
  let N := normalizer (V : Set G)
  let f := conjugationAction V B hB
  let d := conjugationAction V D hD
  have hpi : IsPiGroup twoThreePrimes d.range := by
    apply (IsPiGroup_iff _ _).mpr
    intro p hp
    rw [hcard] at hp
    exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp hp |>.resolve_left p.property.ne_one)
  have himage : (pResidual 2 B).map f ≤ d.range := by
    rintro _ ⟨b, hb, rfl⟩
    have hc : (b : G) ∈ D ⊔ centralizer (V : Set G) := hbound (mem_map_of_mem B.subtype hb)
    let bN : N := ⟨b, hB b.property⟩
    have hcN : bN ∈ D.subgroupOf N ⊔ (centralizer (V : Set G)).subgroupOf N := by
      rw [← subgroupOf_sup hD (Subgroup.centralizer_le_normalizer _)]
      exact hc
    obtain ⟨dN, hdN, cN, hcN, he⟩ := mem_sup_of_normal_right.mp hcN
    refine ⟨⟨dN, hdN⟩, ?_⟩
    change V.normalizerMonoidHom dN = V.normalizerMonoidHom bN
    rw [← he, map_mul]
    have hz : V.normalizerMonoidHom cN = 1 := by
      change cN ∈ V.normalizerMonoidHom.ker
      rw [normalizerMonoidHom_ker]
      exact hcN
    rw [hz, mul_one]
  have hker := piResidual_le_ker_of_twoResidual_image twoThreePrimes (Or.inl rfl)
    f d.range hpi himage
  rw [conjugationAction_ker] at hker
  rintro _ ⟨b, hb, rfl⟩
  exact hker hb
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel
open Subgroup ComponentSelection
open scoped IsMulCommutative
open Matrix.SpecialLinearGroup.RankOneResidual
variable {G : Type*} [Group G] [Finite G]

/-- The higher-field branch consumes the actual local two-residual bound
and the order-three conjugation image of L_v. In particular the prime-set
residual centralization is derived, rather than supplied as a premise. -/
theorem degree_le_two_of_local_source
    (K L T M V : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hK : K ∈ Yz L T z v) (hnorm : Tv T v ≤ normalizer (K : Set G))
    (s : NaturalSection (F := F) (componentRepresentation K L T z v hL hz)
      (movingSpace K L T z v))
    (B : Subgroup G) (hBM : B ≤ Mv M v)
    (hBV : Mv M v ≤ normalizer (V : Set G))
    (hLV : Lv L v ≤ normalizer (V : Set G))
    (hcard : Nat.card (conjugationAction V (Lv L v) hLV).range = 3)
    (hzV : z ∈ V)
    (hlocal : (pResidual 2 (Mv M v)).map (Mv M v).subtype ≤
      Lv L v ⊔ (M ⊓ centralizer (V : Set G)))
    (hB : ((B.subgroupOf K).map (componentMap K L T z v hL hz)).map
      s.actor.toMonoidHom = Matrix.SpecialLinearGroup.rankOneBorel F) : n ≤ 2 := by
  have hres : (pResidual 2 B).map B.subtype ≤
      Lv L v ⊔ centralizer (V : Set G) := by
    have hm := map_mono (f := (Mv M v).subtype)
      (map_pResidual_le 2 (inclusion hBM))
    rw [map_map, subtype_comp_inclusion] at hm
    exact hm.trans (hlocal.trans (sup_le_sup_left inf_le_right _))
  have hfix := residual_centralizes_of_cubic_action B (Lv L v) V
    (hBM.trans hBV) hLV hcard hres
  exact degree_le_two_of_source_action K L T z v hL hz hF hK hnorm s B hB
    (hfix.trans (centralizer_le (Set.singleton_subset_iff.mpr hzV)))
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel

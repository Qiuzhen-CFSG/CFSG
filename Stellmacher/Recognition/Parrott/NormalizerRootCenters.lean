module

public import Stellmacher.Recognition.Parrott.NormalizerRootSets
public import Stellmacher.Recognition.Parrott.NormalizerFusion

/-!
# The central involution in Parrott's root-image formula

If i is an involution in N_G(F) outside its two-core K, the subgroup
⟨K,i⟩ has order 2048. It is therefore a Sylow two-subgroup of G.
Sylow conjugacy transports the known center of order two, supplying a
central generator ε. Self-centralization of F places ε in F.

The center and its generator are embedded literally in G. These facts
supply the central twist used by the four involution-image families,
without assuming any root census or later normalizer generator equations.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.682, the sixteen-root paragraph, using the Sylow structure on p.672.
-/

open Subgroup
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : ParrottSecondElementaryData z}

/-- Adjoining an outside normalizer involution gives a Sylow two-subgroup,
whose center consequently has order two. -/
public theorem ParrottNormalizerFusionData.normalizer_join_center_card (n : ParrottNormalizerFusionData e) (h : ParrottCentralizerHypotheses z)
    (i : G) (hiN : i ∈ normalizer (e.F : Set G))
    (hiK : i ∉ (pCore 2 (normalizer (e.F : Set G))).map
      (normalizer (e.F : Set G)).subtype) (hi2 : orderOf i = 2) :
    let N := normalizer (e.F : Set G)
    let K := (pCore 2 N).map N.subtype
    Nat.card (center (K ⊔ zpowers i : Subgroup G)) = 2 := by
  intro N K
  let S := K ⊔ zpowers i
  have hKcard : Nat.card K = 1024 :=
    (card_map_of_injective N.subtype_injective).trans n.core_card
  have hiKn : i ∈ normalizer (K : Set G) :=
    mem_normalizer_iff''.mpr (fun g => (e.normalizer_core_conj_mem_iff i hiN g).symm)
  have hScard : Nat.card S = 2048 := by
    rw [show S = K ⊔ zpowers i from rfl,
      card_sup_zpowers_of_normalizing_involution K i
        (hi2 ▸ pow_orderOf_eq_one i) hiK hiKn, hKcard]
  have hSp : IsPGroup 2 S := IsPGroup.of_card (n := 11) hScard
  obtain ⟨R, hSR⟩ := hSp.exists_le_sylow
  have hRcard : Nat.card R = 2048 :=
    (Nat.card_congr (Sylow.equiv R e.sylow).toEquiv).trans (e.sylow_card h)
  have hSeq : S = (R : Subgroup G) := eq_of_le_of_card_ge hSR (by rw [hRcard, hScard])
  have he := (MulEquiv.subgroupCongr hSeq).trans (Sylow.equiv R e.sylow)
  exact (Nat.card_congr (Subgroup.centerCongr he).toEquiv).trans (e.sylow_center_card h)

/-- Every outside normalizer involution has the central generator required
by the root-image formula; the generator is itself an involution in F. -/
public theorem ParrottNormalizerFusionData.exists_normalizer_join_center_generator
    (n : ParrottNormalizerFusionData e) (h : ParrottCentralizerHypotheses z)
    (i : G) (hiN : i ∈ normalizer (e.F : Set G))
    (hiK : i ∉ (pCore 2 (normalizer (e.F : Set G))).map
      (normalizer (e.F : Set G)).subtype) (hi2 : orderOf i = 2) :
    let N := normalizer (e.F : Set G)
    let K := (pCore 2 N).map N.subtype
    ∃ ε : G, orderOf ε = 2 ∧ ε ∈ e.F ∧
      zpowers ε = (center (K ⊔ zpowers i : Subgroup G)).map (K ⊔ zpowers i).subtype := by
  intro N K
  let S := K ⊔ zpowers i
  let Z := (center S).map S.subtype
  have hZcard : Nat.card Z = 2 :=
    (card_map_of_injective S.subtype_injective).trans
      (n.normalizer_join_center_card h i hiN hiK hi2)
  let : IsCyclic Z := isCyclic_of_prime_card hZcard
  obtain ⟨ε, hε⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic Z)
  have hgen : zpowers (ε : G) = Z := by
    have hh := congrArg (Subgroup.map Z.subtype) hε
    rw [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, range_subtype] at hh
    exact hh
  refine ⟨ε, ?_, e.normalizer_join_center_le_elementary i ε.property, hgen⟩
  rw [← Nat.card_zpowers, hgen]
  exact hZcard

end Stellmacher.Recognition

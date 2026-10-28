module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityActionRecognition

public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# The literal equality-action normalizers

The layer image in H/O₂(H) has order two. The inverse image of the
source line in U/⟨z⟩ is exactly Z_S, so its stabilizer normalizes the
actual layer. Conversely, normalizing the order-two actor image preserves
its displacement line. This gives the full inverse-image normalizer
identity used to lift pairs from the classified action.

In particular O₂(H) normalizes every H-conjugate of the layer. The known
order-eight core intersection then supplies the index-two premise of
6.2.6 whenever the two conjugates fail to normalize each other.

Source: Aschbacher--Smith, 6.2.13, printed p.687 (PDF p.704).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open M22Recognition.CentralizerExtension
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

theorem LocalAnalysis.equalityActorImage_card
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) :
    Nat.card (equalityActorImage z (layer L R)) = 2 := by
  let H := centralizer ({z} : Set G)
  let B := (layer L R).subgroupOf H
  have hVH := layer_le_involution_centralizer h611 hz
  have hB : Nat.card B = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVH).toEquiv).trans hnatural.2.1.card
  have hI : Nat.card (pCore 2 H ⊓ B : Subgroup H) = 8 := by
    rw [← card_map_of_injective H.subtype_injective, Subgroup.map_inf _ _ _ H.subtype_injective,
      map_subgroupOf_eq_of_le hVH, inf_comm]
    exact A.layer_core_card
  have hc := (relIndex_mul_relIndex (⊥ : Subgroup H) (pCore 2 H ⊓ B) B
    bot_le inf_le_right)
  rw [relIndex_bot_left, relIndex_bot_left, hI, hB, inf_relIndex_right] at hc
  have hi := relIndex_ker B (QuotientGroup.mk' (pCore 2 H))
  rw [QuotientGroup.ker_mk'] at hi
  change (pCore 2 H).relIndex B = Nat.card (equalityActorImage z (layer L R)) at hi
  rw [hi] at hc
  omega

omit [Finite G] in
/-- The quotient line has precisely the source plane as its inverse image in U. -/
theorem equalityDistinguishedLine_preimage
    (hz : z ∈ ZS (T : Subgroup G) L R)
    (u : equalityClosure (T : Subgroup G) L R z) :
    QuotientGroup.mk' _ u ∈ equalityDistinguishedLine (T : Subgroup G) L R z ↔
      u.val ∈ equalityPlane (T : Subgroup G) L R z := by
  change u ∈ (((equalityPlane (T : Subgroup G) L R z).subgroupOf
    (equalityClosure (T : Subgroup G) L R z)).map (QuotientGroup.mk' _)).comap
      (QuotientGroup.mk' _) ↔ _
  rw [QuotientGroup.comap_map_mk', sup_eq_right.mpr]
  · rfl
  · exact fun _ hx => (zpowers_le.mpr hz) hx

/-- Preserving the literal quotient line is equivalent to normalizing Z_S. -/
theorem equalityQuotientAction_preserves_line_iff
    (h611 : Hypothesis611 κ T L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R)
    (h : centralizer ({z} : Set G)) :
    (∀ w ∈ equalityDistinguishedLine (T : Subgroup G) L R z,
      equalityQuotientAction (T : Subgroup G) L R z h w ∈
        equalityDistinguishedLine (T : Subgroup G) L R z) ↔
      (h : G) ∈ normalizer (ZS (T : Subgroup G) L R : Set G) := by
  have hSH : ZS (T : Subgroup G) L R ≤ centralizer ({z} : Set G) :=
    inf_le_left.trans (layer_le_involution_centralizer h611 hz)
  constructor
  · intro hp
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro _ ⟨s, hs, rfl⟩
      let sH : centralizer ({z} : Set G) := ⟨s, hSH hs⟩
      let sU : equalityClosure (T : Subgroup G) L R z := ⟨sH, sourceEight_contains _ hs⟩
      have hh := hp (QuotientGroup.mk' _ sU) (mem_map_of_mem _ hs)
      rw [equalityQuotientAction_mk, equalityDistinguishedLine_preimage hz] at hh
      exact hh
    · rw [card_map_of_injective (MulAut.conj (h : G)).injective]
  · intro hn w hw
    obtain ⟨s, hs, rfl⟩ := hw
    rw [equalityQuotientAction_mk, equalityDistinguishedLine_preimage hz]
    exact (mem_normalizer_iff.mp hn s.val.val).mp hs

/-- O₂(H) normalizes the actual layer, by its action on U/⟨z⟩ and 6.2.1. -/
theorem LocalAnalysis.equalityCoreH_normalizes_layer
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) :
    (centralizer ({z} : Set G)).pCoreIn 2 ≤ normalizer (layer L R : Set G) := by
  rintro _ ⟨x, hx, rfl⟩
  apply A.normalizer_plane
  apply (equalityQuotientAction_preserves_line_iff h611 hz x).mp
  have he : equalityQuotientAction (T : Subgroup G) L R z x = 1 := by
    apply MonoidHom.mem_ker.mp
    rwa [A.equalityQuotientAction_ker]
  intro w hw
  simpa only [he, MulAut.one_apply] using hw

/-- A source-line stabilizer normalizes the actual order-two actor image. -/
theorem LocalAnalysis.equality_line_stabilizer_normalizes_image
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R)
    [IsElementaryAbelian 2 (EqualityVectorQuotient (T : Subgroup G) L R z)]
    (a : EqualityActor z)
    (ha : ∀ w ∈ equalityVectorSubspace (T := (T : Subgroup G)) (L := L) (R := R) (z := z),
      equalityRepresentation A a w ∈ equalityVectorSubspace) :
    a ∈ normalizer (equalityActorImage z (layer L R) : Set (EqualityActor z)) := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ a
  have hN : (h : G) ∈ normalizer (layer L R : Set G) := by
    apply A.normalizer_plane
    apply (equalityQuotientAction_preserves_line_iff h611 hz h).mp
    intro w hw
    exact ha (Additive.ofMul w) hw
  apply ((layer L R).subgroupOf (centralizer ({z} : Set G))).le_normalizer_map
    (QuotientGroup.mk' _)
  apply mem_map_of_mem
  rw [← subgroupOf_normalizer_eq (layer_le_involution_centralizer h611 hz)]
  exact hN

/-- The source-line stabilizer fixes the unique nonidentity layer image. -/
theorem LocalAnalysis.equality_line_stabilizer_fixes_mark
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R)
    [IsElementaryAbelian 2 (EqualityVectorQuotient (T : Subgroup G) L R z)]
    (a : EqualityActor z) (ha : a ∈ equalityActorImage z (layer L R)) (ha1 : a ≠ 1)
    (b : EqualityActor z)
    (hb : ∀ w ∈ equalityVectorSubspace (T := (T : Subgroup G)) (L := L) (R := R) (z := z),
      equalityRepresentation A b w ∈ equalityVectorSubspace) : b * a * b⁻¹ = a := by
  have hn := A.equality_line_stabilizer_normalizes_image h611 hz b hb
  have hc := A.equalityActorImage_card h611 hnatural hz
  have hba := (mem_normalizer_iff.mp hn a).mp ha
  suffices (⟨b * a * b⁻¹, hba⟩ : equalityActorImage z (layer L R)) = ⟨a, ha⟩ from
    congrArg Subtype.val this
  apply ((Nat.card_eq_two_iff' (1 : equalityActorImage z (layer L R))).mp hc).unique
  · intro he
    apply ha1
    exact (MulAut.conj b).injective ((congrArg Subtype.val he).trans (map_one _).symm)
  · exact fun he => ha1 (congrArg Subtype.val he)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open Subgroup Module
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- The full inverse image of the order-two actor normalizer normalizes the
actual layer. This is the point-normalizer identity used to lift model pairs. -/
theorem LocalAnalysis.equalityActorImage_normalizer_preimage
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R =
      ZS (T : Subgroup G) L R) :
    (normalizer (equalityActorImage z (layer L R) : Set (EqualityActor z))).comap
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) =
      (normalizer (layer L R : Set G)).subgroupOf (centralizer ({z} : Set G)) := by
  let := A.sourceEqualityVectorQuotient_elementary h611 hz
  let ρ := equalityRepresentation A
  obtain ⟨a, ha, ha1, _⟩ := A.exists_equalityCentralMark h611 hnatural hz hTH
  have hSH : ZS (T : Subgroup G) L R ≤ centralizer ({z} : Set G) :=
    inf_le_left.trans (layer_le_involution_centralizer h611 hz)
  have hcard := (h611.natural_ZS_geometry hnatural).2.1
  have hline := equalityDisplacement_eq_line A
    (A.layer_closure_commutator_eq_plane h611 hnatural hz hTH hbranch).le
    hSH hz horder hcard a ha ha1
  ext h
  constructor
  · intro hn
    have hc := normalizer_le_centralizer_of_card_two (equalityActorImage z (layer L R))
      (A.equalityActorImage_card h611 hnatural hz) hn a ha
    let b : EqualityActor z := QuotientGroup.mk' _ h
    have he : ρ a * ρ b = ρ b * ρ a := by
      rw [← map_mul, ← map_mul]
      exact congrArg ρ hc
    have hstable : ∀ w ∈ equalityVectorSubspace
        (T := (T : Subgroup G)) (L := L) (R := R) (z := z),
        ρ b w ∈ equalityVectorSubspace := by
      intro w hw
      rw [← hline] at hw ⊢
      obtain ⟨u, rfl⟩ := hw
      refine ⟨ρ b u, ?_⟩
      simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub]
      exact congrArg (fun F : Module.End (ZMod 2)
        (Additive (EqualityVectorQuotient (T : Subgroup G) L R z)) => F u - ρ b u) he
    apply A.normalizer_plane
    apply (equalityQuotientAction_preserves_line_iff h611 hz h).mp
    intro w hw
    exact hstable (Additive.ofMul w) hw
  · intro hn
    apply ((layer L R).subgroupOf (centralizer ({z} : Set G))).le_normalizer_map
      (QuotientGroup.mk' _)
    apply mem_map_of_mem
    rw [← subgroupOf_normalizer_eq (layer_le_involution_centralizer h611 hz)]
    exact hn

/-- The source two-core normalizes every H-conjugate of the layer. -/
theorem LocalAnalysis.equalityCoreH_normalizes_conjugate
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R)
    (g : G) (hg : g ∈ centralizer ({z} : Set G)) :
    (centralizer ({z} : Set G)).pCoreIn 2 ≤
      normalizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G) := by
  have hQ := mem_normalizer_iff_map_conj_eq.mp
    (((centralizer ({z} : Set G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _
        (pCore 2 (centralizer ({z} : Set G))))) hg)
  have hm := map_mono (f := (MulAut.conj g).toMonoidHom)
    (A.equalityCoreH_normalizes_layer h611 hz)
  change ((centralizer ({z} : Set G)).pCoreIn 2).map (MulAut.conj g).toMonoidHom =
    (centralizer ({z} : Set G)).pCoreIn 2 at hQ
  rwa [hQ, map_equiv_normalizer_eq] at hm

/-- Failure of mutual normalization gives the exact index-two premise
of 6.2.6; the known order-eight core intersection supplies the bound. -/
theorem LocalAnalysis.equality_pair_normalizer_relIndex
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R)
    (g : G) (hg : g ∈ centralizer ({z} : Set G))
    (hn : ¬ layer L R ≤ normalizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G)) :
    (layer L R ⊓ normalizer
      ((layer L R).map (MulAut.conj g).toMonoidHom : Set G)).relIndex (layer L R) = 2 := by
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G)
    (layer L R ⊓ (centralizer ({z} : Set G)).pCoreIn 2) (layer L R) bot_le inf_le_left
  rw [relIndex_bot_left, relIndex_bot_left, A.layer_core_card, hnatural.2.1.card] at hc
  have hi : (layer L R ⊓ (centralizer ({z} : Set G)).pCoreIn 2).relIndex (layer L R) = 2 := by
    norm_num at hc
    omega
  have hd := relIndex_dvd_of_le_left (layer L R)
    (inf_le_inf_left (layer L R) (A.equalityCoreH_normalizes_conjugate h611 hz g hg))
  rw [hi] at hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · exact (hn ((relIndex_eq_one.mp h).trans inf_le_right)).elim
  · exact h

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

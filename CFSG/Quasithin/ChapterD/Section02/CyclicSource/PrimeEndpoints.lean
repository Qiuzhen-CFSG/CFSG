module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.PrimeSource
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.NormalizerEndpoint
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.LocalGeneration

/-!
# The complete prime branches D.2.23 and D.2.24

The actual commutator of the prime core with a starred actor has prime order
and saturated support. Canonical support separation makes it normal and
fully moved; the binary normalizer theorem then proves the missing global
join and commutator identities. Each branch returns a concrete witness for
the endpoint classification on the original action.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped ENNReal
namespace CFSG.Quasithin.ChapterD.CyclicSource
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

omit [Finite G] in
private theorem generator_is_small (h : CoreHypotheses ρ)
    {A : Subgroup G} (hA : A ∈ QhatStar ρ) {t : G}
    (ht : orderOf t = 2) (he : zpowers t = A) : t ∈ smallSupportInvolutions ρ := by
  refine ⟨ht,?_⟩
  change Module.finrank (ZMod 2) (ρ t - LinearMap.id).range ≤ 2
  rw [← fixedCodim_zpowers_eq_displacement_rank,he]
  exact_mod_cast (starred_codimension ρ hA (h.rank_one A hA)).trans_le h.ratio_le

/-- Complete D.2.23: no extra generation premise is imposed. -/
theorem five_core_localGeneration (h : Hypotheses ρ)
    {A : Subgroup G} (hA : A ∈ QhatStar ρ) (hm : ⁅pCore 5 G,A⁆ ≠ ⊥) :
    Nonempty (LocalGeneration ρ) := by
  obtain ⟨_,hn,hc,hmove,hdim⟩ := five_core_full_support ρ h hA hm
  let D := (⁅pCore 5 G,A⁆ : Subgroup G)
  let : D.Normal := hn
  obtain ⟨t,ht,he⟩ := starred_generator ρ hA (h.rank_one A hA)
  have hsmall := generator_is_small ρ h.toCoreHypotheses hA ht he
  obtain ⟨hgen,hcomm⟩ := h.toCoreHypotheses.five_normalizer_endpoint D hc hdim t hsmall
  refine ⟨{
    kernel := D
    normal := hn
    prime := 5
    prime_prime := by decide
    prime_odd := by decide
    pgroup := IsPGroup.of_card (n := 1) (by simpa using hc)
    nontrivial := hm
    involution := t
    order_two := ht
    generated := hgen
    commutator := hcomm
    moved := hmove
    codimension := ?_
  }⟩
  rw [fixedCodim_zpowers_eq_displacement_rank]
  exact hsmall.2

/-- Complete D.2.24, using an attained original starred actor. -/
theorem ratio_one_localGeneration (h : Hypotheses ρ) (hq : cubicRatio ρ = 1) :
    Nonempty (LocalGeneration ρ) := by
  obtain ⟨A,hA⟩ := (QhatStar_nonempty_iff ρ).mpr h.ratio_le
  obtain ⟨hn,hc,hmove,hdim⟩ := ratio_one_full_support ρ h hq hA
  let D := (⁅pCore 3 G,A⁆ : Subgroup G)
  let : D.Normal := hn
  obtain ⟨t,ht,he⟩ := starred_generator ρ hA (h.rank_one A hA)
  have hsmall := generator_is_small ρ h.toCoreHypotheses hA ht he
  obtain ⟨hgen,hcomm⟩ := h.toCoreHypotheses.three_normalizer_endpoint D hc hdim t hsmall
  refine ⟨{
    kernel := D
    normal := hn
    prime := 3
    prime_prime := by decide
    prime_odd := by decide
    pgroup := IsPGroup.of_card (n := 1) (by simpa using hc)
    nontrivial := ?_
    involution := t
    order_two := ht
    generated := hgen
    commutator := hcomm
    moved := hmove
    codimension := ?_
  }⟩
  · intro he
    have hh : Nat.card D = 1 := Subgroup.card_eq_one.mpr he
    have hh₃ : Nat.card D = 3 := hc
    omega
  · rw [fixedCodim_zpowers_eq_displacement_rank]
    exact hsmall.2

end CFSG.Quasithin.ChapterD.CyclicSource

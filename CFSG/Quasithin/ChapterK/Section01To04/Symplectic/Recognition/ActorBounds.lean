module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Cover
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
public import Theory.Representation.CharacteristicTwoIrreducibleRank
public import Theory.GroupTheory.PrimeRankHom
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms.Basic

/-!
# A bounded cubic actor in the actual K.3.4 ambient group

The inner symplectic group has two-rank 3r and the full outer group is cyclic.
Consequently the full automorphism group has two-rank at most 3r+1, without
requiring classification of its graph involutions. Faithful irreducibility
embeds every ambient elementary two-subgroup into the component automorphism
group. The source ratio bound therefore produces an actual nontrivial cubic
actor with fixed codimension at most 6r+2.

This bounds fixed codimension, not the degree of the whole module. In
particular it does not supply the different G.9 small-degree hypothesis.
Source: Aschbacher--Smith, Chapter K introduction and K.3.4, pp.451,456--457.
-/

public section
namespace CFSG.Quasithin.ChapterK.Symplectic.Recognition
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- A sufficient unconditional rank bound, retaining the cyclic outer contribution. -/
private theorem automorphism_twoRank_le {r : ℕ} (hr : 1 < r) (hF : Nat.card F = 2^r) :
    primeRank 2 (MulAut (Sp F)) ≤ 3*r+1 := by
  let := ExceptionalGraph.outer_isCyclic_of_card hF hr
    SemilinearClassification.inner_field_of_preservesDiagram
  let P := Classical.choice (inferInstance : Nonempty (Sylow 2 (MulAut.Outer (Sp F))))
  have hout : primeRank 2 (MulAut.Outer (Sp F)) ≤ 1 :=
    P.primeRank_le_one_of_isCyclic inferInstance
  have hinn : primeRank 2 (MulAut.innerSubgroup (Sp F)) = 3*r := by
    let e : Sp F ≃* MulAut.innerSubgroup (Sp F) := MonoidHom.ofInjective InvolutionNormalForms.inner_injective
    rw [← primeRank_equiv 2 e, EvenTwoRank.rank hF (by omega)]
  have h := primeRank_le_ker_add (p := 2)
    (QuotientGroup.mk' (MulAut.innerSubgroup (Sp F)))
  rw [QuotientGroup.ker_mk', hinn] at h
  exact h.trans (Nat.add_le_add_left hout _)

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- The rank bound concerns the actual ambient actors, including outer elements. -/
theorem source_twoRank_le {K : GroupClass} (h : SourceHypothesis K ρ L)
    {r : ℕ} (hr : 1 < r) (hF : Nat.card F = 2^r)
    (e : L ⧸ center L ≃* Sp F) : primeRank 2 G ≤ 3*r+1 := by
  let : IsQuasisimple L := h.quasisimple
  let : IsIrreducible (ρ.comp L.subtype) := h.irreducible
  let : L.Normal := h.fitting ▸ inferInstance
  let d := coverEquiv (ρ.comp L.subtype) (h.faithful.comp Subtype.val_injective) e
  have hb := CharacteristicTwoIrreducible.primeRank_le_automorphisms ρ L h.faithful
  rw [primeRank_equiv 2 (MulAut.congr d)] at hb
  exact hb.trans (automorphism_twoRank_le hr hF)

/-- The source cubic ratio supplies a nontrivial actor and its literal
fixed-codimension bound. No whole-module dimension bound is asserted. -/
theorem source_small_cubic_actor {K : GroupClass} (h : SourceHypothesis K ρ L)
    {r : ℕ} (hr : 1 < r) (hF : Nat.card F = 2^r)
    (e : L ⧸ center L ≃* Sp F) :
    ∃ A : Subgroup G, IsElementaryTwo A ∧ IsCubic ρ A ∧
      rank A ≤ 3*r+1 ∧ fixedCodim ρ A ≤ 2 * rank A ∧ fixedCodim ρ A ≤ 6*r+2 := by
  obtain ⟨A, hA, hc, hcodim⟩ := (cubicRatio_le_nat_iff ρ 2).mp h.cubic_le_two
  have hcard := (primeRank_le_iff_elementary_card_le G).mp
    (source_twoRank_le h hr hF e) A hA.2
  have hrank : rank A ≤ 3*r+1 := by
    have hh := Nat.log_mono_right (b := 2) hcard
    simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using hh
  exact ⟨A, hA, hc, hrank, hcodim, by omega⟩

/-- In particular there is an actual ambient involution of bounded displacement. -/
theorem source_small_involution {K : GroupClass} (h : SourceHypothesis K ρ L)
    {r : ℕ} (hr : 1 < r) (hF : Nat.card F = 2^r)
    (e : L ⧸ center L ≃* Sp F) :
    ∃ t : G, orderOf t = 2 ∧
      Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) ≤ 6*r+2 := by
  obtain ⟨A, hA, _, _, _, hcodim⟩ := source_small_cubic_actor h hr hF e
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨t, ht, ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  refine ⟨t, orderOf_eq_prime_iff.mpr ⟨elemPow_eq_one_of_isElementaryAbelian t ht, ht1⟩, ?_⟩
  exact (displacement_finrank_le_fixedSpace_codim ρ A ht).trans hcodim

end CFSG.Quasithin.ChapterK.Symplectic.Recognition

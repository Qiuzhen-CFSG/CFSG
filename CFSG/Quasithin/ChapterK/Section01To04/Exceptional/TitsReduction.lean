module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.Transport
public import Theory.Representation.BinaryIrreducibleRank
public import Theory.Representation.Tits.FrobeniusDegree
public import Theory.SpecificGroups.Tits.AutomorphismTwoRank.FourthPower

/-!
# The remaining Tits actor in Chapter K

The actual Parrott carrier forces binary degree at least twenty-four.
Schur's lemma embeds each elementary actor in the automorphism group of
the irreducibly acting normal component, whose two-rank is at most ten.
Consequently a cubic actor of ratio at most two has codimension at most
twenty and fixes a subspace of dimension at least four.

These unconditional reductions retain the original ambient actor. In
particular they do not import the small-degree hypothesis of G.9: that
hypothesis does not follow from the cubic-ratio assumption here. The
remaining GM04 Theorem 8.1/Table 17 calculation must exclude this actor.

Source: Aschbacher--Smith, printed p.457; the concrete degree/rank bounds
are proved in the imported Tits modules with their own source attribution.
-/

public section
namespace CFSG.Quasithin.ChapterK.Exceptional
open Representation Representation.BinaryOffender

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G)

omit [Finite G] in
/-- Transport the five-local degree obstruction to the actual component. -/
theorem tits_degree_ge_twenty_four
    (hf : Function.Injective ρ) (e : L ≃* Tits.ParrottGroup) :
    24 ≤ Module.finrank (ZMod 2) V :=
  TitsFrobeniusDegree.finrank_ge_twenty_four
    ((ρ.comp L.subtype).comp e.symm.toMonoidHom)
    (hf.comp (L.subtype_injective.comp e.symm.injective))

omit [FiniteDimensional (ZMod 2) V] in
/-- The original ambient group, rather than an assumed almost-simple
replacement, has two-rank at most ten. -/
theorem tits_ambient_two_rank_le_ten [L.Normal] [IsIrreducible (ρ.comp L.subtype)]
    (hf : Function.Injective ρ) (e : L ≃* Tits.ParrottGroup) :
    primeRank 2 G ≤ 10 := by
  have h := BinaryIrreducibleCentralizer.primeRank_le_automorphisms ρ L hf
  rw [Theory.GroupTheory.primeRank_equiv 2 (MulAut.congr e)] at h
  exact h.trans Tits.AutomorphismTwoRank.FourthPower.automorphism_two_rank_le_ten

/-- An alleged K.3 Tits example supplies this literal bounded cubic actor.
The statement is a reduction, not the Tits representation exclusion. -/
theorem tits_cubic_actor_reduction [L.Normal] [IsIrreducible (ρ.comp L.subtype)]
    (hf : Function.Injective ρ) (e : L ≃* Tits.ParrottGroup)
    (hc : cubicRatio ρ ≤ 2) :
    ∃ A : Subgroup G, IsElementaryTwo A ∧ IsCubic ρ A ∧
      rank A ≤ 10 ∧ fixedCodim ρ A ≤ 2 * rank A ∧
      4 ≤ Module.finrank (ZMod 2) (fixedSpace ρ A) := by
  obtain ⟨A, hA, hcube, hcodim⟩ := (cubicRatio_le_nat_iff ρ 2).mp hc
  have hcard := (primeRank_le_iff_elementary_card_le G).mp
    (tits_ambient_two_rank_le_ten ρ L hf e) A hA.2
  have hr : rank A ≤ 10 := by
    have hlog := Nat.log_mono_right (b := 2) hcard
    simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using hlog
  have hd := tits_degree_ge_twenty_four ρ L hf e
  have he := fixedCodim_add_finrank ρ A
  exact ⟨A, hA, hcube, hr, hcodim, by omega⟩

end CFSG.Quasithin.ChapterK.Exceptional

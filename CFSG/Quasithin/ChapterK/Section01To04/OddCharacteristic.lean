module

public import CFSG.Quasithin.ChapterK.Section01To04.Preliminaries
public import CFSG.Quasithin.ChapterK.Section01To04.OddCharacteristic.Inputs
public import CFSG.Quasithin.ChapterK.Section01To04.OddCharacteristic.Coincidences

/-!
# K.2: assembly of the odd-characteristic families

The independent linear and unitary representation restrictions reduce the
source parameters to PSL₂(5), PSL₂(7), PSL₂(9), and PSU₃(3). The concrete
comparisons then identify the same central quotient with A₅, PSL₃(2), A₆,
or G₂(2)′. These are exactly the branches handed to K.1 and K.3.

The representation restrictions remain explicit premises: this module
proves their complete source-family assembly, not the GM02 estimates.
Their existing producers are named in `OddCharacteristic.Inputs`.
The parent K.1–K.4 assembly must supply both before claiming unconditional
K.2. The original G, L, and binary representation are used throughout;
neither the central cover nor any outer action is discarded.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), K.2,
printed p.453 (PDF p.464).
-/

public section
namespace CFSG.Quasithin.ChapterK.OddCharacteristic

open Subgroup Representation.BinaryOffender
open scoped MatrixGroups ENNReal

universe u v
variable {G : Type u} {V : Type v} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G)

/-- K.2's complete conditional reduction to the four actual quotient models.
The two extra premises are precisely the independently owned GM02 restrictions. -/
theorem coincidence_of_cubicRatio_le_two
    (h : SourceHypotheses ρ L) (hl : LinearRestriction ρ L)
    (hu : UnitaryRestriction ρ L) (hf : SourceFamily (L ⧸ center L))
    (hr : cubicRatio ρ ≤ 2) : IsCoincidence (L ⧸ center L) := by
  cases hf with
  | linear_two p e hp ho he hm =>
    obtain ⟨_, hq⟩ := hl h (linearParameters_of_prime_power_model hp ho he hm) hm hr
    exact coincidence_of_small_psl2 hq hm
  | linear_three p hp ho hm =>
    obtain ⟨hn, _⟩ := hl h (.degreeThree p hp ho) hm hr
    omega
  | unitary_three p hp ho hm =>
    have he := hu h hp ho hm hr
    subst p
    exact Or.inr (Or.inr (Or.inr (g2Derived_of_psu3_three hm)))

/-- The strict bound in the last sentence of K.2, conditional only on the
two representation restrictions and exclusion of the four actual overlaps. -/
theorem two_lt_cubicRatio_of_no_coincidence
    (h : SourceHypotheses ρ L) (hl : LinearRestriction ρ L)
    (hu : UnitaryRestriction ρ L) (hf : SourceFamily (L ⧸ center L))
    (hne : ¬ IsCoincidence (L ⧸ center L)) : 2 < cubicRatio ρ := by
  by_contra! hr
  exact hne (coincidence_of_cubicRatio_le_two ρ L h hl hu hf hr)

/-- Literal consumer application: the alternating and characteristic-two
proofs receive isomorphisms of the original central quotient. Thus their
conclusion may concern the original representation and all its outer actors. -/
theorem resolve_of_cubicRatio_le_two {P : Prop}
    (h : SourceHypotheses ρ L) (hl : LinearRestriction ρ L)
    (hu : UnitaryRestriction ρ L) (hf : SourceFamily (L ⧸ center L))
    (hr : cubicRatio ρ ≤ 2)
    (h5 : (L ⧸ center L) ≃* alternatingGroup (Fin 5) → P)
    (h7 : (L ⧸ center L) ≃* PSL(3, ZMod 2) → P)
    (h9 : (L ⧸ center L) ≃* alternatingGroup (Fin 6) → P)
    (h3 : (L ⧸ center L) ≃* commutator (Atlas.G2.Model (ZMod 2)) → P) : P := by
  have hc := coincidence_of_cubicRatio_le_two ρ L h hl hu hf hr
  rcases hc with e | e | e | e
  · exact e.elim h5
  · exact e.elim h7
  · exact e.elim h9
  · exact e.elim h3

end CFSG.Quasithin.ChapterK.OddCharacteristic

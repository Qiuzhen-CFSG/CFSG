module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Fusion
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Global
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# Choosing the escaping totally singular four-group

The global weak-closure parameter is the minimum of actual binary
codimensions, with value infinity for an empty family. When `r(G,V)=2`,
its finite minimum is attained. Since `|V|=16`, the minimizing subgroup
has order four. The elementary abelian structure supplies an actual
isomorphism with `C₂ × C₂`, and its escaping centralizer gives an
escaping normalizer. A normalizer element outside `M` places this
subgroup in an intersection of conjugates, so 15.3.46(2) makes it totally
singular.

The Sylow adjustment of this choice inside `M` is a separate step.
No field restriction or value of the generation parameter is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the
paragraph between Lemmas 15.3.65 and 15.3.66, printed p.1152.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam
open Subgroup ChapterE
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- Attain the finite weak-closure minimum and identify its four-group. -/
theorem exists_escaping_four_of_globalR_eq_two
    (V M : Subgroup G) [IsElementaryAbelian 2 V]
    (hcardV : Nat.card V = 16) (hM : M = normalizer (V : Set G))
    (hr : globalR V = 2) :
    ∃ E : Subgroup G, E ≤ V ∧ Nat.card E = 4 ∧
      Nonempty (E ≃* Multiplicative (ZMod 2 × ZMod 2)) ∧
      ¬ normalizer (E : Set G) ≤ M := by
  obtain ⟨E, hE⟩ := (ENat.iInf_eq_natCast_iff.mp hr).1
  obtain ⟨⟨hEV, hCE⟩, hcorank⟩ := (ENat.iInf_eq_natCast_iff.mp hE).1
  have hcodim : subgroupCorank V E = 2 := ENat.natCast_inj.mp hcorank
  have hrel : E.relIndex V = 4 := by
    rw [relIndex_eq_two_pow_quotient_finrank,
      ← log_relIndex_eq_quotient_finrank]
    change 2 ^ subgroupCorank V E = 4
    rw [hcodim]
    decide
  have hcard : Nat.card E = 4 := by
    have h := (⊥ : Subgroup G).relIndex_mul_relIndex E V bot_le hEV
    simp only [relIndex_bot_left, hrel, hcardV] at h
    omega
  have hnontriv : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : Nontrivial E := hnontriv
  let : IsElementaryAbelian 2 E := {
    toIsMulCommutative := IsMulCommutative.of_comm fun a b => Subtype.ext
      (setLike_mul_comm (hEV a.property) (hEV b.property))
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun a =>
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (a : G) (hEV a.property)) }
  let : IsKleinFour E := ⟨hcard, IsElementaryAbelian.exponent_eq_prime⟩
  refine ⟨E, hEV, hcard, IsKleinFour.nonempty_mulEquiv, ?_⟩
  intro hn
  exact hCE ((centralizer_le_normalizer (E : Set G)).trans (hn.trans hM.le))

/-- The escaping four-group may be chosen totally singular, using the
intersection conclusion of 15.3.46(2). -/
theorem exists_singular_escaping_four_of_globalR_eq_two
    (V M : Subgroup G) [IsElementaryAbelian 2 V]
    (d : OrthogonalFourBinary.NaturalAction V M)
    (hcardV : Nat.card V = 16) (hM : M = normalizer (V : Set G))
    (hr : globalR V = 2)
    (hsingular : ∀ g : G, g ∉ M →
      ∀ x : ↥(V ⊓ V.map (MulAut.conj g).toMonoidHom),
        d.singular ⟨x, x.property.1⟩) :
    ∃ (E : Subgroup G) (hEV : E ≤ V), Nat.card E = 4 ∧
      Nonempty (E ≃* Multiplicative (ZMod 2 × ZMod 2)) ∧
      ¬ normalizer (E : Set G) ≤ M ∧
      ∀ e : E, d.singular ⟨e, hEV e.property⟩ := by
  obtain ⟨E, hEV, hcard, hequiv, hescape⟩ :=
    exists_escaping_four_of_globalR_eq_two V M hcardV hM hr
  refine ⟨E, hEV, hcard, hequiv, hescape, ?_⟩
  obtain ⟨g, hg, hgM⟩ := SetLike.not_le_iff_exists.mp hescape
  have hEg : E.map (MulAut.conj g).toMonoidHom = E :=
    mem_normalizer_iff_map_conj_eq.mp hg
  have hEVg : E ≤ V.map (MulAut.conj g).toMonoidHom := by
    rw [← hEg]
    exact map_mono hEV
  intro e
  exact hsingular g hgM ⟨e, hEV e.property, hEVg e.property⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam

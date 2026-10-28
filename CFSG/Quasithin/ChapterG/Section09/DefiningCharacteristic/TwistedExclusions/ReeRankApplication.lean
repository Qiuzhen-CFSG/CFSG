module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions
public import Theory.SpecificGroups.ReeF4.AutomorphismTwoRank
public import Theory.SpecificGroups.Tits.AutomorphismTwoRank

/-!
# Applying the Ree and Tits automorphism rank bounds to G.9

The actual component isomorphism transports its automorphism rank to the
canonical Ree carrier or to the simple Parrott carrier. The unconditional
bounds 12*(2*k+1) and 11 suffice for the source inequality d <= 2*(m+1):
at k >= 1 the first gives 2*(m+1) < 26*(2*k+1), and the second gives
2*(m+1) < 26. All automorphism premises are discharged here.

The universal faithful irreducible degree bounds remain explicit. Their
proof and the final exclusions belong to the defining-characteristic
representation assembly. These adapters preserve the original component,
action and model isomorphisms, and do not assert the sharper source ranks
5*(2*k+1) or 5. The old sharper conditional interfaces remain available.

Source: Aschbacher–Smith G.9.3, printed p.356 (PDF p.367), and GLS3,
Sections 2.5 and 2.8. The full Ree group at k = 0 is not the simple endpoint.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions

open Subgroup Theory.GroupTheory

universe u v w

variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {K : GroupClass.{u}} {ρ : Representation (ZMod 2) G V}
  {A L : Subgroup G} {m : ℕ}

private theorem false_of_model_degree_gap
    (h : ComponentHypothesis K ρ A L L m)
    {S : Type w} [Group S] [Finite S] (e : L ≃* S) {b : ℕ}
    (hgap : 2 * (primeRank 2 (MulAut S) + 1) < b)
    (hdegree : ∀ σ : Representation (ZMod 2) S V,
      σ.IsIrreducible → Function.Injective σ → b ≤ Module.finrank (ZMod 2) V) :
    False := by
  let : Representation.IsIrreducible (ρ.comp L.subtype) := h.irreducible
  have hr : m ≤ primeRank 2 (MulAut L) := by
    apply h.toSetup.rank_le_automorphisms
    rw [Subgroup.normalizer_eq_top_iff.mpr h.normal_H]
    exact le_top
  rw [primeRank_equiv 2 (MulAut.congr e)] at hr
  have hd := degree_ge_of_model h e hdegree
  have hu := h.degree_le
  omega

/-- The large Ree exclusion needs only the universal degree bound;
the actual automorphism rank is already strictly below its threshold. -/
theorem not_ree_of_degree_bound
    (h : ComponentHypothesis K ρ A L L m) {k : ℕ} (hk : 1 ≤ k)
    (e : L ≃* ReeF4.Model k)
    (hdegree : ∀ σ : Representation (ZMod 2) (ReeF4.Model k) V,
      σ.IsIrreducible → Function.Injective σ →
        26 * (2 * k + 1) ≤ Module.finrank (ZMod 2) V) : False :=
  false_of_model_degree_gap h e
    (ReeF4.AutomorphismTwoRank.automorphism_two_rank_degree_gap hk) hdegree

/-- The simple derived endpoint uses the genuine Parrott carrier and its
sharp outer count, leaving only the universal degree-26 bound explicit. -/
theorem not_tits_of_degree_bound
    (h : ComponentHypothesis K ρ A L L m) (e : L ≃* Tits.ParrottGroup)
    (hdegree : ∀ σ : Representation (ZMod 2) Tits.ParrottGroup V,
      σ.IsIrreducible → Function.Injective σ → 26 ≤ Module.finrank (ZMod 2) V) : False :=
  false_of_model_degree_gap h e
    Tits.AutomorphismTwoRank.automorphism_two_rank_degree_gap hdegree

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions

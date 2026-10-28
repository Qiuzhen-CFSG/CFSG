module
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions.TrialityReduction
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions.SharpRankApplication
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions.ReeRankApplication
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions.TitsFrobenius
public import Theory.Representation.ReeF4.BinaryDegree.Source
public import Theory.SpecificGroups.ReeF4.Model.LocalBlock

/-!
# Closing the actual triality and Ree source rows

The original G.9 component bound applies to the actual faithful irreducible
representation. Completed triality rank reduction leaves the exponent-two
endpoint, already excluded by its sharp rank bound. For Ree, the proved
universal binary degree bound discharges the final representation input of
the automorphism-rank comparison. The local-block row uses the actual fixed
subgroup isomorphism to the canonical Ree carrier.

The Tits endpoint is re-exported from its completed five-local proof.
Source: Aschbacher–Smith G.9.3, printed p.356, and GLS3 §§2.5,2.8.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions
open Subgroup Theory.GroupTheory
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {K : GroupClass.{u}} {ρ : Representation (ZMod 2) G V}
  {A L : Subgroup G} {m : ℕ}

theorem not_triality_positive_exponent
    (h : ComponentHypothesis K ρ A L L m) {n : ℕ} (hn : 0 < n)
    (model : Triality.Standard.IsTrialityGroupAt (2 ^ n) L) : False := by
  have he := triality_parameter_eq_two_of_source_component h hn model
  subst n
  exact not_triality_four_of_sharp_rank h model

theorem not_ree_of_source_component
    (h : ComponentHypothesis K ρ A L L m) {k : ℕ} (hk : 1 ≤ k)
    (e : L ≃* ReeF4.Model k) : False := by
  apply not_ree_of_degree_bound h hk e
  intro σ hi hf
  let := hi
  exact ReeF4.BinaryDegree.ree_binary_degree_ge hk σ hf

theorem not_ree_of_local_block
    (h : ComponentHypothesis K ρ A L L m) {k : ℕ} (hk : 1 ≤ k)
    (d : ReeF4.LocalBlockInput k) (e : L ≃* d.fixedGroup) : False :=
  not_ree_of_source_component h hk (e.trans d.modelEquiv)
end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions

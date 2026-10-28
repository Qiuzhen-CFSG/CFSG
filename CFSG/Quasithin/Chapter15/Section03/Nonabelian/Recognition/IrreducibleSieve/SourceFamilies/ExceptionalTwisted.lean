module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies.Common
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions.TrialityReduction
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions.SharpRankApplication
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions.ReeRankApplication
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions.TitsFrobenius
public import Theory.Representation.ReeF4.BinaryDegree.Source

/-!
# Exceptional twisted components in the source irreducible sieve

The genuine G.9 component hypothesis follows from the original elementary
actor and faithful irreducible action. Triality is excluded by its seven-local
and primitive-prime degree estimates together with its automorphism rank.
For Ree, the full exceptional tensor theorem gives binary degree at least
26 times the field exponent; the proved automorphism bound makes the source
degree strictly smaller. The Tits endpoint uses its literal five-local
subgroup and fourth-power automorphism estimate.

These exclusions preserve the original component, its representation, and
its exact model isomorphism. Every degree and automorphism input is discharged.
Source: Aschbacher--Smith, G.9.3, printed p.356, applied in the proof of
15.3.58, printed p.1149 (`refs/quasithin.pdf`).
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve

open ChapterG.Section09
open ChapterG.Section09.DefiningCharacteristic.TwistedExclusions

variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} {X K : Subgroup H} {T : Sylow 2 H}
  {v : H} {s : ℕ}

/-- No positive binary triality parameter survives the literal source actor. -/
theorem SourceData.not_triality_model (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) (hq : IsSQTK KnownSimple.IsKnownSimple H)
    (hsimple : IsSimpleGroup K) (hnonab : ¬ IsMulCommutative K)
    {f : ℕ} (hf : 1 ≤ f) (model : Triality.Standard.IsTrialityGroupAt (2 ^ f) K) :
    False := by
  have hc := h.simple_componentHypothesis hK hq hsimple hnonab
  have he := triality_parameter_eq_two_of_source_component hc (by omega) model
  subst f
  exact not_triality_four_of_sharp_rank hc model

/-- Every genuine large Ree parameter contradicts the source degree bound. -/
theorem SourceData.not_ree_f4_model (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) (hq : IsSQTK KnownSimple.IsKnownSimple H)
    (hsimple : IsSimpleGroup K) (hnonab : ¬ IsMulCommutative K)
    {m : ℕ} (hm : 1 ≤ m) (model : Nonempty (K ≃* ReeF4.Model m)) : False := by
  obtain ⟨e⟩ := model
  apply not_ree_of_degree_bound (h.simple_componentHypothesis hK hq hsimple hnonab) hm e
  intro σ hi hf
  let := hi
  exact ReeF4.BinaryDegree.ree_binary_degree_ge hm σ hf

/-- The simple Tits endpoint is excluded on the original faithful action. -/
theorem SourceData.not_tits_model (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) (hq : IsSQTK KnownSimple.IsKnownSimple H)
    (hsimple : IsSimpleGroup K) (hnonab : ¬ IsMulCommutative K)
    (model : Nonempty (K ≃* Tits.ParrottGroup)) : False := by
  obtain ⟨e⟩ := model
  exact not_tits_of_source_component (h.simple_componentHypothesis hK hq hsimple hnonab) e

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve

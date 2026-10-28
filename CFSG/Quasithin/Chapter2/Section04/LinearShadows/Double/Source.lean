module
public import CFSG.Quasithin.Chapter2.Section04.Statement
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.TerminalSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.ThompsonSource
/-!
# Exclusion of the original double linear-block source branch

Choose an index-two overgroup of the original Sylow subgroup. The original
paired setup supplies the invariant square torus and Thompson stability.
The four-family normalizer theorem then makes this overgroup the full
ambient Sylow group. The generated local component and its independent
torus contradict quasithinness. Every intermediate geometric, action and
model input is produced from the original minimal block setup.

Source: Aschbacher–Smith, Theorem 2.4.7, double-block case, pp.539–541.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The literal original double-linear branch is impossible. -/
theorem MinimalBlockSetup.double_linear_source_false
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (_hdelta : (delta (Chapter1.He G) M).Nonempty)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (_hcounter : ¬ IsTheorem241Model G) (hpair : d.L0 ≠ d.block)
    {n : ℕ} (hL : ChapterC.IsL2EvenBlock (d.block.map d.H.subtype) n) : False := by
  obtain ⟨M₀,hSM,hMT,hi⟩ := d.exists_index_two_overgroup T hST
  obtain ⟨c⟩ := d.double_linear_configuration hG T hST.le hpair hL M₀ hSM hMT hi
  have hJ := c.thompson_eq_from_original hG T hM hTM hu hST hL hSM hMT hi
  exact c.false_of_thompson_stable hG T hM hTM hu hST hL hMT hi hJ

end CFSG.Quasithin.Chapter2

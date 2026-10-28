module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies.Odd
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies.Alternating
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies.Sporadic

/-!
# Alternating, odd-characteristic and sporadic branches of the source sieve

These are the three literal Theorem C alternatives for the actual simple
component. Each is excluded using its given model isomorphism and the original
source configuration. The odd reductions use the alternating and small binary
module exclusions; the sporadic reductions use certified degree inequalities
or a fixed element of order three for the marked automorphism.

Source: Aschbacher--Smith, A.2.4 and 15.3.58, printed pp.33 and 1149.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies.OddAndSporadic
open ChapterA.Section02
variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} {X K : Subgroup H} {T : Sylow 2 H}
  {v : H} {s : ℕ}

theorem exclude_alternating (h : SourceData ρ X T v s) (hK : ComponentData ρ K)
    (_hsimple : IsSimpleGroup K) (_hnonab : ¬ IsMulCommutative K)
    (n : ℕ) (hn : n ≤ 8) (iso : Nonempty (K ≃* alternatingGroup (Fin n))) : False := by
  obtain ⟨e⟩ := iso
  exact Alternating.not_component h hK hn e

theorem exclude_odd (h : SourceData ρ X T v s) (hK : ComponentData ρ K)
    (hsimple : IsSimpleGroup K) (hnonab : ¬ IsMulCommutative K)
    (hm : IsTheoremCOddModel K) : False :=
  Odd.exclude h hK hsimple hnonab hm

theorem exclude_sporadic (h : SourceData ρ X T v s) (hK : ComponentData ρ K)
    (hsimple : IsSimpleGroup K) (hnonab : ¬ IsMulCommutative K)
    (hm : IsTheoremCSporadicModel K) : False :=
  Sporadic.exclude h hK hsimple hnonab hm

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies.OddAndSporadic

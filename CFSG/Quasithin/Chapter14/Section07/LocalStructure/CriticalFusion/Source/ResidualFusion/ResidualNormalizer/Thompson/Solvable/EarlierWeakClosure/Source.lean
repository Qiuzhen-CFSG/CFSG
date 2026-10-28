module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Solvable.EarlierWeakClosure.Core
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.SourceKnownSimple

/-!
# Both original clauses of Lemma 14.7.31

The hyperplane and core arguments prove the literal universal contract,
including its corank-zero convention, relative Sylow witness and S₃ quotient.
The known-simple 1.2.7 theorem discharges uniqueness. Only the earlier
structural 12.2.2 theorem remains explicit, as authorized by this source
boundary; qt-d-1222-source owns it and qt-d-14775-source owns final assembly.

Source: Aschbacher–Smith, Lemma 14.7.31, printed p.1055, PDF p.1072.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u

/-- The original two-clause source contract, from the earlier structural theorem. -/
theorem source_theorem14731
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    Theorem14731.{u} := by
  intro G _ _ T L V _ h F hU hplane
  have uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S B hB
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hB
  refine ⟨EarlierWeakClosure.clause_one h structural uniqueness F hU hplane, ?_⟩
  intro A R B _ hSylow hBA hB he hcore hreturn
  obtain ⟨e⟩ := he
  exact EarlierWeakClosure.clause_two h structural F hplane A R B hSylow hBA hB e hcore hreturn

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source

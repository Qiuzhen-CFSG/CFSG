module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Check00
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Check01
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Check02
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Check03
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Check04
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Check05
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Check06
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Check07
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Check08
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Check09
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Check10
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Check11
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Check12
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Check13
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Check14
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Check15
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Check16

/-! Kernel-checked deductions for the literal ATLAS J3G1-P1 subgroup M₁.
Chunks bound the reduction cache; each scan uses previously proved equations. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
open Subgroup.CosetWordCertificate

set_option Elab.async false

/-- Every retained deduction has an actual witness in the literal subgroup M₁. -/
theorem all_hold : ∀ n, n < 277281 →
    Holds M1 generator (definitions.repr generator) (facts n) := by
  have h0 := sound_0 (fun n hn => (Nat.not_lt_zero n hn).elim)
  have h16384 := sound_16384 h0
  have h32768 := sound_32768 h16384
  have h49152 := sound_49152 h32768
  have h65536 := sound_65536 h49152
  have h81920 := sound_81920 h65536
  have h98304 := sound_98304 h81920
  have h114688 := sound_114688 h98304
  have h131072 := sound_131072 h114688
  have h147456 := sound_147456 h131072
  have h163840 := sound_163840 h147456
  have h180224 := sound_180224 h163840
  have h196608 := sound_196608 h180224
  have h212992 := sound_212992 h196608
  have h229376 := sound_229376 h212992
  have h245760 := sound_245760 h229376
  have h262144 := sound_262144 h245760
  exact h262144

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate

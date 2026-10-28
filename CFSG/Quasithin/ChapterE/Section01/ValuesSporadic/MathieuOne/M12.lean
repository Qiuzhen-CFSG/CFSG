module

public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.MathieuOne.Reduction
public import Theory.Mathieu.M12.ValueBoundParabolics.ExtensionPair
public import Theory.Mathieu.M12.ValueBoundParabolics.Ambient

/-!
# Rank-one E-generation for M₁₂ and its almost simple extensions

The native M₁₂ and full automorphism carriers each have a proved generating
pair through every Sylow two-subgroup. Their intrinsic two-core quotients
are S₃, so both members are solvable and satisfy E.1.13. E-member inheritance
then gives E-generation of the ambient group. Faithful conjugation on its
centerless generalized Fitting subgroup identifies every ambient extension
with one of these two actual carriers.

Source: Aschbacher–Smith, E.1.14(4), printed p.214, citing Asc82a Lemma 4.9.
The local pairs are also used in E.4.3(1), printed p.241; their intrinsic
model proofs, including the outer extension, are reused here without any
later chapter theorem.
-/

public section
open Subgroup Theory.GroupTheory Sporadic.Mathieu
namespace CFSG.Quasithin.ChapterE.MathieuOne
variable {G : Type*} [Group G] [Finite G]

/-- The actual simple carrier, transported by a specified group equivalence. -/
theorem isEGenerated_of_equiv_m12 (e : G ≃* M12) : IsEGenerated 1 G := by
  classical
  let T : Sylow 2 G := Classical.choice inferInstance
  obtain ⟨H, J, hH, hJ, hj, ⟨eH⟩, ⟨eJ⟩⟩ :=
    M12SmallPair.ValueBoundParabolics.exists_pair_of_equiv e T
  exact isEGenerated_of_symmetricThree_pair T H J hH hJ hj eH eJ

/-- The full automorphism carrier, including its genuine nonsplit local cores. -/
theorem isEGenerated_of_equiv_m12_extension (e : G ≃* M12ExceptionalExtension.Carrier) :
    IsEGenerated 1 G := by
  classical
  let T : Sylow 2 G := Classical.choice inferInstance
  obtain ⟨H, J, -, hH, hJ, hj, ⟨eH⟩, ⟨eJ⟩⟩ :=
    M12SmallPair.ValueBoundParabolics.Extension.exists_pair_of_equiv e T
  exact isEGenerated_of_symmetricThree_pair T H J hH hJ hj eH eJ

/-- E.1.14(4), upper bound for every ambient group with generalized Fitting
subgroup genuinely isomorphic to M₁₂. No local-generation premise remains. -/
theorem isEGenerated_of_m12_socle (e : generalizedFitting G ≃* M12) :
    IsEGenerated 1 G := by
  have hc := centralizer_generalizedFitting_eq_bot_of_equiv e m12_center_eq_bot
  rcases M12SmallPair.ValueBoundParabolics.Ambient.ambient_equiv_alternatives
      (generalizedFitting G) hc e with ⟨-, ⟨a⟩⟩ | ⟨a, -⟩
  · exact isEGenerated_of_equiv_m12 a
  · exact isEGenerated_of_equiv_m12_extension a
end CFSG.Quasithin.ChapterE.MathieuOne

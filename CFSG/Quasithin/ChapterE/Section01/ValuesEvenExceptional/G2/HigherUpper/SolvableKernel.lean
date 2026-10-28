module

public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.NormalizerDiagonal.Overgroups
public import Theory.GroupTheory.NormalizedSupConsequences

/-!
# Removing solvable kernels in positive-rank E-generation

Quotient lifting puts the generation target together with the kernel equal
to the whole group. If the normal kernel Y is solvable, its join with the
chosen Sylow two-subgroup is solvable. E.1.13 and E-member inheritance put
that entire join in the target, absorbing Y. This applies to the intrinsic
solvable radical of each G₂ parabolic overgroup, including outer extensions.

The imported lifting and inheritance results use the source's local tau,
solvable radical and two-residual conventions. No replacement E-members or
assumption of their existence is introduced here.

Source: Aschbacher--Smith, E.1.8, E.1.10--13, printed pp.210--214;
application to E.1.14(1), citing Aschbacher (1982), Lemma 4.7.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

/-- A normal solvable kernel does not obstruct positive-rank E-generation. -/
theorem IsEGenerated.of_normal_solvable_subgroup {n : ℕ} (hn : 0 < n)
    (Y : Subgroup G) [Y.Normal] [Group.IsSolvable Y]
    (hgen : IsEGenerated n (G ⧸ Y)) : IsEGenerated n G := by
  intro T Ω hΩ
  let : Group.IsNilpotent T := T.isPGroup'.isNilpotent
  let : Group.IsSolvable (Y ⊔ (T : Subgroup G) : Subgroup G) :=
    Group.isSolvable_sup_of_normal_left _ _
  have hY := le_sup_left.trans
    (ChiefOrbit.solvable_overgroup_le_generationTarget hn T
      (Y ⊔ (T : Subgroup G)) le_sup_right hΩ)
  have h := generation_modulo_normal T hΩ Y hgen
  exact (sup_eq_left.mpr hY).symm.trans h

/-- The surjection form retains the literal kernel of the quotient map. -/
theorem IsEGenerated.of_surjective_solvable_kernel {n : ℕ} (hn : 0 < n)
    (q : G →* H) (hq : Function.Surjective q) [Group.IsSolvable q.ker]
    (hgen : IsEGenerated n H) : IsEGenerated n G :=
  IsEGenerated.of_normal_solvable_subgroup hn q.ker
    (hgen.map_equiv (QuotientGroup.quotientKerEquivOfSurjective q hq).symm)

/-- The radical quotient suffices; its generation remains a separate input. -/
theorem IsEGenerated.of_solvableRadical_quotient {n : ℕ} (hn : 0 < n)
    (hgen : IsEGenerated n (G ⧸ solvableRadical G)) : IsEGenerated n G :=
  IsEGenerated.of_normal_solvable_subgroup hn (solvableRadical G) hgen

end CFSG.Quasithin.ChapterE

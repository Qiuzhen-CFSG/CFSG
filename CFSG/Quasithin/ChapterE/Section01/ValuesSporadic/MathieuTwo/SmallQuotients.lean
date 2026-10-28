module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.SimpleSocle
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.QuotientFamily
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.Solvable
public import Theory.Mathieu.M22.ValueBoundParabolics.SmallQuotients
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTransfer
public import Theory.SpecificGroups.SymmetricTwoResidual
public import Theory.Representation.AlternatingSevenConjugatePair.ElementaryGeometry

/-!
# The small quotients for Mathieu rank-two generation

The whole group is an E2 member for every nontrivial elementary actor in
S5 or A7. Their two-ranks are at most two, so this proves actual E-generation,
without an assumed general existence theorem. S3 uses solvable generation.
Generation lifts through the normal two-group kernels of the local actions.

These are the local bounds used for Aschbacher--Smith E.1.14(5), printed
p.214, citing Aschbacher, GF(2)-representations of finite groups, Lemma 4.9.
The E2 proof uses the corrected intrinsic local tau of E.1.2.
-/

public section
namespace CFSG.Quasithin.ChapterE.MathieuTwo
open Subgroup Theory.GroupTheory
open ValuesEvenClassical.RankOneUpper
open Sporadic.Mathieu.M22ValueBound.SmallQuotients

/-- The S5 quotient in both the inner and outer M22 local pairs. -/
theorem symmetricFive_isEGenerated : IsEGenerated 2 (Equiv.Perm (Fin 5)) := by
  let : IsSimpleGroup (generalizedFitting (Equiv.Perm (Fin 5))) := by
    rw [symmetricFive_generalizedFitting_eq_alternating]
    exact alternatingGroup.isSimpleGroup (by simp)
  let := symmetricFive_generalizedFitting_isQuasisimple
  intro T
  apply isEGeneratedAt_of_top_component_and_rank T
  · intro A _ _ hn
    apply eCaseComponent_top (Group.IsPerfect.not_isMulCommutative _) T _ _ _ hn
    rw [symmetricFive_generalizedFitting_eq_alternating,
      ← Equiv.Perm.twoResidual_eq_alternating]
    exact pResidual_sup_sylow_eq_top T
  · intro A hA _
    let := hA
    exact (A.rank_le_primeRank 2 (IsElementaryAbelian.isPGroup 2 A)).trans
      symmetricFive_primeRank_le_two

/-- The solvable quotient in the second M22 local overgroup. -/
theorem symmetricThree_isEGenerated : IsEGenerated 1 (Equiv.Perm (Fin 3)) := by
  let : Group.IsSolvable (alternatingGroup (Fin 3)) :=
    Group.isSolvable_of_comm (by decide)
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    apply Group.isSolvable_of_ker_le_range
      (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]
  exact isEGenerated_one_of_solvable

/-- The alternating quotient of the M23 heptad stabilizer. -/
theorem alternatingSeven_isEGenerated : IsEGenerated 2 (alternatingGroup (Fin 7)) := by
  let : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 7)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : IsQuasisimple (alternatingGroup (Fin 7)) := ⟨
    ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot (by simp))).trans
      QuotientGroup.quotientBot).isSimpleGroup⟩
  have hF := generalizedFitting_eq_top_of_quasisimple (G := alternatingGroup (Fin 7))
  let e : generalizedFitting (alternatingGroup (Fin 7)) ≃* alternatingGroup (Fin 7) :=
    (MulEquiv.subgroupCongr hF).trans Subgroup.topEquiv
  let : IsSimpleGroup (generalizedFitting (alternatingGroup (Fin 7))) := e.isSimpleGroup
  let : IsQuasisimple (generalizedFitting (alternatingGroup (Fin 7))) :=
    IsQuasisimple.of_mulEquiv e.symm
  intro T
  apply isEGeneratedAt_of_top_component_and_rank T
  · intro A _ _ hn
    exact eCaseComponent_top (Group.IsPerfect.not_isMulCommutative _) T
      (by rw [hF, top_sup_eq]) _ _ hn
  · intro A hA _
    let := hA
    have h := A.rank_le_primeRank 2 (IsElementaryAbelian.isPGroup 2 A)
    rwa [Representation.AlternatingSevenConjugatePair.ElementaryGeometry.primeRank_alternating] at h

variable {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q]

/-- Apply a small-quotient bound to the literal epimorphism of a local action. -/
theorem isEGenerated_of_two_kernel {i : ℕ} (f : G →* Q)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hQ : IsEGenerated i Q) : IsEGenerated i G :=
  IsEGenerated.of_normal_two_subgroup f.ker hk
    (hQ.map_equiv (QuotientGroup.quotientKerEquivOfSurjective f hf).symm)

/-- The first intrinsic two-core quotient of the M22 pair has bound two. -/
theorem isEGenerated_of_twoCore_quotient_symmetricFive
    (e : (G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 5)) : IsEGenerated 2 G :=
  IsEGenerated.of_normal_two_subgroup (pCore 2 G) pCore_isPGroup
    (symmetricFive_isEGenerated.map_equiv e.symm)

/-- The second intrinsic two-core quotient even has bound one. -/
theorem isEGenerated_of_twoCore_quotient_symmetricThree
    (e : (G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3)) : IsEGenerated 1 G :=
  IsEGenerated.of_normal_two_subgroup (pCore 2 G) pCore_isPGroup
    (symmetricThree_isEGenerated.map_equiv e.symm)

end CFSG.Quasithin.ChapterE.MathieuTwo

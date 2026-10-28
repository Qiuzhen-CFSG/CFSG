module
public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.Paired.PrimeSharp.Original
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Moved
public import Theory.GroupTheory.CComponent.TwoComponent.ImageQuotient
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension

/-!
# The odd-prime component in a genuine minimal parabolic

The maximal core is the solvable radical. Its intersection with a C-component
is the intrinsic radical, which is exactly the two-core when the component's
two-core quotient is simple. The restricted literal quotient map therefore
identifies K/O₂(K) with its actual image. The paired-prime theorem applies to
that image and lifts through the whole solvable core, not merely O₂(H).
The normal component branch uses the previously proved simple-socle theorem.

Source: Aschbacher--Smith E.2.2 and E.1.11--14, printed pp.212--216;
the application in 10.3.3, printed p.756.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration
variable {H : Type*} [Group H] [Finite H]

theorem minimalParabolic_component_kernel
    (S : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver S ⊤)
    (K : Subgroup H) (hK : K.IsCComponent)
    [IsSimpleGroup (K ⧸ pCore 2 K)] :
    ((QuotientGroup.mk' (ChapterB.minimalParabolicCore S hP)).subgroupMap K).ker =
      pCore 2 K := by
  let : Group.IsPerfect K := hK.perfect
  have hs : ¬Group.IsSolvable H := by
    intro hs
    let := hs
    exact hK.not_isSolvable inferInstance
  rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
  change (ChapterB.minimalParabolicCore S hP).subgroupOf K = _
  rw [ChapterB.minimalParabolic_nonsolvable_core_eq_radical S hP hs,
    solvableRadical_subgroupOf_of_isSubnormal hK.subnormal,
    PerfectCoreTwoExtension.radical_eq_core]

@[expose] noncomputable def minimalParabolic_component_equiv
    (S : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver S ⊤)
    (K : Subgroup H) (hK : K.IsCComponent)
    [IsSimpleGroup (K ⧸ pCore 2 K)] :
    (K ⧸ pCore 2 K) ≃*
      K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore S hP)) :=
  QuotientGroup.liftEquiv _
    ((QuotientGroup.mk' (ChapterB.minimalParabolicCore S hP)).subgroupMap_surjective K)
    (minimalParabolic_component_kernel S hP K hK).symm

theorem minimalParabolic_component_equiv_mk
    (S : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver S ⊤)
    (K : Subgroup H) (hK : K.IsCComponent)
    [IsSimpleGroup (K ⧸ pCore 2 K)] (k : K) :
    minimalParabolic_component_equiv S hP K hK (QuotientGroup.mk' (pCore 2 K) k) =
      (QuotientGroup.mk' (ChapterB.minimalParabolicCore S hP)).subgroupMap K k := rfl

theorem isEGenerated_of_minimalParabolic_odd_component
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (S : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver S ⊤)
    (K : Subgroup H) (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)] (hgen : K ⊔ (S : Subgroup H) = ⊤)
    {p : ℕ} (hprime : p.Prime) (ho : Odd p) (hp : 7 ≤ p)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 p) : ChapterE.IsEGenerated 1 H := by
  by_cases hn : K.Normal
  · let := hn
    exact isEGenerated_of_normal_odd_component hH S K hK hgen ho hp hm
  have hs : ¬Group.IsSolvable H := by
    intro hs
    let := hs
    exact hK.not_isSolvable inferInstance
  have hsimple : IsSimpleGroup (K ⧸ pCore 2 K) := by
    obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := hm
    let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
    exact e.isSimpleGroup
  let := hsimple
  let : Fact p.Prime := ⟨hprime⟩
  exact ChapterE.Structure.NumericalBounds.paired_prime_isEGenerated_one
    ChapterA.Section02.theoremA_knownSimple hH S hP hs K hK hgen hn hp
    (hm.of_mulEquiv (minimalParabolic_component_equiv S hP K hK).symm)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration

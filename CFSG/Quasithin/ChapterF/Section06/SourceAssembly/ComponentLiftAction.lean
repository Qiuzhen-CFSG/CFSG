module
public import CFSG.Quasithin.ChapterF.Section06.Elementary.PrimeToThree
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.OddRadical
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Complete
public import Theory.GroupTheory.CComponent.TwoClosedKernel
public import Theory.GroupTheory.SolvableRadical.TwoCoreOddQuotient
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import Theory.GroupTheory.GeneralizedFitting.SemisimpleCenter
public import Theory.GroupTheory.PerfectCentralizerLift

/-!
# Normal component lifts in the original Goldschmidt quotient

F.6.11 supplies a normal Sylow two-subgroup of the full O₃′ kernel.
The radical of the lifted component modulo its intrinsic two-core is
therefore odd. The actual A.3.6 alternatives exclude the noncentral
radical case, so this two-core quotient is quasisimple.

The kernel centralizes this ordinary component. Perfectness removes a
second commutator, lifting commutation with its O₃′ image to commutation
modulo O₂ of the original ambient group. No kernels are identified or
omitted. The original cubic-span application is in Chapter13 Section02,
OriginalCentralization.SingleComponentAction.

Source: Aschbacher--Smith F.6.11(1), A.3.6 and 13.2.7, printed
pp.306--307,43--45,883--884.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G : Type*} [Group G] [Finite G]

/-- A normal component lift through the literal Goldschmidt kernel has a
quasisimple quotient by its intrinsic two-core. -/
theorem normal_component_lift_twoCore_quasisimple
    {A B : Subgroup G} (hg : ChapterF.IsGoldschmidtTriple A B)
    (hsq : IsSQTK KnownSimple.IsKnownSimple G)
    (K : Subgroup G) (hK : K.IsCComponent) [K.Normal]
    (him : IsComponent (G ⧸ pPrimeCore 3 G)
      (K.map (QuotientGroup.mk' (pPrimeCore 3 G)))) :
    IsQuasisimple (K ⧸ pCore 2 K) := by
  obtain ⟨S,hS⟩ := hg.primeToThreeCore_sylow
  have hSn : (S : Subgroup (pPrimeCore 3 G)).Normal := by
    have he : (S : Subgroup (pPrimeCore 3 G)) = (pCore 2 G).subgroupOf (pPrimeCore 3 G) := by
      apply map_injective (pPrimeCore 3 G).subtype_injective
      rw [hS,map_subgroupOf_eq_of_le ChapterF.twoCore_le_primeToThreeCore]
    rw [he]
    infer_instance
  have ho : Odd (Nat.card (solvableRadical (K ⧸ pCore 2 K))) :=
    odd_radical_twoCore_quotient_iff.mpr
      (odd_radical_relIndex_of_component_quotient (pPrimeCore 3 G) K ⟨S,hSn⟩
        hg.primeToThreeCore_quotient_twoCore_eq_bot him)
  exact Chapter1.Section02.quasisimple_twoCore_quotient_of_a36_of_odd_radical
    (ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)) hsq hK ho

/-- Commutation with a normal component image lifts modulo the two-core,
retaining the entire prime-to-three kernel. -/
theorem normal_component_lift_commutator_le_twoCore
    {A B : Subgroup G} (hg : ChapterF.IsGoldschmidtTriple A B)
    (hsq : IsSQTK KnownSimple.IsKnownSimple G)
    (K Y : Subgroup G) (hK : K.IsCComponent) [K.Normal]
    (him : IsComponent (G ⧸ pPrimeCore 3 G)
      (K.map (QuotientGroup.mk' (pPrimeCore 3 G))))
    (hc : ⁅Y.map (QuotientGroup.mk' (pPrimeCore 3 G)),
      K.map (QuotientGroup.mk' (pPrimeCore 3 G))⁆ = ⊥) :
    ⁅Y,K⁆ ≤ pCore 2 G := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let N := (pPrimeCore 3 G).map q
  let C := K.map q
  let : IsQuasisimple (K ⧸ pCore 2 K) := normal_component_lift_twoCore_quasisimple hg hsq K hK him
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hK)
  have hC : IsComponent (G ⧸ pCore 2 G) C :=
    ⟨hK.subnormal.map (QuotientGroup.mk'_surjective _),inferInstance⟩
  let : Group.IsSolvable (pPrimeCore 3 G) := hg.primeToThreeCore_solvable
  let : Group.IsSolvable N := Group.isSolvable_of_surjective
    (f := q.subgroupMap (pPrimeCore 3 G)) (q.subgroupMap_surjective _)
  let : N.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hNC : N ≤ centralizer (C : Set _) :=
    le_centralizer_iff.mp (hC.le_centralizer_of_solvable_normal N)
  have hYK : ⁅Y,K⁆ ≤ pPrimeCore 3 G := by
    rwa [←map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] at hc
  have hm : ⁅Y.map q,C⁆ ≤ N := by
    rw [show C = K.map q from rfl,←map_commutator]
    exact map_mono hYK
  have hz : ⁅Y.map q,C⁆ = ⊥ := commutator_eq_bot_of_iterated_eq_bot (Y.map q) C
    (commutator_eq_bot_iff_le_centralizer.mpr (hm.trans hNC))
  rwa [show C = K.map q from rfl,←map_commutator,Subgroup.map_eq_bot_iff,
    QuotientGroup.ker_mk'] at hz


end CFSG.Quasithin.ChapterF.SourceAssembly

module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Radical.OddIndex.Extension
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.KernelIdentification
public import CFSG.Quasithin.ChapterA.Section01.RankActions.PrimeSL2CoverRigidity
public import Theory.GroupTheory.Fitting.Equiv
public import Theory.Quasithin.Rank

/-!
# The literal Fitting quotient in the surviving odd extension

The intrinsic SQTK C-component structure identifies the Fitting subgroup
with the odd core after removing O₂(K). In the central-Fitting case,
component minimality makes the proper odd kernel solvable and hence central;
in the noncentral case the proved A.3.6 kernel theorem applies. Transport
through the actual relative component and canonical quotient maps gives
K/O₂,F(K) ≃ SL₂(p) from the source's iterated two-odd quotient.

No nilpotent-kernel row, splitting, or bound on a homocyclic exponent is
assumed. The original-flag application in OddIndex.Source uses this model
to identify the exact remaining radical index. Its numerical bound stays
with qt-d-1222-shadow-component-triangle.
Source: Aschbacher–Smith A.3.6, pp.43–45; 11.1.2(1), p.761;
11.4.1(3), p.776.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical
variable {G : Type*} [Group G] [Finite G]

private theorem component_fitting_eq_oddCore {κ : GroupClass}
    (hs : IsSQTK κ G) (hO : pCore 2 G = ⊥) {A : Subgroup G}
    (hA : A.IsCComponent) {p : ℕ} (hp : 3 < p)
    (hm : Source.IsSL (A ⧸ pPrimeCore 2 A) 2 p) :
    fittingSubgroup A = pPrimeCore 2 A := by
  by_cases hc : fittingSubgroup A ≤ center A
  · have hN : pPrimeCore 2 A ≠ ⊤ := by
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      let : IsQuasisimple (A ⧸ pPrimeCore 2 A) :=
        Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv (by omega) e
      let : IsSimpleGroup ((A ⧸ pPrimeCore 2 A) ⧸ center (A ⧸ pPrimeCore 2 A)) :=
        IsQuasisimple.simple
      let : Nontrivial (A ⧸ pPrimeCore 2 A) := Function.Surjective.nontrivial
        (QuotientGroup.mk'_surjective (center (A ⧸ pPrimeCore 2 A)))
      intro he
      have : Subsingleton (A ⧸ pPrimeCore 2 A) := by
        rw [he]
        exact QuotientGroup.subsingleton_quotient_top
      exact not_subsingleton _ this
    let : Group.IsSolvable (pPrimeCore 2 A) :=
      hA.isSolvable_of_subnormal_lt_top (inferInstance : (pPrimeCore 2 A).Normal).isSubnormal hN
    exact le_antisymm (ChapterA.Section03.NoncentralFitting.fitting_le_oddCore hA hO)
      (((le_solvableRadical _ inferInstance inferInstance).trans
        (solvableRadical_le_center_of_fitting_le_center hc)).trans
        (le_sSup ⟨inferInstance, inferInstance⟩ : center A ≤ fittingSubgroup A))
  · exact (ChapterA.Section03.NoncentralFitting.noncentral_fitting_quotient_consequences
      ChapterA.RankActions.primeSL2CoverRigidity hs hO hA hc).1

/-- Intrinsic component structure identifies the actual odd kernel with F. -/
theorem intrinsic_fitting_eq_oddCore {Q : Type*} [Group Q] [Finite Q]
    {κ : GroupClass} (hs : IsSQTK κ Q) (hO : pCore 2 Q = ⊥)
    (hQ : (⊤ : Subgroup Q).IsCComponent) {p : ℕ} (hp : 3 < p)
    (hm : Source.IsSL (Q ⧸ pPrimeCore 2 Q) 2 p) :
    fittingSubgroup Q = pPrimeCore 2 Q := by
  let e := topEquiv (G := Q)
  obtain ⟨F,_,_,hF,⟨a⟩⟩ := hm
  have hm' : Source.IsSL ((⊤ : Subgroup Q) ⧸ pPrimeCore 2 (⊤ : Subgroup Q)) 2 p :=
    ⟨F,inferInstance,inferInstance,hF,
      ⟨(QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)).trans a⟩⟩
  have he := congrArg (map e.toMonoidHom) (component_fitting_eq_oddCore hs hO hQ hp hm')
  simpa only [map_fitting_equiv, pPrimeCore_map_iso] using he

/-- Relative component membership suffices; no ambient normality is imposed. -/
theorem relative_twoFitting_model_of_twoOdd_sl2 {N K : Subgroup G}
    {κ : GroupClass} (hs : IsSQTK κ N) (hK : Source.ComponentIn N K)
    {p : ℕ} (hp : 3 < p) (hm : Source.IsSL (Source.TwoOddQuotient K) 2 p) :
    Source.IsSL (K ⧸ twoFittingCore K) 2 p := by
  let Q := K ⧸ pCore 2 K
  have hKs : IsSQTK κ K := (IsSQTK.equiv (subgroupOfEquivOfLe hK.1)).mp
    (hs.subgroup (K.subgroupOf N))
  have hQs : IsSQTK κ Q := by
    refine ⟨?_, hKs.isKGroup.quotient _⟩
    intro r hr ho
    let : Fact r.Prime := ⟨hr⟩
    exact (primeRank_quotient_le_of_isTwoGroup r ho _ pCore_isPGroup).trans
      (hKs.stronglyQuasithin r hr ho)
  have htop : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using hK.2.subgroupOf_of_le le_rfl hK.1
  let : Group.IsNilpotent (pCore 2 K) := pCore_isPGroup.isNilpotent
  have hQ : (⊤ : Subgroup Q).IsCComponent := by
    simpa only [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using
      htop.map_quotient (pCore 2 K)
  have hfit := intrinsic_fitting_eq_oddCore hQs (pCore_quotient_pCore_eq_bot 2) hQ hp hm
  let q := (QuotientGroup.mk' (pPrimeCore 2 Q)).comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q :=
    (QuotientGroup.mk'_surjective (pPrimeCore 2 Q)).comp
      (QuotientGroup.mk'_surjective (pCore 2 K))
  have hk : twoFittingCore K = q.ker := by
    change (fittingSubgroup Q).comap (QuotientGroup.mk' _) = _
    rw [hfit]
    ext k
    exact (QuotientGroup.eq_one_iff (N := pPrimeCore 2 Q)
      (QuotientGroup.mk' (pCore 2 K) k)).symm
  obtain ⟨F,_,_,hF,⟨a⟩⟩ := hm
  exact ⟨F,inferInstance,inferInstance,hF,
    ⟨(QuotientGroup.liftEquiv (twoFittingCore K) hq hk).trans a⟩⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical

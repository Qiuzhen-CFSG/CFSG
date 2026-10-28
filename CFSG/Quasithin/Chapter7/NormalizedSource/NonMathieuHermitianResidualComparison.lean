module
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianJankoComparison
public import Theory.GroupTheory.GeneralizedFitting.ComponentFixedInvolution
public import Theory.Mathieu.M22.Properties.ThreeRank
import all CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.OddActorComparison

/-!
# The paired centralizer seed and its ambient comparison component

An injectively embedded full component-centralizer residual is normal in
the paired centralizer when the original component is normal in C_G(r).
Transport its intrinsic C-component property and its actual M₂₂ radical
quotient through that inclusion. The three-rank-two theorem then puts this
same residual in a unique normal C-component of C_G(z), whose full two-core
quotient is quasisimple.

The proof-only import reuses the generic ambient component theorem already
proved in the Mathieu implementation. Its unrelated chapter exports stay
private, avoiding the existing homonymous rank-one export. The Hermitian
consumer supplies the actual residual and both original involutions.
Source: Aschbacher--Smith 1.2.1 and 4.4.3, printed pp.504,623, as used in
8.2.7, p.718, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open MathieuGeneration
variable {G : Type*} [Group G] [Finite G]

/-- The full residual, with its literal map, is a normal paired seed and
has a unique normal containing component in the full involution centralizer. -/
theorem hermitian_paired_seed_component
    {K : Type*} [Group K] [Finite K]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (f : K →* G) (hi : Function.Injective f) (z : K) (hz : orderOf (f z) = 2) (r : G)
    (hKr : f.range ≤ centralizer ({r} : Set G))
    (hn : centralizer ({r} : Set G) ≤ normalizer (f.range : Set G))
    (hseed : (solvableResidual (centralizer ({z} : Set K))).IsCComponent)
    (e : (solvableResidual (centralizer ({z} : Set K)) ⧸
      solvableRadical (solvableResidual (centralizer ({z} : Set K)))) ≃* Sporadic.Mathieu.M22) :
    let E := centralizer ({f z} : Set G) ⊓ centralizer ({r} : Set G)
    ∃ P : Subgroup E, P.IsCComponent ∧ P.Normal ∧
      Nonempty ((P ⧸ solvableRadical P) ≃* Sporadic.Mathieu.M22) ∧
      P.map E.subtype = ((solvableResidual (centralizer ({z} : Set K))).map
        (centralizer ({z} : Set K)).subtype).map f ∧
      ∃! Q : Subgroup (centralizer ({f z} : Set G)),
        Q.IsCComponent ∧ P.map (inclusion inf_le_left) ≤ Q ∧ Q.Normal ∧
          IsQuasisimple (Q ⧸ pCore 2 Q) := by
  let C := centralizer ({z} : Set K)
  let R := solvableResidual C
  let g := f.comp C.subtype
  let S := R.map g
  let E := centralizer ({f z} : Set G) ⊓ centralizer ({r} : Set G)
  have hg : Function.Injective g := hi.comp C.subtype_injective
  have hSE : S ≤ E := by
    rintro _ ⟨x,hx,rfl⟩
    refine ⟨mem_centralizer_singleton_iff.mpr ?_,hKr ⟨x,rfl⟩⟩
    change f (x : K) * f z = f z * f (x : K)
    exact (map_mul f (x : K) z).symm.trans
      ((congrArg f (mem_centralizer_singleton_iff.mp x.property)).trans (map_mul f z (x : K)))
  have hNS : E ≤ normalizer (S : Set G) :=
    (le_inf (inf_le_right.trans hn) inf_le_left).trans
      (centralizer_residual_image_normalized f hi z)
  let P := S.subgroupOf E
  have hPn : P.Normal := (normal_subgroupOf_iff_le_normalizer hSE).mpr hNS
  let t : R ≃* P := (R.equivMapOfInjective g hg).trans
    (subgroupOfEquivOfLe hSE).symm
  have htopR : (⊤ : Subgroup R).IsCComponent := by
    have hh := hseed.subgroupOf (le_refl R)
    change (R.subgroupOf R).IsCComponent at hh
    simpa only [subgroupOf_self] using hh
  have htopP : (⊤ : Subgroup P).IsCComponent := by
    simpa only [map_top_of_surjective t.toMonoidHom t.surjective] using htopR.map_equiv t
  have hP : P.IsCComponent := by
    have hh := htopP.map_subtype hPn.isSubnormal
    simpa only [←MonoidHom.range_eq_map,range_subtype] using hh
  let q := (QuotientGroup.congr _ _ t.symm (map_solvableRadical_equiv t.symm)).trans e
  exact ⟨P,hP,hPn,⟨q⟩,(map_subgroupOf_eq_of_le hSE).trans (map_map _ _ _).symm,
    mathieu_residual_ambient_placement hG hz inf_le_left P hP q⟩


end CFSG.Quasithin.Chapter7.NormalizedSource

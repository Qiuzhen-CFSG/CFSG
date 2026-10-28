module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourCentralizerReselection
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourResidualSeed
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianResidualComparison
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceRankOnePushingUpOrdinary

/-!
# The actual Hermitian residual seed in the ambient involution centralizer

The original module has trivial fixed space under the original intersection
residual. Consequently its involutions survive the central quotient of the
full ordinary J₄ component. The central two-cover theorem then gives the
entire component-centralizer residual its actual M₂₂ radical quotient.

Use the reselected core involution r and the same original T-fixed module
involution z. Their paired centralizer contains that residual as a normal
C-component. Its radical quotient has three-rank two, so the full C_G(z)
has a unique normal containing C-component Q, with quasisimple Q/O₂(Q).
The original odd actor and T both normalize Q. The native nine-space
obstruction forces both the full seed and Q to escape N_G(L).

The remaining comparison must control the actual odd actor on this Q.
The seed is placed in C_G(r) intersect C_G(z); its placement in the odd
actor centralizer has not been asserted. Whole-normalizer control and the
subsequent 8.2.7--13 assembly remain open. The proof-only rank-one import
reuses the original residual's fixed-space calculation without widening
its public boundary.
Source: Aschbacher--Smith 1.2.1, 4.4.3 and 8.2.7, printed pp.504,623,718,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter4 Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl
open Chapter4.Section02.RankOneReciprocalEscape
open Chapter8.Section02.HermitianSource
open Chapter7.NormalizedSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- The original module involution has an actual M22 residual in the full
ordinary component, with all central two-kernels retained. -/
theorem sourceOrbit_hermitian_ordinary_involution_seed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2)
    {A J H W : Subgroup G} (hw : Witness L D.sourceOrbit A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (z : K) (hzV : ((z : H) : G) ∈ D.sourceOrbit) (hz : orderOf z = 2) :
    (solvableResidual (centralizer ({z} : Set K))).IsCComponent ∧
      Nonempty ((solvableResidual (centralizer ({z} : Set K)) ⧸
        solvableRadical (solvableResidual (centralizer ({z} : Set K)))) ≃*
          Sporadic.Mathieu.M22) := by
  obtain ⟨e⟩ := D.sourceOrbit_hermitian_field_four_ordinary_janko
    h hmany hV hnon d B eQ hfield hw K hK
  obtain ⟨_,_,hfix,_⟩ := D.sourceOrbit_pushingUp_residual_data h hmany hV hnon hw
  have hc := hw.2.2.2.2.2.2.1
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hFK : F ≤ K.map H.subtype := by
    intro x hx
    exact ⟨⟨x,hc.component_le.trans hc.local_le hx⟩,
      hc.ordinary_component_contains_original K hK hx,rfl⟩
  let := hK.2
  have hcenter : center K = pCore 2 K :=
    IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot hc.oddCore_eq_bot K)
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hk : f.ker = center K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hzne : f z ≠ 1 := by
    intro he
    have hzc : z ∈ center K := hk ▸ he
    have hzF : ((z : H) : G) ∈ centralizer (F : Set G) := by
      intro x hx
      obtain ⟨y,hy,he⟩ := hFK hx
      rw [←he]
      exact congrArg (H.subtype.comp K.subtype) (mem_center_iff.mp hzc ⟨y,hy⟩)
    have hb := hfix.le ⟨hzV,hzF⟩
    have hez : z = 1 := Subtype.ext (Subtype.ext (mem_bot.mp hb))
    rw [hez,orderOf_one] at hz
    omega
  have hzq : orderOf (f z) = 2 := orderOf_eq_prime (by
    rw [←map_pow,←hz,pow_orderOf_eq_one,map_one]) hzne
  exact janko_two_cover_involution_residual f
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) hk.le
    (hk.symm ▸ (hcenter.symm ▸ pCore_isPGroup)) z hzq

/-- The paired centralizer contains the same full residual as a normal
C-component, and the full z-centralizer has a unique containing component. -/
theorem sourceOrbit_hermitian_paired_residual_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2)
    {A J H W : Subgroup G} (hw : Witness L D.sourceOrbit A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (r : G) (hKr : K.map H.subtype ≤ centralizer ({r} : Set G))
    (hnK : ((K.map H.subtype).subgroupOf (centralizer ({r} : Set G))).Normal)
    (z : K) (hzV : ((z : H) : G) ∈ D.sourceOrbit) (hz : orderOf z = 2) :
    let C := centralizer ({((z : H) : G)} : Set G)
    let E := C ⊓ centralizer ({r} : Set G)
    ∃ P : Subgroup E, P.IsCComponent ∧ P.Normal ∧
      Nonempty ((P ⧸ solvableRadical P) ≃* Sporadic.Mathieu.M22) ∧
      P.map E.subtype = ((solvableResidual (centralizer ({z} : Set K))).map
        (centralizer ({z} : Set K)).subtype).map (H.subtype.comp K.subtype) ∧
      ∃! Q : Subgroup C, Q.IsCComponent ∧ P.map (inclusion inf_le_left) ≤ Q ∧
        Q.Normal ∧ IsQuasisimple (Q ⧸ pCore 2 Q) := by
  obtain ⟨hs,⟨es⟩⟩ := D.sourceOrbit_hermitian_ordinary_involution_seed
    h hmany hV hnon d B eQ hfield hw K hK z hzV hz
  let f := H.subtype.comp K.subtype
  have hf : f.range = K.map H.subtype := by rw [MonoidHom.range_comp,range_subtype]
  have hfn : centralizer ({r} : Set G) ≤ normalizer (f.range : Set G) := by
    rw [hf]
    exact (normal_subgroupOf_iff_le_normalizer hKr).mp hnK
  have hzG : orderOf (f z) = 2 :=
    (orderOf_coe (z : H)).trans ((orderOf_coe z).trans hz)
  exact hermitian_paired_seed_component h.simpleQTKE f
    (H.subtype_injective.comp K.subtype_injective) z hzG r (hf.symm ▸ hKr) hfn hs es

/-- The actual escaping noncubic actor supplies the full paired M22 seed
and a T-normalized ambient component escaping the original normalizer. -/
theorem sourceOrbit_hermitian_oddActor_ambient_residual_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2)
    {p : ℕ} (hp : p.Prime) (hgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    ∃ J H W : Subgroup G, Witness L D.sourceOrbit A J H W ∧
      ∃ K : Subgroup H, IsComponent H K ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
        ∃ (r : G) (z : K),
          r ∈ H.pCoreIn 2 ∧ r ∈ J.pCoreIn 2 ∧ orderOf r = 2 ∧
          ((z : H) : G) ∈ D.sourceOrbit ∧ orderOf z = 2 ∧
          (T : Subgroup G) ≤ centralizer ({((z : H) : G)} : Set G) ∧
          K.map H.subtype ≤ centralizer ({r} : Set G) ∧
          J.pCoreIn 2 ≤ centralizer ({r} : Set G) ⊓ centralizer ({((z : H) : G)} : Set G) ∧
          let C := centralizer ({((z : H) : G)} : Set G)
          let E := C ⊓ centralizer ({r} : Set G)
          let S := ((solvableResidual (centralizer ({z} : Set K))).map
            (centralizer ({z} : Set K)).subtype).map (H.subtype.comp K.subtype)
          ∃ P : Subgroup E, P.IsCComponent ∧ P.Normal ∧
            Nonempty ((P ⧸ solvableRadical P) ≃* Sporadic.Mathieu.M22) ∧ P.map E.subtype = S ∧
            ∃ Q : Subgroup C, Q.IsCComponent ∧ Q.Normal ∧ IsQuasisimple (Q ⧸ pCore 2 Q) ∧
              P.map (inclusion inf_le_left) ≤ Q ∧ S ≤ Q.map C.subtype ∧
              (T : Subgroup G) ≤ normalizer (Q.map C.subtype : Set G) ∧
              A ≤ C ∧ A ≤ normalizer (Q.map C.subtype : Set G) ∧
              ¬ S ≤ normalizer (L : Set G) ∧ ¬ Q.map C.subtype ≤ normalizer (L : Set G) := by
  obtain ⟨J,H,W,hw,K,hK,heK,r,z,hr,hRr,hr2,hzV,hz,hTz,hKr,hRpair,
    _,hnK,hescape,_,_⟩ := D.sourceOrbit_hermitian_oddActor_paired_centralizers
      h hmany hV hnon d B eQ hfield hp hgt A hne hAe hA hout
  obtain ⟨P,hP,hnP,heP,hmP,Q,hQ,_⟩ := D.sourceOrbit_hermitian_paired_residual_component
    h hmany hV hnon d B eQ hfield hw K hK r hKr hnK z hzV hz
  let C := centralizer ({((z : H) : G)} : Set G)
  let := hQ.2.2.1
  have hnQ : C ≤ normalizer (Q.map C.subtype : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      Q.le_normalizer_map C.subtype
  have hAC : A ≤ C := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (((hA ha).2) _ hzV).symm
  have hSQ := map_mono (f := C.subtype) hQ.2.1
  rw [map_map,subtype_comp_inclusion,hmP] at hSQ
  exact ⟨J,H,W,hw,K,hK,heK,r,z,hr,hRr,hr2,hzV,hz,hTz,hKr,hRpair,
    P,hP,hnP,heP,hmP,Q,hQ.1,hQ.2.2.1,hQ.2.2.2,hQ.2.1,hSQ,hTz.trans hnQ,hAC,hAC.trans hnQ,
    hescape,fun he => hescape (hSQ.trans he)⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

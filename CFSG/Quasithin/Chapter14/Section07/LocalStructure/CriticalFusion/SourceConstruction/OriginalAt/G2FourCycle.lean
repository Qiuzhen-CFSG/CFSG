module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2SourceFourCycle
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.G2Lines

/-!
# The original G₂ quotient four-cycle from local structure

The common pencil supplies two distinct commutator planes and its
original point denominator. Transport all four actual seed conjugates
to the same quotient; the generalized hexagon excludes their four-cycle.

Only Structural1222At at the original G,T is used. The source producers
qt-d-1222-source and qt-d-1434-source retain the earlier structural and
faithful inputs. Original residual alternatives, uniqueness, relative
component and alternating recognition retain qt-d-14763-source-data.
Final source 14.7.75 discharge remains with qt-d-14775-source.
Source: Aschbacher–Smith 14.7.53–63, pp.1065–1069; F.9.18, pp.325–326.
The reused concrete model calculations retain LICENSES/ATLAS.txt attribution.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open G2Exclusion G2Exclusion.MarkedGeometry
open G2Exclusion.MarkedGeometry.MarkedPencil.Actors
open G2Exclusion.MarkedGeometry.LocalParabolics.ThreeOffenderOrbit
open Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance
open Atlas.G2.Natural.BinaryPointFlag
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) (HStar F.H) W}
  (c : BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (starMap F)))

include c in
private theorem false_of_conjugate_seed_quadrangle_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (f : HStar F.H →* Atlas.G2.Model (ZMod 2)) (hf : Function.Injective f)
    (hJ : commutator (Atlas.G2.Model (ZMod 2)) ≤ f.range)
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (he : ∀ a v, E (m.action (f a) v) = σ a (E v))
    (U A P Z R S N : Subgroup G)
    (hP : Nat.card P = 2) (hZ : Nat.card Z = 2)
    (hR : Nat.card R = 4) (hS : Nat.card S = 4)
    (hPA : ¬ P ≤ A) (hZU : ¬ Z ≤ U) (hZA : Z ≤ A)
    (hRU : R ≤ U) (hRA : R ≤ A) (hSU : S ≤ U) (hSA : S ≤ A)
    (hNR : N ≤ R) (hNS : N ≤ S) (hRS : R ≠ S)
    (hRP : ∃ g : G, R ⊔ P = conjugate V g)
    (hSP : ∃ g : G, S ⊔ P = conjugate V g)
    (hRZ : ∃ g : G, R ⊔ Z = conjugate V g)
    (hSZ : ∃ g : G, S ⊔ Z = conjugate V g)
    (g : G) (hNg : N = conjugate (F.Vi 1) g) : False := by
  let φ := (MulAut.conj g).toMonoidHom
  have hi : Function.Injective φ := (MulAut.conj g).injective
  have hNφ : N.map φ = F.Vi 1 := by
    rw [hNg]
    exact conjBy_inv' _ _
  have seed (B D : Subgroup G) (hBD : ∃ a : G, B ⊔ D = conjugate V a) :
      ∃ a : G, B.map φ ⊔ D.map φ = conjugate V a := by
    obtain ⟨a,ha⟩ := hBD
    refine ⟨a*g⁻¹,?_⟩
    rw [←Subgroup.map_sup,ha]
    change (V.conjBy a⁻¹).conjBy g = V.conjBy (a*g⁻¹)⁻¹
    rw [←conjBy_mul,mul_inv_rev,inv_inv]
  exact false_of_source_seed_quadrangle c h f hf hJ m E he
    (U.map φ) (A.map φ) (P.map φ) (Z.map φ) (R.map φ) (S.map φ)
    ((card_map_of_injective hi).trans hP) ((card_map_of_injective hi).trans hZ)
    ((card_map_of_injective hi).trans hR) ((card_map_of_injective hi).trans hS)
    (fun hh => hPA ((map_le_map_iff_of_injective hi).mp hh))
    (fun hh => hZU ((map_le_map_iff_of_injective hi).mp hh))
    (map_mono hZA) (map_mono hRU) (map_mono hRA) (map_mono hSU) (map_mono hSA)
    (hNφ ▸ map_mono hNR) (hNφ ▸ map_mono hNS) (fun hh => hRS (map_injective hi hh))
    (seed R P hRP) (seed S P hSP) (seed R Z hRZ) (seed S Z hSZ)

include c in
theorem source_critical_contradiction_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (hfit : Theory.GroupTheory.generalizedFitting (HStar F.H) = star F (K F))
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hf : Function.Injective σ) (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (P : Sylow 2 (HStar F.H)) (hP : star F (K F) ⊔ (P : Subgroup (HStar F.H)) = ⊤)
    (orbit : letI : (star F (K F)).Normal := hfit ▸ inferInstance
      letI : Finite W := Finite.of_surjective (fun x : F.U => (c.coordinates x).toAdd)
        (Multiplicative.toAdd.surjective.comp c.onto)
      OrbitInputs σ (star F (K F)) P hP)
    (path : CriticalPath (L := L) F) (selection : path.RankSelection) : False := by
  have hplace := LocalReduction.critical_le_Ri_at h structural path
  obtain ⟨i,hi,hJ,m,E,he,p,r,q,hA,_,_,_,hpoint,_,_,hseed⟩ :=
    source_reciprocal_geometry_at c h hab hcomponent hfit eK structural hf hcomm P hP orbit
      path hplace selection
  obtain ⟨N,R,S,_,hNR,hNS,hRS,hR,hS,g,hNg⟩ :=
    source_pencil_common_point c h path hplace i hi m E he p hA hpoint
  obtain ⟨hRc,hRU,hRA,hRP,hRZ⟩ := hseed R hR.1 hR.2
  obtain ⟨hSc,hSU,hSA,hSP,hSZ⟩ := hseed S hS.1 hS.2
  have hZc : Nat.card path.Zα = 2 := by
    rw [CriticalPath.Zα,conjugate,card_map_of_injective (MulAut.conj path.conjugator⁻¹).injective]
    simpa using F.card 1 (by decide)
  have hZA : path.Zα ≤ path.Uα := map_mono c.kernel_le
  exact false_of_conjugate_seed_quadrangle_at c h i hi.1 hJ m E he
    F.U path.Uα (F.Vi 1) path.Zα R S N
    (by simpa using F.card 1 (by decide)) hZc hRc hSc hpoint
    (source_critical_point_not_le_span_at c h hab hcomponent hfit eK structural hf hcomm
      P hP orbit path hplace selection) hZA hRU hRA hSU hSA hNR hNS hRS
    (by obtain ⟨a,ha⟩ := hRP; exact ⟨a,ha⟩)
    (by obtain ⟨a,ha⟩ := hSP; exact ⟨a,ha⟩) hRZ hSZ g hNg

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source

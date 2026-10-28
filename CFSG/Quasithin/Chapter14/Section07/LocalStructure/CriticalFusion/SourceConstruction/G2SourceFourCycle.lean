module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2SourcePencil

/-!
# The original reciprocal pencil gives a quotient four-cycle

Every seed conjugate through V₁ is a geometric line on the original
natural/Weyl module. The four seed joins supplied by the reciprocal
commutator family therefore give four lines through its common denominator.
Conjugating that denominator back to V₁ puts them all on the same literal
quotient U/V₁. Relative-index counts identify the four point images, and
the two original noncontainments separate them. The concrete octonion
four-cycle obstruction now gives a contradiction.

The final theorem applies this construction to the original selected
critical path. It constructs the same reciprocal actors, common family,
order-two denominator, four points and four lines; no geometry or marking
premise remains. Selection of the initial critical path and the final
G₂-residual/source-data application are still separate assembly steps.
The faithful action, generalized-Fitting identity, core-commutator identity,
structural and F.9.18 orbit inputs retain their earlier source producers.

Source: Aschbacher--Smith, 14.7.53, 14.7.61--62 and formulas (a)--(d),
(a′),(c′), printed pp.1065--1069. Model conventions retain LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
open Chapter12.Section08 CriticalFusion.Source
open G2Exclusion G2Exclusion.MarkedGeometry
open G2Exclusion.MarkedGeometry.LocalParabolics.ThreeOffenderOrbit
open G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) (HStar F.H) W}
  (c : BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (starMap F)))

omit [Finite G] in
private theorem card_two_disjoint (P A : Subgroup G) (hP : Nat.card P = 2)
    (hne : ¬ P ≤ A) : Disjoint P A := by
  let : Fact (Nat.card P).Prime := ⟨by rw [hP]; decide⟩
  rcases (A.subgroupOf P).eq_bot_or_eq_top_of_prime_card with hb | ht
  · apply disjoint_iff.mpr
    have hh := congrArg (map P.subtype) hb
    simpa only [subgroupOf_map_subtype,Subgroup.map_bot,inf_comm] using hh
  · exact (hne (fun x hx => show (⟨x,hx⟩ : P) ∈ A.subgroupOf P from ht ▸ mem_top _)).elim

include c in
/-- Four actual seed conjugates above the same flag point give the literal
quotient four-cycle contradiction. Every geometric line and point is
constructed from the same source module identification. -/
theorem false_of_source_seed_quadrangle
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (f : HStar F.H →* Atlas.G2.Model (ZMod 2)) (hf : Function.Injective f)
    (hJ : commutator (Atlas.G2.Model (ZMod 2)) ≤ f.range)
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (he : ∀ a v, E (m.action (f a) v) = σ a (E v))
    (U A P Z R S : Subgroup G)
    (hP : Nat.card P = 2) (hZ : Nat.card Z = 2)
    (hR : Nat.card R = 4) (hS : Nat.card S = 4)
    (hPA : ¬ P ≤ A) (hZU : ¬ Z ≤ U) (hZA : Z ≤ A)
    (hRU : R ≤ U) (hRA : R ≤ A) (hSU : S ≤ U) (hSA : S ≤ A)
    (hNR : F.Vi 1 ≤ R) (hNS : F.Vi 1 ≤ S) (hRS : R ≠ S)
    (hRP : ∃ g : G, R ⊔ P = conjugate V g)
    (hSP : ∃ g : G, S ⊔ P = conjugate V g)
    (hRZ : ∃ g : G, R ⊔ Z = conjugate V g)
    (hSZ : ∃ g : G, S ⊔ Z = conjugate V g) : False := by
  let := c.kernel_normal
  let N := (F.Vi 1).subgroupOf F.U
  let π := QuotientGroup.mk' N
  let geom := transportGeometry m.singularMap.geometry (literalModuleEquiv c m E)
  have line (B : Subgroup G) (hNB : F.Vi 1 ≤ B)
      (hB : ∃ g : G, B = conjugate V g) :
      B ≤ F.U ∧ ∃ l : ZeroProductLine (ZMod 2),
        geom.line l = (B.subgroupOf F.U).map π := by
    obtain ⟨g,rfl⟩ := hB
    obtain ⟨hCU,l,hi⟩ := source_conjugate_seed_line c h f hf hJ m E he g hNB
    exact ⟨hCU,l,quotient_image_of_model_image c m E _ _ hi⟩
  obtain ⟨hRPU,lRP,hlRP⟩ := line (R ⊔ P) (hNR.trans le_sup_left) hRP
  obtain ⟨hSPU,lSP,hlSP⟩ := line (S ⊔ P) (hNS.trans le_sup_left) hSP
  obtain ⟨hRZU,lRZ,hlRZ⟩ := line (R ⊔ Z) (hNR.trans le_sup_left) hRZ
  obtain ⟨hSZU,lSZ,hlSZ⟩ := line (S ⊔ Z) (hNS.trans le_sup_left) hSZ
  have hPU : P ≤ F.U := le_sup_right.trans hRPU
  have hZU' : Z ≤ F.U := le_sup_right.trans hRZU
  have hRU' : R ≤ F.U := le_sup_left.trans hRPU
  have hSU' : S ≤ F.U := le_sup_left.trans hSPU
  have card_image (B : Subgroup G) (hBU : B ≤ F.U) :
      Nat.card ((B.subgroupOf F.U).map π) = (F.Vi 1).relIndex B := by
    rw [←relIndex_ker,QuotientGroup.ker_mk',relIndex_subgroupOf hBU]
  have point_card (B D : Subgroup G) (hBU : B ≤ F.U)
      (hc : Nat.card B = 2) (hBD : ¬ B ≤ D) (hND : F.Vi 1 ≤ D) :
      Nat.card ((B.subgroupOf F.U).map π) = 2 := by
    rw [card_image B hBU]
    have hd := (card_two_disjoint B D hc hBD).mono_right hND
    rw [←inf_relIndex_right,inf_comm,hd.eq_bot,relIndex_bot_left,hc]
  have four_card (B : Subgroup G) (hBU : B ≤ F.U)
      (hc : Nat.card B = 4) (hNB : F.Vi 1 ≤ B) :
      Nat.card ((B.subgroupOf F.U).map π) = 2 := by
    rw [card_image B hBU]
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) (F.Vi 1) B bot_le hNB
    rw [relIndex_bot_left,relIndex_bot_left,F.card 1 (by decide),hc] at hh
    omega
  have hPc := point_card P A hPU hP hPA (hNR.trans hRA)
  have hZc := point_card Z U hZU' hZ hZU (hNR.trans hRU)
  have hRc := four_card R hRU' hR hNR
  have hSc := four_card S hSU' hS hNS
  obtain ⟨p,hp,_⟩ := point_of_card_two_le_line m.singularMap (literalModuleEquiv c m E)
    ((P.subgroupOf F.U).map π) hPc lRP (by rw [hlRP]; exact map_mono (comap_mono le_sup_right))
  obtain ⟨z,hz,_⟩ := point_of_card_two_le_line m.singularMap (literalModuleEquiv c m E)
    ((Z.subgroupOf F.U).map π) hZc lRZ (by rw [hlRZ]; exact map_mono (comap_mono le_sup_right))
  obtain ⟨r,hr,_⟩ := point_of_card_two_le_line m.singularMap (literalModuleEquiv c m E)
    ((R.subgroupOf F.U).map π) hRc lRP (by rw [hlRP]; exact map_mono (comap_mono le_sup_left))
  obtain ⟨s,hs,_⟩ := point_of_card_two_le_line m.singularMap (literalModuleEquiv c m E)
    ((S.subgroupOf F.U).map π) hSc lSP (by rw [hlSP]; exact map_mono (comap_mono le_sup_left))
  apply false_of_source_quotient_line_families N geom
    (U.subgroupOf F.U) (A.subgroupOf F.U) (P.subgroupOf F.U) (Z.subgroupOf F.U)
    (R.subgroupOf F.U) (S.subgroupOf F.U)
    (fun hh => hPA (fun x hx => hh (show (⟨x,hPU hx⟩ : F.U) ∈ P.subgroupOf F.U from hx)))
    (fun hh => hZU (fun x hx => hh (show (⟨x,hZU' hx⟩ : F.U) ∈ Z.subgroupOf F.U from hx)))
    (comap_mono hZA) (comap_mono hRU) (comap_mono hRA) (comap_mono hSU) (comap_mono hSA)
    (comap_mono hNR) (comap_mono hNS) ?_ p z r s hp hz hr hs lRP lSP lRZ lSZ
    (by rwa [subgroupOf_sup hRU' hPU] at hlRP)
    (by rwa [subgroupOf_sup hSU' hPU] at hlSP)
    (by rwa [subgroupOf_sup hRU' hZU'] at hlRZ)
    (by rwa [subgroupOf_sup hSU' hZU'] at hlSZ)
  intro hh
  apply hRS
  have hh' := congrArg (map F.U.subtype) hh
  simpa only [map_subgroupOf_eq_of_le hRU',map_subgroupOf_eq_of_le hSU'] using hh'


include c in
/-- Transport the common point back to V₁ before constructing the literal
quotient. The four seed conjugates then lie in one and the same geometry. -/
private theorem false_of_conjugate_seed_quadrangle
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

open Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance

include c in
/-- The actual selected critical pair is impossible in the G₂ residual
branch. Both reciprocal actors, the common family, its denominator and all
four lines in the literal quotient are constructed from the original inputs. -/
theorem source_critical_contradiction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (hfit : Theory.GroupTheory.generalizedFitting (HStar F.H) = star F (K F))
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hf : Function.Injective σ) (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (P : Sylow 2 (HStar F.H)) (hP : star F (K F) ⊔ (P : Subgroup (HStar F.H)) = ⊤)
    (orbit : letI : (star F (K F)).Normal := hfit ▸ inferInstance
      letI : Finite W := Finite.of_surjective (fun x : F.U => (c.coordinates x).toAdd)
        (Multiplicative.toAdd.surjective.comp c.onto)
      OrbitInputs σ (star F (K F)) P hP)
    (path : CriticalPath (L := L) F) (selection : path.RankSelection) : False := by
  have hplace := LocalReduction.critical_le_Ri h structural path
  obtain ⟨i,hi,hJ,m,E,he,p,r,q,hA,_,_,_,hpoint,_,_,hseed⟩ :=
    source_reciprocal_geometry c h hab hcomponent hfit eK structural hf hcomm P hP orbit
      path hplace selection
  obtain ⟨N,R,S,_,hNR,hNS,hRS,hR,hS,g,hNg⟩ :=
    source_pencil_common_point c h path hplace i hi m E he p hA hpoint
  obtain ⟨hRc,hRU,hRA,hRP,hRZ⟩ := hseed R hR.1 hR.2
  obtain ⟨hSc,hSU,hSA,hSP,hSZ⟩ := hseed S hS.1 hS.2
  have hZc : Nat.card path.Zα = 2 := by
    rw [CriticalPath.Zα,conjugate,card_map_of_injective (MulAut.conj path.conjugator⁻¹).injective]
    simpa using F.card 1 (by decide)
  have hZA : path.Zα ≤ path.Uα := map_mono c.kernel_le
  exact false_of_conjugate_seed_quadrangle c h i hi.1 hJ m E he
    F.U path.Uα (F.Vi 1) path.Zα R S N
    (by simpa using F.card 1 (by decide)) hZc hRc hSc hpoint
    (source_critical_point_not_le_span c h hab hcomponent hfit eK structural hf hcomm
      P hP orbit path hplace selection) hZA hRU hRA hSU hSA hNR hNS hRS
    (by obtain ⟨a,ha⟩ := hRP; exact ⟨a,ha⟩)
    (by obtain ⟨a,ha⟩ := hSP; exact ⟨a,ha⟩) hRZ hSZ g hNg

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source

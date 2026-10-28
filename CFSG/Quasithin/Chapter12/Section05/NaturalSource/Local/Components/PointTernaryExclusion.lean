module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.PointCoverExclusion
public import Theory.SpecificGroups.OddThreeSevenResidual

/-!
# Completing the original point-component catalogue

The image of (L₁T) ∩ K₁ has two-core quotient of order dividing 168,
using its actual map from the original L₁T. It contains the full relative
Sylow and normalizes the literal residual image. In either ternary-seven
sign that image is SL₂(7), so the linear or unitary scalar-centralizer
bound excludes the last model. The complete catalogue now gives exactly
the source point alternatives, including Y ≤ K₁ in the large rows.
The checked three-space exclusion then constructs all of LocalComponents
without assuming a point refinement or any normalizer containment.

Components.Source applies this construction to the original normalizer
and strict-enlargement reductions. Those remaining source arguments stay
with qt-d-1251-local; qt-d-1251-source retains final exterior assembly.
Source: Aschbacher--Smith 12.5.3, printed pp.817--819.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 Chapter1.Section02.LocalModels
open Theory.SpecificGroups.OddThreeSevenResidual
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

/-- The original intersection retains the order-168 bound even when its
two-core is nontrivial. -/
theorem pointResidualIntersectionImage_core_quotient_card {K : Subgroup G}
    {X : Type*} [Group X] [Finite X] (ψ : K →* X) :
    Nat.card (s.pointResidualIntersectionImage K ψ ⧸
      pCore 2 (s.pointResidualIntersectionImage K ψ)) ∣ 168 := by
  let J := s.marking.Li 1 ⊔ (T : Subgroup G)
  let A := J ⊓ K
  let f := ψ.comp (inclusion (show A ≤ K from inf_le_right))
  let q := (QuotientGroup.mk' (pCore 2 f.range)).comp f.rangeRestrict
  have hq : Function.Surjective q :=
    (QuotientGroup.mk'_surjective _).comp f.rangeRestrict_surjective
  have hcoref : pCore 2 A ≤ q.ker := by
    have hh : (pCore 2 A).map f.rangeRestrict ≤ pCore 2 f.range :=
      le_sSup ⟨Normal.map inferInstance f.rangeRestrict f.rangeRestrict_surjective,
        pCore_isPGroup.map f.rangeRestrict⟩
    intro x hx
    exact (QuotientGroup.eq_one_iff _).mpr (hh (mem_map_of_mem f.rangeRestrict hx))
  let g := (QuotientGroup.mk' (pCore 2 J)).comp (inclusion (show A ≤ J from inf_le_left))
  have hkg : IsPGroup 2 g.ker := by
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
  have hgcore : g.ker ≤ pCore 2 A := le_sSup ⟨inferInstance,hkg⟩
  let r : (A ⧸ g.ker) →* (f.range ⧸ pCore 2 f.range) :=
    QuotientGroup.lift g.ker q (fun x hx => hcoref (hgcore hx))
  have hr : Function.Surjective r := by
    intro y
    obtain ⟨x,hx⟩ := hq y
    exact ⟨QuotientGroup.mk' g.ker x,hx⟩
  have hd := card_dvd_of_surjective r hr
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv] at hd
  exact (hd.trans g.range.card_subgroup_dvd_card).trans
    (dvd_of_eq s.point_residual_join_core_card)

private theorem signed_ternary_no_small_quotient
    {Q : Type*} [Group Q] [Finite Q] (S : Sylow 2 Q) (B J : Subgroup Q)
    (e : B ≃* SL(2,ZMod 7)) (hBJ : B ≤ J) (hn : J ≤ normalizer (B : Set Q))
    (hSJ : (S : Subgroup Q) ≤ J) (unitary : Bool)
    (hm : IsPSLSign Q unitary 3 7 ∨ IsSLSign Q unitary 3 7) :
    ¬ Nat.card (J ⧸ pCore 2 J) ∣ 168 := by
  have transport {H : Type} [Group H] [Finite H] (a : Q ≃* H)
      (h : ∀ (S : Sylow 2 H) (B J : Subgroup H),
        (B ≃* SL(2,ZMod 7)) → B ≤ J → J ≤ normalizer (B : Set H) →
        (S : Subgroup H) ≤ J → ¬ Nat.card (J ⧸ pCore 2 J) ∣ 168) :
      ¬ Nat.card (J ⧸ pCore 2 J) ∣ 168 := by
    intro hsmall
    let b := B.equivMapOfInjective a.toMonoidHom a.injective
    let j := J.equivMapOfInjective a.toMonoidHom a.injective
    apply h (S.mapSurjective a.surjective) (B.map a.toMonoidHom) (J.map a.toMonoidHom)
      (b.symm.trans e) (map_mono hBJ)
      ((map_mono hn).trans (B.le_normalizer_map a.toMonoidHom)) (map_mono hSJ)
    rwa [←Nat.card_congr (QuotientGroup.congr _ _ j (pCore_map_iso 2 j)).toEquiv]
  cases unitary
  · rcases hm with ⟨F,_,_,hF,⟨a⟩⟩ | ⟨F,_,_,hF,⟨a⟩⟩
    · exact transport a (projective_linear_no_small_quotient hF)
    · exact transport a (special_linear_no_small_quotient hF)
  · rcases hm with ⟨F,_,_,M,hF,hc,⟨a⟩⟩ | ⟨F,_,_,M,hF,hc,⟨a⟩⟩
    · let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup M) :=
        Finite.of_surjective a a.surjective
      exact transport a (projective_unitary_no_small_quotient M hF hc)
    · exact transport a (special_unitary_no_small_quotient M hF hc)

/-- Both signs of the ternary-seven point component are excluded with the
literal residual image and original relative Sylow placement. -/
theorem point_component_not_ternary_seven {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1)) (hLK : s.marking.Li 1 ≤ K)
    (unitary : Bool)
    (hm : IsPSLSign (K ⧸ pCore 2 K) unitary 3 7 ∨ IsSLSign (K ⧸ pCore 2 K) unitary 3 7) : False := by
  let q := QuotientGroup.mk' (pCore 2 K)
  let B := ((s.marking.Li 1).subgroupOf K).map q
  let J := s.pointResidualIntersectionImage K q
  obtain ⟨_,⟨e⟩⟩ := s.point_component_odd_ternary_residual_model hK hLK (by decide) (by decide) unitary hm
  obtain ⟨S,hSJ⟩ := s.pointResidualIntersectionImage_sylow hK q (QuotientGroup.mk'_surjective _)
  have hBJ : B ≤ J := by
    rintro _ ⟨b,hb,rfl⟩
    exact ⟨⟨b,⟨(show s.marking.Li 1 ≤ s.marking.Li 1 ⊔ (T : Subgroup G) from le_sup_left) hb,b.property⟩⟩,rfl⟩
  have hn : J ≤ normalizer (B : Set (K ⧸ pCore 2 K)) := by
    rintro _ ⟨a,rfl⟩
    apply ((s.marking.Li 1).subgroupOf K).le_normalizer_map q
    apply mem_map_of_mem
    intro b
    exact (s.Mi_normalizes_Li 1
      (show (a : G) ∈ s.marking.Mi 1 from
        (sup_le (s.Li_le_Mi 1) (le_inf le_sup_right s.sylow_le_G₁)) a.property.1)) (b : G)
  exact signed_ternary_no_small_quotient S B J e hBJ hn hSJ unitary hm
    (s.pointResidualIntersectionImage_core_quotient_card q)

/-- The original point component has exactly the source alternatives. -/
theorem point_component_alternative_from_source
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1)) (hLK : s.marking.Li 1 ≤ K)
    (hN : (K.subgroupOf (s.marking.Gi 1)).Normal) : LocalComponentAlternative s 1 K := by
  rcases s.point_component_alternative_or_ternary_seven h hK hLK hN with ha | ⟨unitary,hm,_⟩
  · exact ha
  · exact (s.point_component_not_ternary_seven hK hLK unitary hm).elim

/-- Source 12.5.3: all four original components and their relative normality,
with no assumed point-component refinement. -/
theorem local_components_from_source
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) : Nonempty (LocalComponents s) := by
  obtain ⟨K,⟨hK,hLK,hN⟩,_⟩ := s.exists_unique_normal_local_component h 1 (.inl rfl)
  exact ⟨s.localComponentsOfPointAlternative h K hK hLK hN
    (s.point_component_alternative_from_source h hK hLK hN)⟩

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource

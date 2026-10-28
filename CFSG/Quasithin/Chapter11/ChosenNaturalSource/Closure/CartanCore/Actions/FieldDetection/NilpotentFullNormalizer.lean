module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Sieve.NilpotentInner
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.NilpotentNormalizer
public import Theory.SpecificGroups.Alternating.FiveInnerSylowNormalizer
public import Theory.GroupTheory.ReducedNormal.SylowSupplement

/-!
# The full Sylow lift and the symplectic Cartan component action

A moved component I is normal in G₁. Every automorphism of its two-core
quotient acts inner on its SL₂(5) Fitting quotient, by the primary-plane
trace argument. Thus IT acts through the full inner group of that quotient.
Since IT/I is a two-group, the A₅ Sylow-normalizer calculation lifts a cubic
element into I ∩ N_G(T), with the full original Sylow subgroup retained.

For the symplectic natural marking, source 11.0.4 puts such a cubic in L.
The Cartan intersection calculation then makes it trivial. This proves
11.5.6(3) and assembles it with (4), without a component-action assumption.
All extraspecial and arbitrary-exponent homocyclic primary factors remain.
The odd-degree SL₃ branch still requires exclusion of the lifted cubic;
its source assembly remains with qt-d-1222-natural-closure-cartan. Preceding
flag and Cartan inputs retain qt-d-1222-natural-closure as assembly owner.
Source: Aschbacher--Smith 11.0.4 and 11.5.6(3--4), pp.760,780--781.
-/

public noncomputable section
open Subgroup Theory.GroupTheory

open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
open CartanActions.FieldDetection.OddLinear
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    {L V : Subgroup G} {D : ChosenModule T L V} (E : Geometry D)

/-- The remaining moved-component row supplies a cubic in the full Sylow normalizer. -/
theorem moved_component_full_sylow_cubic (hp : E.point ≠ ⊥)
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : E.X ≤ E.G₁)
    (c : LocalGeometry.Coordinates D E.input.field)
    (hcart : LocalGeometry.IsCartan T L E.X)
    (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (hCX : E.X ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁)
    (hz : center (E.L₁ ⧸ pCore 2 E.L₁) = ⊥)
    (hNG : normalizer (T : Set G) ≤ E.M)
    (hthree : 1 ≤ primeRank 3 E.L₁)
    (hexception : E.L₁ < E.K → Even E.input.field.degree)
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    (hmoved : ¬ ⁅I,E.X⁆ ≤ E.Y.pCoreIn 2) :
    ∃ b : G, b ∈ I ∧ b ∈ normalizer (T : Set G) ∧ orderOf b = 3 := by
  obtain ⟨hn,hcommon,_,hinner⟩ := E.moved_component_fitting_quotient_actors_inner
    hp hT hX c hcart hXR hCX hz hNG hthree hexception hI hmoved
  let B := (I.subgroupOf E.G₁).map (QuotientGroup.mk' (pCore 2 E.G₁))
  let R := B ⧸ fittingSubgroup B
  let H := I ⊔ (T : Subgroup G)
  let J := I.subgroupOf H
  have hIH : I ≤ H := le_sup_left
  have hHG : H ≤ E.G₁ := sup_le (hI.1.trans E.Y_le_G₁) hT
  have hnorm : H ≤ normalizer (I : Set G) := hHG.trans
    ((normal_subgroupOf_iff_le_normalizer (hI.1.trans E.Y_le_G₁)).mp
      (E.nilpotent_component_relative_normal hp hI hn))
  let : J.Normal := normal_subgroupOf_of_le_normalizer hnorm
  have hq : IsPGroup 2 (H ⧸ J) := by
    apply isPGroup_quotient_of_sup_eq_top J ((T : Subgroup G).subgroupOf H)
      T.isPGroup'.comap_subtype
    rw [← subgroupOf_sup hIH (show (T : Subgroup G) ≤ H from le_sup_right)]
    exact subgroupOf_self H
  let eqB := E.componentImageQuotientEquiv hI
  let n : H →* normalizer (I : Set G) := H.subtype.codRestrict _ (fun h => hnorm h.property)
  let a : H →* MulAut B := (MulAut.congr eqB).toMonoidHom.comp
    ((coreQuotientAction I).comp n)
  let f : H →* MulAut R := (quotientAut (fittingSubgroup B)).comp a
  have hf : f.range = MulAut.innerSubgroup R := by
    apply le_antisymm
    · rintro _ ⟨h,rfl⟩
      exact hinner (a h)
    · rintro _ ⟨r,rfl⟩
      obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (fittingSubgroup B) r
      obtain ⟨j,hj⟩ := (eqB.surjective.comp (QuotientGroup.mk'_surjective _)) b
      simp only [Function.comp_apply] at hj
      refine ⟨⟨j,hIH j.property⟩,?_⟩
      have ha : a ⟨j,hIH j.property⟩ = MulAut.conj b := by
        apply MulEquiv.ext
        intro w
        obtain ⟨k,rfl⟩ := (eqB.surjective.comp (QuotientGroup.mk'_surjective _)) w
        change eqB (coreQuotientAction I (n ⟨j,hIH j.property⟩)
          (eqB.symm (eqB (QuotientGroup.mk' (pCore 2 I) k)))) = _
        rw [eqB.symm_apply_apply,coreQuotientAction_apply_mk]
        change eqB (QuotientGroup.mk' (pCore 2 I) (j*k*j⁻¹)) = _
        simp only [map_mul,map_inv,MulAut.conj_apply,hj,Function.comp_apply]
      change quotientAut (fittingSubgroup B) (a ⟨j,hIH j.property⟩) = _
      rw [ha]
      ext w
      obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (fittingSubgroup B) w
      rw [quotientAut_apply_mk]
      simp only [MulAut.conj_apply,map_mul,map_inv]
  obtain ⟨F,_,_,hF,⟨em⟩⟩ := hn.2.2.1
  let eR : R ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientMulEquivOfEq hn.1).symm.trans em
  let eZ : (R ⧸ center R) ≃* Theory.PSL2.Group F :=
    QuotientGroup.congr _ _ eR (by
      ext z
      constructor
      · rintro ⟨w,hw,rfl⟩
        exact (centerCongr eR ⟨w,hw⟩).property
      · intro hz
        exact ⟨eR.symm z,(centerCongr eR.symm ⟨z,hz⟩).property,eR.apply_symm_apply z⟩)
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 5 := (ZMod.ringEquivOfPrime F (by decide : Nat.Prime 5)
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  let eA := eZ.trans ((Atlas.fieldEquivPSL 2 eF).trans
    Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five.some)
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  obtain ⟨b,hbJ,hbN,hb⟩ := exists_cubic_in_normal_subgroup_sylow_normalizer_of_inner_action J hq f hf eA S
  have hS : (S : Subgroup H).map H.subtype = (T : Subgroup G) := by
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ H from le_sup_right)]
  refine ⟨b,hbJ,?_,(Subgroup.orderOf_coe b).trans hb⟩
  change (b : G) ∈ normalizer ((T : Subgroup G) : Set G)
  rw [←hS]
  exact (S : Subgroup H).le_normalizer_map H.subtype (mem_map_of_mem H.subtype hbN)
/-- Source 11.5.6(3) for the original symplectic marking. -/
theorem symplectic_component_commutator_of_marked (hp : E.point ≠ ⊥)
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : E.X ≤ E.G₁)
    (m : ActionEquiv D.centralQuotientAction
      (Representation.restrictScalars (k := ZMod 2)
        (Representation.symplecticNatural (k := E.input.field.Carrier) 2)))
    (hcart : LocalGeometry.IsCartan T L E.X)
    (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (hCX : E.X ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁)
    (hz : center (E.L₁ ⧸ pCore 2 E.L₁) = ⊥)
    (hNG : normalizer (T : Set G) ≤ E.M)
    (hthree : 1 ≤ primeRank 3 E.L₁)
    (hexception : E.L₁ < E.K → Even E.input.field.degree)
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I) :
    ⁅I,E.X⁆ ≤ E.Y.pCoreIn 2 := by
  by_contra hmoved
  obtain ⟨b,hbI,hbN,hb⟩ := E.moved_component_full_sylow_cubic hp hT hX
    (.sp4 m) hcart hXR hCX hz hNG hthree hexception hI hmoved
  let x : (E.Y ⊓ normalizer (T : Set G) : Subgroup G) := ⟨b,hI.1 hbI,hbN⟩
  have ho : orderOf x = 3 := (Subgroup.orderOf_coe x).symm.trans hb
  exact E.symplectic_three_not_dvd_point_sylowNormalizer hT hX hcart hCX hz hNG m
    (ho ▸ orderOf_dvd_natCard x)

/-- Both original Cartan action clauses, without a component-action premise. -/
theorem symplectic_cartan_actions_of_marked (hp : E.point ≠ ⊥)
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : E.X ≤ E.G₁)
    (m : ActionEquiv D.centralQuotientAction
      (Representation.restrictScalars (k := ZMod 2)
        (Representation.symplecticNatural (k := E.input.field.Carrier) 2)))
    (hcart : LocalGeometry.IsCartan T L E.X)
    (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (hCX : E.X ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁)
    (hz : center (E.L₁ ⧸ pCore 2 E.L₁) = ⊥)
    (hNG : normalizer (T : Set G) ≤ E.M)
    (hthree : 1 ≤ primeRank 3 E.L₁)
    (hexception : E.L₁ < E.K → Even E.input.field.degree) :
    (∀ I : Subgroup G, Source.ComponentIn E.Y I → ⁅I, E.X⁆ ≤ E.Y.pCoreIn 2) ∧
      (∀ P : Subgroup G, P ≤ T → P = ⁅P, E.X⁆ →
        (frattini P).map P.subtype ≤ E.G₁.pCoreIn 2 → ⁅P, E.Y⁆ ≤ E.Y.pCoreIn 2) := by
  have hcomp := fun I hI => E.symplectic_component_commutator_of_marked hp hT hX m
    hcart hXR hCX hz hNG hthree hexception (I := I) hI
  exact ⟨hcomp, fun P hP hPX hphi =>
    E.frattini_action_of_component_actions hp hT hX hcart.odd hcomp P hP hPX hphi⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry

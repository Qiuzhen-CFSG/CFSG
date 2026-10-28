module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2SourceMarkedActors
public import Theory.Representation.BinaryConjugationSection.DisplacementBound
public import Theory.Representation.BinaryConjugationSection.DisplacementPreimage

/-!
# Critical fixed preimages and the noncontainment branch

Conjugation carries an actor whose commutators lie in the original point
back to the same natural/Weyl module. Its displacement has dimension at
most one; the concrete G₂ involution bound forces its star image to vanish.
Thus the fixed preimage of Uα on U/V₁ lies in the literal reciprocal core
intersection D = U ∩ Qα. In particular the original U₀ lies in D.

If Zα is outside U, its coordinate image is zero. The actual critical rank
comparison then makes Uα* an offender. The concrete model classification
identifies this same actor with a full pencil centralizer. The two fixed
preimages agree, both quotient orders are eight, and the existing original
duality and common-family consumer give V₁ not contained in Uα and formula
(d), without assuming the actor marking or a common-family identity.

The branch Zα ≤ U from 14.7.60, the reciprocal marked geometry, and the final
four-cycle application remain to be proved. This is a case reduction, not
an unconditional G₂ residual exclusion. Earlier recognition and the full
core-commutator identity retain their existing source assembly owners.

Source: Aschbacher–Smith 14.7.60–62, printed pp.1067–1068, especially the
U₀/D transvection argument in 14.7.61. Concrete models retain the attribution
in LICENSES/ATLAS.txt.
-/

public noncomputable section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
open Chapter12.Section08 CriticalFusion.Source
open G2Exclusion.MarkedGeometry.LocalParabolics.ThreeOffenderOrbit

theorem model_involution_fixedCodim_ge_two (m : BinaryG2Module)
    (a : Atlas.G2.Model (ZMod 2)) (hne : a ≠ 1) (hpow : a ^ 2 = 1) :
    2 ≤ fixedCodim m.action (zpowers a) := by
  have hr : rank (zpowers a) = 1 := by
    rw [rank, Nat.card_zpowers, orderOf_eq_prime hpow hne]
    decide
  have he : IsElementaryTwo (zpowers a) :=
    ⟨by simpa using hne, IsElementaryAbelian.zpowers_of_pow_eq_one hpow⟩
  have hh := model_small_rank_bound m (zpowers a) he (by omega)
  omega

theorem model_offender_fullCentralizer (m : BinaryG2Module)
    (A : Subgroup (Atlas.G2.Model (ZMod 2))) (hA : IsOffender m.action A) :
    ∃ p : Atlas.G2.SingularPoints (ZMod 2),
      A = G2Exclusion.MarkedGeometry.MarkedPencil.Actors.fullCentralizer
        m.singularMap m.action p := by
  have hn : IsOffender (Atlas.G2.Natural.action (ZMod 2)) A := by
    cases m with
    | natural => exact hA
    | weyl =>
      refine ⟨hA.1,?_⟩
      rw [← Atlas.G2.Natural.BinaryModelOffenders.weyl_fixedCodim]
      exact hA.2
  obtain ⟨g,hg⟩ := Atlas.G2.NaturalOffenders.natural_offender_conjugate_elementary
    (n := 1) (by norm_num) (by decide) A hn
  rw [← Atlas.G2.Natural.BinaryModelOffenders.elementary_eq] at hg
  have hm : m.singularMap.Equivariant m.action := by
    cases m with
    | natural => exact G2Exclusion.MarkedGeometry.naturalMap_equivariant
    | weyl => exact G2Exclusion.MarkedGeometry.weylMap_equivariant
  refine ⟨g • Atlas.G2.firstPoint,?_⟩
  rw [hg,← G2Exclusion.MarkedGeometry.MarkedPencil.Actors.fullCentralizer_firstPoint
    m.singularMap m.action hm,
    G2Exclusion.MarkedGeometry.MarkedPencil.Actors.fullCentralizer_conjugate
      m.singularMap m.action hm]

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) (HStar F.H) W}
  (c : BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (starMap F)))

include c

theorem source_line_actor_le_core
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (i : HStar F.H →* Atlas.G2.Model (ZMod 2)) (hi : Function.Injective i)
    (he : ∀ a v, E (m.action (i a) v) = σ a (E v))
    (A C : Subgroup G) [IsElementaryAbelian 2 A]
    (hAH : A ≤ F.H) (hcomm : ⁅A,F.U⁆ ≤ C) (hcard : Nat.card C ≤ 2) :
    A ≤ F.H.pCoreIn 2 := by
  let : Finite W := Finite.of_surjective (fun u : F.U => (c.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  intro x hx
  let a : F.H := ⟨x,hAH hx⟩
  have hd := c.displacement_rank_le_of_commutator_bound A C ⊥ bot_le hcomm 1
    (by simpa using hcard) a hx
  have hpow : a ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian x hx)
  have ha : starMap F a = 1 := by
    by_contra hn
    have hn' : i (starMap F a) ≠ 1 := fun hh => hn (hi (hh.trans i.map_one.symm))
    have hp' : i (starMap F a) ^ 2 = 1 := by rw [← map_pow,← map_pow,hpow,map_one,map_one]
    have hh := model_involution_fixedCodim_ge_two m (i (starMap F a)) hn' hp'
    have ht := fixedCodim_map_equivariant (σ.comp (starMap F)) m.action
      (i.comp (starMap F)) E.symm
      (fun a v => by
        change E.symm (σ (starMap F a) v) = m.action (i (starMap F a)) (E.symm v)
        apply E.injective
        rw [E.apply_symm_apply,he,E.apply_symm_apply])
      (zpowers a)
    rw [MonoidHom.map_zpowers,MonoidHom.comp_apply] at ht
    rw [← ht,fixedCodim_zpowers_eq_displacement_rank] at hh
    change Module.finrank (ZMod 2) ((σ.comp (starMap F)) a - LinearMap.id).range ≤ 1 at hd
    omega
  exact mem_map_of_mem F.H.subtype ((QuotientGroup.eq_one_iff a).mp ha)

/-- The fixed preimage in the original section lies in the reciprocal core. -/
theorem source_critical_fixed_preimage_le_reciprocal_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (path : CriticalPath (L := L) F)
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (i : HStar F.H →* Atlas.G2.Model (ZMod 2)) (hi : Function.Injective i)
    (he : ∀ a v, E (m.action (i a) v) = σ a (E v)) :
    commutatorPreimage F.U path.Uα (F.Vi 1) ≤ F.U ⊓ path.Qα := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  let U₀ := commutatorPreimage F.U path.Uα (F.Vi 1)
  have hU₀ : U₀ ≤ F.U := commutatorPreimage_le _ _ _
  let : IsElementaryAbelian 2 U₀ :=
    IsElementaryAbelian.of_injective (inclusion hU₀) (inclusion_injective hU₀)
  let f := (MulAut.conj path.conjugator).toMonoidHom
  let : IsElementaryAbelian 2 (U₀.map f) := IsElementaryAbelian.map f
  have hU : path.Uα.map f = F.U := by
    change (F.U.conjBy path.conjugator⁻¹).conjBy path.conjugator = F.U
    rw [← conjBy_mul,mul_inv_cancel,conjBy_one]
  have hH : (conjugate F.H path.conjugator).map f = F.H := by
    change (F.H.conjBy path.conjugator⁻¹).conjBy path.conjugator = F.H
    rw [← conjBy_mul,mul_inv_cancel,conjBy_one]
  have hQ : path.Qα.map f = F.H.pCoreIn 2 := by
    change ((conjugate F.H path.conjugator).pCoreIn 2).map f = _
    rw [map_pCoreIn_of_injective 2 _ f (MulAut.conj path.conjugator).injective,hH]
  have hA : U₀.map f ≤ F.H :=
    (map_mono (hU₀.trans (reciprocal_placement h path))).trans_eq hH
  have hc : ⁅U₀,path.Uα⁆ ≤ F.Vi 1 :=
    commutator_commutatorPreimage_le F.U path.Uα (F.Vi 1) c.section_le
  have hc' : ⁅U₀.map f,F.U⁆ ≤ (F.Vi 1).map f := by
    have hh := map_mono (f := f) hc
    rwa [map_commutator,hU] at hh
  have hcard : Nat.card ((F.Vi 1).map f) ≤ 2 := by
    rw [card_map_of_injective (MulAut.conj path.conjugator).injective]
    exact (show Nat.card (F.Vi 1) = 2 by simpa using F.card 1 (by decide)).le
  have hcore := source_line_actor_le_core c m E i hi he (U₀.map f) ((F.Vi 1).map f)
    hA hc' hcard
  exact le_inf hU₀ ((map_le_map_iff_of_injective (MulAut.conj path.conjugator).injective).mp
    (hcore.trans_eq hQ.symm))

/-- In particular the whole-group fixed preimage U₀ lies in D. -/
theorem source_fixed_preimage_le_reciprocal_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (path : CriticalPath (L := L) F) (hAH : path.Uα ≤ F.H)
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (i : HStar F.H →* Atlas.G2.Model (ZMod 2)) (hi : Function.Injective i)
    (he : ∀ a v, E (m.action (i a) v) = σ a (E v)) :
    commutatorPreimage F.U F.H (F.Vi 1) ≤ F.U ⊓ path.Qα := by
  apply le_trans ?_ (source_critical_fixed_preimage_le_reciprocal_core c h hab path m E i hi he)
  apply le_commutatorPreimage (commutatorPreimage_le _ _ _)
  exact (commutator_mono le_rfl hAH).trans
    (commutator_commutatorPreimage_le F.U F.H (F.Vi 1) c.section_le)

omit c [Finite G] in
private theorem partner_point_disjoint
    (path : CriticalPath (L := L) F) (hZU : ¬ path.Zα ≤ F.U) :
    F.U ⊓ path.Zα = ⊥ := by
  have hcard : Nat.card path.Zα = 2 := by
    rw [CriticalPath.Zα,conjugate,card_map_of_injective (MulAut.conj _).injective]
    simpa using F.card 1 (by decide)
  let : Fact (Nat.card path.Zα).Prime := ⟨by rw [hcard]; decide⟩
  rcases (F.U.subgroupOf path.Zα).eq_bot_or_eq_top_of_prime_card with hb | ht
  · have hh := congrArg (map path.Zα.subtype) hb
    simpa only [subgroupOf_map_subtype,Subgroup.map_bot] using hh
  · exact (hZU (fun x hx => show (⟨x,hx⟩ : path.Zα) ∈ F.U.subgroupOf path.Zα from
      ht ▸ mem_top _)).elim

omit [Finite G] in
/-- Outside the original span, the reciprocal point has zero coordinate image. -/
theorem source_partner_point_image_eq_bot
    (path : CriticalPath (L := L) F) (hZU : ¬ path.Zα ≤ F.U) :
    c.imageSpace path.Zα = ⊥ := by
  have hb := partner_point_disjoint path hZU
  apply bot_unique
  intro v hv
  obtain ⟨u,hu,rfl⟩ := (c.mem_imageSpace_iff _ _).mp hv
  have hu1 : (u:G) = 1 := by
    have hh : (u:G) ∈ F.U ⊓ path.Zα := ⟨u.property,hu⟩
    rwa [hb,mem_bot] at hh
  have he : u = 1 := Subtype.ext hu1
  rw [he,map_one]
  exact Submodule.zero_mem _

/-- The selected actor is an offender unless its reciprocal point lies in U.
This is the first implication in the proof of 14.7.61. -/
theorem source_critical_offender_of_point_not_le
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (selection : path.RankSelection) (hZU : ¬ path.Zα ≤ F.U) :
    IsOffender σ (star F path.Uα) := by
  let : Finite W := Finite.of_surjective (fun u : F.U => (c.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  obtain ⟨hd,_,hdisp⟩ := critical_linear_bounds c h path hplace selection
  have hz := source_partner_point_image_eq_bot c path hZU
  have hle : c.imageSpace (commutatorPreimage F.U path.Uα path.Zα) ≤
      fixedSpace σ (star F path.Uα) := by
    intro v hv a
    have hh := hdisp a a.property v hv
    rw [hz] at hh
    exact sub_eq_zero.mp hh
  have hh := Submodule.finrank_mono hle
  have h₁ := (c.imageSpace (commutatorPreimage F.U path.Uα path.Zα)).finrank_quotient_add_finrank
  have h₂ := fixedCodim_add_finrank σ (star F path.Uα)
  exact ⟨critical_elementary h hab path hplace selection,by omega⟩

/-- Construct a full pencil marking for the same critical actor in the
noncontainment branch, without an actor-identification premise. -/
theorem source_full_critical_actor_of_point_not_le
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (selection : path.RankSelection) (hZU : ¬ path.Zα ≤ F.U)
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (i : HStar F.H →* Atlas.G2.Model (ZMod 2)) (hi : Function.Injective i)
    (he : ∀ a v, E (m.action (i a) v) = σ a (E v)) :
    ∃ p : Atlas.G2.SingularPoints (ZMod 2),
      (star F path.Uα).map i =
        G2Exclusion.MarkedGeometry.MarkedPencil.Actors.fullCentralizer m.singularMap m.action p := by
  have ho := source_critical_offender_of_point_not_le c h hab path hplace selection hZU
  apply model_offender_fullCentralizer m _
  exact ho.map_equivariant σ m.action i hi E.symm
    (fun a v => by rw [← E.apply_symm_apply v,← he,E.symm_apply_apply,E.symm_apply_apply])

/-- The actual reciprocal core intersection is the fixed preimage of the
same critical actor when its point is outside U. -/
theorem source_core_intersection_eq_fixed_preimage
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (path : CriticalPath (L := L) F) (hAH : path.Uα ≤ F.H)
    (hZU : ¬ path.Zα ≤ F.U)
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (i : HStar F.H →* Atlas.G2.Model (ZMod 2)) (hi : Function.Injective i)
    (he : ∀ a v, E (m.action (i a) v) = σ a (E v)) :
    F.U ⊓ path.Qα = commutatorPreimage F.U path.Uα (F.Vi 1) := by
  apply le_antisymm ?_ (source_critical_fixed_preimage_le_reciprocal_core c h hab path m E i hi he)
  apply le_commutatorPreimage inf_le_left
  have hU : ⁅F.U ⊓ path.Qα,path.Uα⁆ ≤ F.U :=
    (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hAH.trans c.normalized))
  have hZ : ⁅F.U ⊓ path.Qα,path.Uα⁆ ≤ path.Zα :=
    (commutator_mono inf_le_right le_rfl).trans (reciprocal_core_commutator c path)
  have hh := le_inf hU hZ
  rw [partner_point_disjoint path hZU] at hh
  exact hh.trans bot_le

/-- Identify the actual reciprocal intersection and both quotient orders in
the noncontainment branch, using the same full actor on the original marking. -/
theorem source_core_intersection_and_orders
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (path : CriticalPath (L := L) F) (hAH : path.Uα ≤ F.H)
    (hZU : ¬ path.Zα ≤ F.U)
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (i : HStar F.H →* Atlas.G2.Model (ZMod 2)) (hi : Function.Injective i)
    (he : ∀ a v, E (m.action (i a) v) = σ a (E v))
    (p : Atlas.G2.SingularPoints (ZMod 2))
    (hA : (star F path.Uα).map i =
      G2Exclusion.MarkedGeometry.MarkedPencil.Actors.fullCentralizer m.singularMap m.action p) :
    F.U ⊓ path.Qα = (F.U ⊓ path.Uα) ⊔ F.Vi 1 ∧
      (F.U ⊓ path.Qα).relIndex F.U = 8 ∧ Nat.card (star F path.Uα) = 8 := by
  let D := F.U ⊓ path.Qα
  have hD := source_core_intersection_eq_fixed_preimage c h hab path hAH hZU m E i hi he
  have hPD : F.Vi 1 ≤ D := by
    change F.Vi 1 ≤ F.U ⊓ path.Qα
    rw [hD]
    exact le_commutatorPreimage c.kernel_le
      (le_normalizer_iff_commutator_le_left.mp hAH)
  have hDi : c.imageSpace D = fixedSpace σ (star F path.Uα) := by
    rw [show D = commutatorPreimage F.U path.Uα (F.Vi 1) from hD,
      c.fixed_image_eq path.Uα hAH c.section_le,fixedSpace_comp_map]
    rfl
  have hIi := source_marked_intersection_image c h hab path hAH m E i he p hA
  have hEq : D = (F.U ⊓ path.Uα) ⊔ F.Vi 1 := by
    apply le_antisymm
    · intro x hx
      let u : F.U := ⟨x,hx.1⟩
      apply (c.coordinates_mem_imageSpace_iff (F.U ⊓ path.Uα) inf_le_left u).mp
      rw [hIi,← hDi]
      exact (c.mem_imageSpace_iff D _).mpr ⟨u,hx,rfl⟩
    · apply sup_le ?_ hPD
      intro x hx
      let u : F.U := ⟨x,hx.1⟩
      have hm : (c.coordinates u).toAdd ∈ c.imageSpace D := by
        rw [hDi,← hIi]
        exact (c.mem_imageSpace_iff _ _).mpr ⟨u,hx,rfl⟩
      have hh := (c.coordinates_mem_imageSpace_iff D inf_le_left u).mp hm
      simpa only [sup_eq_left.mpr hPD] using hh
  have hm : m.singularMap.Equivariant m.action := by
    cases m with
    | natural => exact G2Exclusion.MarkedGeometry.naturalMap_equivariant
    | weyl => exact G2Exclusion.MarkedGeometry.weylMap_equivariant
  have hc : Nat.card (star F path.Uα) = 8 := by
    rw [← card_map_of_injective (K := star F path.Uα) hi,hA]
    exact (G2Exclusion.MarkedGeometry.MarkedPencil.Actors.fullCentralizer_structure
      m.singularMap m.action hm p).2
  refine ⟨hEq,?_,hc⟩
  rw [show F.U ⊓ path.Qα = (F.U ⊓ path.Uα) ⊔ F.Vi 1 from hEq,
    source_marked_intersection_index c h hab path hAH m E i hi he p hA,hc]

/-- Apply the constructed actor marking to the original common-family
consumer. In this branch neither the actor identity, the first point
noncontainment, nor the common family is an input. -/
theorem source_common_family_of_partner_point_not_le
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (hfit : Theory.GroupTheory.generalizedFitting (HStar F.H) = star F (K F))
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (hf : Function.Injective σ) (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (selection : path.RankSelection) (hZU : ¬ path.Zα ≤ F.U)
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (i : HStar F.H →* Atlas.G2.Model (ZMod 2)) (hi : Function.Injective i)
    (he : ∀ a v, E (m.action (i a) v) = σ a (E v)) :
    ∃ p : Atlas.G2.SingularPoints (ZMod 2),
      (star F path.Uα).map i =
        G2Exclusion.MarkedGeometry.MarkedPencil.Actors.fullCentralizer m.singularMap m.action p ∧
      (F.U ⊓ path.Qα = (F.U ⊓ path.Uα) ⊔ F.Vi 1) ∧
      (F.U ⊓ path.Qα).relIndex F.U = 8 ∧ Nat.card (star F path.Uα) = 8 ∧
      (¬ F.Vi 1 ≤ path.Uα) ∧
      ({C | C ≠ ⊥ ∧ ∃ b ∈ derivedActorLift (i.comp (starMap F)) path.Uα,
          C = ⁅F.U,zpowers b⁆} =
        {C | C ≠ ⊥ ∧ ∃ w ∈ polarLift c m E p, C = ⁅path.Uα,zpowers w⁆}) := by
  obtain ⟨p,hA⟩ := source_full_critical_actor_of_point_not_le c h hab path hplace selection
    hZU m E i hi he
  have hAH : path.Uα ≤ F.H := hplace.trans
    ((pCoreIn_le 2 (F.Li L 1 ⊔ (T : Subgroup G))).trans
      (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)))
  obtain ⟨hD,hidx,hcard⟩ := source_core_intersection_and_orders c h hab path hAH hZU
    m E i hi he p hA
  have hfam := source_common_family_of_full_critical_actor c h hab hcomponent hfit eK hf hcomm
    path hplace selection m E i hi he p hA
  exact ⟨p,hA,hD,hidx,hcard,hfam.1,hfam.2.1⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source

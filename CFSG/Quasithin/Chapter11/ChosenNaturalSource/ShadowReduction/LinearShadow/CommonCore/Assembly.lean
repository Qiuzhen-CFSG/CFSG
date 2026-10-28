module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal

/-!
# Assembly of the original common-core geometry

The exact preceding conclusions of §§11.0--11.2 and 11.3.4--6 first give all
five clauses of 11.3.7. The selected conjugate is the original V, so its
nontrivial action excludes V ≤ O₂(H). We choose h in H outside M and construct
the pair with the original conjugation convention. The pair calculation
excludes Sp₄ and identifies both the supplied flag plane and the plane in
the block calculation with B = V ∩ O₂(H). Thus the local-core equality
transports to the supplied flag, without changing its natural action marking.

The field-four invariant-complement argument has already been discharged by
`source_pair_final_core_identifications`; no exclusion of q=4 is assumed.
This constructs every input to the odd-degree and orthogonal argument.
The remaining earlier-source inputs have producers
qt-d-1222-shadow-parameter-component and qt-d-1222-natural-local-geometry;
qt-d-1222-shadow-linear-geometry owns their final discharge.

Source: Aschbacher--Smith, refs/quasithin.pdf, printed pp.773--774.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}

/-- Exactly the earlier-source inputs used by 11.3.7. None of its action,
fixed-space, conjugate, common-core or orthogonal conclusions is a field.
The flag is the original supplied flag, not a new model flag. -/
structure Preceding1137 (c : Coordinates D S.field) (f : InvariantFlag c)
    (H : Subgroup G) : Prop where
  preceding : Preceding1133 D S (c.binarySubspace (f.space 0)) H
  not_g2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
    (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
  residual_component : Source.NormalComponentIn H (outsideResidual H)
  residual_model : ClassicalGroup.IsPSL
    (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ S.field.degree)
  global_s : @ChapterE.globalS G _ V D.elementary = (S.field.degree : ℕ∞)
  alternative : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∨
    Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree)
  parameters : (S.field.degree : ℕ∞) < ChapterE.globalR V ∨
    (Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
      ChapterE.globalR V = S.field.degree ∧
      ¬ centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G))
  weak : D.centralQuotientPreimage (c.binarySubspace (f.space 0)) ≤
    centralizer (Source.weakClosureZero (T : Subgroup G) V : Set G)
  prime_residual : ∀ p : ℕ, p.Prime →
    ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
        p ∣ 2 ^ S.field.degree - 1 ∧ 3 < p) ∨
      (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
        p ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
    primeToResidual p (normalizer (L : Set G)) = L.subgroupOf (normalizer (L : Set G))
  cubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
    Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L

/-- Output of the common-action and common-core proofs. Its orthogonal state
uses the original flag, transported only along equality of its coordinates.
The separate natural actions carry no compatibility assumption. -/
structure AssembledInput (c : Coordinates D S.field) (f : InvariantFlag c)
    (H A : Subgroup G) where
  marking : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)
  coordinates_eq : c = .sl3 marking
  cartan : Subgroup G
  conjugator : G
  orthogonal : OrthogonalInput D S marking (coordinates_eq ▸ f) H cartan A conjugator
  selected : G
  selected_le : V.map (MulAut.conj selected).toMonoidHom ≤ (T : Subgroup G)
  selected_active : ¬ V.map (MulAut.conj selected).toMonoidHom ≤
    centralizer (omegaClosure T H : Set G)
  selected_eq : V.map (MulAut.conj selected).toMonoidHom = V
  kernel : outsideResidual H ⊓ centralizer (omegaClosure T H : Set G) =
    (outsideResidual H).pCoreIn 2
  faithful : Function.Injective
    (residualQuotientAction T H orthogonal.source.outside.1.1.2)
  component : Source.NormalComponentIn H (outsideResidual H)
  quotient_model : ClassicalGroup.IsPSL
    (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ S.field.degree)
  cover : ∃ q : PerfectCentralCovering.Cover (OriginalBlock.SeedQuotient D)
      (Matrix.SpecialLinearGroup (Fin 3) S.field.Carrier),
    q.toMonoidHom = OriginalBlock.seedQuotientModel D S marking
  star_model : ClassicalGroup.IsPSL (residualStar T H) 2 (2 ^ S.field.degree)
  pair_card : Nat.card (pairCore V H conjugator) = (2 ^ S.field.degree)^4
  radical : f.Ri 1 ⊓ L = pairCore V H conjugator ⊔ V
  thompson : Stellmacher.elementaryAbelianMaxJ (pairCore V H conjugator ⊔ V) =
    pairCore V H conjugator

/-- Construct the complete state before the odd-degree paragraph. In particular
this discharges all the common-action and identification hypotheses of the
orthogonal producer, on the original flag and with one common conjugator. -/
theorem assemble_orthogonal_input
    (c : Coordinates D S.field) (f : InvariantFlag c) (hu : f.IsInnerUnique)
    (s : Hypothesis1131At D S (c.binarySubspace (f.space 0)) H)
    (p : Preceding1137 c f H)
    (hc : ¬ Proposition1132At D S (c.binarySubspace (f.space 0)) H)
    (A : Subgroup G) (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes (A.subgroupOf (H ⊓ normalizer (L : Set G)))) :
    Nonempty (AssembledInput c f H A) := by
  obtain ⟨hclosure,⟨cK⟩,g,hg,ha,_⟩ := exists_selected_natural_action f s p.preceding hc
    p.global_s p.residual_model
  obtain ⟨hcomponent,hkernel,hfaithful,hstar,hAL,hZ,hV,hVH,hgV,⟨R,hR⟩,
      hline,hlineH,X,hX,hAX⟩ := source_action_complete c f hu rfl p.not_g2 s p.preceding
    hc p.residual_component p.residual_model p.global_s p.alternative p.parameters p.weak
    p.prime_residual p.cubic g hg ha A hA hHall
  have hnot : ¬ V ≤ H.pCoreIn 2 := by
    intro h
    apply ha
    rw [hgV]
    exact h.trans (core_centralizes_omegaClosure T H s.outside.1.1.2)
  obtain ⟨h,hh,hm⟩ := exists_outside s
  have hk := source_residual_le_pairGroup s hh hm hnot p.residual_model R hR
  have hz := pair_intersection_eq_bot s hVH hk
  obtain ⟨hI,⟨cP⟩⟩ := source_pair_recognition s hh hm hVH hnot p.residual_model cK
    R hR A hA hHall hAL
  have hindex := axis_card_mul_field s p.residual_model R hR
  cases c with
  | g2 a => exact (p.not_g2 ⟨a⟩).elim
  | sp4 a => exact (cP.not_sp4 s hh hVH hk rfl hindex a f hV).elim
  | sl3 a =>
    have hmult := cP.sl3_multiplicity s hh hz rfl hindex a hV
    have hBcard : Nat.card (axis V H) = (2 ^ S.field.degree)^2 := by
      rw [cP.axis_card s hh hz,hmult]
    have huniq : f.IsUnique := fun i U hd hn => hu i U hd (inf_le_left.trans hn)
    have hB := source_axis_eq_plane a f huniq s p.preceding hc hV hVH
      p.residual_model cK R hR hBcard
    obtain ⟨hcore,hcent,a',hblock,hB',hPV',hE,hcard,hRad,hJ,hI',hK,hL2,hcover⟩ :=
      source_pair_final_core_identifications (.sl3 a) f s p.preceding hc hh hm hV hVH
        hnot p.residual_model p.not_g2 R hR cK A X hA hHall hX hAX
    have hplane : (SL3.flag D S a').Vi 1 = f.Vi 1 := hB'.symm.trans hB
    have hlocal : (SL3.flag D S a').Li 1 = f.Li 1 :=
      congrArg (localResidual L) hplane
    have hradical : (SL3.flag D S a').Ri 1 = f.Ri 1 :=
      congrArg (localRadical T L) hplane
    let d : OrthogonalInput D S a f H X A h := {
      source := s
      preceding := p.preceding
      counterexample := hc
      unique_flag := huniq
      cartan := hX
      hall_le := hA
      hall := hHall
      oddCartan_le := hAX
      residual_component := hcomponent.1.2
      closure_le_sylow := hclosure
      closure_natural := cK
      omega_fixed := hZ
      seed_fixed := hV
      closure_fixed := hVH
      seed_star_sylow := ⟨R,hR⟩
      line_moved := hline.symm
      line_le_closure := hlineH
      conjugator_mem := hh
      conjugator_outside := hm
      pair_normal := pairGroup_normal_in_H s hh hk
      pair_residual := pairGroup_residual_eq s hh hk
      conjugates_disjoint := hz
      pair_core := hI'.symm
      residual_core := hK.symm
      local_core := hlocal ▸ hL2.symm
      axis_eq_plane := hB
      intersection_eq_plane := (pairCore_inf_seed hh).trans hB
      block := hblock
      seed_core := hcore
      seed_centralizer := hcent
      pair_field := S.field
      pair_degree := rfl
      pair_natural := cP
      pair_multiplicity := hmult }
    exact ⟨{
      marking := a
      coordinates_eq := rfl
      cartan := X
      conjugator := h
      orthogonal := d
      selected := g
      selected_le := hg
      selected_active := ha
      selected_eq := hgV
      kernel := hkernel
      faithful := hfaithful
      component := hcomponent
      quotient_model := p.residual_model
      cover := ⟨OriginalBlock.seedCover D S a (by rw [hcore]; exact D.eq_commutator.symm),rfl⟩
      star_model := hstar
      pair_card := hcard
      radical := hradical ▸ hRad
      thompson := hJ }⟩

private theorem transported_Li {c c' : Coordinates D S.field} (he : c = c')
    (f : InvariantFlag c) (i : Fin 2) : (he ▸ f).Li i = f.Li i := by
  subst c'
  rfl

/-- The common-core and orthogonal conclusions on the original source groups.
All local premises of the three input theorem families are discharged here.
The only remaining premises are the named earlier-source results, assigned to
the parameter-component and natural-local-geometry producers. The returned
state also feeds `source_local_natural_sections` and `source_compatible_fields`
with the literal sections V₂ and P/V₂. -/
theorem source_common_core_geometry
    (c : Coordinates D S.field) (f : InvariantFlag c) (hu : f.IsInnerUnique)
    (s : Hypothesis1131At D S (c.binarySubspace (f.space 0)) H)
    (p : Preceding1137 c f H)
    (hc : ¬ Proposition1132At D S (c.binarySubspace (f.space 0)) H)
    (A : Subgroup G) (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes (A.subgroupOf (H ⊓ normalizer (L : Set G)))) :
    ∃ d : AssembledInput c f H A,
      letI := source_pairCore_normal_sylow d.orthogonal
      Odd S.field.degree ∧ oddCartanPart A = A ∧ A ≤ d.cartan ∧
      sourceTL T L = (T : Subgroup G) ∧ (T : Subgroup G) ≤ L ∧
      (∃ t : Sylow 2 L, (t : Subgroup L).map L.subtype = (T : Subgroup G)) ∧
      IsElementaryAbelian 2 ((T : Subgroup G) ⧸ (pairCore V H d.conjugator).subgroupOf T) ∧
      Nat.card ((T : Subgroup G) ⧸ (pairCore V H d.conjugator).subgroupOf T) =
        (2 ^ S.field.degree)^2 ∧
      (∃ e : axis V H × (axis V H).map (MulAut.conj d.conjugator).toMonoidHom ≃*
          pairCore V H d.conjugator,
        ∀ b a, (e (b,a) : G) = (b : G) * (a : G)) ∧
      Source.NormalComponentIn (coreNormalizer V H d.conjugator) (outsideResidual H) ∧
      Source.NormalComponentIn (coreNormalizer V H d.conjugator) (f.Li 1) ∧
      orthogonalJoin (f.Li 1) V d.conjugator = outsideResidual H ⊔ f.Li 1 ∧
      orthogonalJoin (f.Li 1) V d.conjugator =
        (primeToResidual 2 (coreNormalizer V H d.conjugator)).map
          (coreNormalizer V H d.conjugator).subtype ∧
      Nonempty (ProductQuotientMarking (orthogonalJoin (f.Li 1) V d.conjugator)
        (pairCore V H d.conjugator) (outsideResidual H) (f.Li 1) S.field) ∧
      Nonempty (OrthogonalMarking (orthogonalJoin (f.Li 1) V d.conjugator)
        (pairCore V H d.conjugator) (outsideResidual H) (f.Li 1) d.orthogonal.pair_field) ∧
      IsCartan T (orthogonalJoin (f.Li 1) V d.conjugator) d.cartan := by
  obtain ⟨d⟩ := assemble_orthogonal_input c f hu s p hc A hA hHall
  have hLi := transported_Li d.coordinates_eq f 1
  refine ⟨d,?_⟩
  let := source_pairCore_normal_sylow d.orthogonal
  refine ⟨source_degree_odd d.orthogonal,source_hall_eq_oddCartanPart d.orthogonal,
    source_hall_le_cartan d.orthogonal,
    (source_original_sylow_placement d.orthogonal).1,
    (source_original_sylow_placement d.orthogonal).2.1,
    (source_original_sylow_placement d.orthogonal).2.2,
    (source_original_sylow_quotient d.orthogonal).1,
    (source_original_sylow_quotient d.orthogonal).2,
    pairCore_direct_product d.orthogonal.source d.orthogonal.conjugator_mem
      d.orthogonal.conjugates_disjoint,
    source_residual_normal_component d.orthogonal,?_,?_,?_,?_,?_,?_⟩
  · simpa only [hLi] using source_local_normal_component d.orthogonal
  · simpa only [hLi] using (source_factorJoin_and_residual d.orthogonal).1
  · simpa only [hLi] using (source_factorJoin_and_residual d.orthogonal).2
  · simpa only [hLi] using source_product_quotient d.orthogonal
  · simpa only [hLi] using source_orthogonal_marking d.orthogonal
  · simpa only [hLi] using source_orthogonal_cartan d.orthogonal

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore

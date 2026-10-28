module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.LinearThreeSuitable
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.LinearThreeCoverExclusion
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Residuals
public import CFSG.Quasithin.ChapterD.Section02.LinearThreeDetectingActor
public import Theory.Representation.BinaryConjugationSection.FixedKernel
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.ResidualSupport

/-!
# Full supports and a suitable vector in the single linear-three branch

In original14.6.21(1), the actual residual equality and its concrete quotient
model imply Mc = KT: the quotient residual has a two-group of outer
automorphisms. The placed source actor is therefore faithful on the chosen
component. Detecting-actor recognition gives natural central quotients for
all its homogeneous seeds; the full orbit bound and paired-cover obstruction
force dimension three.

The diagram action excludes FF modules on detecting quotients, so F.9.18
exhausts [U,K]. Since Mc = KT, the same natural/dual seed pair is invariant
under the whole Mc and its join equals [U,K], including the original kernel Z.
The existing normal-seed geometry constructs S = N_T(A), fitting placement,
index two, the full local normalizer, and separated conjugates. One u in A
is fixed modulo Z by S, moved modulo Z by K, and satisfies all U0--U3 clauses.
Both support markings and every clause refer to this same original module.

This completes the support and suitable-vector construction in the single
L3(2) source alternative. Establishing the terminal catalogue, excluding
normal PSL2(4), constructing the normal-pair supports and handling A6 remain
with qt-e-suitable-component-supports. Original14.6.18 is the explicit hsolv
input discharged by qt-e-14625-source; the final14.6.24 classification and
critical-pair assembly remain with their existing owners.
Source: Aschbacher--Smith F.9.18(2--4,7),14.6.21(1)--24(1),
printed pp.325--326,1037--1039.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
open Representation.BinaryOffender.Homogeneous Representation.OneCohomology
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Classification Classification.Sieve
open Chapter13.Section08.SourceCompletion.F918
open Subgroup.NormalSylowQuotientAction
open Chapter13.Section08.CriticalGeometry.Reorientation
variable {G : Type*} [Group G] [Finite G]

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
include hG hempty hM hunique hmany hcard e hab hsolv


/-- In the single-component source alternative, the concrete residual model
supplies the original generation Mc = KT. -/
theorem terminal_single_component_generated
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hr : (solvableResidual Mc).map Mc.subtype = K)
    (hm : ComponentQuotientModels K) :
    (K.subgroupOf Mc).Normal ∧ K ⊔ (T : Subgroup G) = Mc := by
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  have hTH : (T : Subgroup G) ≤ Mc := hout.1.2
  have hKi : solvableResidual Mc = K.subgroupOf Mc := by
    apply map_injective Mc.subtype_injective
    rwa [map_subgroupOf_eq_of_le hKM]
  have hn : (K.subgroupOf Mc).Normal := hKi ▸ inferInstance
  let : Group.IsNilpotent (pCore 2 Mc) := pCore_isPGroup.isNilpotent
  let ec : (K ⧸ pCore 2 K) ≃* actorImage Mc K :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKM)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hKM))).symm.trans (cComponentTwoCoreQuotientEquiv hK)
  have he : actorImage Mc K = solvableResidual (Mc ⧸ pCore 2 Mc) := by
    change (K.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc)) = _
    rw [←hKi,map_solvableResidual_eq _ (QuotientGroup.mk'_surjective _)]
  have hmR : ResidualQuotientModels (solvableResidual (Mc ⧸ pCore 2 Mc)) := by
    rcases hm with f | f
    · exact Or.inl ⟨(MulEquiv.subgroupCongr he).symm.trans (ec.symm.trans (Classical.choice f))⟩
    · exact Or.inr (Or.inl ⟨(MulEquiv.subgroupCongr he).symm.trans (ec.symm.trans (Classical.choice f))⟩)
  have hrp := (terminal_residual_structure_of_models
    hG T hempty hM hunique hmany hcard e hab hsolv hmR).1
  have hh := congrArg (Subgroup.map Mc.subtype)
    (pResidual_sup_sylow_eq_top (T.subtype hTH))
  rw [←hrp,Subgroup.map_sup,hr,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH,
    ←MonoidHom.range_eq_map,range_subtype] at hh
  exact ⟨hn,hh⟩

/-- The single L3(2) alternative constructs a homogeneous natural seed of
dimension three in the original U/Z. No generation or cover-size input remains. -/
theorem terminal_single_l3_natural_seed
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hr : (solvableResidual Mc).map Mc.subtype = K)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    ∃ hU : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc),
      let _ := hU
      ∃ a : LocalQuotientAction Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T),
      ∃ (I : Submodule (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) Mc) ⧸
        (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) Mc))))
        (hI : IsIrrPlusWith a.representation (actorImage Mc K)
          (actorImage Mc T ⊓ normalizer (actorImage Mc K : Set (Mc ⧸ pCore 2 Mc))) I),
        Nonempty (ChapterB.QuasisimpleSource.ActionEquiv
          (centralQuotientRepresentation a.representation (actorImage Mc K) I hI.isIrrPlus.choose)
          (ChapterB.QuasisimpleSource.linearNatural ChapterB.QuasisimpleSource.BinaryField.two 3)) ∧
        Module.finrank (ZMod 2) I = 3 ∧
        quadraticRatio (invariantSubspace a.representation (actorImage Mc K)
          (orbitSpan a.representation
            (actorImage Mc T ⊓ normalizer (actorImage Mc K : Set (Mc ⧸ pCore 2 Mc))) I)
          (orbitSpan_component_invariant a.representation hI.normalizes hI.isIrrPlus)).toRepresentation ≤ 2 := by
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  have hTH : (T : Subgroup G) ≤ Mc := hout.1.2
  obtain ⟨hn,hgen⟩ := terminal_single_component_generated
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hr (Or.inl ⟨eK⟩)
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    hout.1.2.trans ((normal_subgroupOf_iff_le_normalizer hKM).mp hn)
  have hspan : conjugateSpanBy K (T : Subgroup G) = K :=
    le_antisymm (conjugateSpanBy_le le_rfl hTK) (le_conjugateSpanBy _ _)
  obtain ⟨hU,a,B,I,hB,hI,_,hA,hfaith,_⟩ := source_component_span_inputs
    hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K hKM hK
    (by rw [hspan,hgen])
  let := hU
  let : Module.Finite (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) Mc) ⧸
    (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) Mc))) := Module.Finite.of_finite
  let D := actorImage Mc K
  let : D.Normal := hn.map (QuotientGroup.mk' (pCore 2 Mc)) (QuotientGroup.mk'_surjective _)
  have hD := source_quotient_component hG T hempty hM hunique hmany hcard e hab hsolv
    Mc hout K hKM hK
  let : IsQuasisimple D := hD.2
  let : Group.IsNilpotent (pCore 2 Mc) := pCore_isPGroup.isNilpotent
  let ec : (K ⧸ pCore 2 K) ≃* D :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKM)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hKM))).symm.trans (cComponentTwoCoreQuotientEquiv hK)
  let j := ec.symm.trans eK
  have hz : center D = ⊥ := by
    apply bot_unique
    intro k hk
    have hh := (centerCongr j ⟨k,hk⟩).property
    change j k ∈ center BinaryLinearThree.Group at hh
    rw [show center BinaryLinearThree.Group = ⊥ from Matrix.PSL3Two.center_eq_bot,mem_bot] at hh
    exact j.injective (hh.trans j.map_one.symm)
  have ho := quotient_componentOrbit Mc K T hKM hout.1.2
  rw [hspan] at ho hfaith
  have hIQ : IsIrrPlusWith a.representation D
      (actorImage Mc T ⊓ normalizer (D : Set (Mc ⧸ pCore 2 Mc))) I := by
    rw [ho] at hI
    change IsIrrPlusWith a.representation D (actorImage Mc T) I at hI
    simpa only [normalizer_eq_top,inf_top_eq] using hI
  have hs : IsSQTK KnownSimple.IsKnownSimple (Mc ⧸ pCore 2 Mc) := by
    have hsH := Chapter3.sqtk_of_mem_H hG hout.1.1
    refine ⟨?_,hsH.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hsH.stronglyQuasithin p hp ho)
  have hm : ClassicalGroup.IsPSL D 3 2 :=
    ⟨ZMod 2,inferInstance,inferInstance,Nat.card_zmod 2,⟨j.trans Matrix.PSL3Two.equiv⟩⟩
  let A := B.map (QuotientGroup.mk' (pCore 2 Mc))
  have hAN : A ≤ normalizer (D : Set (Mc ⧸ pCore 2 Mc)) := by
    rw [normalizer_eq_top]; exact le_top
  obtain ⟨b⟩ := ChapterD.central_linear_three_of_detecting_actor a.representation
    hD.1 hz hs hm hAN hA hfaith hIQ.isIrrPlus
  have hAP := le_inf (source_internal_actor_le_sylow T hout.1.2 B hB) hAN
  have hP : IsPGroup 2 (actorImage Mc T ⊓ normalizer (D : Set (Mc ⧸ pCore 2 Mc)) :
      Subgroup (Mc ⧸ pCore 2 Mc)) := by
    rw [normalizer_eq_top,inf_top_eq]
    exact (quotientSylow Mc T hout.1.2).isPGroup'
  have hsmall := ChapterD.linear_three_orbit_bound_of_detecting_actor
    a.representation hz hP hAP hA hfaith hIQ b
  exact ⟨hU,a,I,hIQ,⟨b⟩,(source_l3_natural_seed_sections
    hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K hKM hK a hIQ b hsmall).1,hsmall⟩

/-- The full seed orbit exhausts the literal residual support. The strong
quotient alternative is excluded using its actual irreducible subquotients. -/
theorem source_normal_l3_full_orbit_exhaustion
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : (K.subgroupOf H).Normal)
    (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (T : Subgroup G) = H)
    [hU : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
    {I : Submodule (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) H) ⧸
      (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) H)))}
    (hI : IsIrrPlusWith a.representation (actorImage H K)
      (actorImage H T ⊓ normalizer (actorImage H K : Set (H ⧸ pCore 2 H))) I)
    (b : ChapterB.QuasisimpleSource.ActionEquiv
      (centralQuotientRepresentation a.representation (actorImage H K) I hI.isIrrPlus.choose)
      (ChapterB.QuasisimpleSource.linearNatural ChapterB.QuasisimpleSource.BinaryField.two 3))
    (hsmall : quadraticRatio (invariantSubspace a.representation (actorImage H K)
      (orbitSpan a.representation
        (actorImage H T ⊓ normalizer (actorImage H K : Set (H ⧸ pCore 2 H))) I)
      (orbitSpan_component_invariant a.representation hI.normalizes hI.isIrrPlus)).toRepresentation ≤ 2) :
    Function.Injective (seedOrbit a.representation I).toRepresentation ∧
    ¬ IsFFModule (imageRepresentation (seedOrbit a.representation I).toRepresentation) ∧
    orbitSpan a.representation ⊤ I = subspaceCommutator a.representation ⊤
        (actorImage H (conjugateSpanBy K (T : Subgroup G))) := by
  let : Module.Finite (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) H) ⧸
    (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) H))) := Module.Finite.of_finite
  obtain ⟨hf,hnf,heq | ⟨hfQ,hffQ⟩⟩ := source_l3_full_orbit_exhaustion_or_strong_quotient
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hgen a hI b hsmall
  · exact ⟨hf,hnf,heq⟩
  have hD := source_quotient_component hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK
  have hd : ¬ actorImage H K ≤ (seedOrbit a.representation I).quotientRepresentation.ker := by
    intro hk
    exact hD.isCComponent.ne_bot (bot_unique
      (hk.trans ((MonoidHom.ker_eq_bot_iff _).mpr hfQ).le))
  obtain ⟨B,hB,hBA,hq,hr,hfaith⟩ := source_rankTwo_placed_quadratic_actor
    hG T hempty hM hunique hmany hcard e hab H hH hU a
  rw [source_component_orbit_eq_residual hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK hgen] at hfaith
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    hH.1.2.trans ((normal_subgroupOf_iff_le_normalizer hKH).mp hn)
  have hspan : conjugateSpanBy K (T : Subgroup G) = K :=
    le_antisymm (conjugateSpanBy_le le_rfl hTK) (le_conjugateSpanBy _ _)
  rw [hspan] at hfaith
  let D := actorImage H K
  let A := B.map (QuotientGroup.mk' (pCore 2 H))
  let : D.Normal := hn.map (QuotientGroup.mk' (pCore 2 H)) (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple D := hD.2
  let j : D ≃* BinaryLinearThree.Group := b.groupEquiv
  have hz : center D = ⊥ := by
    apply bot_unique
    intro k hk
    have hh := (centerCongr j ⟨k,hk⟩).property
    change j k ∈ center BinaryLinearThree.Group at hh
    rw [show center BinaryLinearThree.Group = ⊥ from Matrix.PSL3Two.center_eq_bot,mem_bot] at hh
    exact j.injective (hh.trans j.map_one.symm)
  have hAN : A ≤ normalizer (D : Set (H ⧸ pCore 2 H)) := by
    rw [normalizer_eq_top]; exact le_top
  have hm : ClassicalGroup.IsPSL D 3 2 :=
    ⟨ZMod 2,inferInstance,inferInstance,Nat.card_zmod 2,⟨j.trans Matrix.PSL3Two.equiv⟩⟩
  have hsQ : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
    have hsH := Chapter3.sqtk_of_mem_H hG hH.1.1
    refine ⟨?_,hsH.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hsH.stronglyQuasithin p hp ho)
  let W := seedOrbit a.representation I
  have hno : ¬ IsFFModule W.quotientRepresentation := by
    obtain ⟨U,N,hi,hd⟩ := QuadraticFourGroup.exists_irreducible_section_surviving_perfect D hd
    let τ := N.quotientRepresentation
    let q : a.representation.IntertwiningMap W.quotientRepresentation := {
      toLinearMap := W.toSubmodule.mkQ
      isIntertwining' := fun _ => rfl }
    have hs : QuadraticFourGroup.IsIrreducibleSection W.quotientRepresentation τ :=
      ⟨hi,U,N,⟨Representation.Equiv.refl _⟩⟩
    obtain ⟨_,U',N',⟨c⟩⟩ := hs.of_surjective_intertwining q W.toSubmodule.mkQ_surjective
    have hi' : IsIrreducible N'.quotientRepresentation :=
      (RepEquiv.irreducible_euqiv (RepEquiv.ofRepresentationEquiv c)).mpr hi
    have hd' : ¬ D ≤ N'.quotientRepresentation.ker :=
      fun hk => hd (hk.trans (QuadraticFourGroup.ker_le_of_equiv c))
    let : Finite (U' ⧸ N'.toSubmodule) := Module.finite_of_finite (ZMod 2)
    let : IsIrreducible N'.quotientRepresentation := hi'
    let : IsSemisimpleRepresentation (N'.quotientRepresentation.comp D.subtype) :=
      (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mpr
        (subnormal_restriction_semisimple N'.quotientRepresentation D hD.1)
    have hf' := source_faithful_of_component_detected
      hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hgen
      N'.quotientRepresentation hd'
    have hnat := ChapterD.subquotient_linear_three_of_detecting_actor a.representation
      hD.1 hz hsQ hm hAN ⟨hBA,hq,hr⟩ hfaith U' N' hi'
    have hnot := source_l3_natural_types_not_ff
      hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hgen
      N'.quotientRepresentation hf' hnat
    have hnτ : ¬ IsFFModule τ := by
      intro hh
      apply hnot
      exact hh.map_equivariant τ N'.quotientRepresentation (MonoidHom.id _)
        Function.injective_id c.symm.toLinearEquiv (fun g v =>
          LinearMap.congr_fun (c.symm.isIntertwining' g) v)
    rintro ⟨C,hC,hbound⟩
    apply hnτ
    refine ⟨C,hC,?_⟩
    have hq := fixedCodim_quotient_add_subrepresentation_le U.toRepresentation N C
    have hu := fixedCodim_subrepresentation_le W.quotientRepresentation U C
    change fixedCodim N.quotientRepresentation C ≤ rank C
    omega
  obtain ⟨C,hC,hlt⟩ := hffQ
  exact (not_ff_image_of_faithful _ hfQ hno ⟨C,hC,hlt.le⟩).elim

/-- Original case (1), with linear-three quotient, supplies the full natural
and dual supports and a single involution satisfying all suitable clauses. -/
theorem terminal_single_l3_full_supports_suitable
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hr : (solvableResidual Mc).map Mc.subtype = K)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    let h := terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
    ∃ (j : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (A B : Subgroup G),
      Nonempty (BinaryConjugationSection K A (centralInvolutions T)
        (BinaryLinearThree.W.comp (j.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))))) ∧
      Nonempty (BinaryConjugationSection K B (centralInvolutions T)
        (BinaryLinearThree.W.dual.comp (j.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))))) ∧
      ⁅conjugateSpanBy (localModule T M) Mc,K⁆ = A ⊔ B ∧
      A ⊓ B = centralInvolutions T ∧
      (∃ s : T, B = A.map (MulAut.conj (s:G)⁻¹).toMonoidHom) ∧
      conjugateSpanBy A (T : Subgroup G) = A ⊔ B ∧
      (normalizer (A : Set G)).relIndex (T : Subgroup G) = 2 ∧
      Mc ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) ∧
      Geometry T Mc (conjugateSpanBy (localModule T M) Mc) K A
        ((T : Subgroup G) ⊓ normalizer (A : Set G)) ∧
      ∃ u ∈ A, u ^ 2 = 1 ∧ u ≠ 1 ∧
        suitableQuotientCentralizer h u = (T : Subgroup G) ⊓ normalizer (A : Set G) ∧
        (∀ s ∈ (T : Subgroup G) ⊓ normalizer (A : Set G), ⁅u,s⁆ ∈ centralInvolutions T) ∧
        (∃ k ∈ K, ⁅u,k⁆ ∉ centralInvolutions T) ∧
        Suitable h Mc u := by
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  obtain ⟨hn,hgen⟩ := terminal_single_component_generated
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hr (Or.inl ⟨eK⟩)
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    hout.1.2.trans ((normal_subgroupOf_iff_le_normalizer hKM).mp hn)
  have hspanK : conjugateSpanBy K (T : Subgroup G) = K :=
    le_antisymm (conjugateSpanBy_le le_rfl hTK) (le_conjugateSpanBy _ _)
  obtain ⟨hU,a,I,hI,⟨b⟩,hdim,hsmall⟩ := terminal_single_l3_natural_seed
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hr eK
  let := hU
  let A := (originalSection a).subspacePreimage I
  obtain ⟨_,j,B,⟨d⟩,⟨ddual⟩,hA,hB,hAB,hconj,hspanA,hindex⟩ := source_l3_natural_seed_sections
    hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K hKM hK a hI b hsmall
  rw [inf_eq_left.mpr hTK] at hconj hspanA hindex
  have hWK : K ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) :=
    (le_inf d.normalized ddual.normalized).trans (normalizer_inf_normalizer_le_normalizer_sup A B)
  have hWT : (T : Subgroup G) ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
    rw [←hspanA]
    exact le_normalizer_conjugateSpanBy _ _
  have hWM : Mc ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
    rw [←hgen]
    exact sup_le hWK hWT
  have hspanM : conjugateSpanBy A Mc = A ⊔ B := by
    apply le_antisymm (conjugateSpanBy_le le_sup_left hWM)
    rw [←hspanA]
    exact conjugateSpanBy_mono le_rfl hout.1.2
  have hexhaust := (source_normal_l3_full_orbit_exhaustion
    hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K hKM hK hn
    (by rw [hspanK,hgen]) a hI b hsmall).2.2
  have hfull := source_residual_support_eq_seed_span
    hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K hKM hK a I hexhaust
  rw [hspanK] at hfull
  have hgeo := source_normal_l3_seed_geometry
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn hgen a hI b
  have hzero : ∀ v, (∀ k : K, (BinaryLinearThree.W.comp
      (j.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))) k v = v) → v = 0 := by
    intro v hv
    have hh : v ∈ fixed (specialLinearNatural (k := ZMod 2) 3) := by
      intro g
      obtain ⟨k,rfl⟩ := (j.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 K))) g
      exact hv k
    rwa [SLHigherNatural.fixed_eq_bot (by decide : 2 ≤ 3)] at hh
  have hsep := d.centralizer_le_kernel_of_fixed_eq_zero hzero
  have hgeom : Geometry T Mc (conjugateSpanBy (localModule T M) Mc) K A
      ((T : Subgroup G) ⊓ normalizer (A : Set G)) := by
    refine ⟨hgeo.fitting,hgeo.support_le,hgeo.point_le,hgeo.normalized,
      hgeo.sylow_le,hgeo.index,hgeo.local_normalizer,?_⟩
    intro t ht hnt
    have hh := hgeo.separated t ht hnt
    exact ⟨(le_inf inf_le_left hh.1).trans hsep,hh.2⟩
  obtain ⟨u,hu,hu2,hune,heq,hsuit⟩ := source_exists_on_normal_l3_seed_of_three
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn hgen a hI b hdim
  let h := terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  have huH : u ∈ Mc := (originalSection a).section_le ((originalSection a).subspacePreimage_le I hu)
  have hfixed : ∀ s ∈ (T : Subgroup G) ⊓ normalizer (A : Set G), ⁅u,s⁆ ∈ centralInvolutions T := by
    intro s hs
    have hs' : s ∈ suitableQuotientCentralizer h u := heq.symm ▸ hs
    exact ((h.mem_kernel_iff (zpowers_le.mpr huH)).mp hs'.2).2 u (mem_zpowers u)
  have hmoved : ∃ k ∈ K, ⁅u,k⁆ ∉ centralInvolutions T := by
    by_contra hno
    push Not at hno
    have hv : (d.coordinates ⟨u,hu⟩).toAdd = 0 := hzero _ (fun k =>
      (d.fixed_coordinate_iff_commutator_mem k ⟨u,hu⟩).mpr (hno k k.property))
    have huz : u ∈ centralInvolutions T := (d.coordinates_eq_one_iff ⟨u,hu⟩).mp hv
    apply hsuit.2.2.2.1
    intro q hq
    exact mem_centralizer_singleton_iff.mpr
      ((h.H_centralizes (pCoreIn_le 2 Mc hq)) u huz).symm
  exact ⟨j,A,B,⟨d⟩,⟨ddual⟩,hfull.trans hspanM,hAB,hconj,hspanA,hindex,hWM,hgeom,
    u,hu,hu2,hune,heq,hfixed,hmoved,hsuit⟩

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition

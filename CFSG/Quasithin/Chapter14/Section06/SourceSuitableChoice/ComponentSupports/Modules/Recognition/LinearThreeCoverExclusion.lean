module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.LinearThreeFullAction
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.LinearThreeMovement
public import Theory.Representation.BinaryOffender.Homogeneous.LinearThreeCoverPair
public import Theory.Representation.BinaryConjugationSection.Relabel

/-!
# Excluding four-dimensional terminal seeds and marking their original supports

The full component orbit has quadratic ratio at most two, and the actual
source parabolic swap moves every marked natural-cover seed. The paired
cover obstruction therefore forces dimension three. Its chosen conjugate
is the dual module for the same component marking.

Lift both equivalences through the original U/Z coordinates. This constructs
literal natural and dual BinaryConjugationSection witnesses over the same
centralInvolutions T, with an actual K/O₂(K) isomorphism, supports in [U,K],
intersection exactly Z, their conjugate-span identity, and index-two inertia.
The terminal exchanged-component application supplies the ratio premise.

The identity of this seed orbit with the full [U,K], FF elimination,
normal PSL₂(4) exclusion and suitable-vector assembly remain with
qt-e-suitable-component-supports. These seeds alone do not supply the four
full supports required by TwoComponents/SourceSections. Original14.6.18
remains hsolv, discharged by qt-e-14625-source; the final suitable witness
must be shared by every support consumer.

Source: Aschbacher--Smith B.4.8(2), F.9.18(2), and14.6.22--24,
printed pp.91,325,1038--1039.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Classification Classification.Sieve
open Chapter13.Section08.SourceCompletion.F918
open Chapter13.Section08.CriticalGeometry.Reorientation
open Chapter13.Section08.Components.SourceModels
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


/-- A small full component orbit gives literal natural and dual sections
over the original Z. This identifies the seed orbit, not yet all of [U,K]. -/
theorem source_l3_natural_seed_sections
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
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
    let A := (originalSection a).subspacePreimage I
    let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
    Module.finrank (ZMod 2) I = 3 ∧
      ∃ (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (B : Subgroup G),
      Nonempty (BinaryConjugationSection K A (centralInvolutions T)
        (BinaryLinearThree.W.comp (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))))) ∧
      Nonempty (BinaryConjugationSection K B (centralInvolutions T)
        (BinaryLinearThree.W.dual.comp (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))))) ∧
      A ≤ ⁅conjugateSpanBy (localModule T M) H,K⁆ ∧
      B ≤ ⁅conjugateSpanBy (localModule T M) H,K⁆ ∧
      A ⊓ B = centralInvolutions T ∧
      (∃ s : S, B = A.map (MulAut.conj (s:G)⁻¹).toMonoidHom) ∧
      conjugateSpanBy A S = A ⊔ B ∧
      (normalizer (A : Set G)).relIndex S = 2 := by
  let : Module.Finite (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) H) ⧸
    (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) H))) := Module.Finite.of_finite
  let c := originalSection a
  let A := c.subspacePreimage I
  let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
  let R := actorImage H T ⊓ normalizer (actorImage H K : Set (H ⧸ pCore 2 H))
  let q := QuotientGroup.mk' (pCore 2 H)
  have hR : actorImage H S = R := source_component_normalizer_image T H hH K hKH hK
  obtain ⟨⟨s,hs⟩,hindex⟩ := source_l3_seed_stabilizer_index
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK a hI b
  have hmove : orbitSpan a.representation R I ≠ I := by
    intro hh
    have hinv : R ≤ subspaceStabilizer a.representation I :=
      hh ▸ orbitSpan_invariant a.representation R I
    let v : H := ⟨s,hH.1.2 s.property.1⟩
    have hqv : q v ∈ R := hR ▸ (show q v ∈ actorImage H S from ⟨v,s.property,rfl⟩)
    apply hs
    exact (c.mem_normalizer_subspacePreimage_iff I v).mpr
      ((subspace_map_eq_iff a.representation I (q v)).mpr (hinv hqv))
  have hd := (hI.finrank_three_of_small_orbit a.representation b.groupEquiv
    b.linearEquiv b.intertwines hmove hsmall).1
  obtain ⟨t,l,m,hspan,hdis,hl,hm⟩ := hI.natural_dual_pair_of_small_orbit
    a.representation b.groupEquiv b.linearEquiv b.intertwines hmove hsmall
  let J := I.map (a.representation t.val)
  let B := c.subspacePreimage J
  have hJ := hI.isIrrPlus.map_normalizer a.representation (hI.normalizes t.property)
  let e₀ : (K ⧸ pCore 2 K) ≃* actorImage H K :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKH)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hKH))).symm.trans (cComponentTwoCoreQuotientEquiv hK)
  let eK := e₀.trans b.groupEquiv
  let f := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let qK : K →* actorImage H K :=
    ((QuotientGroup.mk' (pCore 2 H)).subgroupMap (K.subgroupOf H)).comp
      (subgroupOfEquivOfLe hKH).symm.toMonoidHom
  obtain ⟨d,_⟩ := source_component_seed_coordinates
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK a hI.isIrrPlus
  obtain ⟨d',_⟩ := source_component_seed_coordinates
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK a hJ
  let E : Representation.Equiv
      (BinaryConjugationSection.subspaceAction K hKH I (originalSection_irrPlus a K hI.isIrrPlus).choose)
      (BinaryLinearThree.W.comp f) := {
    toLinearEquiv := l
    isIntertwining' k := by
      apply LinearMap.ext
      intro v
      exact hl (qK k) v }
  let E' : Representation.Equiv
      (BinaryConjugationSection.subspaceAction K hKH J (originalSection_irrPlus a K hJ).choose)
      (BinaryLinearThree.W.dual.comp f) := {
    toLinearEquiv := m
    isIntertwining' k := by
      apply LinearMap.ext
      intro v
      exact hm (qK k) v }
  have hAB : A ⊓ B = centralInvolutions T := by
    change c.subspacePreimage I ⊓ c.subspacePreimage J = centralInvolutions T
    rw [←c.subspacePreimage_inf,hdis.eq_bot]
    apply le_antisymm
    · intro x hx
      obtain ⟨hx,hz⟩ := (c.mem_subspacePreimage ⊥ x).mp hx
      exact (c.coordinates_eq_one_iff ⟨x,hx⟩).mp hz
    · exact c.kernel_le_subspacePreimage ⊥
  obtain ⟨v,hv,hvQ⟩ := (show t.val ∈ actorImage H S from hR.symm ▸ t.property)
  let s₀ : S := ⟨(v:G)⁻¹,S.inv_mem hv⟩
  have hB : B = A.map (MulAut.conj (s₀:G)⁻¹).toMonoidHom := by
    have hh := c.subspacePreimage_map I v
    change c.subspacePreimage (I.map (a.representation (q v))) =
      A.map (MulAut.conj (v:G)).toMonoidHom at hh
    rw [hvQ] at hh
    simpa only [s₀,inv_inv] using hh
  have hBA : B ≠ A := by
    intro hh
    have hj : J = I := c.subspacePreimage_injective hh
    have hdis' : Disjoint I J := hdis
    rw [hj] at hdis'
    have hi : I = ⊥ := disjoint_self.mp hdis'
    exact hI.isIrrPlus.ne_bot a.representation hi
  obtain ⟨s₁,hpairs,hspan',_⟩ := source_seed_two_conjugates T H hH K hKH hK a hI
    b.groupEquiv (by omega)
  have hother := hpairs s₀
  rw [←hB] at hother
  have hB' := hother.resolve_left hBA
  refine ⟨hd,eK,B,⟨d.relabel (MonoidHom.id K) E⟩,⟨d'.relabel (MonoidHom.id K) E'⟩,
    (source_component_seed_geometry hG T hempty hM hunique hmany hcard e hab hsolv
      H hH K hKH hK a hI.isIrrPlus).2.1,
    (source_component_seed_geometry hG T hempty hM hunique hmany hcard e hab hsolv
      H hH K hKH hK a hJ).2.1,hAB,⟨s₀,hB⟩,?_,hindex⟩
  rw [hB']
  exact hspan'

/-- The original exchanged-component hypotheses give actual natural and
dual sections on the two seeds, with their literal central kernel and span. -/
theorem terminal_nonnormal_natural_seed_sections
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hn : ¬ (K.subgroupOf Mc).Normal) :
    ∃ (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (A B : Subgroup G),
      Nonempty (BinaryConjugationSection K A (centralInvolutions T)
        (BinaryLinearThree.W.comp (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))))) ∧
      Nonempty (BinaryConjugationSection K B (centralInvolutions T)
        (BinaryLinearThree.W.dual.comp (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))))) ∧
      A ≤ ⁅conjugateSpanBy (localModule T M) Mc,K⁆ ∧
      B ≤ ⁅conjugateSpanBy (localModule T M) Mc,K⁆ ∧
      A ⊓ B = centralInvolutions T ∧
      (∃ s : ((T : Subgroup G) ⊓ normalizer (K : Set G) : Subgroup G),
        B = A.map (MulAut.conj (s:G)⁻¹).toMonoidHom) ∧
      conjugateSpanBy A ((T : Subgroup G) ⊓ normalizer (K : Set G)) = A ⊔ B ∧
      (normalizer (A : Set G)).relIndex ((T : Subgroup G) ⊓ normalizer (K : Set G)) = 2 := by
  obtain ⟨hU,a,I,hI,⟨b⟩,_,hsmall,_⟩ := terminal_nonnormal_full_component_action
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn
  let := hU
  obtain ⟨_,eK,B,hB⟩ := source_l3_natural_seed_sections hG T hempty hM hunique hmany hcard e hab hsolv
    Mc (terminal_outside hG T hempty hM hunique hmany hcard e) K hKM hK a hI b hsmall
  exact ⟨eK,(originalSection a).subspacePreimage I,B,hB⟩

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition

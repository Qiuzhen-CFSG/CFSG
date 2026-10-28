module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.QuotientNonFF
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# Exhausting the full original residual commutator support

F.9.18 leaves either exhaustion or a faithful strong-FF quotient after the
full seed orbit is proved non-FF. The component-detecting quotient theorem
excludes the second alternative. Thus the full H-orbit of the selected seed
is exactly the residual commutator in U/Z. The subgroup correspondence lifts
this to the actual residual support, retaining the original central kernel.

At H=Mc the same seed supplies the marked natural/dual subgroup sections,
their central intersection, normalizer span and index two, together with
the full residual-span identity. This does not yet identify their sum with
the individual support [U,K]. Individual full supports, cross-centralization,
separation, the normal PSL2(4) exclusion and suitable-vector assembly remain
with qt-e-suitable-component-supports. Original14.6.18 remains hsolv for
qt-e-14625-source. The waiting paired-component consumer is
ComponentCriticalPair.TwoComponents.SourceSections.

Source: Aschbacher--Smith F.9.18(6--7),14.6.22--23, printed pp.326,1038.
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
universe u
variable {G : Type u} [Group G] [Finite G]
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


/-- The full seed orbit exhausts the literal residual support. The strong
quotient alternative is excluded using its actual irreducible subquotients. -/
theorem source_nonnormal_full_orbit_exhaustion
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : ¬ (K.subgroupOf H).Normal)
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
  have hno := source_nonnormal_quotient_not_ff
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hn hgen a
    (B.map (QuotientGroup.mk' (pCore 2 H)))
    (source_internal_actor_le_sylow T hH.1.2 B hB) ⟨hBA,hq,hr⟩ hfaith
    (seedOrbit a.representation I) hd
  obtain ⟨C,hC,hlt⟩ := hffQ
  exact (not_ff_image_of_faithful _ hfQ hno ⟨C,hC,hlt.le⟩).elim

/-- Full residual-support exhaustion on the original terminal U/Z. -/
theorem terminal_nonnormal_full_orbit_exhaustion
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hn : ¬ (K.subgroupOf Mc).Normal) :
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
      Function.Injective (seedOrbit a.representation I).toRepresentation ∧
      ¬ IsFFModule (imageRepresentation (seedOrbit a.representation I).toRepresentation) ∧
      orbitSpan a.representation ⊤ I = subspaceCommutator a.representation ⊤
          (actorImage Mc (conjugateSpanBy K (T : Subgroup G))) := by
  obtain ⟨hU,a,I,hI,⟨b⟩,_,hsmall,_⟩ := terminal_nonnormal_full_component_action
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn
  let := hU
  exact ⟨hU,a,I,hI,⟨b⟩,source_nonnormal_full_orbit_exhaustion
    hG T hempty hM hunique hmany hcard e hab hsolv Mc
    (terminal_outside hG T hempty hM hunique hmany hcard e) K hKM hK hn
    (terminal_nonnormal_generated hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn)
    a hI b hsmall⟩

/-- Coordinate exhaustion identifies the full original residual support,
including the central kernel Z, with the ambient conjugate span of the seed. -/
theorem source_residual_support_eq_seed_span
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
    (I : Submodule (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) H) ⧸
      (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) H))))
    (hexhaust : orbitSpan a.representation ⊤ I = subspaceCommutator a.representation ⊤
      (actorImage H (conjugateSpanBy K (T : Subgroup G)))) :
    ⁅conjugateSpanBy (localModule T M) H,conjugateSpanBy K (T : Subgroup G)⁆ =
      conjugateSpanBy ((originalSection a).subspacePreimage I) H := by
  let X := conjugateSpanBy K (T : Subgroup G)
  have hXH : X ≤ H := conjugateSpanBy_le hKH (hH.1.2.trans H.le_normalizer)
  have hz := (source_component_support_placement hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK).1.trans (commutator_mono le_rfl (le_conjugateSpanBy K (T : Subgroup G)))
  apply originalSection_commutator_eq_support_span a X H hXH le_rfl I hz
  rw [commutator_comm,(originalSection a).imageSpace_commutator X _ hXH le_rfl,
    (originalSection a).imageSpace_self,subspaceCommutator_comp_map]
  have htop : actorImage H H = ⊤ := by
    change (H.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) = ⊤
    rw [subgroupOf_self,←MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
  rw [htop]
  exact hexhaust.symm

/-- The same original natural/dual seed pair spans the full residual
support under Mc. Individual component exhaustion is a separate assertion. -/
theorem terminal_nonnormal_natural_sections_residual_span
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
      (normalizer (A : Set G)).relIndex ((T : Subgroup G) ⊓ normalizer (K : Set G)) = 2 ∧
      ⁅conjugateSpanBy (localModule T M) Mc,conjugateSpanBy K (T : Subgroup G)⁆ =
        conjugateSpanBy A Mc := by
  obtain ⟨hU,a,I,hI,⟨b⟩,_,hsmall,_⟩ := terminal_nonnormal_full_component_action
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn
  let := hU
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  obtain ⟨_,eK,B,hA,hB,hAU,hBU,hAB,hconj,hspan,hindex⟩ := source_l3_natural_seed_sections
    hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K hKM hK a hI b hsmall
  have hexhaust := (source_nonnormal_full_orbit_exhaustion
    hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K hKM hK hn
    (terminal_nonnormal_generated hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn)
    a hI b hsmall).2.2
  exact ⟨eK,(originalSection a).subspacePreimage I,B,hA,hB,hAU,hBU,hAB,hconj,hspan,hindex,
    source_residual_support_eq_seed_span hG T hempty hM hunique hmany hcard e hab hsolv
      Mc hout K hKM hK a I hexhaust⟩

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition

module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.OriginalConsequences
public import CFSG.Quasithin.Chapter10.SourceA5HallGeneration
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.NoncentralMovement
public import CFSG.Quasithin.ChapterB.Section06To07.NormalActor
/-!
# Actual H* Thompson movement in the natural alternating-five branch

The original natural-four module excludes the paired symmetric-five action
forced by an escaping Baumann normalizer. Thus the Baumann normalizer lies
in M. On H, the literal orbit of the original Sylow omega-center is reduced
and has proper centralizer. If Thompson centralized it, B.2.10 would make
Baum(T) normal in H, contradicting H outside M. The same movement also gives
the exact residual commutator identity from 10.2.2(2).

Source: Aschbacher--Smith 10.2.1--3, printed pp.742--746.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB ChapterE.ThompsonAction
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The original omega-center orbit in H, without the unrelated qrc centralizing guard. -/
theorem source_hstar_omega_orbit_reduced
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    IsPReduced 2 ((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H) := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  exact (D.qrcHypotheses hu hH).sylowOmega_reduced (D.simpleQTKE.evenCharacteristic T)

/-- Noncentrality of the seed makes the actual reduced action nontrivial. -/
theorem source_hstar_omega_orbit_centralizer_proper
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    centralizer (((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H) : Set H) ≠ ⊤ := by
  intro he
  apply hZH
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro z hz h hh
  have hzH : z ∈ H := hH.1.1.2 ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hc : (⟨h,hh⟩ : H) ∈ centralizer
      (((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H) : Set H) :=
    he.symm ▸ mem_top _
  exact (congrArg H.subtype (hc ⟨z,hzH⟩ (le_conjugateSpanBy _ _ hz))).symm

variable {F : Type*} [Field F] [CharP F 2]
local instance hstarSourceMovementFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- Natural-four and paired five-letter actions cannot occur on the same original component. -/
theorem source_natural_four_baumann_normalizer_le
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hF : Nat.card F = 4) (f : alternatingGroup (Fin 5) ≃* SL(2,F))
    (n : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))) :
    normalizer (baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal := by
  by_contra hout
  exact source_original_not_paired_five_of_natural_four D e hn
    (source_local_thompson_not_centralizes D hout) hF f n
    (source_a5_paired_five_action D e hn hout)

/-- The literal H* omega-orbit satisfies the missing movement premise of E.2.3. -/
theorem source_hstar_thompson_moves_omega_orbit_of_natural_four
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥)
    (hF : Nat.card F = 4) (f : alternatingGroup (Fin 5) ≃* SL(2,F))
    (n : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))) :
    ¬ elementaryAbelianMaxJ (T.subtype hH.1.1.2 : Subgroup H) ≤ centralizer
      (((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H) : Set H) := by
  let S := T.subtype hH.1.1.2
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  apply thompson_moves_of_noncentral_reduced_baumann_not_normal S
    (source_a5_hstar_minimal_parabolic D e hn hH) U
    (source_hstar_omega_orbit_reduced D hH)
    (source_hstar_omega_orbit_centralizer_proper D hH hZH)
  intro hB
  let := hB
  have hbmap : (baumann (S : Subgroup H)).map H.subtype = baumann (T : Subgroup G) := by
    have he := baumann_map_injective H.subtype H.subtype_injective (S : Subgroup H)
    change (baumann (S : Subgroup H)).map H.subtype =
      baumann ((S : Subgroup H).map H.subtype) at he
    exact he.trans (congrArg baumann (map_subgroupOf_eq_of_le hH.1.1.2))
  have hnB := (baumann (S : Subgroup H)).le_normalizer_map H.subtype
  rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype,hbmap] at hnB
  exact hH.1.2 (hnB.trans (source_natural_four_baumann_normalizer_le D e hn hF f n))

/-- Original 10.2.2(2), retaining the intrinsic H and original Sylow subgroup. -/
theorem source_hstar_residual_eq_thompson_commutator_of_natural_four
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥)
    (hF : Nat.card F = 4) (f : alternatingGroup (Fin 5) ≃* SL(2,F))
    (n : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))) :
    pResidual 2 H = ⁅pResidual 2 H,elementaryAbelianMaxJ (T.subtype hH.1.1.2 : Subgroup H)⁆ := by
  let S := T.subtype hH.1.1.2
  have hJ := source_hstar_thompson_moves_omega_orbit_of_natural_four D e hn hH hZH hF f n
  have hU := source_hstar_omega_orbit_reduced D hH
  apply minimalParabolic_residual_commutator_of_normalized_two_actor S
    (source_a5_hstar_minimal_parabolic D e hn hH) _ (sSup_le fun _ hA => hA.1)
    ((S : Subgroup H).le_normalizer.trans (normalizer_le_normalizer_elementaryAbelianMaxJ _))
  exact fun hc => hJ (hc.trans (le_centralizer_iff.mp hU.le_centralizer_pCore))
end CFSG.Quasithin.Chapter10

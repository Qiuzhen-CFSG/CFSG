module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceRankOneReciprocalEscape
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceRankOneSuzukiCentered
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.PushingUpOrdinary
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedNormalization
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels

/-!
# Ordinary components in the original rank-one pushing-up pair

The actual residual LH covers L modulo O₂(L), so the unchanged chosen orbit
has no LH-fixed points. It embeds in every ordinary component's central
quotient and retains rank at least twelve. The SQTK catalogue excludes the
unitary branch completely and places the Suzuki branch in its actual Ree
parabolic. The unitary reciprocal escape therefore selects a constrained
component with the literal C.2.7 star marking.

This is progress on residual uniqueness, not an assertion of uniqueness.
Source: Aschbacher--Smith C.3.5 and 4.2.12--13, pp.150,610--612.
-/
public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl
open Chapter4.Section02.RankOneReciprocalEscape Chapter7.NormalizedSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private theorem sourceOrbit_pushingUp_residual_data
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {A J H W : Subgroup G} (hw : Witness L D.sourceOrbit A J H W) :
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    (H ⊓ normalizer (L : Set G)) ≤ normalizer (F : Set G) ∧
      D.sourceOrbit ≤ F.pCoreIn 2 ∧
      D.sourceOrbit ⊓ centralizer (F : Set G) = ⊥ ∧
      Nonempty (((F ⧸ pCore 2 F) ⧸ center (F ⧸ pCore 2 F)) ≃*
        (D.orbitComponent ⧸ center D.orbitComponent)) := by
  rcases hw with ⟨_,_,_,_,_,_,hc,hcover,hn,hcomm,hUF,_,_⟩
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hFL : F ≤ L := (map_subtype_le _).trans inf_le_left
  have hnorm := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp hn
  let : IsElementaryAbelian 2 D.sourceOrbit := hV ▸ D.elementary
  have hcore : D.sourceOrbit ≤ F.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 D.sourceOrbit) hUF
    (le_normalizer_iff_commutator_le_left.mpr hcomm.symm.le)
  have hLC : L.pCoreIn 2 ≤ centralizer (D.sourceOrbit : Set G) := by
    rw [← hV]
    exact (pCoreIn_mono_of_normalizes (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le L.le_normalizer D.sylow_normalizes_component)).trans D.core_centralizes
  have hfixed : D.sourceOrbit ⊓ centralizer (L : Set G) = ⊥ := by
    rw [← hV]
    exact (D.sourceOrbit_fixed_and_thompson_of_many h hmany hnon).1
  have hfixF : D.sourceOrbit ⊓ centralizer (F : Set G) = ⊥ := by
    apply bot_unique
    intro x hx
    apply hfixed.le
    refine ⟨hx.1,?_⟩
    intro y hy
    obtain ⟨f,hf,c,hc,he⟩ := hcover.subset hy
    have hfx := hx.2 f hf
    have hcx := (le_centralizer_iff.mp hLC) hx.1 c hc
    rw [← he, mul_assoc, hcx, ← mul_assoc, hfx, mul_assoc]
  exact ⟨hnorm,hcore,hfixF,
    D.sourceOrbit_covering_central_quotient h.toHypothesis1221 hFL hcover.subset⟩

/-- Every ordinary component of the actual unitary pushing-up pair is impossible. -/
theorem sourceOrbit_unitary_pushingUp_no_ordinary
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hu : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2 ^ s))
    {A J H W : Subgroup G} (hw : Witness L D.sourceOrbit A J H W)
    (K : Subgroup H) (hK : IsComponent H K) : False := by
  obtain ⟨hn,hcore,hfix,⟨e⟩⟩ := D.sourceOrbit_pushingUp_residual_data h hmany hV hnon hw
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let := D.orbitComponent_quasisimple h.toHypothesis1221
  let : IsSimpleGroup (D.orbitComponent ⧸ center D.orbitComponent) := IsQuasisimple.simple
  let : Group.IsPerfect (D.orbitComponent ⧸ center D.orbitComponent) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  let π := e.toMonoidHom.comp ((QuotientGroup.mk' (center (F ⧸ pCore 2 F))).comp
    (QuotientGroup.mk' (pCore 2 F)))
  have hπ : Function.Surjective π := e.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  rcases hw with ⟨_,_,_,_,_,_,hc,_,_,hcomm,_,_⟩
  exact no_ordinary_unitary hc hn hcore (hV ▸ D.ne_bot) hcomm hfix
    (D.sourceOrbit_unitary_twoRank_ge_twelve hs hs2 hu)
    (Group.IsPerfect.not_isSolvable _) π hπ hs2 hu K hK

/-- The original Suzuki pair's ordinary component retains its actual Ree parabolic map. -/
theorem sourceOrbit_suzuki_pushingUp_ordinary_ree
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {a : ℕ} (ha : 1 ≤ a)
    (es : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup a)
    {A J H W : Subgroup G} (hw : Witness L D.sourceOrbit A J H W)
    (K : Subgroup H) (hK : IsComponent H K) :
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    ∃ hFK : F ≤ K.map H.subtype,
      ∃ m : ℕ, 1 ≤ m ∧ ∃ e : (K.map H.subtype ⧸ center (K.map H.subtype)) ≃* ReeF4.Model m,
        ∃ g : ReeF4.Model m,
          (residualQuotientMap hFK e).range.map (MulAut.conj g).toMonoidHom ≤
            ReeF4.ConverseParabolics.parabolic m .suzuki := by
  obtain ⟨hn,hcore,hfix,⟨e⟩⟩ := D.sourceOrbit_pushingUp_residual_data h hmany hV hnon hw
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let := D.orbitComponent_quasisimple h.toHypothesis1221
  let : IsSimpleGroup (D.orbitComponent ⧸ center D.orbitComponent) := IsQuasisimple.simple
  let : Group.IsPerfect (D.orbitComponent ⧸ center D.orbitComponent) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  let π := e.toMonoidHom.comp ((QuotientGroup.mk' (center (F ⧸ pCore 2 F))).comp
    (QuotientGroup.mk' (pCore 2 F)))
  have hπ : Function.Surjective π := e.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  rcases hw with ⟨_,_,_,_,_,_,hc,_,_,hcomm,_,_⟩
  exact ordinary_suzuki_ree_parabolic hc hn hcore (hV ▸ D.ne_bot) hcomm hfix
    (D.sourceOrbit_suzuki_twoRank_ge_twelve hs ha es)
    (Group.IsPerfect.not_isSolvable _) π hπ ha es K hK

/-- The full unitary reciprocal escape selects a constrained component with
its proved C.2.7 star marking. No residual uniqueness is assumed. -/
theorem sourceOrbit_unitary_pushingUp_constrained_of_not_unique
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hu : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2 ^ s))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    ∃ J H W : Subgroup G, Witness L D.sourceOrbit A J H W ∧
      ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
        ¬ K ≤ (normalizer (L : Set G)).subgroupOf H ∧
        generalizedFitting K = pCore 2 K ∧
        ChapterC.C27Source.StarModels.Model
          (Chapter1.RadicalExclusions.ModelReduction.starImage
            (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype)) := by
  obtain ⟨J,H,W,hw,hescape⟩ := D.sourceOrbit_unitary_reciprocal_escape
    h hmany hV hs hnm hnon hs2 hu A hne hA ho hnot
  have hc := hw.2.2.2.2.2.2.1
  have hescape' : ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H := by
    intro hf
    exact hescape (hf.trans (subgroupOf_mono H inf_le_right))
  obtain ⟨K,hK,hq,hout,_,hcases⟩ := hc.ordinary_or_constrained_escape hescape'
  rcases hcases with hordinary | hconstrained
  · exact (D.sourceOrbit_unitary_pushingUp_no_ordinary h hmany hV hs hnon
      hs2 hu hw K hordinary).elim
  refine ⟨J,H,W,hw,K,hK,hq,?_,hconstrained,?_⟩
  · intro hh
    exact hout (fun k hk => ⟨k.property,hh hk⟩)
  · exact ChapterC.C27Source.star_model_from_source
      (hc.constrained_source_input K hK hq hout hconstrained)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

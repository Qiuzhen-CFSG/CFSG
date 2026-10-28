module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.SourceDegrees
public import Theory.Representation.BinaryAlternatingFiveFixedPoint.Orbit

/-!
# The normalized A₅ seed and its orthogonal module

The source seed is a binary line fixed by the original M-intersection.
For a normalized component, the literal terminal quotient sends its Sylow
normalizer onto a point Borel of A₅. Borel containment therefore fixes the
same seed vector. Normality of the component and irreducibility of the
ambient terminal action give zero component fixed space, so the five-point
orbit construction embeds the augmentation core through that seed.

When the terminal degree is four this embedding is an equivalence on the
whole space. The original group marking, terminal action and source form
hypotheses are retained. This recognizes the component module; it does not
assert the ambient field-four recognition or the final Borel contradiction.
Source: Aschbacher–Smith 5.1.19, 14.3.6(1), and 14.3.14–15,
printed pp.643–644,991,993–994.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
section Source
variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
include hG hempty hM hu hmany hcard e hne

/-- The literal seed line is fixed pointwise by the original M-intersection. -/
theorem source_terminal_seed_fixed :
    ∃ w : Additive F.Uhat, w ≠ 0 ∧
      hatSpace F (rankTwoSeed T M) = Submodule.span (ZMod 2) {w} ∧
      ∀ a : F.H, (a : G) ∈ M →
        F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) w = w := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let d := Recognition.rankTwo_closure_geometry h F hne
  have hline : finrank (ZMod 2) (hatSpace F (rankTwoSeed T M)) = 1 := by
    have hh := finrank_hatSpace_plane F (by decide) d.seed_center
    exact (congrArg (fun A : Subgroup G => finrank (ZMod 2) (hatSpace F A)) F.last).symm.trans hh
  let U := hatSpace F (rankTwoSeed T M)
  have hU : 0 < finrank (ZMod 2) U := by
    change 0 < finrank (ZMod 2) (hatSpace F (rankTwoSeed T M))
    rw [hline]
    decide
  let : Nontrivial U := Module.nontrivial_of_finrank_pos hU
  obtain ⟨w,hw⟩ := exists_ne (0 : U)
  have hw0 : (w : Additive F.Uhat) ≠ 0 := fun he => hw (Subtype.ext he)
  have hspan : U = Submodule.span (ZMod 2) {(w : Additive F.Uhat)} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hline w.property hw0
  refine ⟨w,hw0,hspan,?_⟩
  intro a haM
  let c := QuotientGroup.mk' F.terminalHatAction.ker a
  have hstable : F.terminalRepresentation c (w : Additive F.Uhat) ∈ U := by
    change (F.terminalRepresentation c (w : Additive F.Uhat)).toMul ∈ hatImage F (rankTwoSeed T M)
    obtain ⟨u,hu,he⟩ := w.property
    rw [F.terminalRepresentation_apply_mk,←he,F.terminalHatAction_apply_mk]
    refine ⟨_,?_,rfl⟩
    exact (mem_normalizer_iff.mp (RankTwoHypothesis.M_normalizes_seed haM) (u:G)).mp hu
  have hnz : F.terminalRepresentation c (w : Additive F.Uhat) ≠ 0 := by
    intro he
    apply hw0
    have hh := congrArg (F.terminalRepresentation c⁻¹) he
    simpa only [← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one,
      Module.End.one_apply,map_zero] using hh
  obtain ⟨b,hb⟩ := Submodule.mem_span_singleton.mp (hspan.le hstable)
  have hb0 : b ≠ 0 := by intro hh; exact hnz (by simpa [hh] using hb.symm)
  have hb1 : b = 1 := (by decide : ∀ b : ZMod 2, b ≠ 0 → b = 1) b hb0
  simpa only [hb1,one_smul,c] using hb.symm

variable (hnot : ¬ ClassificationModels.IsTheoremEModel G) (g : G)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    {K : Subgroup G} (hK : ComponentLift F g K)
include hnot hgP hgH hyp hK

/-- The original normalized A₅ contains an orthogonal four-dimensional module
through the actual seed line. The original A₅ marking is unchanged. -/
theorem source_single_a5_seed_core_embedding
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G)) :
    let σ := (F.terminalRepresentation.comp (F.terminalDot K).subtype).comp e5.symm.toMonoidHom
    ∃ f : IntertwiningMap (BinaryPermutation.alternatingCoreRepresentation (Fin 5)) σ,
      Function.Injective f ∧ hatSpace F (rankTwoSeed T M) ≤ LinearMap.range f.toLinearMap := by
  let L := F.terminalDot K
  let σ : Representation (ZMod 2) (alternatingGroup (Fin 5)) (Additive F.Uhat) :=
    (F.terminalRepresentation.comp L.subtype).comp e5.symm.toMonoidHom
  have hnK : (K.subgroupOf F.H).Normal := by
    have hh := hK.normal_span
    rwa [← hspan] at hh
  let : L.Normal := Normal.map hnK _ (QuotientGroup.mk'_surjective _)
  let : IsIrreducible F.terminalRepresentation := hyp.irreducible_of_not_solvable hK.terminal_not_solvable
  have hz : Representation.invariants (F.terminalRepresentation.comp L.subtype) = ⊥ := by
    by_contra hz
    have hker := F.terminalRepresentation.le_ker_of_normal_invariants_ne_bot L hz
    rw [(MonoidHom.ker_eq_bot_iff _).mpr hyp.faithful] at hker
    exact hK.image_moved (by rw [show F.terminalDot K = ⊥ from bot_unique hker,commutator_bot_left])
  have hfixed : σ.invariants = ⊥ := by
    apply bot_unique
    intro w hw
    apply hz.le
    intro l
    simpa only [σ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e5.symm_apply_apply] using hw (e5 l)
  obtain ⟨w,hw,hline,hfix⟩ := source_terminal_seed_fixed hG T hempty hM hu hmany hcard e F hne
  obtain ⟨⟨eK⟩,_,_,_,_,_,hb⟩ := source_terminal_single_a5_parabolic
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hyp hK e5 hspan
  have hnorm : (T : Subgroup G) ≤ normalizer (K : Set G) := by
    rw [hspan]
    exact le_normalizer_conjugateSpanBy K (T : Subgroup G)
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T K hnorm
  let a := (subgroupOfEquivOfLe hK.le_pointNormalizer).symm
  let j : (K.subgroupOf F.H) →* F.terminalDot K :=
    (QuotientGroup.mk' F.terminalHatAction.ker).subgroupMap (K.subgroupOf F.H)
  let q : K →* alternatingGroup (Fin 5) := e5.toMonoidHom.comp (j.comp a.toMonoidHom)
  have hq : Function.Surjective q := e5.surjective.comp
    (((QuotientGroup.mk' F.terminalHatAction.ker).subgroupMap_surjective (K.subgroupOf F.H)).comp a.surjective)
  let S := P.mapSurjective hq
  obtain ⟨i,hi⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer S
  have hpoint (b : alternatingGroup (Fin 5)) (hbi : b.val i = i) : σ b w = w := by
    have hbN : b ∈ (normalizer (P : Set K)).map q := by
      rw [P.normalizer_map_surjective q hq]
      change b ∈ normalizer (S : Set (alternatingGroup (Fin 5)))
      rw [hi]
      exact hbi
    obtain ⟨k,hk,rfl⟩ := hbN
    have hkM : (k : G) ∈ M := hb (mem_map_of_mem K.subtype (hP ▸ hk))
    change F.terminalRepresentation (e5.symm (e5 (j (a k)))) w = w
    exact (congrArg (fun l : F.terminalDot K => F.terminalRepresentation l w)
      (e5.symm_apply_apply (j (a k)))).trans
        (hfix ⟨k,hK.le_pointNormalizer k.property⟩ hkM)
  obtain ⟨f,hf,hwf⟩ := BinaryAlternatingFiveFixedPoint.core_embedding_of_point_fixed σ w hw hfixed i hpoint
  exact ⟨f,hf,hline ▸ (Submodule.span_singleton_le_iff_mem _ _).mpr hwf⟩

/-- In degree four, the actual normalized component acts as the orthogonal
five-point augmentation module on all of U-hat. -/
theorem source_single_a5_equiv_core_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) :
    Nonempty (Representation.Equiv
      ((F.terminalRepresentation.comp (F.terminalDot K).subtype).comp e5.symm.toMonoidHom)
      (BinaryPermutation.alternatingCoreRepresentation (Fin 5))) := by
  obtain ⟨f,hf,_⟩ := source_single_a5_seed_core_embedding
    hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan
  have hdim : finrank (ZMod 2) (BinaryPermutation.core (Fin 5)) =
      finrank (ZMod 2) (Additive F.Uhat) := by
    rw [BinaryPermutation.finrank_core,hd]
    decide
  exact ⟨(f.ofBijective ⟨hf,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hf⟩).symm⟩

end Source
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable

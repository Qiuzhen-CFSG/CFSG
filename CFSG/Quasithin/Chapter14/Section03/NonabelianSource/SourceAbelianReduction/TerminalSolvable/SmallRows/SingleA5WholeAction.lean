module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.SingleA5BorelModule
public import Theory.Representation.OrthogonalFourMinusRankOne.FivePoint.Ambient
public import Theory.Representation.BinaryPermutation.FiveSylowSingular

/-!
# The full five-point action of the normalized terminal A₅

In terminal degree four the Borel-fixed seed identifies the component module
with the binary five-point augmentation core. Normality of the same dotted
component then extends this marking to a faithful five-point action of the
whole terminal group. Its image is A₅ or S₅, with actual group equivalences.

The original seed is fixed by the intersection of the Sylow subgroup with K.
The literal terminal quotient maps that intersection onto an A₅ Sylow
subgroup, so its image in the core is singular. The same coordinates retain
pointwise fixation by the original M-intersection.

This supplies whole-action and marked-point data for the field-four local
recognition. It does not assert the ambient recognition in 14.2.7 or the
Borel contradiction of 14.3.6(1). Source: Aschbacher–Smith 5.1.19,
14.3.6(1), 14.3.14–15 and K.3.1.2, printed pp.643–644,991,993–994,454.
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

variable (hnot : ¬ ClassificationModels.IsTheoremEModel G) (g : G)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    {K : Subgroup G} (hK : ComponentLift F g K)
include hnot hgP hgH hyp hK


include hG hempty hM hu hmany hcard e hne

/-- The whole terminal group has a faithful five-point action extending the
original normalized component marking, in the same four-dimensional coordinates. -/
theorem source_single_a5_whole_action_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) :
    ∃ (c : Additive F.Uhat ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 5))
      (p : F.TerminalHdot →* Equiv.Perm (Fin 5)),
      Function.Injective p ∧
      (∀ l : F.terminalDot K, p l = (e5 l).val) ∧
      (∀ a w, c (F.terminalRepresentation a w) =
        BinaryPermutation.coreRepresentation (Fin 5) (p a) (c w)) := by
  obtain ⟨r⟩ := source_single_a5_equiv_core_of_four hG T hempty hM hu hmany hcard e
    F hne hnot g hgP hgH hyp hK e5 hspan hd
  let c := r.toLinearEquiv
  let n := BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
  have hc (l : F.terminalDot K) (w : Additive F.Uhat) :
      c (F.terminalRepresentation l w) =
        BinaryPermutation.coreRepresentation (Fin 5) (e5 l).val (c w) := by
    have hh := IntertwiningMap.isIntertwining _ _ r.toIntertwiningMap (e5 l) w
    simpa only [c, Representation.Equiv.toLinearEquiv_apply,
      MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e5.symm_apply_apply,
      Subgroup.subtype_apply] using hh
  have hL : (F.terminalDot K).Normal := by
    have hnK : (K.subgroupOf F.H).Normal := by
      have hh := hK.normal_span
      rwa [←hspan] at hh
    exact Normal.map hnK _ (QuotientGroup.mk'_surjective _)
  let := hL
  obtain ⟨p,hp,he,hm⟩ := Representation.OrthogonalFourMinus.FivePoint.exists_ambient_permutation
    F.terminalRepresentation (F.terminalDot K) e5 (c.trans n)
    (fun l w => by
      change n (c (F.terminalRepresentation l w)) = _
      rw [hc]
      exact BinaryPermutation.coreEquivNatural_equivariant (Fin 5) (by decide) (e5 l).val (c w))
    hyp.faithful
  refine ⟨c,p,hp,hm,?_⟩
  intro a w
  apply n.injective
  exact (he a w).trans
    (BinaryPermutation.coreEquivNatural_equivariant (Fin 5) (by decide) (p a) (c w)).symm

/-- Both possible full dotted groups are identified by actual equivalences.
The S₅ alternative is retained until its ambient source exclusion is proved. -/
theorem source_single_a5_whole_group_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) :
    Nonempty (F.TerminalHdot ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (F.TerminalHdot ≃* Equiv.Perm (Fin 5)) := by
  obtain ⟨c,p,hp,hm,_⟩ := source_single_a5_whole_action_of_four
    hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  by_cases ht : F.terminalDot K = ⊤
  · exact Or.inl ⟨((MulEquiv.subgroupCongr ht).trans topEquiv).symm.trans e5⟩
  · have hmap : (F.terminalDot K).map p = alternatingGroup (Fin 5) := by
      ext a
      constructor
      · rintro ⟨l,hl,rfl⟩
        exact hm ⟨l,hl⟩ ▸ (e5 ⟨l,hl⟩).property
      · intro ha
        obtain ⟨l,hl⟩ := e5.surjective ⟨a,ha⟩
        exact ⟨l,l.property,(hm l).trans (congrArg Subtype.val hl)⟩
    exact Or.inr ⟨MulEquiv.ofBijective p ⟨hp,
      Representation.OrthogonalFourMinus.FivePoint.surjective_of_marked_alternating
        (F.terminalDot K) p hp hmap ht⟩⟩


/-- The same whole-action coordinates send the original seed to a nonzero
singular vector. This retains the point needed for the field-four local recognition. -/
theorem source_single_a5_whole_action_seed_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) :
    ∃ (c : Additive F.Uhat ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 5))
      (p : F.TerminalHdot →* Equiv.Perm (Fin 5)) (w : Additive F.Uhat),
      Function.Injective p ∧
      (∀ l : F.terminalDot K, p l = (e5 l).val) ∧
      (∀ a x, c (F.terminalRepresentation a x) =
        BinaryPermutation.coreRepresentation (Fin 5) (p a) (c x)) ∧
      w ≠ 0 ∧ hatSpace F (rankTwoSeed T M) = Submodule.span (ZMod 2) {w} ∧
      BinaryPermutation.FiveGeometry.form (c w) = 0 ∧
      ∀ a : F.H, (a : G) ∈ M →
        BinaryPermutation.coreRepresentation (Fin 5)
          (p (QuotientGroup.mk' F.terminalHatAction.ker a)) (c w) = c w := by
  obtain ⟨c,p,hp,hm,he⟩ := source_single_a5_whole_action_of_four
    hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  obtain ⟨w,hw,hline,hfix⟩ := source_terminal_seed_fixed hG T hempty hM hu hmany hcard e F hne
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
  refine ⟨c,p,w,hp,hm,he,hw,hline,?_,?_⟩
  · apply BinaryPermutation.FiveSylowSingular.fixed_singular S
    intro b hb
    obtain ⟨k,hk,rfl⟩ := hb
    have hkT : (k : G) ∈ (T : Subgroup G) := by
      change k ∈ (T : Subgroup G).subgroupOf K
      rwa [← hP]
    have hkw : F.terminalRepresentation (j (a k)) w = w :=
      hfix ⟨k,hK.le_pointNormalizer k.property⟩ (hM.1.2 hkT)
    have hh := he (j (a k)) w
    rw [hm,hkw] at hh
    exact hh.symm
  · intro a ha
    exact (he (QuotientGroup.mk' F.terminalHatAction.ker a) w).symm.trans
      (congrArg c (hfix a ha))

end Source
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable

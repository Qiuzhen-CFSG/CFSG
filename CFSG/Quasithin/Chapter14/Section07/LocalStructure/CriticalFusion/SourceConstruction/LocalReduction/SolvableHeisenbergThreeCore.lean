module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SolvableHeisenbergComparison
public import Theory.GroupTheory.HeisenbergIrreducibleCore

/-!
# The full three-core and the remaining SL₂(3) extension

The actual local residual belongs to Ξ(G,T). Restrict it to the full point
normalizer and transport its two-core/Frattini action along the literal
quotient map. Its image is irreducible under the full quotient action,
and hence is exactly the full three-core.

Apply this to the proper local supplied by original solvability. The
full-residual exclusion rules out equality; a cubic quotient would make
the full two-residual a three-group, contradicting the identified core.
Thus the remaining quotient is literally SL₂(3). The extension is retained
without an assumed splitting or a rank-three conclusion.

Source: Aschbacher–Smith 14.7.15(2–3), 14.7.27–29, printed
pp.1047,1054–1055, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private def imageFrattiniEquiv {D : Type*} [Group D]
    (N : Subgroup D) [N.Normal] :
    XiFrattiniQuotient N ≃*
      ((N.map (QuotientGroup.mk' (pCore 2 D))) ⧸
        frattini (N.map (QuotientGroup.mk' (pCore 2 D)))) :=
  QuotientGroup.congr _ _ (coreQuotientEquivImage 2 N) (frattini_map_mulEquiv _)

private theorem imageFrattiniEquiv_mk {D : Type*} [Group D]
    (N : Subgroup D) [N.Normal] (x : N) :
    imageFrattiniEquiv N (QuotientGroup.mk' _ (QuotientGroup.mk' _ x)) =
      QuotientGroup.mk' _ (coreQuotientEquivImage 2 N (QuotientGroup.mk' _ x)) := rfl

private theorem imageFrattiniEquiv_action {D : Type*} [Group D]
    (N S : Subgroup D) [N.Normal] (hn : S ≤ normalizer (N : Set D))
    (s : S) (x : XiFrattiniQuotient N) :
    imageFrattiniEquiv N (xiFrattiniAction S N hn s x) =
      quotientAut (frattini (N.map (QuotientGroup.mk' (pCore 2 D))))
        (MulAut.conjNormal (QuotientGroup.mk' (pCore 2 D) (s : D)))
        (imageFrattiniEquiv N x) := by
  induction x using QuotientGroup.induction_on with | H x =>
    induction x using QuotientGroup.induction_on with | H x =>
      change imageFrattiniEquiv N (xiFrattiniAction S N hn s
        (QuotientGroup.mk' _ (QuotientGroup.mk' _ x))) =
          quotientAut (frattini (N.map (QuotientGroup.mk' (pCore 2 D))))
            (MulAut.conjNormal (QuotientGroup.mk' (pCore 2 D) (s : D)))
            (imageFrattiniEquiv N (QuotientGroup.mk' _ (QuotientGroup.mk' _ x)))
      simp only [xiFrattiniAction,MonoidHom.comp_apply,quotientAut_apply_mk,
        imageFrattiniEquiv_mk]
      apply congrArg (QuotientGroup.mk' _)
      apply Subtype.ext
      simp only [coreQuotientEquivImage_apply_mk]
      change QuotientGroup.mk' (pCore 2 D) _ =
        QuotientGroup.mk' (pCore 2 D) (s : D) *
          (coreQuotientEquivImage 2 N _) *
          (QuotientGroup.mk' (pCore 2 D) (s : D))⁻¹
      rw [coreQuotientEquivImage_apply_mk,←map_inv,←map_mul,←map_mul]
      rfl

private theorem xi_image_frattini_irreducible {D : Type*} [Group D]
    (N S : Subgroup D) [N.Normal] (hXi : N ∈ Xi D S)
    (J : Subgroup ((N.map (QuotientGroup.mk' (pCore 2 D))) ⧸
        frattini (N.map (QuotientGroup.mk' (pCore 2 D)))))
    (hJ : ∀ a : D ⧸ pCore 2 D, ∀ x ∈ J,
      quotientAut (frattini (N.map (QuotientGroup.mk' (pCore 2 D))))
        (MulAut.conjNormal a) x ∈ J) : J = ⊥ ∨ J = ⊤ := by
  let e := imageFrattiniEquiv N
  have hinv : ∀ s : S, ∀ x ∈ J.comap e.toMonoidHom,
      xiFrattiniAction S N hXi.invariant s x ∈ J.comap e.toMonoidHom := by
    intro s x hx
    change e (xiFrattiniAction S N hXi.invariant s x) ∈ J
    rw [imageFrattiniEquiv_action]
    exact hJ _ _ hx
  rcases hXi.irreducible _ hinv with he | he
  · left
    have hh := congrArg (map e.toMonoidHom) he
    simpa only [map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective,Subgroup.map_bot] using hh
  · right
    have hh := congrArg (map e.toMonoidHom) he
    simpa only [map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective,
      map_top_of_surjective e.toMonoidHom e.surjective] using hh


/-- The proper local Heisenberg image is the full three-core of the original
point quotient, using the actual transported Ξ action. -/
theorem local_solvable_full_three_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hs : Group.IsSolvable F.H)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    (he : Nonempty (pResidual 2 (HStar I) ≃* HeisenbergPrime 3)) :
    pCore 3 (HStar F.H) = star F ((pResidual 2 I).map I.subtype) := by
  let R₀ := (pResidual 2 I).map I.subtype
  let A := R₀.subgroupOf F.H
  let R := star F R₀
  have hIH : I ≤ F.H := hI.2.1
  let := hs
  have hIs : Group.IsSolvable I := Group.isSolvable_of_isSolvable_injective (inclusion_injective hIH)
  have hpoint : F.Vi 1 ≠ ⊥ := by
    intro he
    have hc := F.card 1 (by decide)
    rw [he,card_bot] at hc
    norm_num at hc
  have hH : IsTwoLocal F.H := ⟨F.Vi 1,hpoint,
    IsPGroup.of_card (p := 2) (n := 1) (F.card 1 (by decide)),rfl⟩
  let : A.Normal := local_solvable_heisenberg_normal_in_twoLocal h hab structural previous faithful
    I hI hIs hn he F.H hH hIH
  have hX := local_solvable_heisenberg_residual_mem_Xi h hab structural previous faithful I hI hIs hn he
  have hXi : A ∈ Xi F.H ((T : Subgroup G).subgroupOf F.H) :=
    (mem_XiIn_iff_subgroupOf ((F.sylow_le_of_mem_Hz hI).trans hIH)
      ((map_subtype_le _).trans hIH)).mp ⟨(map_subtype_le _).trans hIH,hX⟩
  obtain ⟨hRn,heR,_,_,hZ,hC⟩ := local_solvable_heisenberg_full_star_centralizer
    h hab structural previous faithful hs I hI hn he
  let : R.Normal := hRn
  have hc : centralizer (R : Set (HStar F.H)) ≤ R := by
    rw [hC,hZ]
    exact map_subtype_le _
  apply heisenberg_pCore_eq_of_irreducible R heR.some hc
  exact xi_image_frattini_irreducible A ((T : Subgroup G).subgroupOf F.H) hXi

/-- Under original solvability the only surviving residual comparison is a
proper Heisenberg three-core with literal SL₂(3) quotient. This does not assert
that the extension splits. -/
theorem original_solvable_full_residual_sl23
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (hs : Group.IsSolvable F.H) :
    ∃ I : Subgroup G, I < F.H ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      let R := star F ((pResidual 2 I).map I.subtype)
      ∃ hRn : R.Normal, letI := hRn
        Nonempty (R ≃* HeisenbergPrime 3) ∧
        pCore 3 (HStar F.H) = R ∧ R < pResidual 2 (HStar F.H) ∧
        star F (F.Li L 1) = (center R).map R.subtype ∧
        centralizer (R : Set (HStar F.H)) = star F (F.Li L 1) ∧
        Nonempty (((pResidual 2 (HStar F.H)) ⧸
          R.subgroupOf (pResidual 2 (HStar F.H))) ≃*
            Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) := by
  obtain ⟨I,hIH,hI,_,_,hn,he,_⟩ := original_solvable_proper_heisenberg_normal
    d h hab structural previous faithful earlier hs
  obtain ⟨hRn,heR,_,hRres,hZ,hC⟩ := local_solvable_heisenberg_full_star_centralizer
    h hab structural previous faithful hs I hI hn he
  let R := star F ((pResidual 2 I).map I.subtype)
  let : R.Normal := hRn
  change Nonempty (R ≃* HeisenbergPrime 3) at heR
  have hcore := local_solvable_full_three_core h hab structural previous faithful hs I hI hn he
  have hc : centralizer (R : Set (HStar F.H)) ≤ R := by
    rw [hC,hZ]
    exact map_subtype_le _
  have hne : R ≠ pResidual 2 (HStar F.H) := by
    intro heq
    apply extraspecial_star_residual_impossible d h hab structural previous faithful earlier
    exact ⟨(MulEquiv.subgroupCongr heq).symm.trans heR.some⟩
  exact ⟨I,hIH,hI,hRn,heR,hcore,lt_of_le_of_ne hRres hne,hZ,hC,
    heisenberg_twoResidual_sl23_of_pCore_eq R heR.some hc hcore hRres hne⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction

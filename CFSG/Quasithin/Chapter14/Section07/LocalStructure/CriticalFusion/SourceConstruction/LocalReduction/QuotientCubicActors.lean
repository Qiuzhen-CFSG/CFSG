module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.QuotientPlaneLifting


/-!
# Cubic actors without a Sylow-normalization premise

The actor Y in 14.7.2 is two-perfect, lies in the original point normalizer,
and has an S₃ quotient after adjoining the original Sylow T. The printed
statement does not require T to normalize Y. Put J = ⟨Y,T⟩ and replace Y
by the embedded two-residual R = O²(J). Residual functoriality gives Y ≤ R;
characteristicity gives T-normalization; and the Sylow supplement gives
RT = J. Thus the proved normalized-actor endgame applies to R with precisely
the same Sylow overgroup and quotient.

Containment in N_G(L), plane centralization and the plane-orbit bound descend
to the original Y. Seed separation then proves the rank-one-or-two and fixed
plane conclusions on the literal proper invariant quotient of U/V₁. The final
consumer constructs its canonical projection. The earlier universal structural,
module and faithful-classification inputs are retained as in the endgame.

This removes the extra normalization premise in clauses 14.7.2(2),(3).
It does not establish fixation by the full S₈ quotient stabilizer's cubic
closure, whose S₃-over-Sylow hypothesis is unavailable.

Source: Aschbacher–Smith, refs/quasithin.pdf, 14.7.2, printed p.1043
(PDF p.1060), and the normalized-actor reduction 14.5.3, printed p.1013.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem source_actor_residual_enlargement
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y) :
    ∃ R : Subgroup G, Y ≤ R ∧ R ≤ F.H ∧ IsPPerfect 2 R ∧
      (T : Subgroup G) ≤ normalizer (R : Set G) ∧
      R ⊔ (T : Subgroup G) = Y ⊔ (T : Subgroup G) := by
  let J := Y ⊔ (T : Subgroup G)
  let R := (pResidual 2 J).map J.subtype
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right
  have hYR : Y ≤ R := by
    have hh := embedded_pResidual_mono 2 (show Y ≤ J from le_sup_left)
    simpa only [(pResidual_eq_top_iff 2 Y).mpr hYp,
      ← MonoidHom.range_eq_map, range_subtype] using hh
  have hjoin := congrArg (map J.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTJ))
  rw [Subgroup.map_sup, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTJ,
    ← MonoidHom.range_eq_map, range_subtype] at hjoin
  refine ⟨R, hYR, (map_subtype_le _).trans (sup_le hYH (F.invariant 1)),
    isPPerfect_embedded_pResidual 2 J, ?_, hjoin⟩
  exact (hTJ.trans J.le_normalizer).trans
    (normalizer_le_normalizer_characteristic_image J (pResidual 2 J))

/-- The source cubic actor need not be normalized by T: its canonical residual
enlargement has the same Sylow join and supplies the contained-or-fixed alternative. -/
theorem original_cubic_actor_contained_or_plane_fixed_of_join
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    Y ≤ normalizer (L : Set G) ∨ ⁅F.Vi 2,Y⁆ = ⊥ := by
  obtain ⟨R,hYR,hRH,hRp,hTR,hjoin⟩ := source_actor_residual_enlargement Y hYH hYp
  have heR : Nonempty (((R ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (R ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) := by
    exact hjoin.symm ▸ he
  rcases original_cubic_actor_contained_or_plane_fixed h hab structural previous faithful
    R hRH hRp hTR heR with hRM | hfix
  · exact Or.inl (hYR.trans hRM)
  · exact Or.inr (eq_bot_iff.mpr ((commutator_mono le_rfl hYR).trans hfix.le))

/-- The original plane orbit stays in the seed without an actor-normalization premise. -/
theorem original_cubic_plane_span_le_seed_of_join
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    conjugateSpanBy (F.Vi 2) Y ≤ V := by
  obtain ⟨R,hYR,hRH,hRp,hTR,hjoin⟩ := source_actor_residual_enlargement Y hYH hYp
  have heR : Nonempty (((R ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (R ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) := by
    exact hjoin.symm ▸ he
  exact (conjugateSpanBy_mono le_rfl hYR).trans
    (original_cubic_plane_span_le_seed h hab structural previous faithful R hRH hRp hTR heR)

/-- Source 14.7.2(3) for a two-perfect actor with the original S₃-over-Sylow
quotient, without assuming that T normalizes the actor. -/
theorem original_quotient_plane_fixed_of_join
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    {W X : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup X] [Module (ZMod 2) X]
    {ρ : Representation (ZMod 2) F.H W} {σ : Representation (ZMod 2) F.H X}
    (c : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (p : ρ.IntertwiningMap σ) (hp : p.toLinearMap.ker ≠ ⊤)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (hfix : ∀ y (hy : y ∈ Y) (v : F.U), (v : G) ∈ F.Vi 2 →
      σ ⟨y,hYH hy⟩ (p (c.coordinates v).toAdd) = p (c.coordinates v).toAdd) :
    ⁅F.Vi 2,Y⁆ = ⊥ := by
  rcases original_cubic_actor_contained_or_plane_fixed_of_join
    h hab structural previous faithful Y hYH hYp he with hYM | hc
  · have hne : F.Vi 1 ≠ ⊥ := by
      intro hz
      have hh := F.card 1 (by decide)
      simp [hz] at hh
    have hs : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T :=
      structural G T
    have hn := hs.intersection_normalizer h.source h.chosen
      hne (F.le_seed 1) (le_rfl : F.H ≤ normalizer (F.Vi 1 : Set G))
    have hYV : Y ≤ normalizer (V : Set G) := by
      have hh := le_inf hYH hYM
      rw [hn] at hh
      exact hh.trans inf_le_right
    exact quotient_plane_fixed_of_seed_normalized h c p hp Y hYH hYp hYV hfix
  · exact hc

/-- Source 14.7.2(2): the literal cubic orbit image has dimension one or two
in every proper invariant quotient of the original section. -/
theorem original_quotient_cubic_plane_span_dimension_of_join
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    {W X : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup X] [Module (ZMod 2) X]
    {ρ : Representation (ZMod 2) F.H W} {σ : Representation (ZMod 2) F.H X}
    (c : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (p : ρ.IntertwiningMap σ) (hp : p.toLinearMap.ker ≠ ⊤)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let E := (c.imageSpace (conjugateSpanBy (F.Vi 2) Y)).map p.toLinearMap
    Module.finrank (ZMod 2) E = 1 ∨ Module.finrank (ZMod 2) E = 2 := by
  let : Finite W := Finite.of_surjective (fun v : F.U => (c.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  let E := (c.imageSpace (conjugateSpanBy (F.Vi 2) Y)).map p.toLinearMap
  have hindex : (F.Vi 1).relIndex V = 4 := by
    have hh := relIndex_mul_card_of_le (F.le_seed 1)
    have hcard : Nat.card V = 8 := by
      simpa only [F.last,Nat.reducePow] using F.card 3 (by decide)
    rw [F.card 1 (by decide),hcard] at hh
    norm_num at hh ⊢
    omega
  have hdim : Module.finrank (ZMod 2) (c.imageSpace V) = 2 :=
    c.imageSpace_finrank_of_index V (le_conjugateSpanBy V F.H) 2 hindex
  have hupper : Module.finrank (ZMod 2) E ≤ 2 :=
    (Submodule.finrank_map_le p.toLinearMap _).trans
      ((Submodule.finrank_mono (c.imageSpace_mono
        (original_cubic_plane_span_le_seed_of_join h hab structural previous faithful
          Y hYH hYp he))).trans_eq hdim)
  have hnot : ¬ F.Vi 2 ≤ F.Vi 1 := by
    intro hle
    have hh := card_le_of_le hle
    rw [F.card 2 (by decide),F.card 1 (by decide)] at hh
    norm_num at hh
  obtain ⟨v,hv,hvZ⟩ := SetLike.not_le_iff_exists.mp hnot
  let vU : F.U := ⟨v,(le_conjugateSpanBy V F.H) (F.le_seed 2 hv)⟩
  have hsep := seed_intersection h c p.toLinearMap.ker (by
    intro g w hw
    change p (ρ g w) = 0
    rw [p.isIntertwining,show p w = 0 from hw,map_zero]) hp
  have hv0 : p (c.coordinates vU).toAdd ≠ 0 := by
    intro hz
    exact hvZ ((hsep vU (F.le_seed 2 hv)).mp hz)
  have hvE : p (c.coordinates vU).toAdd ∈ E :=
    ⟨_,(c.mem_imageSpace_iff _ _).mpr
      ⟨vU,le_conjugateSpanBy _ _ hv,rfl⟩,rfl⟩
  have hpos : 0 < Module.finrank (ZMod 2) E :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨_,hvE⟩,
      fun hz => hv0 (congrArg Subtype.val hz)⟩
  change Module.finrank (ZMod 2) E = 1 ∨ Module.finrank (ZMod 2) E = 2
  omega


/-- The literal proper invariant quotient satisfies both clauses 14.7.2(2),(3)
for the original actor, with no T-normalization or alternative quotient assumed. -/
theorem original_invariant_quotient_cubic_conclusions_of_join
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (c : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (I : Subrepresentation ρ) (hI : I.toSubmodule ≠ ⊤)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    (let E := (c.imageSpace (conjugateSpanBy (F.Vi 2) Y)).map I.toSubmodule.mkQ
     Module.finrank (ZMod 2) E = 1 ∨ Module.finrank (ZMod 2) E = 2) ∧
    ((∀ y (hy : y ∈ Y) (v : F.U), (v : G) ∈ F.Vi 2 →
      I.quotientRepresentation ⟨y,hYH hy⟩ (I.toSubmodule.mkQ (c.coordinates v).toAdd) =
        I.toSubmodule.mkQ (c.coordinates v).toAdd) → ⁅F.Vi 2,Y⁆ = ⊥) := by
  let p : ρ.IntertwiningMap I.quotientRepresentation := {
    toLinearMap := I.toSubmodule.mkQ
    isIntertwining' := fun _ => rfl }
  have hp : p.toLinearMap.ker ≠ ⊤ := by
    change I.toSubmodule.mkQ.ker ≠ ⊤
    rwa [Submodule.ker_mkQ]
  exact ⟨original_quotient_cubic_plane_span_dimension_of_join
      h hab structural previous faithful c p hp Y hYH hYp he,
    fun hfix => original_quotient_plane_fixed_of_join
      h hab structural previous faithful c p hp Y hYH hYp he hfix⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction

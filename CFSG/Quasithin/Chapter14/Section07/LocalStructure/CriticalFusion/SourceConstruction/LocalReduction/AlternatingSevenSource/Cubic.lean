module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.Seed
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded.CubicMovingEndgame
public import Theory.Representation.BinaryConjugationSection.ImageDimensions

/-!
# The original cubic theorem on a proper quotient of each local span

The moving-plane endgame is used only at the original G,T. Enlarging a
two-perfect actor Y to O²(⟨Y,T⟩) removes any unprinted T-normalization
assumption. Seed separation at the selected local I then lifts fixation
in its proper quotient to centralization of the original flag plane.
The same argument bounds the cubic plane orbit by rank two.

These are the literal 14.7.2(2–3) inputs needed in 14.7.50. Neither a
splitting of O₂(I) nor a quotient-centralizer lift is assumed.
Source: Aschbacher–Smith, pp.1043 and 1064–1065, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u v w
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
theorem cubic_actor_contained_or_plane_fixed_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    Y ≤ normalizer (L : Set G) ∨ ⁅F.Vi 2,Y⁆ = ⊥ := by
  obtain ⟨R,hYR,hRH,hRp,hTR,hjoin⟩ := source_actor_residual_enlargement Y hYH hYp
  have heR : Nonempty (((R ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (R ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) := by
    exact hjoin.symm ▸ he
  rcases InnerLinearExclusion.Guarded.original_cubic_actor_contained_or_plane_fixed h hab structural previous faithful
    R hRH hRp hTR heR with hRM | hfix
  · exact Or.inl (hYR.trans hRM)
  · exact Or.inr (eq_bot_iff.mpr ((commutator_mono le_rfl hYR).trans hfix.le))

/-- The cubic orbit of the original flag plane stays in the seed. -/
theorem cubic_plane_span_le_seed_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    conjugateSpanBy (F.Vi 2) Y ≤ V := by
  rcases cubic_actor_contained_or_plane_fixed_at h hab structural previous faithful
    Y hYH hYp he with hYL | hc
  · have hne : F.Vi 1 ≠ ⊥ := by
      intro hz
      have hh := F.card 1 (by decide)
      simp [hz] at hh
    have hn := structural.intersection_normalizer h.source h.chosen
      hne (F.le_seed 1) (le_rfl : F.H ≤ normalizer (F.Vi 1 : Set G))
    have hYV : Y ≤ normalizer (V : Set G) := by
      have hh := le_inf hYH hYL
      rw [hn] at hh
      exact hh.trans inf_le_right
    exact conjugateSpanBy_le (F.le_seed 2) hYV
  · have hYC : Y ≤ centralizer (F.Vi 2 : Set G) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)
    exact (conjugateSpanBy_le le_rfl
      (hYC.trans (Subgroup.centralizer_le_normalizer _))).trans (F.le_seed 2)

/-- Source 14.7.2(3) for a two-perfect actor with the original S₃-over-Sylow
quotient, without assuming that T normalizes the actor. -/
theorem local_quotient_plane_fixed_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    {W : Type v} {X : Type w} [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup X] [Module (ZMod 2) X]
    {ρ : Representation (ZMod 2) I W} {σ : Representation (ZMod 2) I X}
    (c : BinaryConjugationSection I (F.UH I) (F.Vi 1) ρ)
    (p : ρ.IntertwiningMap σ) (hp : p.toLinearMap.ker ≠ ⊤)
    (Y : Subgroup G) (hYI : Y ≤ I) (hYp : IsPPerfect 2 Y)
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (hfix : ∀ y (hy : y ∈ Y) (v : F.UH I), (v : G) ∈ F.Vi 2 →
      σ ⟨y,hYI hy⟩ (p (c.coordinates v).toAdd) = p (c.coordinates v).toAdd) :
    ⁅F.Vi 2,Y⁆ = ⊥ := by
  rcases cubic_actor_contained_or_plane_fixed_at
    h hab structural previous faithful Y (hYI.trans hI.2.1) hYp he with hYM | hc
  · have hne : F.Vi 1 ≠ ⊥ := by
      intro hz
      have hh := F.card 1 (by decide)
      simp [hz] at hh
    have hn := structural.intersection_normalizer h.source h.chosen
      hne (F.le_seed 1) (le_rfl : F.H ≤ normalizer (F.Vi 1 : Set G))
    have hYV : Y ≤ normalizer (V : Set G) := by
      have hh : Y ≤ F.H ⊓ normalizer (L : Set G) := le_inf (hYI.trans hI.2.1) hYM
      rw [hn] at hh
      exact hh.trans inf_le_right
    exact local_quotient_plane_fixed_of_seed_normalized h I hI c p hp Y hYI hYp hYV hfix
  · exact hc

/-- Source 14.7.2(2): the literal cubic orbit image has dimension one or two
in every proper invariant quotient of the original section. -/
theorem local_quotient_cubic_plane_span_dimension_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    {W : Type v} {X : Type w} [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup X] [Module (ZMod 2) X]
    {ρ : Representation (ZMod 2) I W} {σ : Representation (ZMod 2) I X}
    (c : BinaryConjugationSection I (F.UH I) (F.Vi 1) ρ)
    (p : ρ.IntertwiningMap σ) (hp : p.toLinearMap.ker ≠ ⊤)
    (Y : Subgroup G) (hYI : Y ≤ I) (hYp : IsPPerfect 2 Y)
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let E := (c.imageSpace (conjugateSpanBy (F.Vi 2) Y)).map p.toLinearMap
    Module.finrank (ZMod 2) E = 1 ∨ Module.finrank (ZMod 2) E = 2 := by
  let : Finite W := Finite.of_surjective (fun v : F.UH I => (c.coordinates v).toAdd)
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
    c.imageSpace_finrank_of_index V (le_conjugateSpanBy V I) 2 hindex
  have hupper : Module.finrank (ZMod 2) E ≤ 2 :=
    (Submodule.finrank_map_le p.toLinearMap _).trans
      ((Submodule.finrank_mono (c.imageSpace_mono
        (cubic_plane_span_le_seed_at h hab structural previous faithful
          Y (hYI.trans hI.2.1) hYp he))).trans_eq hdim)
  have hnot : ¬ F.Vi 2 ≤ F.Vi 1 := by
    intro hle
    have hh := card_le_of_le hle
    rw [F.card 2 (by decide),F.card 1 (by decide)] at hh
    norm_num at hh
  obtain ⟨v,hv,hvZ⟩ := SetLike.not_le_iff_exists.mp hnot
  let vU : F.UH I := ⟨v,(le_conjugateSpanBy V I) (F.le_seed 2 hv)⟩
  have hsep := local_seed_intersection h I hI c p.toLinearMap.ker (by
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



end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource

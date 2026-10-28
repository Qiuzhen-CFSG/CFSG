module
public import Theory.Representation.ExtraspecialSmallCentralQuotient
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialPointCentral
/-!
# Exact kernels of the remaining small extraspecial chief intervals

A point-central, K-moved chief interval in C_H(U)/U has dimension two
or four. The literal star residual image has order three in dimension
two, with residual kernel of order nine. In dimension four its image
has order nine and the full star kernel is exactly L₁*, the embedded
extraspecial center. Pullback identifies the original H-action kernel
as O₂(H)L₁, retaining the original quotient map.

In the four-dimensional case the selected reciprocal involution moves
at least two dimensions, by inversion on the elementary residual image.
The previously proved centralizer bound is therefore saturated. Its
upper and lower centralization, together with reciprocal normal
generation, confines all original K-movement to this chief interval.

The final Heisenberg application constructs the interval and gives its
exact original action data. It preserves the order-64 faithful branch.
The order-four and order-sixteen branches still require exclusion from
the original ambient hypotheses; this is not source 14.7.20(2) or the
residual classification through 14.7.52.

Source: Aschbacher–Smith, 14.7.20(2), printed p.1049, with the small
central-quotient representations distinguished in D.2.17, printed p.188.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The small chief action retains its exact residual image and, in
dimension four, its full star kernel. -/
theorem extraspecial_point_central_chief_kernel
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    {B N : Subgroup G} (hB : B ≤ centralizer (F.U : Set G)) (hUN : F.U ≤ N)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W} [ρ.IsIrreducible]
    (s : BinaryConjugationSection F.H B N ρ)
    (hp : ⁅B,F.Li L 1⁆ ≤ N) (hm : ¬ ⁅B,K F⁆ ≤ N) :
    ∃ σ : Representation (ZMod 2) (HStar F.H) W,
      σ.comp (starMap F) = ρ ∧
      ((Module.finrank (ZMod 2) W = 2 ∧
        Nat.card ((pResidual 2 (HStar F.H)) ⧸
          (σ.comp (pResidual 2 (HStar F.H)).subtype).ker) = 3 ∧
        Nat.card (σ.ker.subgroupOf (pResidual 2 (HStar F.H))) = 9) ∨
      (Module.finrank (ZMod 2) W = 4 ∧
        Nat.card ((pResidual 2 (HStar F.H)) ⧸
          (σ.comp (pResidual 2 (HStar F.H)).subtype).ker) = 9 ∧
        σ.ker = star F (F.Li L 1))) := by
  let : Finite W := Finite.of_surjective (fun b : B => (s.coordinates b).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  obtain ⟨σ,hσ,hZ,hmP,_,_,hd⟩ := extraspecial_point_central_chief_degree
    h hab structural previous hex hcard hexp hB hUN s hp hm
  let : σ.IsIrreducible := (irreducible_comp_surjective_iff (starMap F)
    (QuotientGroup.mk'_surjective _) σ).mp (hσ ▸ inferInstance)
  let P := pResidual 2 (HStar F.H)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  have hP : Nat.card P = 27 := (Nat.card_congr (residualStarEquiv F).toEquiv).symm.trans hcard
  refine ⟨σ,hσ,?_⟩
  rcases extraspecial_center_kernel_residual_card σ P hP rfl hZ hmP hd with h2 | h4
  · exact Or.inl h2
  · refine Or.inr ⟨h4.1,h4.2.1,?_⟩
    rw [extraspecial_full_kernel_of_restriction_kernel σ P
      (Theory.GroupTheory.centralizer_pResidual_le_of_pCore_eq_bot
        (pCore_quotient_pCore_eq_bot 2)) h4.2.2]
    exact (point_star_eq_center_of_extraspecial_residual h hab structural previous hex hcard hexp).symm


/-- A four-dimensional point-central chief factor exhausts the original
K-movement above and below its literal interval. -/
theorem extraspecial_four_chief_localization
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    {B N : Subgroup G} (hB : B ≤ centralizer (F.U : Set G)) (hUN : F.U ≤ N)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W} [ρ.IsIrreducible]
    (s : BinaryConjugationSection F.H B N ρ)
    (hp : ⁅B,F.Li L 1⁆ ≤ N) (hm : ¬ ⁅B,K F⁆ ≤ N)
    (hd : Module.finrank (ZMod 2) W = 4) :
    ⁅centralizer (F.U : Set G),K F⁆ ≤ B ∧ ⁅N,K F⁆ ≤ F.U := by
  let : Finite W := Finite.of_surjective (fun b : B => (s.coordinates b).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  obtain ⟨σ,hσ,hZ,hmP,_,_,_⟩ := extraspecial_point_central_chief_degree
    h hab structural previous hex hcard hexp hB hUN s hp hm
  subst ρ
  let : σ.IsIrreducible := (irreducible_comp_surjective_iff (starMap F)
    (QuotientGroup.mk'_surjective _) σ).mp inferInstance
  let P := pResidual 2 (HStar F.H)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  have hP : Nat.card P = 27 := (Nat.card_congr (residualStarEquiv F).toEquiv).symm.trans hcard
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  obtain ⟨c,hs,_,_,_⟩ := exists_selected_critical_geometry_of_point_normal h hab structural previous hn
  obtain ⟨a,ha,_,ht,hne,hcenter⟩ :=
    exists_extraspecial_critical_actor h hab structural previous hex hcard hexp c hs
  have hb := extraspecial_center_kernel_dimension_bound σ P hP hZ hmP
    (starMap F a) ht hne hcenter
  have hr : 2 ≤ Module.finrank (ZMod 2) (LinearMap.range (σ (starMap F a) - 1)) := by
    rw [hd] at hb
    omega
  obtain ⟨_,_,hupper,hlower⟩ := extraspecial_centralizer_section_saturation
    h hab structural previous hex hcard hexp c hs hB hUN s a ha hr
  have hU : F.H ≤ normalizer (F.U : Set G) := le_normalizer_conjugateSpanBy V F.H
  have hN : F.H ≤ normalizer (N : Set G) := by
    apply le_normalizer_iff.mpr
    intro x hx n hnN
    have hnB := s.kernel_le hnN
    apply (s.coordinates_eq_one_iff ⟨x*n*x⁻¹,
      (mem_normalizer_iff.mp (s.normalized hx) n).mp hnB⟩).mp
    apply Multiplicative.toAdd.injective
    rw [s.equivariant ⟨x,hx⟩ ⟨n,hnB⟩,(s.coordinates_eq_one_iff _).mpr hnN]
    exact map_zero _
  exact ⟨extraspecial_residual_commutator_of_critical_commutator
    h hab structural previous hex hcard hexp c hs _ _
      (hU.trans (normalizer_le_normalizer_centralizer _)) s.normalized hupper,
    extraspecial_residual_commutator_of_critical_commutator
      h hab structural previous hex hcard hexp c hs _ _ hN hU hlower⟩


open NoncentralChiefRefinement in
/-- Construct the small chief interval and pull its precise action kernel
back to the original H, keeping its residual index and adjacent layers. -/
theorem extraspecial_point_central_interval_kernels
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (hp : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U)
    (hm : ¬ ⁅centralizer (F.U : Set G),K F⁆ ≤ F.U) :
    ∃ N B : NormalNode F.H, N ⋖ B ∧
      F.U ≤ N.val.map F.H.subtype ∧ B.val.map F.H.subtype ≤ centralizer (F.U : Set G) ∧
      ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype ∧
      pCore 2 F.H ⊔ (F.Li L 1).subgroupOf F.H ≤ (sectionAction N B).ker ∧
      ((Nat.card (Section N B) = 4 ∧
        (sectionAction N B).ker.relIndex (pResidual 2 F.H) = 3) ∨
       (Nat.card (Section N B) = 16 ∧
        (sectionAction N B).ker = pCore 2 F.H ⊔ (F.Li L 1).subgroupOf F.H ∧
        ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype ∧
        ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U)) := by
  obtain ⟨N,B,hNB,hUN,hBC,hmove,_,hker⟩ := extraspecial_exists_point_central_moved_chief
    h hab structural previous hex hcard hexp hp hm
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨τ,⟨sU⟩⟩ := exists_section F
  let Q := (centralizer (F.U : Set G)).subgroupOf F.H
  have hQ : IsPGroup 2 Q :=
    ((isPGroup_pCoreIn 2 F.H).to_le
      (centralizer_U_le_core_of_escape h structural (h.flag_escape F previous) sU)).comap_subtype
  have hBQ : B.val ≤ Q := fun b hb => hBC (mem_map_of_mem F.H.subtype hb)
  let : IsElementaryAbelian 2 (Section N B) := chief_elementary N B hNB (hQ.to_le hBQ)
  let ρ := binarySectionRepresentation N B
  let : ρ.IsIrreducible := binarySection_irreducible N B hNB
  let s := ambientBinarySection F.H N B hNB.le
  have hpoint : ⁅B.val.map F.H.subtype,F.Li L 1⁆ ≤ N.val.map F.H.subtype :=
    (commutator_mono hBC le_rfl).trans (hp.trans hUN)
  obtain ⟨σ,hσ,hcases⟩ := extraspecial_point_central_chief_kernel
    h hab structural previous hex hcard hexp hBC hUN s hpoint hmove
  have hact : (sectionAction N B).ker = ρ.ker := by
    ext a
    change sectionAction N B a = 1 ↔ ρ a = 1
    constructor
    · intro ha
      ext w
      exact congrArg (fun f : MulAut (Section N B) => f w.toMul) ha
    · intro ha
      ext w
      exact congrArg Additive.toMul
        (congrArg (fun f : Module.End (ZMod 2) (Additive (Section N B)) => f (Additive.ofMul w)) ha)
  refine ⟨N,B,hNB,hUN,hBC,hmove,hker,?_⟩
  rcases hcases with h2 | h4
  · refine Or.inl ⟨?_,?_⟩
    · change Nat.card (Additive (Section N B)) = 4
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,h2.1]
      norm_num
    · rw [hact]
      change (binarySectionRepresentation N B).ker.relIndex (pResidual 2 F.H) = 3
      rw [←hσ,←MonoidHom.comap_ker,relIndex_comap,
        map_pResidual_of_surjective 2 (starMap F) (QuotientGroup.mk'_surjective _)]
      exact h2.2.1
  · refine Or.inr ⟨?_,?_,extraspecial_four_chief_localization
      h hab structural previous hex hcard hexp hBC hUN s hpoint hmove h4.1⟩
    · change Nat.card (Additive (Section N B)) = 16
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,h4.1]
      norm_num
    · rw [hact]
      change (binarySectionRepresentation N B).ker = _
      rw [←hσ,←MonoidHom.comap_ker,h4.2.2]
      change (((F.Li L 1).subgroupOf F.H).map (starMap F)).comap (starMap F) = _
      rw [comap_map_eq,starMap,QuotientGroup.ker_mk',sup_comm]


open NoncentralChiefRefinement in
/-- Original-group application with exact kernels for every chief alternative.
The small point-central branches are retained as outstanding exclusions. -/
theorem extraspecial_centralizer_exact_chief_alternatives
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ⁅centralizer (F.U : Set G),K F⁆ ≤ F.U ∨
      ∃ N B : NormalNode F.H, N ⋖ B ∧
        F.U ≤ N.val.map F.H.subtype ∧ B.val.map F.H.subtype ≤ centralizer (F.U : Set G) ∧
        ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype ∧
        ((Nat.card (Section N B) = 64 ∧ (sectionAction N B).ker = pCore 2 F.H ∧
          ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype ∧
          ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U) ∨
         (⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U ∧
          pCore 2 F.H ⊔ (F.Li L 1).subgroupOf F.H ≤ (sectionAction N B).ker ∧
          ((Nat.card (Section N B) = 4 ∧
            (sectionAction N B).ker.relIndex (pResidual 2 F.H) = 3) ∨
           (Nat.card (Section N B) = 16 ∧
            (sectionAction N B).ker = pCore 2 F.H ⊔ (F.Li L 1).subgroupOf F.H ∧
            ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype ∧
            ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U)))) := by
  classical
  by_cases hc : ⁅centralizer (F.U : Set G),K F⁆ ≤ F.U
  · exact Or.inl hc
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  apply Or.inr
  by_cases hp : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U
  · obtain ⟨N,B,hNB,hUN,hBC,hm,hker,hsmall⟩ := extraspecial_point_central_interval_kernels
      h hab structural previous hex hcard hexp hp hc
    exact ⟨N,B,hNB,hUN,hBC,hm,Or.inr ⟨hp,hker,hsmall⟩⟩
  · obtain ⟨N,B,hNB,hUN,hBC,hm,hd,hker,hu,hl⟩ := extraspecial_exists_point_moved_chief
      h hab structural previous hex hcard hexp hp
    refine ⟨N,B,hNB,hUN,hBC,?_,Or.inl ⟨hd,hker,hu,hl⟩⟩
    intro hh
    apply hm
    rw [commutator_comm]
    exact (commutator_mono le_rfl (pointResidual_le F)).trans hh

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction

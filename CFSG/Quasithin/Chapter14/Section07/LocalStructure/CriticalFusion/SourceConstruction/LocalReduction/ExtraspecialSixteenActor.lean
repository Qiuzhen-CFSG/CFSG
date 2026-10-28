module
public import Theory.LinearAlgebra.OrderFourFixedLine
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialPointCoreRoots
/-!
# The order-four actor on the remaining order-sixteen interval

The original point core supplies a square root in Q of the selected critical
involution. On a point-central chief four-space, the square moves at least
two dimensions. Its root has order four and a fixed line. Consequently Q
cannot fix the reciprocal centralizer modulo the lower chief endpoint:
that would put a two-dimensional displacement inside the fixed line.

The final application constructs the literal binary chief action and
strengthens the existing original-group alternatives. It retains the exact
kernel O₂(H)L₁, both central flanks, and the central and faithful order-64
branches. No recognition callback or later Data is assumed.
The remaining ambient containment [Q,C_{Uα}(U)] ≤ U would exclude the
order-sixteen branch, but is not proved here. The residual classification
and four-input source assembly through 14.7.52 remain open.

Source: Aschbacher–Smith, 14.7.15(2), 14.7.16(3), and 14.7.20(2),
printed pp.1047–1049. The linear fixed-line argument is structural.
-/
public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- On the remaining four-dimensional chief section, a literal Q-element
squares to the critical actor and has a one-dimensional fixed space. -/
theorem extraspecial_four_chief_order_four_actor
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {B N : Subgroup G} (hB : B ≤ centralizer (F.U : Set G)) (hUN : F.U ≤ N)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W} [ρ.IsIrreducible]
    (s : BinaryConjugationSection F.H B N ρ)
    (hp : ⁅B,F.Li L 1⁆ ≤ N) (hm : ¬ ⁅B,K F⁆ ≤ N)
    (hd : Module.finrank (ZMod 2) W = 4)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection) :
    ∃ a b : F.H, (a : G) ∈ c.Uα ∧ (b : G) ∈ Q T L ∧
      (starMap F b)^2=starMap F a ∧ orderOf (starMap F b)=4 ∧
      (ρ b)^2=ρ a ∧ (ρ b)^4=1 ∧
      2 ≤ Module.finrank (ZMod 2) (ρ a-1).range ∧
      Module.finrank (ZMod 2) (ρ b-1).ker=1 := by
  let : Finite W := Finite.of_surjective (fun b : B => (s.coordinates b).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  obtain ⟨σ,hσ,hZ,hmP,_,_,_⟩ := extraspecial_point_central_chief_degree
    h hab structural previous hex hcard hexp hB hUN s hp hm
  subst ρ
  let : σ.IsIrreducible := (irreducible_comp_surjective_iff (starMap F)
    (QuotientGroup.mk'_surjective _) σ).mp inferInstance
  let P := pResidual 2 (HStar F.H)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  have hP : Nat.card P = 27 := (Nat.card_congr (residualStarEquiv F).toEquiv).symm.trans hcard
  obtain ⟨a,b,ha,_,ha2,hne,hcenter,hb,hba,hbo⟩ :=
    exists_extraspecial_critical_actor_square_root h hab structural previous faithful ⟨e⟩ c hs
  have hlower := extraspecial_center_kernel_dimension_bound σ P hP hZ hmP
    (starMap F a) ha2 hne hcenter
  have hr : 2 ≤ Module.finrank (ZMod 2) (σ (starMap F a)-1).range := by
    rw [hd] at hlower
    omega
  have hsq : (σ (starMap F b))^2=σ (starMap F a) := by rw [←map_pow,hba]
  have hb4 : (starMap F b)^4=1 := hbo ▸ pow_orderOf_eq_one (starMap F b)
  have h4 : (σ (starMap F b))^4=1 := by rw [←map_pow,hb4,map_one]
  have h2ne : (σ (starMap F b))^2≠1 := by
    intro hzero
    rw [hsq] at hzero
    rw [hzero,sub_self,LinearMap.range_zero,finrank_bot] at hr
    omega
  have hrank : Module.finrank (ZMod 2) ((σ (starMap F b))^2-1).range≠1 := by
    rw [hsq]
    omega
  exact ⟨a,b,ha,hb,hba,hbo,hsq,h4,hr,
    LinearMap.order_four_fixed_line hd _ h4 h2ne hrank⟩

/-- An order-sixteen chief section forces Q to move the reciprocal centralizer
modulo its literal lower endpoint. -/
theorem extraspecial_four_chief_core_moves_reciprocal_centralizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {B N : Subgroup G} (hB : B ≤ centralizer (F.U : Set G)) (hUN : F.U ≤ N)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W} [ρ.IsIrreducible]
    (s : BinaryConjugationSection F.H B N ρ)
    (hp : ⁅B,F.Li L 1⁆ ≤ N) (hm : ¬ ⁅B,K F⁆ ≤ N)
    (hd : Module.finrank (ZMod 2) W = 4)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection) :
    ¬ ⁅Q T L,c.Uα ⊓ centralizer (F.U : Set G)⁆ ≤ N := by
  let : Finite W := Finite.of_surjective (fun b : B => (s.coordinates b).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  obtain ⟨a,b,ha,hb,_,_,_,_,hr,hfix⟩ := extraspecial_four_chief_order_four_actor
    h hab structural previous faithful he hB hUN s hp hm hd c hs
  intro hcomm
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨τ,⟨sU⟩⟩ := exists_section F
  have hA := critical_card_two_of_normal_extraspecial_residual h hab structural hn hex hcard c hs
  have hmove : ⁅c.Uα,B⁆ ≤ c.Uα ⊓ centralizer (F.U : Set G) := by
    rw [commutator_comm]
    exact (commutator_mono hB le_rfl).trans
      (centralizer_critical_commutator_of_normal_card_two h hab structural
        (h.flag_escape F previous) hn sU c hs hA)
  have hle : (ρ a-1).range ≤ (ρ b-1).ker := by
    intro v hv
    change ρ b v-v=0
    exact sub_eq_zero.mpr (s.fixed_on_imageSpace_of_commutator_le (Q T L)
      (c.Uα ⊓ centralizer (F.U : Set G)) hcomm b hb v
      (s.displacement_range_le_imageSpace_of_commutator_le c.Uα
        (c.Uα ⊓ centralizer (F.U : Set G)) hmove a ha hv))
  have hdim := Submodule.finrank_mono hle
  omega

open NoncentralChiefRefinement in
/-- Construct the action on the actual order-sixteen interval and apply the
order-four-root obstruction to its literal reciprocal centralizer. -/
theorem extraspecial_sixteen_interval_core_movement
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (N B : NormalNode F.H) (hNB : N ⋖ B)
    (hUN : F.U ≤ N.val.map F.H.subtype)
    (hBC : B.val.map F.H.subtype ≤ centralizer (F.U : Set G))
    (hp : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U)
    (hm : ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype)
    (hc : Nat.card (Section N B) = 16)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection) :
    ¬ ⁅Q T L,c.Uα ⊓ centralizer (F.U : Set G)⁆ ≤ N.val.map F.H.subtype := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨τ,⟨sU⟩⟩ := exists_section F
  let C := (centralizer (F.U : Set G)).subgroupOf F.H
  have hC : IsPGroup 2 C :=
    ((isPGroup_pCoreIn 2 F.H).to_le
      (centralizer_U_le_core_of_escape h structural (h.flag_escape F previous) sU)).comap_subtype
  have hBC' : B.val ≤ C := fun b hb => hBC (mem_map_of_mem F.H.subtype hb)
  let : IsElementaryAbelian 2 (Section N B) := chief_elementary N B hNB (hC.to_le hBC')
  let ρ := binarySectionRepresentation N B
  let : ρ.IsIrreducible := binarySection_irreducible N B hNB
  let s := ambientBinarySection F.H N B hNB.le
  have hd : Module.finrank (ZMod 2) (Additive (Section N B)) = 4 := by
    have hh : Nat.card (Additive (Section N B)) = 16 := hc
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hh
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) hh
  exact extraspecial_four_chief_core_moves_reciprocal_centralizer h hab structural previous faithful
    he hBC hUN s ((commutator_mono hBC le_rfl).trans (hp.trans hUN)) hm hd c hs

open NoncentralChiefRefinement in
/-- The original centralizer-core alternatives, retaining the exact interval
kernel and both central flanks, now require Q-movement of every selected
reciprocal centralizer in the order-sixteen branch. -/
theorem extraspecial_centralizer_core_reduction_with_reciprocal_movement
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    (((F.Li L 1).pCoreIn 2 = (K F).pCoreIn 2) ∧
      (⁅centralizer (F.U : Set G),K F⁆ ≤ F.U ∨
        ∃ N B : NormalNode F.H, N ⋖ B ∧
          F.U ≤ N.val.map F.H.subtype ∧ B.val.map F.H.subtype ≤ centralizer (F.U : Set G) ∧
          ¬ ⁅F.Li L 1,B.val.map F.H.subtype⁆ ≤ N.val.map F.H.subtype ∧
          Nat.card (Section N B) = 64 ∧ (sectionAction N B).ker = pCore 2 F.H ∧
          ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype ∧
          ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U)) ∨
    (⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U ∧
      ∃ N B : NormalNode F.H, N ⋖ B ∧
        F.U ≤ N.val.map F.H.subtype ∧ B.val.map F.H.subtype ≤ centralizer (F.U : Set G) ∧
        ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype ∧
        Nat.card (Section N B) = 16 ∧
        (sectionAction N B).ker = pCore 2 F.H ⊔ (F.Li L 1).subgroupOf F.H ∧
        ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype ∧
        ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U ∧
        ∀ c : CriticalPath (L := L) F, c.RankSelection →
          ¬ ⁅Q T L,c.Uα ⊓ centralizer (F.U : Set G)⁆ ≤ N.val.map F.H.subtype) := by
  rcases extraspecial_centralizer_core_reduction_no_four h hab structural previous faithful he
    with hcase | ⟨hp,N,B,hNB,hUN,hBC,hm,hc,hker,hupper,hlower⟩
  · exact Or.inl hcase
  · refine Or.inr ⟨hp,N,B,hNB,hUN,hBC,hm,hc,hker,hupper,hlower,?_⟩
    intro c hs
    exact extraspecial_sixteen_interval_core_movement h hab structural previous faithful he
      N B hNB hUN hBC hp hm hc c hs
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction

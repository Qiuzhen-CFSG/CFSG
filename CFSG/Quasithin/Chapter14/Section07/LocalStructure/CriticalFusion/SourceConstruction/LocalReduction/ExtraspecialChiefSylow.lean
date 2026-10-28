module
public import Theory.GroupTheory.PGroup.ExtraspecialThreeSmallKernel
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialSmallChief
/-!
# The star Sylow restriction from an order-four chief interval

In the point-central extraspecial branch, an order-four chief interval
has a normal residual kernel of order nine. That kernel defines a stable
line in the extraspecial Frattini quotient. Coprime complements give two
Sylow-invariant generating cubics, so the faithful star Sylow action is
elementary abelian of order at most four. Original critical reciprocity
supplies divisibility by four, and the literal point-core index is two.
Thus the star Sylow has order four and the point-core image has order two.

The original Heisenberg application constructs the binary chief action and
retains the existing exact kernels and localization in all three dimensions.
If the point-core image is known to have order different from two, the
order-four case is excluded and point-central movement is confined to an
order-sixteen interval with kernel O₂(H)L₁. The required source Sylow
restriction, the order-sixteen exclusion, and the remaining classification
through 14.7.52 are still unproved; none is assumed by the unconditional
original-group application.

Source: Aschbacher–Smith, 14.7.15(2) and 14.7.20(2), printed pp.1047–1049.
This is a restriction on the remaining branch, not a proof of either source
statement from the chief interval's order alone.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- A point-central chief factor of binary dimension two forces the original
star Sylow to be elementary of order four and its point core to have order two. -/
theorem extraspecial_two_chief_star_orders
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
    (hd : Module.finrank (ZMod 2) W = 2) :
    IsElementaryAbelian 2 (star F (T : Subgroup G)) ∧
      Nat.card (star F (T : Subgroup G)) = 4 ∧
      Nat.card (star F (F.Ri L 1)) = 2 := by
  let : Finite W := Finite.of_surjective (fun b : B => (s.coordinates b).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  obtain ⟨σ,hσ,hZ,hmP,_,_,_⟩ := extraspecial_point_central_chief_degree
    h hab structural previous hex hcard hexp hB hUN s hp hm
  let : σ.IsIrreducible := (irreducible_comp_surjective_iff (starMap F)
    (QuotientGroup.mk'_surjective _) σ).mp (hσ ▸ inferInstance)
  let P := pResidual 2 (HStar F.H)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  have hP : Nat.card P = 27 := (Nat.card_congr (residualStarEquiv F).toEquiv).symm.trans hcard
  have heP : Monoid.exponent P = 3 :=
    (Monoid.exponent_eq_of_mulEquiv (residualStarEquiv F)).symm.trans hexp
  have hN : Nat.card (σ.ker.subgroupOf P) = 9 := by
    rcases extraspecial_center_kernel_residual_card σ P hP rfl hZ hmP (Or.inl hd) with h2 | h4
    · exact h2.2.2
    · omega
  have hS2 : IsPGroup 2 (star F (T : Subgroup G)) :=
    T.isPGroup'.comap_subtype.map (starMap F)
  obtain ⟨hel,hbound⟩ := IsExtraspecial.small_two_subgroup_of_normal_nine_intersection P hP heP
    (Theory.GroupTheory.centralizer_pResidual_le_of_pCore_eq_bot (pCore_quotient_pCore_eq_bot 2))
    σ.ker hN (fun z hz => hZ (mem_map_of_mem P.subtype hz)) _ hS2
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  obtain ⟨c,hs,_,_,_⟩ := exists_selected_critical_geometry_of_point_normal h hab structural previous hn
  let S : Sylow 2 (HStar F.H) := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective (pCore 2 F.H))
  have hSc : (S : Subgroup (HStar F.H)) = star F (T : Subgroup G) := rfl
  have hdiv : 4 ∣ Nat.card (star F (T : Subgroup G)) := by
    rw [←hSc]
    exact four_dvd_star_sylow_card h structural c S
  have hsize : Nat.card (star F (T : Subgroup G)) = 4 :=
    Nat.le_antisymm hbound (Nat.le_of_dvd Nat.card_pos hdiv)
  have hRT : star F (F.Ri L 1) ≤ star F (T : Subgroup G) := by
    rw [point_core_star_eq_centralizer_of_normal h structural hn]
    exact inf_le_left
  have hcount := relIndex_mul_card_of_le hRT
  rw [point_core_star_index_two_of_normal h structural hn,hsize] at hcount
  exact ⟨hel,hsize,by omega⟩

open NoncentralChiefRefinement in
/-- Apply the Sylow restriction to the literal original order-four chief
interval, constructing its binary action rather than assuming a module. -/
theorem extraspecial_four_interval_star_orders
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (N B : NormalNode F.H) (hNB : N ⋖ B)
    (hUN : F.U ≤ N.val.map F.H.subtype)
    (hBC : B.val.map F.H.subtype ≤ centralizer (F.U : Set G))
    (hp : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U)
    (hm : ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype)
    (hc : Nat.card (Section N B) = 4) :
    IsElementaryAbelian 2 (star F (T : Subgroup G)) ∧
      Nat.card (star F (T : Subgroup G)) = 4 ∧
      Nat.card (star F (F.Ri L 1)) = 2 := by
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
  have hd : Module.finrank (ZMod 2) (Additive (Section N B)) = 2 := by
    have he : Nat.card (Additive (Section N B)) = 4 := hc
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at he
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) he
  exact extraspecial_two_chief_star_orders h hab structural previous hex hcard hexp hBC hUN s
    ((commutator_mono hBC le_rfl).trans (hp.trans hUN)) hm hd


open NoncentralChiefRefinement in
/-- The actual Heisenberg branch with exact chief kernels and the forced
original Sylow structure in the order-four case. No irreducibility of the
Sylow action on the extraspecial Frattini quotient is assumed. -/
theorem extraspecial_centralizer_chief_sylow_reduction
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
            (sectionAction N B).ker.relIndex (pResidual 2 F.H) = 3 ∧
            IsElementaryAbelian 2 (star F (T : Subgroup G)) ∧
            Nat.card (star F (T : Subgroup G)) = 4 ∧
            Nat.card (star F (F.Ri L 1)) = 2) ∨
           (Nat.card (Section N B) = 16 ∧
            (sectionAction N B).ker = pCore 2 F.H ⊔ (F.Li L 1).subgroupOf F.H ∧
            ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype ∧
            ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U)))) := by
  rcases extraspecial_centralizer_exact_chief_alternatives h hab structural previous he with hc | hc
  · exact Or.inl hc
  obtain ⟨N,B,hNB,hUN,hBC,hm,hcases⟩ := hc
  refine Or.inr ⟨N,B,hNB,hUN,hBC,hm,?_⟩
  rcases hcases with h64 | ⟨hp,hker,h4 | h16⟩
  · exact Or.inl h64
  · obtain ⟨e⟩ := he
    have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
      (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
    have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
      (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
    have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
      (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
    exact Or.inr ⟨hp,hker,Or.inl ⟨h4.1,h4.2,
      extraspecial_four_interval_star_orders h hab structural previous hex hcard hexp
        N B hNB hUN hBC hp hm h4.1⟩⟩
  · exact Or.inr ⟨hp,hker,Or.inr h16⟩

open NoncentralChiefRefinement in
/-- Once the order-two point-core image is excluded, the point-central
movement has an order-sixteen interval exhausting K-movement, with original action
kernel O₂(H)L₁. The remaining point-core bound and this interval's exclusion
are explicit source obligations, not consequences of this conditional lemma. -/
theorem extraspecial_point_central_sixteen_of_point_core_ne_two
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (hR : Nat.card (star F (F.Ri L 1)) ≠ 2)
    (hp : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U)
    (hm : ¬ ⁅centralizer (F.U : Set G),K F⁆ ≤ F.U) :
    ∃ N B : NormalNode F.H, N ⋖ B ∧
      F.U ≤ N.val.map F.H.subtype ∧ B.val.map F.H.subtype ≤ centralizer (F.U : Set G) ∧
      ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype ∧
      Nat.card (Section N B) = 16 ∧
      (sectionAction N B).ker = pCore 2 F.H ⊔ (F.Li L 1).subgroupOf F.H ∧
      ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype ∧
      ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U := by
  obtain ⟨N,B,hNB,hUN,hBC,hmove,_,h4 | h16⟩ :=
    extraspecial_point_central_interval_kernels h hab structural previous hex hcard hexp hp hm
  · exact (hR (extraspecial_four_interval_star_orders h hab structural previous
      hex hcard hexp N B hNB hUN hBC hp hmove h4.1).2.2).elim
  · exact ⟨N,B,hNB,hUN,hBC,hmove,h16⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction

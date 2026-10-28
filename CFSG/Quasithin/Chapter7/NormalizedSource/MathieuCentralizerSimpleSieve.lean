module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuCentralizerCoverSieve
public import Theory.SpecificGroups.PSL2.OddAutomorphismRank
public import Theory.SpecificGroups.BinaryLinear.ActionCardinality
public import Theory.Mathieu.M12.Properties.Order
public import Theory.Mathieu.M22.Properties.Order
public import Theory.Mathieu.M23.Properties.Order
public import Theory.SpecificGroups.Janko1.Model.Certification.Order
public import Theory.SpecificGroups.Janko4.Model.Cardinality.Thompson.Divisibility
public import Theory.SpecificGroups.Rudvalis.Model.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.CarrierOrder

/-!
# Simple containing carriers for the original Mathieu residual

The residual order 17280 eliminates all small alternating carriers, higher
binary linear carriers, M₁₁, M₁₂, M₂₂, M₂₃, J₁ and HS. Its elementary
sixteen excludes every odd-field row by two-rank; full-Sylow placement
excludes Bender rows. A faithful binary action in dimension twelve rules
out both J₄ and Rudvalis, since their orders contain 29 while GL₁₂(2)
does not. Only rank-two carriers, M₂₄, J₂ and Held remain.

Source: Aschbacher–Smith, A.3.12 and 8.2.13, printed pp.47–48 and 722–723.
This does not complete the component identification: the remaining source
rows and final application remain with qt-d-1222-nonff-mathieu.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextet
open ChapterA.Section03.SourceEmbeddings Chapter1.Section02.LocalModels

private theorem not_binary_higher_order
    {G : Type*} [Group G] [Finite G] (hd : 17280 ∣ Nat.card G)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (hm : ClassicalGroup.IsPSL G n 2) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let a : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,hF,ZMod.card])
  let b : SL(n,F) ≃* SL(n,ZMod 2) := {
    Matrix.SpecialLinearGroup.map a.toRingHom with
    invFun := Matrix.SpecialLinearGroup.map a.symm.toRingHom
    left_inv := by intro g; ext i j; exact a.symm_apply_apply (g i j)
    right_inv := by intro g; ext i j; exact a.apply_symm_apply (g i j) }
  have hh := card_quotient_dvd_card (center SL(n,F))
  change Nat.card PSL(n,F) ∣ Nat.card SL(n,F) at hh
  rw [←Nat.card_congr e.toEquiv,Nat.card_congr b.toEquiv,BinaryLinear.card_SL] at hh
  have ht := hd.trans hh
  rcases hn with rfl | rfl <;> norm_num [BinaryLinear.order,Fin.prod_univ_succ] at ht

private theorem no_twentyNine_of_binary_twelve
    {G W : Type*} [Group G] [Finite G] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) G W) (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) W = 12) : ¬ 29 ∣ Nat.card G := by
  let : FiniteDimensional (ZMod 2) W := Module.finite_of_finrank_pos (by omega)
  let f := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).toMonoidHom.comp ρ.asGroupHom
  have hi : Function.Injective f := by
    intro x y h
    apply hf
    exact congrArg Units.val
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).injective h)
  have hh := card_dvd_of_injective f hi
  rw [BinaryLinear.card_GL_of_finrank hd] at hh
  intro h
  have hc := h.trans hh
  norm_num [BinaryLinear.order,Fin.prod_univ_succ] at hc

/-- The remaining simple carriers are the rank-two source rows and three
literal sporadic carriers. Order and two-rank exclude every other source row. -/
theorem simple_containing_shortlist
    {G : Type*} [Group G] [Finite G] [IsQuasisimple G]
    (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ ChapterA.Section03.localCComponents S)
    (hne : B ≠ ⊤) (hcard : Nat.card B = 17280) (hr : 4 ≤ primeRank 2 G)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) G W) (hf : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) W = 12) (hm : TheoremCModel G) :
    RankTwoTheoremC G ∨
      Nonempty (G ≃* Sporadic.Mathieu.M24) ∨
      Nonempty (G ≃* Sporadic.LeechRelated.J2.Carrier) ∨
      Nonempty (G ≃* Held.He) := by
  have hd : 17280 ∣ Nat.card G := hcard ▸ B.card_subgroup_dvd_card
  have ht : (⊤ : Subgroup G).IsCComponent :=
    (show IsComponent G ⊤ from ⟨.top,IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent
  cases hm with
  | alternating n hn hm =>
    rw [Nat.card_congr hm.some.toEquiv] at hd
    obtain ⟨hlo,hhi⟩ := hn
    interval_cases n <;> rw [nat_card_alternatingGroup] at hd <;> norm_num [Nat.factorial] at hd
  | linear_odd p k hp ho hk _ hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : Finite PGL(2,F) :=
      Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
    have hh : primeRank 2 G ≤ 2 := by
      rw [primeRank_equiv 2 e]
      exact (Theory.GroupTheory.primeRank_le_of_injective 2
        Matrix.ProjectiveSpecialLinearGroup.toPGL
        Matrix.ProjectiveSpecialLinearGroup.toPGL_injective).trans
          (Theory.PSL2.odd_pgl_two_rank F ⟨p,k,hp,ho,by omega,hF⟩)
    omega
  | three_odd p hp ho unitary hm =>
    let : Fact p.Prime := ⟨hp⟩
    have hh := odd_three_two_rank ho unitary (Or.inl hm)
    omega
  | rank_one hm =>
    exact (hne (eq_of_bender_containing_component S hB ht le_top
      (hm.of_mulEquiv topEquiv))).elim
  | rank_two hm => exact .inl hm
  | binary_linear n hn hm => exact (not_binary_higher_order hd hn hm).elim
  | janko_one hm =>
    rw [Nat.card_congr hm.some.toEquiv,Janko1.card_model] at hd
    norm_num at hd
  | sporadic name hne hm =>
    obtain ⟨e⟩ := hm
    cases name with
    | m11 =>
      rw [Nat.card_congr e.toEquiv,ClassificationModels.SporadicName.Carrier,Sporadic.Mathieu.m11_order] at hd
      norm_num at hd
    | m12 =>
      rw [Nat.card_congr e.toEquiv,ClassificationModels.SporadicName.Carrier,Sporadic.Mathieu.m12_order] at hd
      norm_num at hd
    | m22 =>
      rw [Nat.card_congr e.toEquiv,ClassificationModels.SporadicName.Carrier,Sporadic.Mathieu.m22_order] at hd
      norm_num at hd
    | m23 =>
      rw [Nat.card_congr e.toEquiv,ClassificationModels.SporadicName.Carrier,Sporadic.Mathieu.m23_order] at hd
      norm_num at hd
    | m24 => exact .inr (.inl ⟨e⟩)
    | j2 => exact .inr (.inr (.inl ⟨e⟩))
    | j3 => exact (hne rfl).elim
    | j4 =>
      apply (no_twentyNine_of_binary_twelve ρ hf hdim).elim
      rw [Nat.card_congr e.toEquiv]
      exact (by decide : 29 ∣ 86775571046077562880).trans
        Janko4.Cardinality.Thompson.source_order_dvd_model_card
    | hs =>
      rw [Nat.card_congr e.toEquiv,ClassificationModels.SporadicName.Carrier,Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier] at hd
      norm_num at hd
    | he => exact .inr (.inr (.inr ⟨e⟩))
    | ru =>
      apply (no_twentyNine_of_binary_twelve ρ hf hdim).elim
      rw [Nat.card_congr e.toEquiv,ClassificationModels.SporadicName.Carrier,Rudvalis.model_card]
      decide

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextet

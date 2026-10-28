module

import Mathlib.Data.List.GetD
public import Theory.Alternating.A6DoubleCoverBlockAction
set_option linter.style.nameCheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

/- Chapter 5-specific declarations, kept out of the general Theory library. -/

/- BEGIN Theory.A6DoubleCoverOrderStep0 -/
open Theory.GroupTheory
open Theory.GroupTheory.Covering

namespace GLS3.Chapter5

end GLS3.Chapter5
/- END Theory.A6DoubleCoverOrderStep0 -/

/- BEGIN Theory.A6DoubleCoverOrder -/
namespace GLS3.Chapter5
end GLS3.Chapter5
/- END Theory.A6DoubleCoverOrder -/



/- BEGIN Theory.A6DoubleCoverPerfect -/
namespace GLS3.Chapter5
open scoped commutatorElement
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

public lemma a6DoubleCover_comm1 :
    ⁅(a6DoubleCoverGen1Sub ^ 2),
      (a6DoubleCoverGen2Sub⁻¹ * a6DoubleCoverGen1Sub * a6DoubleCoverGen2Sub⁻¹ *
        a6DoubleCoverGen1Sub ^ 2 * a6DoubleCoverGen2Sub * a6DoubleCoverGen1Sub *
        a6DoubleCoverGen2Sub⁻¹)⁆ = a6DoubleCoverGen1Sub⁻¹ := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  fin_cases x <;> decide +revert +kernel

public lemma a6DoubleCover_comm2 :
    ⁅a6DoubleCoverGen2Sub,
      (a6DoubleCoverGen1Sub * a6DoubleCoverGen2Sub⁻¹ * a6DoubleCoverGen1Sub *
        a6DoubleCoverGen2Sub * a6DoubleCoverGen1Sub⁻¹ * a6DoubleCoverGen1Sub⁻¹)⁆ =
      a6DoubleCoverGen2Sub⁻¹ := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  fin_cases x <;> decide +revert +kernel

public lemma a6DoubleCover_gen1_mem : a6DoubleCoverGen1Sub ∈ commutator a6DoubleCoverPermutationSubgroup := by
  let a := a6DoubleCoverGen1Sub ^ 2
  let b := a6DoubleCoverGen2Sub⁻¹ * a6DoubleCoverGen1Sub * a6DoubleCoverGen2Sub⁻¹ *
    a6DoubleCoverGen1Sub ^ 2 * a6DoubleCoverGen2Sub * a6DoubleCoverGen1Sub *
    a6DoubleCoverGen2Sub⁻¹
  have h : ⁅a, b⁆ ∈ commutator a6DoubleCoverPermutationSubgroup :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
  rw [show ⁅a, b⁆ = a6DoubleCoverGen1Sub⁻¹ by exact a6DoubleCover_comm1] at h
  simpa using (commutator a6DoubleCoverPermutationSubgroup).inv_mem h

public lemma a6DoubleCover_gen2_mem : a6DoubleCoverGen2Sub ∈ commutator a6DoubleCoverPermutationSubgroup := by
  let a := a6DoubleCoverGen2Sub
  let b := a6DoubleCoverGen1Sub * a6DoubleCoverGen2Sub⁻¹ * a6DoubleCoverGen1Sub *
    a6DoubleCoverGen2Sub * a6DoubleCoverGen1Sub⁻¹ * a6DoubleCoverGen1Sub⁻¹
  have h : ⁅a, b⁆ ∈ commutator a6DoubleCoverPermutationSubgroup :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
  rw [show ⁅a, b⁆ = a6DoubleCoverGen2Sub⁻¹ by exact a6DoubleCover_comm2] at h
  simpa using (commutator a6DoubleCoverPermutationSubgroup).inv_mem h

public lemma a6DoubleCover_comm_top : commutator a6DoubleCoverPermutationSubgroup = ⊤ := by
  apply top_unique
  rintro ⟨g, hg⟩ _
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
      rcases Set.mem_insert_iff.mp hg with rfl | hg
      · simpa [a6DoubleCoverGen1Sub] using a6DoubleCover_gen1_mem
      · rw [Set.mem_singleton_iff] at hg
        subst g
        simpa [a6DoubleCoverGen2Sub] using a6DoubleCover_gen2_mem
  | one => exact Subgroup.one_mem _
  | mul x y hx hy ihx ihy => exact Subgroup.mul_mem _ (ihx (Subgroup.mem_top _)) (ihy (Subgroup.mem_top _))
  | inv x hx ih => exact Subgroup.inv_mem _ (ih (Subgroup.mem_top _))

public instance : Group.IsPerfect a6DoubleCoverPermutationSubgroup := ⟨a6DoubleCover_comm_top⟩
end GLS3.Chapter5
/- END Theory.A6DoubleCoverPerfect -/

/- BEGIN Theory.A6DoubleCoverQuasisimple -/
namespace GLS3.Chapter5
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

@[reducible, expose] public def a6DoubleCoverCentralSub : a6DoubleCoverPermutationSubgroup :=
  ⟨a6DoubleCoverCentral, by
    change (a6DoubleCoverGen1 * a6DoubleCoverGen2) ^ 4 ∈
      Subgroup.closure {a6DoubleCoverGen1, a6DoubleCoverGen2}
    exact Subgroup.pow_mem _ (Subgroup.mul_mem _
      (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))) 4⟩

public lemma a6DoubleCover_central_comm_gen1 : Commute a6DoubleCoverCentral a6DoubleCoverGen1 := by
  change a6DoubleCoverCentral * a6DoubleCoverGen1 = a6DoubleCoverGen1 * a6DoubleCoverCentral
  apply Equiv.ext
  intro x
  fin_cases x <;> decide +revert +kernel
public lemma a6DoubleCover_central_comm_gen2 : Commute a6DoubleCoverCentral a6DoubleCoverGen2 := by
  change a6DoubleCoverCentral * a6DoubleCoverGen2 = a6DoubleCoverGen2 * a6DoubleCoverCentral
  apply Equiv.ext
  intro x
  fin_cases x <;> decide +revert +kernel

public lemma a6DoubleCoverCentralSub_mem_center : a6DoubleCoverCentralSub ∈ Subgroup.center a6DoubleCoverPermutationSubgroup := by
  rw [Subgroup.mem_center_iff]
  rintro ⟨g, hg⟩
  apply Subtype.ext
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
      rcases Set.mem_insert_iff.mp hg with rfl | hg
      · exact a6DoubleCover_central_comm_gen1.eq.symm
      · rw [Set.mem_singleton_iff] at hg
        subst g
        exact a6DoubleCover_central_comm_gen2.eq.symm
  | one => simp
  | mul x y hx hy ihx ihy =>
      have ihx' : x * a6DoubleCoverCentral = a6DoubleCoverCentral * x := by
        simpa [a6DoubleCoverCentralSub] using ihx
      have ihy' : y * a6DoubleCoverCentral = a6DoubleCoverCentral * y := by
        simpa [a6DoubleCoverCentralSub] using ihy
      calc
        (x * y) * a6DoubleCoverCentral = x * (y * a6DoubleCoverCentral) := by rw [mul_assoc]
        _ = x * (a6DoubleCoverCentral * y) := by rw [ihy']
        _ = (x * a6DoubleCoverCentral) * y := by rw [mul_assoc]
        _ = (a6DoubleCoverCentral * x) * y := by rw [ihx']
        _ = a6DoubleCoverCentral * (x * y) := by rw [mul_assoc]
  | inv x hx ih =>
      exact (show Commute x a6DoubleCoverCentral from ih).inv_left.eq

public lemma a6DoubleCover_central_block (x : Fin 144) :
    a6DoubleCoverBlockIndex (a6DoubleCoverCentral x) = a6DoubleCoverBlockIndex x := by
  fin_cases x <;> decide +revert +kernel

public lemma a6DoubleCoverCentralSub_mem_ker : a6DoubleCoverCentralSub ∈ a6DoubleCoverBlockCoverHom.ker := by
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  change a6DoubleCoverBlockPermHom a6DoubleCoverCentralSub = 1
  apply FiberAction.quotient_unique a6DoubleCoverBlockIndex a6DoubleCoverBlockIndex_surjective
  · exact FiberAction.quotientPerm_spec a6DoubleCoverBlockIndex
      (a6DoubleCoverToFiberHom a6DoubleCoverCentralSub)
  · intro x
    change a6DoubleCoverBlockIndex (a6DoubleCoverCentral x) = a6DoubleCoverBlockIndex x
    exact a6DoubleCover_central_block x

public lemma a6DoubleCoverCentralSub_sq : a6DoubleCoverCentralSub ^ 2 = 1 := by
  apply Subtype.ext
  exact a6DoubleCoverCentral_sq
public lemma a6DoubleCoverCentralSub_ne_one : a6DoubleCoverCentralSub ≠ 1 := by
  intro h
  exact a6DoubleCoverCentral_ne_one (congrArg Subtype.val h)
public lemma a6DoubleCoverCentralSub_order : orderOf a6DoubleCoverCentralSub = 2 :=
  orderOf_eq_prime a6DoubleCoverCentralSub_sq a6DoubleCoverCentralSub_ne_one

public lemma zpowers_a6DoubleCoverCentralSub_eq_ker : Subgroup.zpowers a6DoubleCoverCentralSub = a6DoubleCoverBlockCoverHom.ker := by
  apply Subgroup.eq_of_le_of_card_ge
  · rw [Subgroup.zpowers_le]
    exact a6DoubleCoverCentralSub_mem_ker
  · rw [Nat.card_zpowers, a6DoubleCoverCentralSub_order, a6DoubleCoverBlockCoverHom_kernel_card]

public lemma a6DoubleCover_center_le_ker : Subgroup.center a6DoubleCoverPermutationSubgroup ≤
    a6DoubleCoverBlockCoverHom.ker := by
  intro g hg
  rw [MonoidHom.mem_ker]
  have hcenter : a6DoubleCoverBlockCoverHom g ∈
      Subgroup.center (alternatingGroup (Fin 6)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := a6DoubleCoverBlockCoverHom_surjective y
    simpa only [map_mul] using congrArg a6DoubleCoverBlockCoverHom
      (Subgroup.mem_center_iff.mp hg x)
  rw [alternatingGroup.center_eq_bot (by norm_num : 4 ≤ Nat.card (Fin 6))] at hcenter
  simpa using hcenter

public lemma a6DoubleCover_center_eq_ker : Subgroup.center a6DoubleCoverPermutationSubgroup =
    a6DoubleCoverBlockCoverHom.ker := by
  apply le_antisymm a6DoubleCover_center_le_ker
  rw [← zpowers_a6DoubleCoverCentralSub_eq_ker, Subgroup.zpowers_le]
  exact a6DoubleCoverCentralSub_mem_center

@[expose] public noncomputable def a6DoubleCover_centerQuotientEquiv :
    a6DoubleCoverPermutationSubgroup ⧸ Subgroup.center a6DoubleCoverPermutationSubgroup ≃*
      alternatingGroup (Fin 6) :=
  (QuotientGroup.quotientMulEquivOfEq a6DoubleCover_center_eq_ker).trans
    (QuotientGroup.quotientKerEquivOfSurjective a6DoubleCoverBlockCoverHom
      a6DoubleCoverBlockCoverHom_surjective)

public instance : IsQuasisimple a6DoubleCoverPermutationSubgroup where
  toIsPerfect := inferInstance
  simple := by
    let : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by norm_num)
    exact a6DoubleCover_centerQuotientEquiv.isSimpleGroup

@[expose] public noncomputable def a6DoubleCover_covering : Covering a6DoubleCoverPermutationSubgroup
    (alternatingGroup (Fin 6)) where
  toMonoidHom := a6DoubleCoverBlockCoverHom
  surjective := a6DoubleCoverBlockCoverHom_surjective
end GLS3.Chapter5
/- END Theory.A6DoubleCoverQuasisimple -/

/- BEGIN Theory.SchurAlternatingNoncommutingWitnessIndexTwo -/
noncomputable section

namespace GLS3.Chapter5.SchurPresentation

/-- In the explicit Schur cover, a quotient-centralizing element whose chosen
lift does not commute with the symmetric lift is a twisted fiber witness and
forces fixed-image index two. -/
public theorem schurAlternatingFixedSubgroup_index_two_of_noncommuting_witness
    (n : Nat) (w : SchurPresentedGroup n) (y : SchurAlternatingGroup n)
    (hquot : Commute (schurSymmetricProjection n w)
      (schurAlternatingProjection n y).1)
    (hnoncomm : ¬ Commute w y.1) :
    let beta : MulAut (alternatingGroup (Fin (n + 5))) :=
      MulAut.conjNormal (H := alternatingGroup (Fin (n + 5)))
        (schurSymmetricProjection n w)
    let alpha : MulAut (SchurAlternatingGroup n) :=
      doubleCoverLiftMulAut n (schurAlternatingCovering n)
        (natCard_ker_schurAlternatingCovering n) beta
    ∃ _hle :
        (automorphismFixedSubgroup alpha).map
            (schurAlternatingProjection n) ≤
          automorphismFixedSubgroup beta,
      (((automorphismFixedSubgroup alpha).map
          (schurAlternatingProjection n)).subgroupOf
            (automorphismFixedSubgroup beta)).index = 2 ∧
        ∃ g : SchurAlternatingGroup n, alpha g =
          (DoubleCoverUniqueness.kernelInvolution
            (schurAlternatingProjection n)
            (natCard_ker_schurAlternatingProjection n) :
              SchurAlternatingGroup n) * g := by
  dsimp only
  let beta : MulAut (alternatingGroup (Fin (n + 5))) :=
    MulAut.conjNormal (H := alternatingGroup (Fin (n + 5)))
      (schurSymmetricProjection n w)
  let alpha : MulAut (SchurAlternatingGroup n) :=
    doubleCoverLiftMulAut n (schurAlternatingCovering n)
      (natCard_ker_schurAlternatingCovering n) beta
  have halpha : alpha = schurAlternatingConj n w := by
    exact doubleCoverLiftMulAut_conjNormal_eq_schurAlternatingConj n w
  have hcompat : ∀ g : SchurAlternatingGroup n,
      schurAlternatingProjection n (alpha g) =
        beta (schurAlternatingProjection n g) := by
    intro g
    rw [halpha]
    exact schurAlternatingConj_fac n w g
  have hyQuotFixed : beta (schurAlternatingProjection n y) =
      schurAlternatingProjection n y := by
    apply Subtype.ext
    change schurSymmetricProjection n w *
        schurAlternatingProjection n y *
          (schurSymmetricProjection n w)⁻¹ =
      schurAlternatingProjection n y
    rw [hquot.eq, mul_inv_cancel_right]
  have hyNotFixed : alpha y ≠ y := by
    rw [halpha]
    intro hy
    apply hnoncomm
    rw [commute_iff_eq]
    have hcoe := congrArg Subtype.val hy
    rw [schurAlternatingConj_apply_coe] at hcoe
    have h := congrArg (fun z : SchurPresentedGroup n => z * w) hcoe
    simpa [mul_assoc] using h
  have hyCases := doubleCoverLift_fixed_or_twisted
    (schurAlternatingProjection n)
    (natCard_ker_schurAlternatingProjection n)
    alpha beta hcompat y hyQuotFixed
  rcases hyCases with hyFixed | hyTwist
  · exact (hyNotFixed hyFixed).elim
  · exact involutionFixedSubgroup_index_two_of_twisted_lift
      (schurAlternatingProjection n)
      (schurAlternatingProjection_surjective n)
      (by
        rw [schurAlternatingProjection_ker_eq_zpowers,
          Subgroup.zpowers_le]
        exact schurAlternatingCentral_mem_center n)
      (natCard_ker_schurAlternatingProjection n)
      alpha beta hcompat y hyQuotFixed hyTwist

end GLS3.Chapter5.SchurPresentation
/- END Theory.SchurAlternatingNoncommutingWitnessIndexTwo -/

/- BEGIN Theory.proposition_5_2_4_c_general -/
noncomputable section

namespace GLS3.Chapter5.SchurPresentation

/-- Proposition 5.2.4(c) for an arbitrary Schur double cover. -/
public theorem proposition_5_2_4_c_general
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2) :
    Nonempty (↥((standardRootA4 n).comap f.toMonoidHom) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) := by
  obtain ⟨e⟩ := nonempty_doubleCoverPreimageMulEquiv n f hcard (standardRootA4 n)
  obtain ⟨d⟩ := proposition_5_2_4_c n
  exact ⟨e.trans d⟩

end GLS3.Chapter5.SchurPresentation
/- END Theory.proposition_5_2_4_c_general -/

/- BEGIN Theory.InvolutionWreathSolvableSmall -/
noncomputable section

namespace GLS3.Chapter5

/-- The involution wreath product on at most two coordinates is solvable. -/
public theorem involutionWreath_isSolvable_of_le_two
    (r : Nat) (hr : r ≤ 2) : Group.IsSolvable (InvolutionWreath r) := by
  have hperm : Group.IsSolvable (Equiv.Perm (Fin r)) := by
    interval_cases r <;> exact Group.isSolvable_of_comm (by decide)
  let : Group.IsSolvable (Equiv.Perm (Fin r)) := hperm
  let N := Fin r → Multiplicative (ZMod 2)
  let φ := SchurPresentation.permuteCoordinatesHom
    (Fin r) (Multiplicative (ZMod 2))
  change Group.IsSolvable (N ⋊[φ] Equiv.Perm (Fin r))
  exact Group.isSolvable_of_ker_le_range
    (SemidirectProduct.inl : N →* N ⋊[φ] Equiv.Perm (Fin r))
    (SemidirectProduct.rightHom :
      N ⋊[φ] Equiv.Perm (Fin r) →* Equiv.Perm (Fin r))
    (by rw [← SemidirectProduct.range_inl_eq_ker_rightHom])

end GLS3.Chapter5
/- END Theory.InvolutionWreathSolvableSmall -/

/- BEGIN Theory.TraceZeroPermutationModuleFaithful -/
noncomputable section

namespace GLS3.Chapter5

/-- For at least three coordinates, the symmetric factor in a trace-zero
permutation module acts faithfully on the abelian factor. -/
public theorem traceZeroPermutationModule_disjoint_centralizer
    {G : Type*} [Group G] (R L : Subgroup G) (r : Nat)
    (hr : 3 ≤ r) (hmod : IsTraceZeroPermutationModule R L r) :
    Disjoint L (Subgroup.centralizer (R : Set G)) := by
  classical
  obtain ⟨eR, eL, haction⟩ := hmod
  rw [Subgroup.disjoint_def]
  intro g hgL hgC
  let l : L := ⟨g, hgL⟩
  have hσ : eL l = 1 := by
    apply Equiv.ext
    intro i
    by_contra hi
    obtain ⟨k, hki, hkσi⟩ :=
      Fin.exists_ne_and_ne_of_two_lt i (eL l i) (by omega)
    let f : Fin r → ZMod 2 := Pi.single i 1 + Pi.single k 1
    have hf : f ∈ traceZeroTwoSubgroup r := by
      rw [mem_traceZeroTwoSubgroup]
      simp [f, Finset.sum_add_distrib, Pi.single_apply]
      exact ZMod.natCast_self 2
    let v0 : Multiplicative ↥(traceZeroTwoSubgroup r) :=
      Multiplicative.ofAdd ⟨f, hf⟩
    let v : R := eR.symm v0
    obtain ⟨w, hwconj, hwaction⟩ := haction l v
    have hgv : g * v.1 * g⁻¹ = v.1 := by
      have hcomm := Subgroup.mem_centralizer_iff.mp hgC v.1 v.2
      calc
        g * v.1 * g⁻¹ = v.1 * g * g⁻¹ := by rw [hcomm]
        _ = v.1 := by simp
    have hwv : w = v := by
      apply Subtype.ext
      exact hwconj.trans hgv
    have hcoord := congrFun hwaction (eL l i)
    rw [hwv] at hcoord
    have hev : eR v = v0 := eR.apply_symm_apply v0
    rw [hev] at hcoord
    change f (eL l i) = f ((eL l).symm (eL l i)) at hcoord
    have hσine_i : eL l i ≠ i := hi
    have hσine_k : eL l i ≠ k := Ne.symm hkσi
    have hkne_i : k ≠ i := hki
    simp [f, hσine_i, hσine_k, hkne_i] at hcoord
  have hl : l = 1 := eL.injective (by simpa using hσ)
  have hg : g = 1 := congrArg Subtype.val hl
  simpa using hg

end GLS3.Chapter5
/- END Theory.TraceZeroPermutationModuleFaithful -/

/- BEGIN Theory.proposition_5_2_8_a -/
noncomputable section

namespace GLS3.Chapter5

/-- Proposition 5.2.8(a): the centralizer of an involution in the alternating
quotient, including the trace-zero module, index-two wreath realization, and
the full extensions when at least two fixed points occur. -/
public theorem proposition_5_2_8_a
    (n : Nat) (a : alternatingGroup (Fin n)) (ha : orderOf a = 2) :
    let x : Equiv.Perm (Fin n) := a
    let r := Fintype.card x.cycleFactorsFinset
    let s := Fintype.card (Function.fixedPoints x)
    ∃ (Rbar Lbar H1bar H2bar : Subgroup (alternatingGroup (Fin n)))
      (tbar : alternatingGroup (Fin n)),
      automorphismFixedSubgroup (MulAut.conj a) =
          (H1bar ⊔ H2bar) ⊔ Subgroup.zpowers tbar ∧
        H1bar = Rbar ⊔ Lbar ∧
        (Rbar.subgroupOf H1bar).Normal ∧
        Disjoint H1bar H2bar ∧
        (∀ g : H1bar, ∀ h : H2bar, Commute g.1 h.1) ∧
        IsTraceZeroPermutationModule Rbar Lbar r ∧
        (∃ P : Subgroup (InvolutionWreath r),
          P.index = 2 ∧ Nonempty (H1bar ≃* P)) ∧
        Nonempty (Rbar ≃* Multiplicative ↥(traceZeroTwoSubgroup r)) ∧
        Nonempty (Lbar ≃* Equiv.Perm (Fin r)) ∧
        Nonempty (H2bar ≃* alternatingGroup (Fin s)) ∧
        tbar ^ 2 = 1 ∧
        (s ≤ 1 → tbar = 1) ∧
        (2 ≤ s →
          Nonempty (↥(H1bar ⊔ Subgroup.zpowers tbar) ≃*
            InvolutionWreath r) ∧
          Nonempty (↥(H2bar ⊔ Subgroup.zpowers tbar) ≃*
            Equiv.Perm (Fin s))) := by
  obtain ⟨Rbar, Lbar, H1bar, H2bar, tbar, hfixed, hH1, hRnormal,
      hdisjoint, hcommute, hmodule, hindex, hR, hL, hH2, ht2, _htHnorm,
      _htH2norm, hsmall, hfull⟩ :=
    involutionAlternatingCentralizerCoreStructure n
      (a : Equiv.Perm (Fin n)) ((Subgroup.orderOf_coe a).trans ha)
  exact ⟨Rbar, Lbar, H1bar, H2bar, tbar, by
    simpa [MulAut.conjNormal_val] using hfixed, hH1, hRnormal, hdisjoint,
    hcommute, hmodule, hindex, hR, hL, ⟨hH2.choose⟩, ht2, hsmall, hfull⟩

end GLS3.Chapter5
/- END Theory.proposition_5_2_8_a -/

/- BEGIN Theory.ExtensionProductBaseNormal -/
namespace GLS3.Chapter5

/-- If the extension factor normalizes both factors, their product is normal
in the subgroup generated by the product and the extension factor. -/
public theorem extensionProduct_base_normal
    {G : Type*} [Group G]
    (A B T : Subgroup G)
    (hTA : T ≤ Subgroup.normalizer A)
    (hTB : T ≤ Subgroup.normalizer B) :
    ((A ⊔ B).subgroupOf ((A ⊔ B) ⊔ T)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
  apply sup_le
  · exact Subgroup.le_normalizer
  · exact (fun t ht =>
      Subgroup.normalizer_inf_normalizer_le_normalizer_sup A B
        ⟨hTA ht, hTB ht⟩)

end GLS3.Chapter5
/- END Theory.ExtensionProductBaseNormal -/

/- BEGIN Theory.A6StandardNineLiftCommutator -/
noncomputable section

namespace GLS3.Chapter5

open scoped commutatorElement

/-- In a triple cover of `A₆`, lifts of the standard `E₉` basis have a
nontrivial central commutator which generates the covering kernel. -/
public theorem exists_a6StandardNine_lifts_commutator
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (f : Covering K (alternatingGroup (Fin 6)))
    (hker : Nat.card f.toMonoidHom.ker = 3) :
    ∃ u v : K,
      f u = SchurPresentation.Theorem523BaseNine.a6X ∧
      f v = SchurPresentation.Theorem523BaseNine.a6Y ∧
      ⁅u, v⁆ ∈ f.toMonoidHom.ker ∧
      ⁅u, v⁆ ≠ 1 ∧
      ⁅u, v⁆ ∈ Subgroup.center K ∧
      ⁅u, v⁆ ^ 3 = 1 ∧
      Subgroup.zpowers ⁅u, v⁆ = f.toMonoidHom.ker := by
  obtain ⟨u, hu⟩ := f.surjective SchurPresentation.Theorem523BaseNine.a6X
  obtain ⟨v, hv⟩ := f.surjective SchurPresentation.Theorem523BaseNine.a6Y
  change f u = SchurPresentation.Theorem523BaseNine.a6X at hu
  change f v = SchurPresentation.Theorem523BaseNine.a6Y at hv
  have hcKer : ⁅u, v⁆ ∈ f.toMonoidHom.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    change ⁅f u, f v⁆ = 1
    rw [hu, hv]
    exact commutatorElement_eq_one_iff_commute.mpr
      SchurPresentation.Theorem523BaseNine.a6_commute
  have hcNe : ⁅u, v⁆ ≠ 1 := by
    intro hc
    apply a6StandardNine_lifts_not_commute f hker u v hu hv
    exact commutatorElement_eq_one_iff_commute.mp hc
  have hcCenter : ⁅u, v⁆ ∈ Subgroup.center K := f.ker_le_center hcKer
  let c : f.toMonoidHom.ker := ⟨⁅u, v⁆, hcKer⟩
  have hcSubNe : c ≠ 1 := by
    intro hc
    apply hcNe
    exact congrArg Subtype.val hc
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hgen : Subgroup.zpowers c = ⊤ :=
    zpowers_eq_top_of_prime_card hker hcSubNe
  have hcOrder : orderOf c = 3 := by
    rw [orderOf_eq_card_of_zpowers_eq_top hgen, hker]
  have hcPowSub : c ^ 3 = 1 := by
    rw [← hcOrder]
    exact pow_orderOf_eq_one c
  have hcPow : ⁅u, v⁆ ^ 3 = 1 := congrArg Subtype.val hcPowSub
  have hgenKer : Subgroup.zpowers ⁅u, v⁆ = f.toMonoidHom.ker := by
    ext z
    constructor
    · intro hz
      obtain ⟨n, rfl⟩ := hz
      exact f.toMonoidHom.ker.zpow_mem hcKer n
    · intro hz
      have hzTop : (⟨z, hz⟩ : f.toMonoidHom.ker) ∈ (⊤ : Subgroup f.toMonoidHom.ker) :=
        Subgroup.mem_top _
      rw [← hgen] at hzTop
      obtain ⟨n, hn⟩ := hzTop
      exact ⟨n, congrArg Subtype.val hn⟩
  exact ⟨u, v, hu, hv, hcKer, hcNe, hcCenter, hcPow, hgenKer⟩

end GLS3.Chapter5
/- END Theory.A6StandardNineLiftCommutator -/

/- BEGIN Theory.A6StandardNineLiftsNotCommuteSixCover -/
noncomputable section

namespace GLS3.Chapter5

/-- Lifts of the displayed basis of the standard `E₉` cannot commute in a
sixfold cover of `A₆`. -/
public theorem a6StandardNine_lifts_not_commute_of_kernel_card_six
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (f : Covering K (alternatingGroup (Fin 6)))
    (hker : Nat.card f.toMonoidHom.ker = 6)
    (u v : K)
    (hu : f u = SchurPresentation.Theorem523BaseNine.a6X)
    (hv : f v = SchurPresentation.Theorem523BaseNine.a6Y) :
    ¬ Commute u v := by
  obtain ⟨L₀, instL₀, finL₀, qsL₀, f₀, hf₀, _hcyc, hcard₀⟩ :=
    SchurPresentation.theorem_5_2_3_c_multiplier_a6
  let : Group L₀ := instL₀
  let : Finite L₀ := finL₀
  let : IsQuasisimple L₀ := qsL₀
  obtain ⟨G, instG, finG, qsG, g, hgker, _hgSylow⟩ :=
    SchurPresentation.theorem_5_2_3_d_sylow3_3A6
  let : Group G := instG
  let : Finite G := finG
  let : IsQuasisimple G := qsG
  let liftK : Covering L₀ K := Covering.IsUniversal.lift hf₀ f
  let liftG : Covering L₀ G := Covering.IsUniversal.lift hf₀ g
  have hfacK : f.comp liftK = f₀ := Covering.IsUniversal.lift_fac hf₀ f
  have hfacG : g.comp liftG = f₀ := Covering.IsUniversal.lift_fac hf₀ g
  have hLcard : Nat.card L₀ =
      Nat.card (alternatingGroup (Fin 6)) * Nat.card f₀.toMonoidHom.ker := by
    simpa only [Subgroup.comap_top, Subgroup.card_top] using
      SchurPresentation.card_comap_mul f₀.toMonoidHom f₀.surjective
        (⊤ : Subgroup (alternatingGroup (Fin 6)))
  have hKcard : Nat.card K =
      Nat.card (alternatingGroup (Fin 6)) * Nat.card f.toMonoidHom.ker := by
    simpa only [Subgroup.comap_top, Subgroup.card_top] using
      SchurPresentation.card_comap_mul f.toMonoidHom f.surjective
        (⊤ : Subgroup (alternatingGroup (Fin 6)))
  have hLKcard : Nat.card L₀ = Nat.card K := by
    rw [hLcard, hKcard, hcard₀, hker]
  have hbij : Function.Bijective liftK := by
    let : Fintype L₀ := Fintype.ofFinite L₀
    let : Fintype K := Fintype.ofFinite K
    apply (Fintype.bijective_iff_surjective_and_card liftK).2
    refine ⟨liftK.surjective, ?_⟩
    simpa [Nat.card_eq_fintype_card] using hLKcard
  obtain ⟨u₀, hu₀⟩ := liftK.surjective u
  obtain ⟨v₀, hv₀⟩ := liftK.surjective v
  have hu₀' : liftK.toMonoidHom u₀ = u := hu₀
  have hv₀' : liftK.toMonoidHom v₀ = v := hv₀
  have hgu : g (liftG u₀) = SchurPresentation.Theorem523BaseNine.a6X := by
    calc
      g (liftG u₀) = f₀ u₀ := by
        simpa using DFunLike.congr_fun hfacG u₀
      _ = f (liftK u₀) := by
        simpa using (DFunLike.congr_fun hfacK u₀).symm
      _ = f u := by simpa using congrArg f hu₀
      _ = SchurPresentation.Theorem523BaseNine.a6X := hu
  have hgv : g (liftG v₀) = SchurPresentation.Theorem523BaseNine.a6Y := by
    calc
      g (liftG v₀) = f₀ v₀ := by
        simpa using DFunLike.congr_fun hfacG v₀
      _ = f (liftK v₀) := by
        simpa using (DFunLike.congr_fun hfacK v₀).symm
      _ = f v := by simpa using congrArg f hv₀
      _ = SchurPresentation.Theorem523BaseNine.a6Y := hv
  intro huv
  apply a6StandardNine_lifts_not_commute g hgker
    (liftG u₀) (liftG v₀) hgu hgv
  apply Commute.map
  rw [commute_iff_eq]
  apply hbij.1
  simp only [map_mul]
  change liftK.toMonoidHom u₀ * liftK.toMonoidHom v₀ =
    liftK.toMonoidHom v₀ * liftK.toMonoidHom u₀
  rw [hu₀', hv₀']
  exact huv.eq

end GLS3.Chapter5
/- END Theory.A6StandardNineLiftsNotCommuteSixCover -/

/- BEGIN Theory.A7StandardNineLiftsNotCommuteSixCover -/
noncomputable section

namespace GLS3.Chapter5

/-- Lifts of the displayed basis of the standard `E₉` cannot commute in a
sixfold cover of `A₇`. -/
public theorem a7StandardNine_lifts_not_commute_of_kernel_card_six
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (f : Covering K (alternatingGroup (Fin 7)))
    (hker : Nat.card f.toMonoidHom.ker = 6)
    (u v : K)
    (hu : f u = SchurPresentation.Theorem523BaseNine.a7X)
    (hv : f v = SchurPresentation.Theorem523BaseNine.a7Y) :
    ¬ Commute u v := by
  obtain ⟨L₀, instL₀, finL₀, qsL₀, f₀, hf₀, _hcyc, hcard₀⟩ :=
    SchurPresentation.theorem_5_2_3_c_multiplier_a7
  let : Group L₀ := instL₀
  let : Finite L₀ := finL₀
  let : IsQuasisimple L₀ := qsL₀
  obtain ⟨G, instG, finG, qsG, g, hgker, _hgSylow⟩ :=
    SchurPresentation.theorem_5_2_3_d_sylow3_3A7
  let : Group G := instG
  let : Finite G := finG
  let : IsQuasisimple G := qsG
  let liftK : Covering L₀ K := Covering.IsUniversal.lift hf₀ f
  let liftG : Covering L₀ G := Covering.IsUniversal.lift hf₀ g
  have hfacK : f.comp liftK = f₀ := Covering.IsUniversal.lift_fac hf₀ f
  have hfacG : g.comp liftG = f₀ := Covering.IsUniversal.lift_fac hf₀ g
  have hLcard : Nat.card L₀ =
      Nat.card (alternatingGroup (Fin 7)) * Nat.card f₀.toMonoidHom.ker := by
    simpa only [Subgroup.comap_top, Subgroup.card_top] using
      SchurPresentation.card_comap_mul f₀.toMonoidHom f₀.surjective
        (⊤ : Subgroup (alternatingGroup (Fin 7)))
  have hKcard : Nat.card K =
      Nat.card (alternatingGroup (Fin 7)) * Nat.card f.toMonoidHom.ker := by
    simpa only [Subgroup.comap_top, Subgroup.card_top] using
      SchurPresentation.card_comap_mul f.toMonoidHom f.surjective
        (⊤ : Subgroup (alternatingGroup (Fin 7)))
  have hLKcard : Nat.card L₀ = Nat.card K := by
    rw [hLcard, hKcard, hcard₀, hker]
  have hbij : Function.Bijective liftK := by
    let : Fintype L₀ := Fintype.ofFinite L₀
    let : Fintype K := Fintype.ofFinite K
    apply (Fintype.bijective_iff_surjective_and_card liftK).2
    refine ⟨liftK.surjective, ?_⟩
    simpa [Nat.card_eq_fintype_card] using hLKcard
  obtain ⟨u₀, hu₀⟩ := liftK.surjective u
  obtain ⟨v₀, hv₀⟩ := liftK.surjective v
  have hu₀' : liftK.toMonoidHom u₀ = u := hu₀
  have hv₀' : liftK.toMonoidHom v₀ = v := hv₀
  have hgu : g (liftG u₀) = SchurPresentation.Theorem523BaseNine.a7X := by
    calc
      g (liftG u₀) = f₀ u₀ := by simpa using DFunLike.congr_fun hfacG u₀
      _ = f (liftK u₀) := by
        simpa using (DFunLike.congr_fun hfacK u₀).symm
      _ = f u := by simpa using congrArg f hu₀
      _ = SchurPresentation.Theorem523BaseNine.a7X := hu
  have hgv : g (liftG v₀) = SchurPresentation.Theorem523BaseNine.a7Y := by
    calc
      g (liftG v₀) = f₀ v₀ := by simpa using DFunLike.congr_fun hfacG v₀
      _ = f (liftK v₀) := by
        simpa using (DFunLike.congr_fun hfacK v₀).symm
      _ = f v := by simpa using congrArg f hv₀
      _ = SchurPresentation.Theorem523BaseNine.a7Y := hv
  intro huv
  apply a7StandardNine_lifts_not_commute g hgker
    (liftG u₀) (liftG v₀) hgu hgv
  apply Commute.map
  rw [commute_iff_eq]
  apply hbij.1
  simp only [map_mul]
  change liftK.toMonoidHom u₀ * liftK.toMonoidHom v₀ =
    liftK.toMonoidHom v₀ * liftK.toMonoidHom u₀
  rw [hu₀', hv₀']
  exact huv.eq

end GLS3.Chapter5
/- END Theory.A7StandardNineLiftsNotCommuteSixCover -/

/- BEGIN Theory.SchurSingleSwapNoncommutingWitness -/
noncomputable section

namespace GLS3.Chapter5.SchurPresentation

/-- Four distinct points give the standard witness for the single-transposition
case: the lift of the product of two disjoint swaps lies in the alternating
cover, centralizes the first swap in the quotient, but not in the cover. -/
public theorem singleSwap_noncommuting_alternating_witness
    (n : Nat) {a b c d : Fin (n + 5)} (hnodup : [a, b, c, d].Nodup) :
    let w := permutationLift n (Equiv.swap a b)
    ∃ y : SchurAlternatingGroup n,
      Commute (schurSymmetricProjection n w)
        (schurAlternatingProjection n y).1 ∧
      ¬ Commute w y.1 := by
  dsimp only
  let w := permutationLift n (Equiv.swap a b)
  let t := permutationLift n (Equiv.swap c d)
  have hab : a ≠ b := by grind
  have hcd : c ≠ d := by grind
  have hprojW : schurSymmetricProjection n w = Equiv.swap a b := by
    exact permutationLift_projection n (Equiv.swap a b)
  have hprojT : schurSymmetricProjection n t = Equiv.swap c d := by
    exact permutationLift_projection n (Equiv.swap c d)
  have hdisjoint : Equiv.Perm.Disjoint (Equiv.swap a b) (Equiv.swap c d) :=
    Equiv.Perm.disjoint_swap_swap hnodup
  have hcommBase : Commute (Equiv.swap a b)
      (Equiv.swap a b * Equiv.swap c d) := by
    have hst : Commute (Equiv.swap a b) (Equiv.swap c d) :=
      hdisjoint.commute
    exact (Commute.refl (Equiv.swap a b)).mul_right hst
  have hyAlt : schurSymmetricProjection n (w * t) ∈
      alternatingGroup (Fin (n + 5)) := by
    rw [map_mul, hprojW, hprojT, Equiv.Perm.mem_alternatingGroup]
    simp [hab, hcd]
  let y : SchurAlternatingGroup n := ⟨w * t, hyAlt⟩
  refine ⟨y, ?_, ?_⟩
  · change Commute (schurSymmetricProjection n w)
      (schurSymmetricProjection n (w * t))
    rw [hprojW, map_mul, hprojW, hprojT]
    exact hcommBase
  · intro hwy
    have hwt : Commute w t := by
      rw [commute_iff_eq] at hwy ⊢
      change w * (w * t) = (w * t) * w at hwy
      have h := congrArg (fun z : SchurPresentedGroup n => w⁻¹ * z) hwy
      simpa [mul_assoc] using h
    have hcommutator : w * t * w⁻¹ * t⁻¹ = schurCentral n := by
      exact permutationLift_disjoint_swaps_commutator n hnodup
    have hcommutatorOne : w * t * w⁻¹ * t⁻¹ = 1 :=
      commutatorElement_eq_one_iff_commute.mpr hwt
    have hzOne : schurCentral n = 1 := hcommutator.symm.trans hcommutatorOne
    exact schurCentral_ne_one n hzOne

end GLS3.Chapter5.SchurPresentation
/- END Theory.SchurSingleSwapNoncommutingWitness -/

/- BEGIN Theory.proposition_5_2_4_d_general -/
noncomputable section

namespace GLS3.Chapter5.SchurPresentation

/-- Proposition 5.2.4(d) for an arbitrary Schur double cover. -/
public theorem proposition_5_2_4_d_general
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2) :
    Nonempty (↥((RootFourSubgroup.rootFourSubgroup n).comap f.toMonoidHom) ≃*
      QuaternionGroup 2) := by
  obtain ⟨e⟩ := nonempty_doubleCoverPreimageMulEquiv n f hcard
    (RootFourSubgroup.rootFourSubgroup n)
  obtain ⟨d⟩ := RootFourSubgroup.proposition_5_2_4_d n
  let c := MulEquiv.subgroupCongr
    (RootFourSubgroup.rootFourPreimage_eq_comap n)
  exact ⟨e.trans (c.symm.trans d)⟩

end GLS3.Chapter5.SchurPresentation
/- END Theory.proposition_5_2_4_d_general -/

/- BEGIN Theory.proposition_5_2_8_d_3 -/
noncomputable section

namespace GLS3.Chapter5.SchurPresentation

/-- Proposition 5.2.8(d)(3): fixed-point alternating factors lift to the
corresponding Schur double covers, including the exceptional `2A₄ = SL₂(3)`
endpoint. -/
public theorem proposition_5_2_8_d_3
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2) :
    Nonempty (↥((standardRootA4 n).comap f.toMonoidHom) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) ∧
    ∀ s : Nat, ∀ _h5 : 5 ≤ s, ∀ hsn : s ≤ n + 5,
      Nonempty (↥((RootAm.rootAm n s hsn).comap f.toMonoidHom) ≃*
        SchurAlternatingGroup (s - 5)) := by
  constructor
  · exact proposition_5_2_4_c_general n f hcard
  · intro s _h5 hsn
    exact proposition_5_2_4_b_general n s f hcard _h5 hsn

end GLS3.Chapter5.SchurPresentation
/- END Theory.proposition_5_2_8_d_3 -/

/- BEGIN Theory.ExtensionProductDerivedLeBase -/
namespace GLS3.Chapter5

/-- The derived subgroup of an extension by a cyclic factor lies in its
normal base product. -/
public theorem extensionProduct_derived_le_base
    {G : Type*} [Group G]
    (A B : Subgroup G) (t : G)
    (hTA : Subgroup.zpowers t ≤ Subgroup.normalizer A)
    (hTB : Subgroup.zpowers t ≤ Subgroup.normalizer B) :
    _root_.commutator (↥((A ⊔ B) ⊔ Subgroup.zpowers t)) ≤
      (A ⊔ B).subgroupOf ((A ⊔ B) ⊔ Subgroup.zpowers t) := by
  let C := (A ⊔ B) ⊔ Subgroup.zpowers t
  let N : Subgroup C := (A ⊔ B).subgroupOf C
  let T : Subgroup C := (Subgroup.zpowers t).subgroupOf C
  let : N.Normal := extensionProduct_base_normal A B (Subgroup.zpowers t) hTA hTB
  have hsup : N ⊔ T = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (B := C) le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_self C
  have : IsMulCommutative T := inferInstance
  exact Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance

end GLS3.Chapter5
/- END Theory.ExtensionProductDerivedLeBase -/

/- BEGIN Theory.TripleCoverA6ExceptionalKernelInversion -/
noncomputable section

namespace GLS3.Chapter5

open scoped commutatorElement

/-- A lift of the determinant-minus-one action on the standard `E₉` basis
inverts the kernel of every triple cover of `A₆`. -/
public theorem tripleCoverA6_kernel_inverted_of_standardNine_matrix
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (f : Covering K (alternatingGroup (Fin 6)))
    (hker : Nat.card f.toMonoidHom.ker = 3)
    (α : MulAut K) (β : MulAut (alternatingGroup (Fin 6)))
    (hcompat : ∀ k : K, f (α k) = β (f k))
    (hβX : β SchurPresentation.Theorem523BaseNine.a6X =
      SchurPresentation.Theorem523BaseNine.a6X ^ 2 *
        SchurPresentation.Theorem523BaseNine.a6Y)
    (hβY : β SchurPresentation.Theorem523BaseNine.a6Y =
      SchurPresentation.Theorem523BaseNine.a6X ^ 2 *
        SchurPresentation.Theorem523BaseNine.a6Y ^ 2) :
    ∀ z : K, z ∈ f.toMonoidHom.ker → α z = z⁻¹ := by
  obtain ⟨u, v, hu, hv, hcKer, _hcNe, hcCenter, hcPow, hgen⟩ :=
    exists_a6StandardNine_lifts_commutator f hker
  have hXpow : SchurPresentation.Theorem523BaseNine.a6X ^ 3 = 1 := by
    rw [← SchurPresentation.Theorem523BaseNine.a6X_order]
    exact pow_orderOf_eq_one _
  have hYpow : SchurPresentation.Theorem523BaseNine.a6Y ^ 3 = 1 := by
    rw [← SchurPresentation.Theorem523BaseNine.a6Y_order]
    exact pow_orderOf_eq_one _
  have hXinv : SchurPresentation.Theorem523BaseNine.a6X⁻¹ =
      SchurPresentation.Theorem523BaseNine.a6X ^ 2 := by
    apply inv_eq_of_mul_eq_one_left
    simpa [pow_succ] using hXpow
  have hYinv : SchurPresentation.Theorem523BaseNine.a6Y⁻¹ =
      SchurPresentation.Theorem523BaseNine.a6Y ^ 2 := by
    apply inv_eq_of_mul_eq_one_left
    simpa [pow_succ] using hYpow
  let a : K := u⁻¹ * v
  let b : K := u⁻¹ * v⁻¹
  have hfa : f a =
      SchurPresentation.Theorem523BaseNine.a6X ^ 2 *
        SchurPresentation.Theorem523BaseNine.a6Y := by
    dsimp [a]
    rw [map_mul, map_inv, hu, hv, hXinv]
  have hfb : f b =
      SchurPresentation.Theorem523BaseNine.a6X ^ 2 *
        SchurPresentation.Theorem523BaseNine.a6Y ^ 2 := by
    dsimp [b]
    rw [map_mul, map_inv, map_inv, hu, hv, hXinv, hYinv]
  let za : K := α u * a⁻¹
  let zb : K := α v * b⁻¹
  have hzaKer : za ∈ f.toMonoidHom.ker := by
    rw [MonoidHom.mem_ker]
    change f (α u * a⁻¹) = 1
    rw [map_mul, map_inv, hcompat, hu, hβX, hfa]
    group
  have hzbKer : zb ∈ f.toMonoidHom.ker := by
    rw [MonoidHom.mem_ker]
    change f (α v * b⁻¹) = 1
    rw [map_mul, map_inv, hcompat, hv, hβY, hfb]
    group
  have hzaCenter : za ∈ Subgroup.center K := f.ker_le_center hzaKer
  have hzbCenter : zb ∈ Subgroup.center K := f.ker_le_center hzbKer
  have hαu : α u = za * a := by
    dsimp [za]
    group
  have hαv : α v = zb * b := by
    dsimp [zb]
    group
  have hcAction : α ⁅u, v⁆ = ⁅u, v⁆⁻¹ := by
    rw [map_commutatorElement, hαu, hαv,
      commutatorElement_central_mul_left za a (zb * b) hzaCenter,
      commutatorElement_central_mul_right a zb b hzbCenter]
    exact commutatorElement_exceptional_matrix u v hcCenter hcPow
  intro z hz
  rw [← hgen] at hz
  obtain ⟨n, rfl⟩ := hz
  rw [map_zpow, hcAction]
  exact inv_zpow _ _

end GLS3.Chapter5
/- END Theory.TripleCoverA6ExceptionalKernelInversion -/

/- BEGIN Theory.TripleCoverA6NaturalKernelInversion -/
noncomputable section

namespace GLS3.Chapter5

open scoped commutatorElement

/-- A lift of the reflection `X ↦ X⁻¹`, `Y ↦ Y` on the standard `E₉`
inverts the kernel of every triple cover of `A₆`. -/
public theorem tripleCoverA6_kernel_inverted_of_standardNine_reflection
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (f : Covering K (alternatingGroup (Fin 6)))
    (hker : Nat.card f.toMonoidHom.ker = 3)
    (α : MulAut K) (β : MulAut (alternatingGroup (Fin 6)))
    (hcompat : ∀ k : K, f (α k) = β (f k))
    (hβX : β SchurPresentation.Theorem523BaseNine.a6X =
      SchurPresentation.Theorem523BaseNine.a6X⁻¹)
    (hβY : β SchurPresentation.Theorem523BaseNine.a6Y =
      SchurPresentation.Theorem523BaseNine.a6Y) :
    ∀ z : K, z ∈ f.toMonoidHom.ker → α z = z⁻¹ := by
  obtain ⟨u, v, hu, hv, hcKer, _hcNe, hcCenter, _hcPow, hgen⟩ :=
    exists_a6StandardNine_lifts_commutator f hker
  let a : K := u⁻¹
  let b : K := v
  have hfa : f a = SchurPresentation.Theorem523BaseNine.a6X⁻¹ := by
    dsimp [a]
    rw [map_inv, hu]
  have hfb : f b = SchurPresentation.Theorem523BaseNine.a6Y := by
    exact hv
  let za : K := α u * a⁻¹
  let zb : K := α v * b⁻¹
  have hzaKer : za ∈ f.toMonoidHom.ker := by
    rw [MonoidHom.mem_ker]
    change f (α u * a⁻¹) = 1
    rw [map_mul, map_inv, hcompat, hu, hβX, hfa]
    group
  have hzbKer : zb ∈ f.toMonoidHom.ker := by
    rw [MonoidHom.mem_ker]
    change f (α v * b⁻¹) = 1
    rw [map_mul, map_inv, hcompat, hv, hβY]
    group
  have hzaCenter : za ∈ Subgroup.center K := f.ker_le_center hzaKer
  have hzbCenter : zb ∈ Subgroup.center K := f.ker_le_center hzbKer
  have hαu : α u = za * a := by
    dsimp [za]
    group
  have hαv : α v = zb * b := by
    dsimp [zb]
    group
  have hcAction : α ⁅u, v⁆ = ⁅u, v⁆⁻¹ := by
    rw [map_commutatorElement, hαu, hαv,
      commutatorElement_central_mul_left za a (zb * b) hzaCenter,
      commutatorElement_central_mul_right a zb b hzbCenter]
    exact commutatorElement_inv_left_of_mem_center u v hcCenter
  intro z hz
  rw [← hgen] at hz
  obtain ⟨n, rfl⟩ := hz
  rw [map_zpow, hcAction]
  exact inv_zpow _ _

end GLS3.Chapter5
/- END Theory.TripleCoverA6NaturalKernelInversion -/

/- BEGIN Theory.A6StandardNineLiftCommutatorSixCover -/
noncomputable section

namespace GLS3.Chapter5

open scoped commutatorElement

/-- In a sixfold cover of `A₆`, lifts of the standard `E₉` basis have a
nontrivial central commutator of order three. -/
public theorem exists_a6StandardNine_lifts_commutator_of_kernel_card_six
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (f : Covering K (alternatingGroup (Fin 6)))
    (hker : Nat.card f.toMonoidHom.ker = 6) :
    ∃ u v : K,
      f u = SchurPresentation.Theorem523BaseNine.a6X ∧
      f v = SchurPresentation.Theorem523BaseNine.a6Y ∧
      ⁅u, v⁆ ∈ f.toMonoidHom.ker ∧
      ⁅u, v⁆ ≠ 1 ∧
      ⁅u, v⁆ ∈ Subgroup.center K ∧
      ⁅u, v⁆ ^ 3 = 1 ∧
      orderOf ⁅u, v⁆ = 3 := by
  obtain ⟨u, hu⟩ := f.surjective SchurPresentation.Theorem523BaseNine.a6X
  obtain ⟨v, hv⟩ := f.surjective SchurPresentation.Theorem523BaseNine.a6Y
  change f u = SchurPresentation.Theorem523BaseNine.a6X at hu
  change f v = SchurPresentation.Theorem523BaseNine.a6Y at hv
  have hcKer : ⁅u, v⁆ ∈ f.toMonoidHom.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    change ⁅f u, f v⁆ = 1
    rw [hu, hv]
    exact commutatorElement_eq_one_iff_commute.mpr
      SchurPresentation.Theorem523BaseNine.a6_commute
  have hcNe : ⁅u, v⁆ ≠ 1 := by
    intro hc
    apply a6StandardNine_lifts_not_commute_of_kernel_card_six
      f hker u v hu hv
    exact commutatorElement_eq_one_iff_commute.mp hc
  have hcCenter : ⁅u, v⁆ ∈ Subgroup.center K := f.ker_le_center hcKer
  let c : K := ⁅u, v⁆
  have hu' : f.toMonoidHom u =
      SchurPresentation.Theorem523BaseNine.a6X := hu
  have huPowKer : u ^ 3 ∈ f.toMonoidHom.ker := by
    rw [MonoidHom.mem_ker, map_pow, hu']
    rw [← SchurPresentation.Theorem523BaseNine.a6X_order]
    exact pow_orderOf_eq_one _
  have huPowCenter : u ^ 3 ∈ Subgroup.center K := f.ker_le_center huPowKer
  have hcTwo : ⁅u ^ 2, v⁆ = c ^ 2 := by
    rw [pow_two, commutatorElement_mul_left_eq_conj_mul]
    have huc : Commute u c :=
      Subgroup.mem_center_iff.mp hcCenter u
    change u * c * u⁻¹ * c = c ^ 2
    rw [huc.eq]
    simp [pow_two]
  have hcThree : ⁅u ^ 3, v⁆ = c ^ 3 := by
    rw [show u ^ 3 = u * u ^ 2 by simp [pow_succ, mul_assoc],
      commutatorElement_mul_left_eq_conj_mul, hcTwo]
    have hcTwoCenter : c ^ 2 ∈ Subgroup.center K :=
      Subgroup.pow_mem _ hcCenter 2
    have hucTwo : Commute u (c ^ 2) :=
      Subgroup.mem_center_iff.mp hcTwoCenter u
    change u * c ^ 2 * u⁻¹ * c = c ^ 3
    rw [hucTwo.eq]
    simp [pow_succ]
  have hcPow : ⁅u, v⁆ ^ 3 = 1 := by
    change c ^ 3 = 1
    rw [← hcThree]
    exact commutatorElement_eq_one_iff_commute.mpr
      (Subgroup.mem_center_iff.mp huPowCenter v).symm
  have hcOrder : orderOf ⁅u, v⁆ = 3 := by
    have hdvd : orderOf ⁅u, v⁆ ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hcPow
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with hOne | hThree
    · exact (hcNe (orderOf_eq_one_iff.mp hOne)).elim
    · exact hThree
  exact ⟨u, v, hu, hv, hcKer, hcNe, hcCenter, hcPow, hcOrder⟩

end GLS3.Chapter5
/- END Theory.A6StandardNineLiftCommutatorSixCover -/

/- BEGIN Theory.A7StandardNineLiftCommutator -/
noncomputable section

namespace GLS3.Chapter5

open scoped commutatorElement

/-- If an `A₇` covering kernel has order three or six, lifts of the standard
`E₉` basis have a nontrivial central commutator of order three. -/
public theorem exists_a7StandardNine_lifts_commutator
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (f : Covering K (alternatingGroup (Fin 7)))
    (hker : Nat.card f.toMonoidHom.ker = 3 ∨
      Nat.card f.toMonoidHom.ker = 6) :
    ∃ u v : K,
      f u = SchurPresentation.Theorem523BaseNine.a7X ∧
      f v = SchurPresentation.Theorem523BaseNine.a7Y ∧
      ⁅u, v⁆ ∈ f.toMonoidHom.ker ∧ ⁅u, v⁆ ≠ 1 ∧
      ⁅u, v⁆ ∈ Subgroup.center K ∧ ⁅u, v⁆ ^ 3 = 1 ∧
      orderOf ⁅u, v⁆ = 3 := by
  obtain ⟨u, hu⟩ := f.surjective SchurPresentation.Theorem523BaseNine.a7X
  obtain ⟨v, hv⟩ := f.surjective SchurPresentation.Theorem523BaseNine.a7Y
  change f u = SchurPresentation.Theorem523BaseNine.a7X at hu
  change f v = SchurPresentation.Theorem523BaseNine.a7Y at hv
  have hcKer : ⁅u, v⁆ ∈ f.toMonoidHom.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    change ⁅f u, f v⁆ = 1
    rw [hu, hv]
    exact commutatorElement_eq_one_iff_commute.mpr
      SchurPresentation.Theorem523BaseNine.a7_commute
  have hcNe : ⁅u, v⁆ ≠ 1 := by
    intro hc
    have huv : Commute u v := commutatorElement_eq_one_iff_commute.mp hc
    rcases hker with hthree | hsix
    · exact a7StandardNine_lifts_not_commute f hthree u v hu hv huv
    · exact a7StandardNine_lifts_not_commute_of_kernel_card_six
        f hsix u v hu hv huv
  have hcCenter : ⁅u, v⁆ ∈ Subgroup.center K := f.ker_le_center hcKer
  let c : K := ⁅u, v⁆
  have hu' : f.toMonoidHom u = SchurPresentation.Theorem523BaseNine.a7X := hu
  have huPowKer : u ^ 3 ∈ f.toMonoidHom.ker := by
    rw [MonoidHom.mem_ker, map_pow, hu']
    rw [← SchurPresentation.Theorem523BaseNine.a7X_order]
    exact pow_orderOf_eq_one _
  have huPowCenter : u ^ 3 ∈ Subgroup.center K := f.ker_le_center huPowKer
  have hcTwo : ⁅u ^ 2, v⁆ = c ^ 2 := by
    rw [pow_two, commutatorElement_mul_left_eq_conj_mul]
    have huc : Commute u c := Subgroup.mem_center_iff.mp hcCenter u
    change u * c * u⁻¹ * c = c ^ 2
    rw [huc.eq]
    simp [pow_two]
  have hcThree : ⁅u ^ 3, v⁆ = c ^ 3 := by
    rw [show u ^ 3 = u * u ^ 2 by simp [pow_succ, mul_assoc],
      commutatorElement_mul_left_eq_conj_mul, hcTwo]
    have hcTwoCenter : c ^ 2 ∈ Subgroup.center K :=
      Subgroup.pow_mem _ hcCenter 2
    have hucTwo : Commute u (c ^ 2) :=
      Subgroup.mem_center_iff.mp hcTwoCenter u
    change u * c ^ 2 * u⁻¹ * c = c ^ 3
    rw [hucTwo.eq]
    simp [pow_succ]
  have hcPow : ⁅u, v⁆ ^ 3 = 1 := by
    change c ^ 3 = 1
    rw [← hcThree]
    exact commutatorElement_eq_one_iff_commute.mpr
      (Subgroup.mem_center_iff.mp huPowCenter v).symm
  have hcOrder : orderOf ⁅u, v⁆ = 3 := by
    have hdvd : orderOf ⁅u, v⁆ ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hcPow
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with hOne | hThree
    · exact (hcNe (orderOf_eq_one_iff.mp hOne)).elim
    · exact hThree
  exact ⟨u, v, hu, hv, hcKer, hcNe, hcCenter, hcPow, hcOrder⟩

end GLS3.Chapter5
/- END Theory.A7StandardNineLiftCommutator -/

/- BEGIN Theory.SchurSupportTwoNoncommutingWitness -/
noncomputable section

namespace GLS3.Chapter5.SchurPresentation

/-- Every transposition in degree at least five admits an alternating lift
witness that centralizes it in the quotient but not in the Schur cover. -/
public theorem supportTwo_noncommuting_alternating_witness
    (n : Nat) (σ : Equiv.Perm (Fin (n + 5)))
    (hsupport : σ.support.card = 2) :
    ∃ y : SchurAlternatingGroup n,
      Commute (schurSymmetricProjection n (permutationLift n σ))
        (schurAlternatingProjection n y).1 ∧
      ¬ Commute (permutationLift n σ) y.1 := by
  have hswap : σ.IsSwap := Equiv.Perm.card_support_eq_two.mp hsupport
  obtain ⟨a, b, hab, rfl⟩ := hswap
  have hcompl : 1 < (Equiv.swap a b).supportᶜ.card := by
    rw [Finset.card_compl, hsupport]
    simp only [Fintype.card_fin]
    omega
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp hcompl
  have hca : c ≠ a := by
    intro hca
    apply (Finset.mem_compl.mp hc)
    rw [Equiv.Perm.support_swap hab]
    simp [hca]
  have hcb : c ≠ b := by
    intro hcb
    apply (Finset.mem_compl.mp hc)
    rw [Equiv.Perm.support_swap hab]
    simp [hcb]
  have hda : d ≠ a := by
    intro hda
    apply (Finset.mem_compl.mp hd)
    rw [Equiv.Perm.support_swap hab]
    simp [hda]
  have hdb : d ≠ b := by
    intro hdb
    apply (Finset.mem_compl.mp hd)
    rw [Equiv.Perm.support_swap hab]
    simp [hdb]
  exact singleSwap_noncommuting_alternating_witness n
    (a := a) (b := b) (c := c) (d := d)
    (by
      simp [hab, Ne.symm hca, Ne.symm hcb, Ne.symm hda, Ne.symm hdb, hcd])

end GLS3.Chapter5.SchurPresentation
/- END Theory.SchurSupportTwoNoncommutingWitness -/

/- BEGIN Theory.proposition_5_2_4_g_general -/
noncomputable section

namespace GLS3.Chapter5.SchurPresentation

/-- Proposition 5.2.4(g) for an arbitrary Schur double cover. -/
public theorem proposition_5_2_4_g_general
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hkerCard : Nat.card f.toMonoidHom.ker = 2)
    (Lbar : Subgroup (alternatingGroup (Fin (n + 5))))
    (hLbar : IsMulCommutative ↥Lbar ∧
      ∀ x : ↥Lbar, orderOf x = 1 ∨ orderOf x = 2)
    (hcard : 8 ≤ Nat.card ↥Lbar)
    (hsemiregular : ∀ x : ↥Lbar, x ≠ 1 →
      ∀ omega : Fin (n + 5),
        (∃ y : ↥Lbar, y.1.1 omega ≠ omega) → x.1.1 omega ≠ omega) :
    let L := Lbar.comap f.toMonoidHom
    IsMulCommutative ↥L ∧ ∀ x : ↥L, orderOf x = 1 ∨ orderOf x = 2 := by
  let L := Lbar.comap f.toMonoidHom
  obtain ⟨e⟩ := nonempty_doubleCoverPreimageMulEquiv n f hkerCard Lbar
  have hexplicit := proposition_5_2_4_g n Lbar hLbar hcard hsemiregular
  let L0 := Lbar.comap (schurAlternatingProjection n)
  change IsMulCommutative ↥L ∧ ∀ x : ↥L, orderOf x = 1 ∨ orderOf x = 2
  change IsMulCommutative ↥L0 ∧
    (∀ x : ↥L0, orderOf x = 1 ∨ orderOf x = 2) at hexplicit
  let : IsMulCommutative ↥L0 := hexplicit.1
  constructor
  · refine ⟨⟨?_⟩⟩
    intro a b
    apply e.injective
    simpa only [map_mul] using
      (Std.Commutative.comm (e a) (e b))
  · intro x
    have hx := hexplicit.2 (e x)
    rw [e.orderOf_eq] at hx
    exact hx

end GLS3.Chapter5.SchurPresentation
/- END Theory.proposition_5_2_4_g_general -/

/- BEGIN Theory.PerfectSubgroupExtensionLeBase -/
namespace GLS3.Chapter5

/-- A perfect subgroup of a cyclic extension lies in the normal base product. -/
public theorem perfect_subgroup_le_extension_base
    {G : Type*} [Group G]
    (A B I : Subgroup G) (t : G)
    [Group.IsPerfect I]
    (hI : I ≤ (A ⊔ B) ⊔ Subgroup.zpowers t)
    (hTA : Subgroup.zpowers t ≤ Subgroup.normalizer A)
    (hTB : Subgroup.zpowers t ≤ Subgroup.normalizer B) :
    I ≤ A ⊔ B := by
  let C : Subgroup G := (A ⊔ B) ⊔ Subgroup.zpowers t
  let J : Subgroup C := I.subgroupOf C
  let hderiv : _root_.commutator (↥C) ≤ (A ⊔ B).subgroupOf C := by
    exact extensionProduct_derived_le_base A B t hTA hTB
  have hcommJ :
      Subgroup.map C.subtype ⁅J, J⁆ = ⁅I, I⁆ := by
    rw [Subgroup.map_commutator]
    rw [Subgroup.map_subgroupOf_eq_of_le hI]
  have hcommI : ⁅I, I⁆ = I := by
    rw [← Subgroup.map_subtype_commutator I,
      Group.IsPerfect.commutator_eq_top]
    apply le_antisymm
    · rintro x ⟨y, _, rfl⟩
      exact y.property
    · intro x hx
      exact ⟨⟨x, hx⟩, trivial, rfl⟩
  have hJtop : Subgroup.map C.subtype ⁅J, J⁆ = I :=
    hcommJ.trans hcommI
  have hJderiv : ⁅J, J⁆ ≤ _root_.commutator (↥C) := by
    simpa only [_root_.commutator_def] using
      (Subgroup.commutator_mono (H₁ := J) (H₂ := J)
        (K₁ := (⊤ : Subgroup C)) (K₂ := ⊤) le_top le_top)
  intro i hi
  have himap : i ∈ Subgroup.map C.subtype ⁅J, J⁆ := by
    rw [hJtop]
    exact hi
  rcases himap with ⟨j, hj, hji⟩
  have hjbase : j ∈ (A ⊔ B).subgroupOf C := hderiv (hJderiv hj)
  have hjbase' : (j : G) ∈ A ⊔ B := hjbase
  have heq : (j : G) = i := hji
  rw [heq] at hjbase'
  exact hjbase'

end GLS3.Chapter5
/- END Theory.PerfectSubgroupExtensionLeBase -/

/- BEGIN Theory.TripleCoverA6CenterInversionTransport -/
noncomputable section

namespace GLS3.Chapter5

/-- Left multiplication of the quotient action by an inner automorphism can be
lifted without changing the action on the center. -/
public theorem tripleCoverA6_center_inverted_of_reflection_normalForm
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (f : Covering K (alternatingGroup (Fin 6)))
    (hker : Nat.card f.toMonoidHom.ker = 3)
    (x : MulAut K) (β : MulAut (alternatingGroup (Fin 6)))
    (hcompat : ∀ k : K, f (x k) = β (f k))
    (δ : alternatingGroup (Fin 6))
    (hX : (MulAut.conj δ * β) SchurPresentation.Theorem523BaseNine.a6X =
      SchurPresentation.Theorem523BaseNine.a6X⁻¹)
    (hY : (MulAut.conj δ * β) SchurPresentation.Theorem523BaseNine.a6Y =
      SchurPresentation.Theorem523BaseNine.a6Y) :
    ∀ z : K, z ∈ Subgroup.center K → x z = z⁻¹ := by
  obtain ⟨d, hd⟩ := f.surjective δ
  change f d = δ at hd
  let α : MulAut K := MulAut.conj d * x
  let γ : MulAut (alternatingGroup (Fin 6)) := MulAut.conj δ * β
  have hαcompat : ∀ k : K, f (α k) = γ (f k) := by
    intro k
    change f (d * x k * d⁻¹) = (MulAut.conj δ * β) (f k)
    change f (d * x k * d⁻¹) = δ * β (f k) * δ⁻¹
    rw [map_mul, map_inv, map_mul, hd, hcompat k]
  have hinv := tripleCoverA6_kernel_inverted_of_standardNine_reflection
    f hker α γ hαcompat (by simpa [γ] using hX) (by simpa [γ] using hY)
  let : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  have hfker : f.toMonoidHom.ker = Subgroup.center K :=
    f.ker_eq_center_of_isSimple
  intro z hz
  have hzα : α z = x z := by
    dsimp [α]
    have hxz : x z ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g, rfl⟩ := x.surjective g
      simpa [map_mul] using congrArg x (Subgroup.mem_center_iff.mp hz g)
    have hcomm : Commute d (x z) := Subgroup.mem_center_iff.mp hxz d
    rw [hcomm.eq, mul_inv_cancel_right]
  rw [← hzα]
  exact hinv z (by rw [hfker]; exact hz)


/-- The exceptional determinant-minus-one normal form also inverts the center
of every triple cover of `A₆`. -/
public theorem tripleCoverA6_center_inverted_of_matrix_normalForm
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (f : Covering K (alternatingGroup (Fin 6)))
    (hker : Nat.card f.toMonoidHom.ker = 3)
    (x : MulAut K) (β : MulAut (alternatingGroup (Fin 6)))
    (hcompat : ∀ k : K, f (x k) = β (f k))
    (δ : alternatingGroup (Fin 6))
    (hX : (MulAut.conj δ * β) SchurPresentation.Theorem523BaseNine.a6X =
      SchurPresentation.Theorem523BaseNine.a6X ^ 2 *
        SchurPresentation.Theorem523BaseNine.a6Y)
    (hY : (MulAut.conj δ * β) SchurPresentation.Theorem523BaseNine.a6Y =
      SchurPresentation.Theorem523BaseNine.a6X ^ 2 *
        SchurPresentation.Theorem523BaseNine.a6Y ^ 2) :
    ∀ z : K, z ∈ Subgroup.center K → x z = z⁻¹ := by
  obtain ⟨d, hd⟩ := f.surjective δ
  change f d = δ at hd
  let α : MulAut K := MulAut.conj d * x
  let γ : MulAut (alternatingGroup (Fin 6)) := MulAut.conj δ * β
  have hαcompat : ∀ k : K, f (α k) = γ (f k) := by
    intro k
    change f (d * x k * d⁻¹) = (MulAut.conj δ * β) (f k)
    change f (d * x k * d⁻¹) = δ * β (f k) * δ⁻¹
    rw [map_mul, map_inv, map_mul, hd, hcompat k]
  have hinv := tripleCoverA6_kernel_inverted_of_standardNine_matrix
    f hker α γ hαcompat (by simpa [γ] using hX) (by simpa [γ] using hY)
  let : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  have hfker : f.toMonoidHom.ker = Subgroup.center K :=
    f.ker_eq_center_of_isSimple
  intro z hz
  have hzα : α z = x z := by
    dsimp [α]
    have hxz : x z ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g, rfl⟩ := x.surjective g
      simpa [map_mul] using congrArg x (Subgroup.mem_center_iff.mp hz g)
    have hcomm : Commute d (x z) := Subgroup.mem_center_iff.mp hxz d
    rw [hcomm.eq, mul_inv_cancel_right]
  rw [← hzα]
  exact hinv z (by rw [hfker]; exact hz)

/-- Conjugating an automorphism does not change whether it inverts the center. -/
public theorem center_inversion_of_conjugate
    {K : Type*} [Group K] (x h : MulAut K)
    (hinv : ∀ z : K, z ∈ Subgroup.center K →
      ((h⁻¹ * x * h) z) = z⁻¹) :
    ∀ z : K, z ∈ Subgroup.center K → x z = z⁻¹ := by
  intro z hz
  have hhzinv : h⁻¹ z ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hzcomm := Subgroup.mem_center_iff.mp hz (h g)
    have hback := congrArg (h⁻¹ : MulAut K) hzcomm
    simpa [map_mul] using hback
  have hstep := hinv (h⁻¹ z) hhzinv
  have hstep' := congrArg h hstep
  simpa [map_inv] using hstep'

end GLS3.Chapter5
/- END Theory.TripleCoverA6CenterInversionTransport -/

/- BEGIN Theory.SixCoverA6ExceptionalCenterThreeInversion -/
noncomputable section

namespace GLS3.Chapter5

open scoped commutatorElement

/-- A lift of the determinant-minus-one action on the standard `E₉` basis
inverts a nontrivial central element of order three in every sixfold cover of
`A₆`. -/
public theorem sixCoverA6_exists_center_orderThree_inverted_of_matrix
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (f : Covering K (alternatingGroup (Fin 6)))
    (hker : Nat.card f.toMonoidHom.ker = 6)
    (α : MulAut K) (β : MulAut (alternatingGroup (Fin 6)))
    (hcompat : ∀ k : K, f (α k) = β (f k))
    (hβX : β SchurPresentation.Theorem523BaseNine.a6X =
      SchurPresentation.Theorem523BaseNine.a6X ^ 2 *
        SchurPresentation.Theorem523BaseNine.a6Y)
    (hβY : β SchurPresentation.Theorem523BaseNine.a6Y =
      SchurPresentation.Theorem523BaseNine.a6X ^ 2 *
        SchurPresentation.Theorem523BaseNine.a6Y ^ 2) :
    ∃ c : K, c ∈ f.toMonoidHom.ker ∧ c ≠ 1 ∧
      c ∈ Subgroup.center K ∧ c ^ 3 = 1 ∧ orderOf c = 3 ∧ α c = c⁻¹ := by
  obtain ⟨u, v, hu, hv, hcKer, hcNe, hcCenter, hcPow, hcOrder⟩ :=
    exists_a6StandardNine_lifts_commutator_of_kernel_card_six f hker
  have hXpow : SchurPresentation.Theorem523BaseNine.a6X ^ 3 = 1 := by
    rw [← SchurPresentation.Theorem523BaseNine.a6X_order]
    exact pow_orderOf_eq_one _
  have hYpow : SchurPresentation.Theorem523BaseNine.a6Y ^ 3 = 1 := by
    rw [← SchurPresentation.Theorem523BaseNine.a6Y_order]
    exact pow_orderOf_eq_one _
  have hXinv : SchurPresentation.Theorem523BaseNine.a6X⁻¹ =
      SchurPresentation.Theorem523BaseNine.a6X ^ 2 := by
    apply inv_eq_of_mul_eq_one_left
    simpa [pow_succ] using hXpow
  have hYinv : SchurPresentation.Theorem523BaseNine.a6Y⁻¹ =
      SchurPresentation.Theorem523BaseNine.a6Y ^ 2 := by
    apply inv_eq_of_mul_eq_one_left
    simpa [pow_succ] using hYpow
  let a : K := u⁻¹ * v
  let b : K := u⁻¹ * v⁻¹
  have hfa : f a = SchurPresentation.Theorem523BaseNine.a6X ^ 2 *
      SchurPresentation.Theorem523BaseNine.a6Y := by
    dsimp [a]
    rw [map_mul, map_inv, hu, hv, hXinv]
  have hfb : f b = SchurPresentation.Theorem523BaseNine.a6X ^ 2 *
      SchurPresentation.Theorem523BaseNine.a6Y ^ 2 := by
    dsimp [b]
    rw [map_mul, map_inv, map_inv, hu, hv, hXinv, hYinv]
  let za : K := α u * a⁻¹
  let zb : K := α v * b⁻¹
  have hzaKer : za ∈ f.toMonoidHom.ker := by
    rw [MonoidHom.mem_ker]
    change f (α u * a⁻¹) = 1
    rw [map_mul, map_inv, hcompat, hu, hβX, hfa]
    group
  have hzbKer : zb ∈ f.toMonoidHom.ker := by
    rw [MonoidHom.mem_ker]
    change f (α v * b⁻¹) = 1
    rw [map_mul, map_inv, hcompat, hv, hβY, hfb]
    group
  have hzaCenter : za ∈ Subgroup.center K := f.ker_le_center hzaKer
  have hzbCenter : zb ∈ Subgroup.center K := f.ker_le_center hzbKer
  have hαu : α u = za * a := by
    dsimp [za]
    group
  have hαv : α v = zb * b := by
    dsimp [zb]
    group
  refine ⟨⁅u, v⁆, hcKer, hcNe, hcCenter, hcPow, hcOrder, ?_⟩
  rw [map_commutatorElement, hαu, hαv,
    commutatorElement_central_mul_left za a (zb * b) hzaCenter,
    commutatorElement_central_mul_right a zb b hzbCenter]
  exact commutatorElement_exceptional_matrix u v hcCenter hcPow

end GLS3.Chapter5
/- END Theory.SixCoverA6ExceptionalCenterThreeInversion -/

/- BEGIN Theory.SixCoverA6NaturalCenterThreeInversion -/
noncomputable section

namespace GLS3.Chapter5

open scoped commutatorElement

/-- A lift of the reflection `X ↦ X⁻¹`, `Y ↦ Y` on the standard `E₉`
inverts a nontrivial central element of order three in every sixfold cover of
`A₆`. -/
public theorem sixCoverA6_exists_center_orderThree_inverted_of_reflection
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (f : Covering K (alternatingGroup (Fin 6)))
    (hker : Nat.card f.toMonoidHom.ker = 6)
    (α : MulAut K) (β : MulAut (alternatingGroup (Fin 6)))
    (hcompat : ∀ k : K, f (α k) = β (f k))
    (hβX : β SchurPresentation.Theorem523BaseNine.a6X =
      SchurPresentation.Theorem523BaseNine.a6X⁻¹)
    (hβY : β SchurPresentation.Theorem523BaseNine.a6Y =
      SchurPresentation.Theorem523BaseNine.a6Y) :
    ∃ c : K, c ∈ f.toMonoidHom.ker ∧ c ≠ 1 ∧
      c ∈ Subgroup.center K ∧ c ^ 3 = 1 ∧ orderOf c = 3 ∧ α c = c⁻¹ := by
  obtain ⟨u, v, hu, hv, hcKer, hcNe, hcCenter, hcPow, hcOrder⟩ :=
    exists_a6StandardNine_lifts_commutator_of_kernel_card_six f hker
  let a : K := u⁻¹
  let b : K := v
  have hfa : f a = SchurPresentation.Theorem523BaseNine.a6X⁻¹ := by
    dsimp [a]
    rw [map_inv, hu]
  let za : K := α u * a⁻¹
  let zb : K := α v * b⁻¹
  have hzaKer : za ∈ f.toMonoidHom.ker := by
    rw [MonoidHom.mem_ker]
    change f (α u * a⁻¹) = 1
    rw [map_mul, map_inv, hcompat, hu, hβX, hfa]
    group
  have hzbKer : zb ∈ f.toMonoidHom.ker := by
    rw [MonoidHom.mem_ker]
    change f (α v * b⁻¹) = 1
    rw [map_mul, map_inv, hcompat, hv, hβY]
    group
  have hzaCenter : za ∈ Subgroup.center K := f.ker_le_center hzaKer
  have hzbCenter : zb ∈ Subgroup.center K := f.ker_le_center hzbKer
  have hαu : α u = za * a := by
    dsimp [za]
    group
  have hαv : α v = zb * b := by
    dsimp [zb, b]
    group
  refine ⟨⁅u, v⁆, hcKer, hcNe, hcCenter, hcPow, hcOrder, ?_⟩
  rw [map_commutatorElement, hαu, hαv,
    commutatorElement_central_mul_left za a (zb * b) hzaCenter,
    commutatorElement_central_mul_right a zb b hzbCenter]
  exact commutatorElement_inv_left_of_mem_center u v hcCenter

end GLS3.Chapter5
/- END Theory.SixCoverA6NaturalCenterThreeInversion -/

/- BEGIN Theory.A7CenterThreeInversion -/
noncomputable section

namespace GLS3.Chapter5

open scoped commutatorElement

/-- A lift of the standard reflection on `E₉` inverts a nontrivial central
element of order three in every `A₇` cover whose kernel has order three or
six. -/
public theorem a7_exists_center_orderThree_inverted_of_reflection
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (f : Covering K (alternatingGroup (Fin 7)))
    (hker : Nat.card f.toMonoidHom.ker = 3 ∨
      Nat.card f.toMonoidHom.ker = 6)
    (α : MulAut K) (β : MulAut (alternatingGroup (Fin 7)))
    (hcompat : ∀ k : K, f (α k) = β (f k))
    (hβX : β SchurPresentation.Theorem523BaseNine.a7X =
      SchurPresentation.Theorem523BaseNine.a7X⁻¹)
    (hβY : β SchurPresentation.Theorem523BaseNine.a7Y =
      SchurPresentation.Theorem523BaseNine.a7Y) :
    ∃ c : K, c ∈ f.toMonoidHom.ker ∧ c ≠ 1 ∧
      c ∈ Subgroup.center K ∧ c ^ 3 = 1 ∧ orderOf c = 3 ∧ α c = c⁻¹ := by
  obtain ⟨u, v, hu, hv, hcKer, hcNe, hcCenter, hcPow, hcOrder⟩ :=
    exists_a7StandardNine_lifts_commutator f hker
  let a : K := u⁻¹
  let b : K := v
  have hfa : f a = SchurPresentation.Theorem523BaseNine.a7X⁻¹ := by
    dsimp [a]
    rw [map_inv, hu]
  let za : K := α u * a⁻¹
  let zb : K := α v * b⁻¹
  have hzaKer : za ∈ f.toMonoidHom.ker := by
    rw [MonoidHom.mem_ker]
    change f (α u * a⁻¹) = 1
    rw [map_mul, map_inv, hcompat, hu, hβX, hfa]
    group
  have hzbKer : zb ∈ f.toMonoidHom.ker := by
    rw [MonoidHom.mem_ker]
    change f (α v * b⁻¹) = 1
    rw [map_mul, map_inv, hcompat, hv, hβY]
    group
  have hzaCenter : za ∈ Subgroup.center K := f.ker_le_center hzaKer
  have hzbCenter : zb ∈ Subgroup.center K := f.ker_le_center hzbKer
  have hαu : α u = za * a := by
    dsimp [za]
    group
  have hαv : α v = zb * b := by
    dsimp [zb, b]
    group
  refine ⟨⁅u, v⁆, hcKer, hcNe, hcCenter, hcPow, hcOrder, ?_⟩
  rw [map_commutatorElement, hαu, hαv,
    commutatorElement_central_mul_left za a (zb * b) hzaCenter,
    commutatorElement_central_mul_right a zb b hzbCenter]
  exact commutatorElement_inv_left_of_mem_center u v hcCenter

end GLS3.Chapter5
/- END Theory.A7CenterThreeInversion -/

/- BEGIN Theory.SchurSupportTwoNoncommutingWitnessForLift -/
noncomputable section

namespace GLS3.Chapter5.SchurPresentation

/-- A support-two permutation has a noncommuting alternating witness for every
lift in its Schur projection fiber, not only for the chosen permutation lift. -/
public theorem supportTwo_noncommuting_witness_for_lift
    (n : Nat) (w : SchurPresentedGroup n)
    (hsupport : (schurSymmetricProjection n w).support.card = 2) :
    ∃ y : SchurAlternatingGroup n,
      Commute (schurSymmetricProjection n w)
        (schurAlternatingProjection n y).1 ∧
      ¬ Commute w y.1 := by
  let x := schurSymmetricProjection n w
  let p := permutationLift n x
  obtain ⟨y, hxy, hpy⟩ :=
    supportTwo_noncommuting_alternating_witness n x hsupport
  refine ⟨y, by simpa [x, p, permutationLift_projection] using hxy, ?_⟩
  let d := w * p⁻¹
  have hdker : d ∈ (schurSymmetricProjection n).ker := by
    rw [MonoidHom.mem_ker]
    simp [d, p, x, permutationLift_projection]
  have hdcenter : d ∈ Subgroup.center (SchurPresentedGroup n) := by
    rw [schurSymmetricProjection_ker_eq_zpowers] at hdker
    exact (Subgroup.zpowers_le.mpr (schurCentral_mem_center n)) hdker
  intro hwy
  apply hpy
  have hdy : Commute d y.1 :=
    (Subgroup.mem_center_iff.mp hdcenter y.1).symm
  have hproduct : Commute (d⁻¹ * w) y.1 :=
    Commute.mul_left hdy.inv_left hwy
  simpa [d, p] using hproduct

end GLS3.Chapter5.SchurPresentation
/- END Theory.SchurSupportTwoNoncommutingWitnessForLift -/

/- BEGIN Theory.InvolutionLiftSquare -/
noncomputable section

namespace GLS3.Chapter5.SchurPresentation

/-- In the explicit alternating double cover, every lift of an involution
moving `4m` points has square `z^m`. -/
public theorem involutionLift_sq_of_support_card
    (n m : Nat) (hm : 1 ≤ m) (h4m : 4 * m ≤ n + 5)
    (σ : alternatingGroup (Fin (n + 5))) (hσorder : orderOf σ = 2)
    (hsupport : σ.1.support.card = 4 * m)
    (x : SchurAlternatingGroup n)
    (hxproj : schurAlternatingProjection n x = σ) :
    x ^ 2 = schurAlternatingCentral n ^ m := by
  let y := canonicalLift n m h4m
  let ybar := schurAlternatingProjection n y
  have hσsqAlt : σ ^ 2 = 1 := by
    simpa [hσorder] using pow_orderOf_eq_one σ
  have hσsq : σ.1 ^ 2 = 1 := congrArg Subtype.val hσsqAlt
  have hybarOrder : orderOf ybar = 2 :=
    canonicalLift_proj_order_two n m h4m hm
  have hybarSq : ybar.1 ^ 2 = 1 := by
    exact congrArg Subtype.val
      (by simpa [hybarOrder] using pow_orderOf_eq_one ybar)
  have hsupportY : ybar.1.support.card = 4 * m := by
    rw [show ybar.1 = canonicalPerm n m h4m by
      exact canonicalLift_proj n m h4m]
    exact canonicalPerm_support_card n m h4m
  have hσne : σ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hσorder
    norm_num at hσorder
  have hconj : IsConj σ ybar :=
    alternating_involution_isConj_of_card_support_eq hσsq hybarSq hσne
      (hsupport.trans hsupportY.symm)
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hker : Nat.card (schurAlternatingProjection n).ker = 2 := by
    simpa [schurAlternatingCovering] using
      natCard_ker_schurAlternatingCovering n
  have hxCoverSq : schurAlternatingCovering n x ^ 2 = 1 := by
    change schurAlternatingProjection n x ^ 2 = 1
    rw [hxproj]
    exact hσsqAlt
  have hsquare : x ^ 2 = y ^ 2 :=
    DoubleCoverUniqueness.sq_eq_sq_of_conjugate_images
      (schurAlternatingCovering n) hker hxCoverSq (by
        change c * schurAlternatingProjection n x * c⁻¹ =
          schurAlternatingProjection n y
        rw [hxproj]
        exact hc)
  exact hsquare.trans (canonicalLift_sq n m h4m)

end GLS3.Chapter5.SchurPresentation
/- END Theory.InvolutionLiftSquare -/

/- BEGIN Theory.A7OuterCenterThreeInversion -/
noncomputable section

namespace GLS3.Chapter5

/-- Every non-inner automorphism compatible with an `A₇` covering action
inverts a nontrivial central element of order three when the covering kernel
has order three or six. -/
public theorem a7_outer_exists_center_orderThree_inverted
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (f : Covering K (alternatingGroup (Fin 7)))
    (hker : Nat.card f.toMonoidHom.ker = 3 ∨
      Nat.card f.toMonoidHom.ker = 6)
    (x : MulAut K) (β : MulAut (alternatingGroup (Fin 7)))
    (hcompat : ∀ k : K, f (x k) = β (f k))
    (hxNoninner : ∀ k : K, x ≠ MulAut.conj k) :
    ∃ c : K, c ∈ f.toMonoidHom.ker ∧ c ≠ 1 ∧
      c ∈ Subgroup.center K ∧ c ^ 3 = 1 ∧ orderOf c = 3 ∧ x c = c⁻¹ := by
  have hβNoninner : ∀ g : alternatingGroup (Fin 7), β ≠ MulAut.conj g :=
    coveringQuotientAction_noninner_of_noninner f x β hcompat hxNoninner
  obtain ⟨δ, hX, hY⟩ :=
    a7_noninner_standardNine_reflection_normalForm β hβNoninner
  obtain ⟨d, hd⟩ := f.surjective δ
  change f d = δ at hd
  let α : MulAut K := MulAut.conj d * x
  let γ : MulAut (alternatingGroup (Fin 7)) := MulAut.conj δ * β
  have hαcompat : ∀ k : K, f (α k) = γ (f k) := by
    intro k
    change f (d * x k * d⁻¹) = δ * β (f k) * δ⁻¹
    rw [map_mul, map_inv, map_mul, hd, hcompat]
  obtain ⟨c, hcKer, hcNe, hcCenter, hcPow, hcOrder, hαc⟩ :=
    a7_exists_center_orderThree_inverted_of_reflection
      f hker α γ hαcompat hX hY
  have hxcCenter : x c ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := x.surjective g
    simpa [map_mul] using congrArg x (Subgroup.mem_center_iff.mp hcCenter g)
  have hαcEq : α c = x c := by
    dsimp [α]
    have hcomm : Commute d (x c) :=
      Subgroup.mem_center_iff.mp hxcCenter d
    rw [hcomm.eq, mul_inv_cancel_right]
  exact ⟨c, hcKer, hcNe, hcCenter, hcPow, hcOrder,
    hαcEq.symm.trans hαc⟩

end GLS3.Chapter5
/- END Theory.A7OuterCenterThreeInversion -/

/- BEGIN Theory.DoubleCoverInvolutionLiftSquare -/
noncomputable section

namespace GLS3.Chapter5.SchurPresentation

/-- In an arbitrary Schur double cover, the square of a lift of an involution
moving `4m` points is the `m`-th power of the unique nontrivial kernel
element. -/
public theorem doubleCoverInvolutionLift_sq_of_support_card
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    (m : Nat) (hm : 1 ≤ m)
    (σ : alternatingGroup (Fin (n + 5))) (hσorder : orderOf σ = 2)
    (hsupport : σ.1.support.card = 4 * m)
    (x : G) (hxproj : f x = σ) :
    x ^ 2 =
      ((DoubleCoverUniqueness.kernelInvolution f.toMonoidHom hcard :
        f.toMonoidHom.ker) : G) ^ m := by
  have h4m : 4 * m ≤ n + 5 := by
    rw [← hsupport]
    simpa using Finset.card_le_univ σ.1.support
  obtain ⟨e, he, _⟩ := theorem_5_2_3_a_2 n f
    (schurAlternatingCovering n) hcard
    (natCard_ker_schurAlternatingCovering n)
  let z : G :=
    (DoubleCoverUniqueness.kernelInvolution f.toMonoidHom hcard :
      f.toMonoidHom.ker)
  have hzKer : z ∈ f.toMonoidHom.ker :=
    (DoubleCoverUniqueness.kernelInvolution f.toMonoidHom hcard).2
  have hezKer : e z ∈ (schurAlternatingProjection n).ker := by
    rw [MonoidHom.mem_ker]
    have heval := DFunLike.congr_fun he z
    change schurAlternatingProjection n (e z) = f z at heval
    rw [heval]
    exact MonoidHom.mem_ker.mp hzKer
  have hezNe : e z ≠ 1 := by
    intro hez
    apply DoubleCoverUniqueness.kernelInvolution_ne_one f.toMonoidHom hcard
    apply Subtype.ext
    change z = 1
    apply e.injective
    simpa using hez
  have hcentralKer : schurAlternatingCentral n ∈
      (schurAlternatingProjection n).ker := by
    rw [schurAlternatingProjection_ker_eq_zpowers]
    exact Subgroup.mem_zpowers _
  have hcentralNe : schurAlternatingCentral n ≠ 1 :=
    schurAlternatingCentral_ne_one n
  have hezEq : e z = schurAlternatingCentral n := by
    let ez : (schurAlternatingProjection n).ker := ⟨e z, hezKer⟩
    let c : (schurAlternatingProjection n).ker :=
      ⟨schurAlternatingCentral n, hcentralKer⟩
    have hezKI := DoubleCoverUniqueness.eq_kernelInvolution_of_ne_one
      (schurAlternatingProjection n)
      (natCard_ker_schurAlternatingCovering n) ez (by
        intro h
        exact hezNe (congrArg Subtype.val h))
    have hcKI := DoubleCoverUniqueness.eq_kernelInvolution_of_ne_one
      (schurAlternatingProjection n)
      (natCard_ker_schurAlternatingCovering n) c (by
        intro h
        exact hcentralNe (congrArg Subtype.val h))
    exact congrArg Subtype.val (hezKI.trans hcKI.symm)
  have hxproj' : schurAlternatingProjection n (e x) = σ := by
    have heval := DFunLike.congr_fun he x
    change schurAlternatingProjection n (e x) = f x at heval
    exact heval.trans hxproj
  have hsquare := involutionLift_sq_of_support_card n m hm h4m σ
    hσorder hsupport (e x) hxproj'
  apply e.injective
  change e (x ^ 2) = e (z ^ m)
  rw [map_pow, map_pow, hezEq]
  exact hsquare

end GLS3.Chapter5.SchurPresentation
/- END Theory.DoubleCoverInvolutionLiftSquare -/

/- BEGIN Theory.SchurCyclePairNoncommutingLifts -/
noncomputable section
namespace GLS3.Chapter5.SchurPresentation
open GLS3.Chapter5
universe __ch5_SchurCyclePairNoncommutingLifts_u

public theorem cyclePair_noncommuting_lifts
    (n : Nat) (x : Equiv.Perm (Fin (n + 5))) (hx : orderOf x = 2)
    (c d : x.cycleFactorsFinset) (hcd : c ≠ d) :
    let e := theorem_5_2_2_d_3_a x (by simpa [hx] using Nat.prime_two)
    let l := e.symm (Equiv.swap c d)
    let v : x.cycleFactorsFinset → Multiplicative (ZMod 2) :=
      fun k => if k = c ∨ k = d then Multiplicative.ofAdd 1 else 1
    let a := (involutionCycleRotationCoordinates x hx).symm v
    ∃ __ch5_SchurCyclePairNoncommutingLifts_u v : SchurAlternatingGroup n,
      schurAlternatingProjection n __ch5_SchurCyclePairNoncommutingLifts_u =
        ⟨l.1.1, Equiv.Perm.mem_alternatingGroup.mpr
          (involutionCyclePermutation_sign x hx l)⟩ ∧
      schurAlternatingProjection n v =
        ⟨(cycleRotationToCentralizer x a).1,
          Equiv.Perm.mem_alternatingGroup.mpr
            (involutionTwoCycleRotation_sign x hx c d hcd)⟩ ∧
      ¬ Commute __ch5_SchurCyclePairNoncommutingLifts_u v := by
  dsimp only
  let hp : (orderOf x).Prime := by simpa [hx] using Nat.prime_two
  let e := theorem_5_2_2_d_3_a x hp
  let l := e.symm (Equiv.swap c d)
  let vcoord : x.cycleFactorsFinset → Multiplicative (ZMod 2) :=
    fun k => if k = c ∨ k = d then Multiplicative.ofAdd 1 else 1
  let a := (involutionCycleRotationCoordinates x hx).symm vcoord
  let ρ := cycleRotationToCentralizer x a
  have hlSign : Equiv.Perm.sign l.1.1 = 1 := involutionCyclePermutation_sign x hx l
  have hρSign : Equiv.Perm.sign ρ.1 = 1 := by
    simpa [vcoord, a, ρ] using involutionTwoCycleRotation_sign x hx c d hcd
  let lA : alternatingGroup (Fin (n + 5)) :=
    ⟨l.1.1, Equiv.Perm.mem_alternatingGroup.mpr hlSign⟩
  let ρA : alternatingGroup (Fin (n + 5)) :=
    ⟨ρ.1, Equiv.Perm.mem_alternatingGroup.mpr hρSign⟩
  let pA : alternatingGroup (Fin (n + 5)) := lA * ρA
  have hl2 : l ^ 2 = 1 := by
    apply e.injective
    simp [l, pow_two]
  have hlA2 : lA ^ 2 = 1 := by
    apply Subtype.ext
    exact congrArg (fun z : cyclePermutationSubgroup x => z.1.1) hl2
  have ha2 : a ^ 2 = 1 := by
    simpa [hx] using cycleRotationGroup_pow_orderOf_eq_one_of_primeOrder x hp a
  have hρA2 : ρA ^ 2 = 1 := by
    apply Subtype.ext
    change ρ.1 ^ 2 = 1
    change (cycleRotationToCentralizer x a).1 ^ 2 = 1
    rw [cycleRotationToCentralizer_pow_coe x a 2, ha2, map_one]
    rfl
  have hcomm : Commute lA ρA := by
    rw [commute_iff_eq]
    apply Subtype.ext
    exact (involutionCycleSwap_commute_twoCycleRotation x hx c d hcd).eq
  have hpA2 : pA ^ 2 = 1 := by
    exact hcomm.mul_pow 2 |>.trans (by rw [hlA2, hρA2, one_mul])
  have hlCard : lA.1.support.card = 4 := by
    simpa [lA, e, l] using involutionCycleSwap_support_card x hx c d hcd
  have hρCard : ρA.1.support.card = 4 := by
    simpa [ρA, ρ, vcoord, a] using involutionTwoCycleRotation_support_card x hx c d hcd
  have hpCard : pA.1.support.card = 4 := by
    simpa [pA, lA, ρA, e, l, ρ, vcoord, a] using
      involutionCycleSwapRotationProduct_support_card x hx c d hcd
  have hlNe : lA ≠ 1 := by
    intro h
    have hval : lA.1 = 1 := congrArg Subtype.val h
    rw [hval] at hlCard
    simp at hlCard
  have hρNe : ρA ≠ 1 := by
    intro h
    have hval : ρA.1 = 1 := congrArg Subtype.val h
    rw [hval] at hρCard
    simp at hρCard
  have hpNe : pA ≠ 1 := by
    intro h
    have hval : pA.1 = 1 := congrArg Subtype.val h
    rw [hval] at hpCard
    simp at hpCard
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hlOrder : orderOf lA = 2 := orderOf_eq_prime hlA2 hlNe
  have hρOrder : orderOf ρA = 2 := orderOf_eq_prime hρA2 hρNe
  have hpOrder : orderOf pA = 2 := orderOf_eq_prime hpA2 hpNe
  have h4 : 4 ≤ n + 5 := by
    rw [← hlCard]
    simpa using Finset.card_le_univ lA.1.support
  obtain ⟨__ch5_SchurCyclePairNoncommutingLifts_u, hu⟩ := schurAlternatingProjection_surjective n lA
  obtain ⟨v, hv⟩ := schurAlternatingProjection_surjective n ρA
  have hu2 : __ch5_SchurCyclePairNoncommutingLifts_u ^ 2 = schurAlternatingCentral n := by
    simpa using involutionLift_sq_of_support_card n 1 (by omega) h4 lA hlOrder
      (by simpa using hlCard) __ch5_SchurCyclePairNoncommutingLifts_u hu
  have hv2 : v ^ 2 = schurAlternatingCentral n := by
    simpa using involutionLift_sq_of_support_card n 1 (by omega) h4 ρA hρOrder
      (by simpa using hρCard) v hv
  have huvProj : schurAlternatingProjection n (__ch5_SchurCyclePairNoncommutingLifts_u * v) = pA := by
    rw [map_mul, hu, hv]
  have huv2 : (__ch5_SchurCyclePairNoncommutingLifts_u * v) ^ 2 = schurAlternatingCentral n := by
    simpa using involutionLift_sq_of_support_card n 1 (by omega) h4 pA hpOrder
      (by simpa using hpCard) (__ch5_SchurCyclePairNoncommutingLifts_u * v) huvProj
  refine ⟨__ch5_SchurCyclePairNoncommutingLifts_u, v, ?_, ?_, ?_⟩
  · simpa [lA, e, l] using hu
  · simpa [ρA, ρ, vcoord, a] using hv
  · exact not_commute_of_equal_nontrivial_squares __ch5_SchurCyclePairNoncommutingLifts_u v (schurAlternatingCentral n)
      (schurAlternatingCentral_sq n) (schurAlternatingCentral_ne_one n)
      hu2 hv2 huv2

end GLS3.Chapter5.SchurPresentation
/- END Theory.SchurCyclePairNoncommutingLifts -/

/- BEGIN Theory.proposition_5_2_4_e_E4_general -/
noncomputable section

namespace GLS3.Chapter5.SchurPresentation

/-- Proposition 5.2.4(e), arbitrary-cover elementary-abelian case. -/
public theorem proposition_5_2_4_e_E4_general
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n m : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hkerCard : Nat.card f.toMonoidHom.ker = 2)
    (σ : alternatingGroup (Fin (n + 5))) (hσorder : orderOf σ = 2)
    (hm : 1 ≤ m) (hsupport : σ.1.support.card = 4 * m)
    (heven : Even m) :
    Nonempty (↥((Subgroup.zpowers σ).comap f.toMonoidHom) ≃*
      Multiplicative (ZMod 2 × ZMod 2)) := by
  have h4m : 4 * m ≤ n + 5 := by
    rw [← hsupport]
    simpa using Finset.card_le_univ σ.1.support
  obtain ⟨e⟩ := nonempty_doubleCoverPreimageMulEquiv n f hkerCard
    (Subgroup.zpowers σ)
  obtain ⟨x, hxcover⟩ := (schurAlternatingCovering n).surjective σ
  have hxproj : schurAlternatingProjection n x = σ := hxcover
  have hxsq : x ^ 2 = 1 := by
    rw [involutionLift_sq_of_support_card n m hm h4m σ hσorder
      hsupport x hxproj]
    exact central_pow_of_even n heven
  have hxne : x ≠ 1 := by
    intro h
    have hmap := congrArg (schurAlternatingProjection n) h
    rw [hxproj, map_one] at hmap
    have hσne : σ ≠ 1 := by
      intro hσ
      rw [hσ, orderOf_one] at hσorder
      norm_num at hσorder
    exact hσne hmap
  let Lx := InvolutionPreimage.involutionPreimage n x
  have hxorder : orderOf (schurAlternatingProjection n x) = 2 := by
    rw [hxproj]
    exact hσorder
  let : IsKleinFour Lx :=
    InvolutionPreimage.involutionPreimage_kleinFour n hxorder hxsq hxne
  obtain ⟨d⟩ := IsKleinFour.nonempty_mulEquiv
    (G₁ := Lx) (G₂ := Multiplicative (ZMod 2 × ZMod 2))
  have hL : (Subgroup.zpowers σ).comap (schurAlternatingProjection n) = Lx := by
    ext w
    change schurAlternatingProjection n w ∈ Subgroup.zpowers σ ↔
      schurAlternatingProjection n w ∈
        Subgroup.zpowers (schurAlternatingProjection n x)
    rw [hxproj]
  exact ⟨e.trans ((MulEquiv.subgroupCongr hL).trans d)⟩

end GLS3.Chapter5.SchurPresentation
/- END Theory.proposition_5_2_4_e_E4_general -/

/- BEGIN Theory.RootInvolutionLiftsNotCommute -/
noncomputable section

namespace GLS3.Chapter5.SchurPresentation

/-- Lifts of two root involutions whose product is again a root involution do
not commute in an arbitrary Schur double cover. -/
public theorem rootInvolutionLifts_not_commute
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    (u v : G)
    (huOrder : orderOf (f u) = 2) (hvOrder : orderOf (f v) = 2)
    (huvOrder : orderOf (f (u * v)) = 2)
    (huSupport : (f u).1.support.card = 4)
    (hvSupport : (f v).1.support.card = 4)
    (huvSupport : (f (u * v)).1.support.card = 4) :
    ¬ Commute u v := by
  let z : G :=
    (DoubleCoverUniqueness.kernelInvolution f.toMonoidHom hcard :
      f.toMonoidHom.ker)
  have hz2 : z ^ 2 = 1 :=
    DoubleCoverUniqueness.kernelInvolution_sq f.toMonoidHom hcard
  have hzne : z ≠ 1 := by
    intro hz
    apply DoubleCoverUniqueness.kernelInvolution_ne_one f.toMonoidHom hcard
    exact Subtype.ext hz
  have hu2 : u ^ 2 = z := by
    simpa [z] using doubleCoverInvolutionLift_sq_of_support_card
      n f hcard 1 (by omega) (f u) huOrder (by simpa using huSupport) u rfl
  have hv2 : v ^ 2 = z := by
    simpa [z] using doubleCoverInvolutionLift_sq_of_support_card
      n f hcard 1 (by omega) (f v) hvOrder (by simpa using hvSupport) v rfl
  have huv2 : (u * v) ^ 2 = z := by
    simpa [z] using doubleCoverInvolutionLift_sq_of_support_card
      n f hcard 1 (by omega) (f (u * v)) huvOrder
        (by simpa using huvSupport) (u * v) rfl
  exact not_commute_of_equal_nontrivial_squares u v z hz2 hzne hu2 hv2 huv2

end GLS3.Chapter5.SchurPresentation
/- END Theory.RootInvolutionLiftsNotCommute -/

/- BEGIN Theory.SchurCyclePairNoncommutingWitness -/
noncomputable section
namespace GLS3.Chapter5.SchurPresentation
open GLS3.Chapter5

public theorem cyclePair_noncommuting_witness_for_lift
    (n : Nat) (w : SchurPresentedGroup n)
    (hx : orderOf (schurSymmetricProjection n w) = 2)
    (c d : (schurSymmetricProjection n w).cycleFactorsFinset) (hcd : c ≠ d) :
    ∃ y : SchurAlternatingGroup n,
      Commute (schurSymmetricProjection n w)
        (schurAlternatingProjection n y).1 ∧
      ¬ Commute w y.1 := by
  let x := schurSymmetricProjection n w
  let hp : (orderOf x).Prime := by simpa [x, hx] using Nat.prime_two
  let e := theorem_5_2_2_d_3_a x hp
  let l := e.symm (Equiv.swap c d)
  let vcoord : x.cycleFactorsFinset → Multiplicative (ZMod 2) :=
    fun k => if k = c ∨ k = d then Multiplicative.ofAdd 1 else 1
  let a := (involutionCycleRotationCoordinates x hx).symm vcoord
  let ρ := cycleRotationToCentralizer x a
  obtain ⟨u, v, hu, hv, huv⟩ := cyclePair_noncommuting_lifts n x hx c d hcd
  have huSymm : schurSymmetricProjection n u.1 = l.1.1 := by
    exact congrArg Subtype.val hu
  have hvSymm : schurSymmetricProjection n v.1 = ρ.1 := by
    exact congrArg Subtype.val hv
  have hdisjoint : Equiv.Perm.Disjoint
      (schurSymmetricProjection n u.1)
      (schurSymmetricProjection n (w * v.1)) := by
    rw [huSymm, map_mul, hvSymm]
    simpa [x, e, l, vcoord, a, ρ] using
      involutionRemainder_disjoint_cycleSwap x hx c d hcd
  have huEven : schurSymmetricProjection n u.1 ∈
      alternatingGroup (Fin (n + 5)) := by
    rw [huSymm]
    exact Equiv.Perm.mem_alternatingGroup.mpr
      (involutionCyclePermutation_sign x hx l)
  have huwvComm : Commute u.1 (w * v.1) := by
    apply commutatorElement_eq_one_iff_commute.mp
    exact proposition_5_2_4_f_1 n u.1 (w * v.1) hdisjoint (Or.inl huEven)
  have hwu : ¬ Commute w u.1 := by
    intro hwu
    have huw : Commute u.1 w := hwu.symm
    apply huv
    rw [commute_iff_eq]
    apply Subtype.ext
    have hcancel : w * (u.1 * v.1) = w * (v.1 * u.1) := by
      calc
        w * (u.1 * v.1) = (w * u.1) * v.1 := by simp [mul_assoc]
        _ = (u.1 * w) * v.1 := by rw [huw.eq]
        _ = u.1 * (w * v.1) := by simp [mul_assoc]
        _ = (w * v.1) * u.1 := huwvComm.eq
        _ = w * (v.1 * u.1) := by simp [mul_assoc]
    exact mul_left_cancel hcancel
  refine ⟨u, ?_, hwu⟩
  rw [hu, commute_iff_eq]
  exact (Subgroup.mem_centralizer_singleton_iff.mp l.1.2).symm

end GLS3.Chapter5.SchurPresentation
/- END Theory.SchurCyclePairNoncommutingWitness -/

/- BEGIN Theory.AlternatingEmbeddingPreimageSplit -/
noncomputable section

namespace GLS3.Chapter5.SchurPresentation

open RootFourSubgroup

/-- If an embedded alternating factor sends its standard root involution to an
involution moving eight points, then its full preimage in a Schur double cover
splits over the covering kernel, with the derived subgroup as complement. -/
public theorem alternatingEmbeddingPreimage_kernel_isComplement'_commutator_of_root_support_eight
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n q : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    (j : alternatingGroup (Fin (q + 5)) →*
      alternatingGroup (Fin (n + 5)))
    (hj : Function.Injective j)
    (hrootSupport :
      (j (⟨rho1 q, rho1_mem_alternating q⟩ :
        alternatingGroup (Fin (q + 5)))).1.support.card = 8) :
    let Lbar := j.range
    let E := Lbar.comap f.toMonoidHom
    let jEquiv : alternatingGroup (Fin (q + 5)) ≃* Lbar :=
      MonoidHom.ofInjective hj
    let r : E →* alternatingGroup (Fin (q + 5)) :=
      jEquiv.symm.toMonoidHom.comp
        ((f.toMonoidHom.comp E.subtype).codRestrict Lbar (fun z => z.2))
    r.ker.IsComplement' (_root_.commutator E) := by
  dsimp only
  let Lbar := j.range
  let E := Lbar.comap f.toMonoidHom
  let jEquiv : alternatingGroup (Fin (q + 5)) ≃* Lbar :=
    MonoidHom.ofInjective hj
  let toRange : E →* Lbar :=
    (f.toMonoidHom.comp E.subtype).codRestrict Lbar (fun z => z.2)
  let r : E →* alternatingGroup (Fin (q + 5)) :=
    jEquiv.symm.toMonoidHom.comp toRange
  have hr : Function.Surjective r := by
    intro a
    obtain ⟨g, hg⟩ := f.surjective (j a)
    let gE : E := ⟨g, by
      change f g ∈ j.range
      exact ⟨a, hg.symm⟩⟩
    refine ⟨gE, ?_⟩
    change jEquiv.symm (toRange gE) = a
    apply jEquiv.injective
    rw [jEquiv.apply_symm_apply]
    apply Subtype.ext
    exact hg
  have hrKer : r.ker ≤ Subgroup.center E := by
    intro z hz
    have hfz : (z : G) ∈ f.toMonoidHom.ker := by
      rw [MonoidHom.mem_ker]
      have hz1 := MonoidHom.mem_ker.mp hz
      have hzRange : toRange z = 1 := by
        apply jEquiv.symm.injective
        simpa [r] using hz1
      exact congrArg Subtype.val hzRange
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (f.ker_le_center hfz) y
  let D := _root_.commutator E
  let rD := r.comp D.subtype
  have hcardD : Nat.card rD.ker ≤ 2 := by
    let incl : rD.ker → f.toMonoidHom.ker := fun z =>
      ⟨((z : D) : E), by
        rw [MonoidHom.mem_ker]
        have hz1 := MonoidHom.mem_ker.mp z.2
        have hzRange : toRange ((z : D) : E) = 1 := by
          apply jEquiv.symm.injective
          simpa [rD, r] using hz1
        exact congrArg Subtype.val hzRange⟩
    have hincl : Function.Injective incl := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : f.toMonoidHom.ker => (z : G)) hab
    calc
      Nat.card rD.ker ≤ Nat.card f.toMonoidHom.ker :=
        Nat.card_le_card_of_injective incl hincl
      _ = 2 := hcard
  have hroot : ∀ u : D,
      rD u = (⟨rho1 q, rho1_mem_alternating q⟩ :
        alternatingGroup (Fin (q + 5))) → u ^ 2 = 1 := by
    intro u hu
    let root : alternatingGroup (Fin (q + 5)) :=
      ⟨rho1 q, rho1_mem_alternating q⟩
    let sigma : alternatingGroup (Fin (n + 5)) := j root
    have hfu : f (((u : D) : E) : G) = sigma := by
      have huRange : toRange ((u : D) : E) = jEquiv root := by
        apply jEquiv.symm.injective
        simpa [rD, r, root] using hu
      exact congrArg Subtype.val huRange
    have hsigmaSq : sigma ^ 2 = 1 := by
      have hrootSq : root ^ 2 = 1 := by
        apply Subtype.ext
        simpa [pow_two] using rho1_sq q
      dsimp [sigma]
      rw [← map_pow, hrootSq, map_one]
    have hsigmaNe : sigma ≠ 1 := by
      intro hsigma
      have hval := congrArg (fun z : alternatingGroup (Fin (n + 5)) =>
        z.1.support.card) hsigma
      rw [hrootSupport] at hval
      simp at hval
    have hsigmaOrder : orderOf sigma = 2 :=
      orderOf_eq_prime hsigmaSq hsigmaNe
    obtain ⟨e⟩ := proposition_5_2_4_e_E4_general n 2 f hcard sigma
      hsigmaOrder (by omega) (by simpa [sigma] using hrootSupport) (by decide)
    let uPre : (Subgroup.zpowers sigma).comap f.toMonoidHom :=
      ⟨(((u : D) : E) : G), by
        change f (((u : D) : E) : G) ∈ Subgroup.zpowers sigma
        rw [hfu]
        exact Subgroup.mem_zpowers sigma⟩
    have heSq : e uPre ^ 2 = 1 := by
      rcases e uPre with ⟨a, b⟩
      change Multiplicative.ofAdd (a, b) ^ 2 = 1
      rw [pow_two]
      change Multiplicative.ofAdd ((a, b) + (a, b)) = Multiplicative.ofAdd 0
      apply Multiplicative.ofAdd.injective
      simp [ZModModule.add_self]
    have huPreSq : uPre ^ 2 = 1 := by
      apply e.injective
      simpa only [map_pow, map_one] using heSq
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : (Subgroup.zpowers sigma).comap f.toMonoidHom =>
      (z : G)) huPreSq
  have hbot : rD.ker = ⊥ :=
    derivedKernel_eq_bot_of_root_lifts_sq_one q r hr hrKer hcardD hroot
  exact projectionKernel_isComplement'_commutator_of_derivedKernel_eq_bot
    r hr hbot

end GLS3.Chapter5.SchurPresentation
/- END Theory.AlternatingEmbeddingPreimageSplit -/

/- BEGIN Theory.InvolutionCycleAlternatingPreimageSplitFour -/
noncomputable section

namespace GLS3.Chapter5.SchurPresentation

open GLS3.Chapter5

/-- When an involution has exactly four nontrivial cycles, the full preimage of
its alternating cycle-permutation factor splits over the Schur kernel. -/
public theorem involutionCycleAlternatingPreimageFour_kernel_isComplement'
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    (x : Equiv.Perm (Fin (n + 5))) (hx : orderOf x = 2)
    (eFin : x.cycleFactorsFinset ≃ Fin 4) :
    let j := (involutionCycleAlternatingEmbedding x hx).comp
      eFin.altCongrHom.symm.toMonoidHom
    let Lbar := j.range
    let E := Lbar.comap f.toMonoidHom
    let jEquiv : alternatingGroup (Fin 4) ≃* Lbar :=
      MonoidHom.ofInjective
        (involutionCycleAlternatingEmbedding_comp_altCongr_injective x hx eFin)
    let r : E →* alternatingGroup (Fin 4) :=
      jEquiv.symm.toMonoidHom.comp
        ((f.toMonoidHom.comp E.subtype).codRestrict Lbar (fun z => z.2))
    ∃ S : Subgroup E, r.ker.IsComplement' S := by
  dsimp only
  let j := (involutionCycleAlternatingEmbedding x hx).comp
    eFin.altCongrHom.symm.toMonoidHom
  let Lbar := j.range
  let E := Lbar.comap f.toMonoidHom
  let jEquiv : alternatingGroup (Fin 4) ≃* Lbar :=
    MonoidHom.ofInjective
      (involutionCycleAlternatingEmbedding_comp_altCongr_injective x hx eFin)
  let toRange : E →* Lbar :=
    (f.toMonoidHom.comp E.subtype).codRestrict Lbar (fun z => z.2)
  let r : E →* alternatingGroup (Fin 4) :=
    jEquiv.symm.toMonoidHom.comp toRange
  have hjSupport (a : alternatingGroup (Fin 4)) :
      (j a).1.support.card = 2 * a.1.support.card := by
    let cycleEquiv := theorem_5_2_2_d_3_a x
      (by simpa [hx] using Nat.prime_two)
    let l : cyclePermutationSubgroup x :=
      cycleEquiv.symm (eFin.altCongrHom.symm a).1
    have h := involutionCyclePermutation_support_card_eq_two_mul x hx l
    change l.1.1.support.card = 2 * (cycleEquiv l).support.card at h
    change ((theorem_5_2_2_d_3_a x
      (by simpa [hx] using Nat.prime_two)).symm
        (eFin.altCongrHom.symm a).1).1.1.support.card =
          2 * a.1.support.card
    change l.1.1.support.card = 2 * a.1.support.card
    rw [h]
    congr 1
    change (cycleEquiv
      (cycleEquiv.symm (eFin.symm.permCongr a.1))).support.card =
        a.1.support.card
    rw [cycleEquiv.apply_symm_apply]
    apply Finset.card_bij (fun i _ => eFin i)
    · intro i hi
      rw [Equiv.Perm.mem_support] at hi ⊢
      intro heq
      apply hi
      rw [Equiv.permCongr_apply, Equiv.symm_symm, heq,
        eFin.symm_apply_apply]
    · intro i hi k hk hik
      exact eFin.injective hik
    · intro i hi
      refine ⟨eFin.symm i, ?_, ?_⟩
      · rw [Equiv.Perm.mem_support] at hi ⊢
        intro heq
        apply hi
        have h := congrArg eFin heq
        simpa [Equiv.permCongr_apply] using h
      · exact eFin.apply_symm_apply i
  have hr : Function.Surjective r := by
    intro a
    obtain ⟨g, hg⟩ := f.surjective (j a)
    let gE : E := ⟨g, by
      change f g ∈ j.range
      exact ⟨a, hg.symm⟩⟩
    refine ⟨gE, ?_⟩
    change jEquiv.symm (toRange gE) = a
    apply jEquiv.injective
    rw [jEquiv.apply_symm_apply]
    apply Subtype.ext
    exact hg
  have hrKerCenter : r.ker ≤ Subgroup.center E := by
    intro z hz
    have hfz : (z : G) ∈ f.toMonoidHom.ker := by
      rw [MonoidHom.mem_ker]
      have hz1 := MonoidHom.mem_ker.mp hz
      have hzRange : toRange z = 1 := by
        apply jEquiv.symm.injective
        simpa [r] using hz1
      exact congrArg Subtype.val hzRange
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (f.ker_le_center hfz) y
  have hrKer : r.ker = f.toMonoidHom.ker.comap E.subtype := by
    ext z
    constructor
    · intro hz
      have hz1 := MonoidHom.mem_ker.mp hz
      have hzRange : toRange z = 1 := by
        apply jEquiv.symm.injective
        simpa [r] using hz1
      exact MonoidHom.mem_ker.mpr (congrArg Subtype.val hzRange)
    · intro hz
      apply MonoidHom.mem_ker.mpr
      change jEquiv.symm (toRange z) = 1
      apply jEquiv.injective
      rw [jEquiv.apply_symm_apply, map_one]
      apply Subtype.ext
      exact MonoidHom.mem_ker.mp hz
  have hrKerCard : Nat.card r.ker = 2 := by
    rw [hrKer]
    let eKer : f.toMonoidHom.ker.comap E.subtype ≃* f.toMonoidHom.ker :=
      { toFun := fun z => ⟨z.1.1, z.2⟩
        invFun := fun z => ⟨⟨z.1, by
          change f z.1 ∈ Lbar
          have hz1 : f z.1 = 1 := MonoidHom.mem_ker.mp z.2
          rw [hz1]
          exact Lbar.one_mem⟩, z.2⟩
        left_inv := fun z => by ext; rfl
        right_inv := fun z => by ext; rfl
        map_mul' := fun _ _ => rfl }
    exact (Nat.card_congr eKer.toEquiv).trans hcard
  have hsquare : ∀ z : E,
      (r z).1.support.card = 4 → z ^ 2 = 1 := by
    intro z hzSupport
    let a : alternatingGroup (Fin 4) := r z
    let sigma : alternatingGroup (Fin (n + 5)) := j a
    have haSq : a ^ 2 = 1 := by
      have hAll : ∀ b : alternatingGroup (Fin 4),
          b.1.support.card = 4 → b ^ 2 = 1 := by decide
      exact hAll a hzSupport
    have hsigmaSq : sigma ^ 2 = 1 := by
      dsimp [sigma]
      rw [← map_pow, haSq, map_one]
    have hsigmaSupport : sigma.1.support.card = 8 := by
      dsimp [sigma]
      rw [hjSupport, hzSupport]
    have hsigmaNe : sigma ≠ 1 := by
      intro hsigma
      have hval := congrArg (fun y : alternatingGroup (Fin (n + 5)) =>
        y.1.support.card) hsigma
      rw [hsigmaSupport] at hval
      simp at hval
    have hsigmaOrder : orderOf sigma = 2 :=
      orderOf_eq_prime hsigmaSq hsigmaNe
    have hfz : f z.1 = sigma := by
      have hzRange : toRange z = jEquiv a := by
        apply jEquiv.symm.injective
        simp [r, a]
      exact congrArg Subtype.val hzRange
    obtain ⟨e⟩ := proposition_5_2_4_e_E4_general n 2 f hcard sigma
      hsigmaOrder (by omega) (by simpa [sigma] using hsigmaSupport) (by decide)
    let zPre : (Subgroup.zpowers sigma).comap f.toMonoidHom :=
      ⟨z.1, by
        change f z.1 ∈ Subgroup.zpowers sigma
        rw [hfz]
        exact Subgroup.mem_zpowers sigma⟩
    have heSq : e zPre ^ 2 = 1 := by
      rcases e zPre with ⟨a, b⟩
      change Multiplicative.ofAdd (a, b) ^ 2 = 1
      rw [pow_two]
      change Multiplicative.ofAdd ((a, b) + (a, b)) = Multiplicative.ofAdd 0
      apply Multiplicative.ofAdd.injective
      simp [ZModModule.add_self]
    have hzPreSq : zPre ^ 2 = 1 := by
      apply e.injective
      simpa only [map_pow, map_one] using heSq
    apply Subtype.ext
    exact congrArg (fun y : (Subgroup.zpowers sigma).comap f.toMonoidHom =>
      (y : G)) hzPreSq
  exact alternatingFour_kernel_isComplement'_of_root_lifts_sq_one
    r hr hrKerCenter hrKerCard hsquare

end GLS3.Chapter5.SchurPresentation
/- END Theory.InvolutionCycleAlternatingPreimageSplitFour -/

/- BEGIN Theory.proposition_5_2_4_e_Z4_general -/
noncomputable section

namespace GLS3.Chapter5.SchurPresentation

/-- Proposition 5.2.4(e), arbitrary-cover cyclic case. -/
public theorem proposition_5_2_4_e_Z4_general
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n m : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hkerCard : Nat.card f.toMonoidHom.ker = 2)
    (σ : alternatingGroup (Fin (n + 5))) (hσorder : orderOf σ = 2)
    (hm : 1 ≤ m) (hsupport : σ.1.support.card = 4 * m)
    (hodd : Odd m) :
    Nonempty (↥((Subgroup.zpowers σ).comap f.toMonoidHom) ≃*
      Multiplicative (ZMod 4)) := by
  have h4m : 4 * m ≤ n + 5 := by
    rw [← hsupport]
    simpa using Finset.card_le_univ σ.1.support
  obtain ⟨e⟩ := nonempty_doubleCoverPreimageMulEquiv n f hkerCard
    (Subgroup.zpowers σ)
  obtain ⟨x, hxcover⟩ := (schurAlternatingCovering n).surjective σ
  have hxproj : schurAlternatingProjection n x = σ := hxcover
  have hxsq : x ^ 2 = schurAlternatingCentral n := by
    rw [involutionLift_sq_of_support_card n m hm h4m σ hσorder
      hsupport x hxproj]
    exact central_pow_of_odd n hodd
  have hxne : x ≠ 1 := by
    intro h
    have hmap := congrArg (schurAlternatingProjection n) h
    rw [hxproj, map_one] at hmap
    have hσne : σ ≠ 1 := by
      intro hσ
      rw [hσ, orderOf_one] at hσorder
      norm_num at hσorder
    exact hσne hmap
  let Lx := InvolutionPreimage.involutionPreimage n x
  have hxorder : orderOf (schurAlternatingProjection n x) = 2 := by
    rw [hxproj]
    exact hσorder
  have hcyc : IsCyclic Lx :=
    InvolutionPreimage.involutionPreimage_cyclic n hxorder hxsq hxne
  have hcardL : Nat.card Lx = 4 :=
    InvolutionPreimage.involutionPreimage_card n hxorder
  have d : Lx ≃* Multiplicative (ZMod 4) :=
    (hcardL ▸ zmodCyclicMulEquiv hcyc).symm
  have hL : (Subgroup.zpowers σ).comap (schurAlternatingProjection n) = Lx := by
    ext w
    change schurAlternatingProjection n w ∈ Subgroup.zpowers σ ↔
      schurAlternatingProjection n w ∈
        Subgroup.zpowers (schurAlternatingProjection n x)
    rw [hxproj]
  exact ⟨e.trans ((MulEquiv.subgroupCongr hL).trans d)⟩

end GLS3.Chapter5.SchurPresentation
/- END Theory.proposition_5_2_4_e_Z4_general -/

/- BEGIN Theory.NonconstantTraceZeroRotationLift -/
noncomputable section
namespace GLS3.Chapter5.SchurPresentation

open GLS3.Chapter5

/-- A lift of a nonzero, nonconstant trace-zero involution rotation is not
central in the full preimage of the trace-zero rotation subgroup. -/
public theorem nonconstantTraceZeroRotationLift_noncommuting_witness
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    (x : Equiv.Perm (Fin (n + 5))) (hx : orderOf x = 2)
    (r : Nat) (e : x.cycleFactorsFinset ≃ Fin r)
    (w : evenInvolutionCycleRotations x) (y : G)
    (hy : f y = evenInvolutionCycleRotationToAlternating x w)
    (hzero : (Multiplicative.toAdd
      (evenInvolutionCycleRotations_mulEquiv_traceZero x hx r e w)).1 ≠ 0)
    (hall : (Multiplicative.toAdd
      (evenInvolutionCycleRotations_mulEquiv_traceZero x hx r e w)).1 ≠
        fun _ => 1) :
    ∃ q : G, f q ∈ involutionEvenRotationSubgroup x ∧ ¬ Commute y q := by
  let t : traceZeroTwoSubgroup r :=
    Multiplicative.toAdd
      (evenInvolutionCycleRotations_mulEquiv_traceZero x hx r e w)
  obtain ⟨i, j, k, hij, hik, hjk, hi, hj, hk⟩ :=
    traceZero_exists_two_one_one_zero_coordinates t hzero hall
  let ci := e.symm i
  let cj := e.symm j
  let ck := e.symm k
  have hcij : ci ≠ cj := by
    intro h
    exact hij (e.symm.injective h)
  have hcik : ci ≠ ck := by
    intro h
    exact hik (e.symm.injective h)
  have hcjk : cj ≠ ck := by
    intro h
    exact hjk (e.symm.injective h)
  let E := involutionCycleRotationCoordinates x hx
  let vij : x.cycleFactorsFinset → Multiplicative (ZMod 2) :=
    fun q => if q = ci ∨ q = cj then Multiplicative.ofAdd 1 else 1
  let vik : x.cycleFactorsFinset → Multiplicative (ZMod 2) :=
    fun q => if q = ci ∨ q = ck then Multiplicative.ofAdd 1 else 1
  let a := E.symm vij
  let v := E.symm vik
  have haEven : a ∈ evenInvolutionCycleRotations x := by
    rw [mem_evenInvolutionCycleRotations]
    simpa [a, vij] using involutionTwoCycleRotation_sign x hx ci cj hcij
  have hvEven : v ∈ evenInvolutionCycleRotations x := by
    rw [mem_evenInvolutionCycleRotations]
    simpa [v, vik] using involutionTwoCycleRotation_sign x hx ci ck hcik
  let ae : evenInvolutionCycleRotations x := ⟨a, haEven⟩
  let ve : evenInvolutionCycleRotations x := ⟨v, hvEven⟩
  let aA := evenInvolutionCycleRotationToAlternating x ae
  let vA := evenInvolutionCycleRotationToAlternating x ve
  let vjk : x.cycleFactorsFinset → Multiplicative (ZMod 2) :=
    fun q => if q = cj ∨ q = ck then Multiplicative.ofAdd 1 else 1
  let c := E.symm vjk
  have hcEven : c ∈ evenInvolutionCycleRotations x := by
    rw [mem_evenInvolutionCycleRotations]
    simpa [c, vjk] using involutionTwoCycleRotation_sign x hx cj ck hcjk
  let ce : evenInvolutionCycleRotations x := ⟨c, hcEven⟩
  let cA := evenInvolutionCycleRotationToAlternating x ce
  have hav : a * v = c := by
    simpa [a, v, c, vij, vik, vjk, E] using
      involutionTwoCycleRotation_mul x hx ci cj ck hcij hcik hcjk
  have haAvA : aA * vA = cA := by
    apply Subtype.ext
    change (cycleRotationToCentralizer x a).1 *
        (cycleRotationToCentralizer x v).1 =
      (cycleRotationToCentralizer x c).1
    simpa using congrArg (fun q : CycleRotationGroup x =>
      (cycleRotationToCentralizer x q).1) hav
  obtain ⟨aLift, haLift⟩ := f.surjective aA
  obtain ⟨vLift, hvLift⟩ := f.surjective vA
  have haLift' : f aLift = aA := haLift
  have hvLift' : f vLift = vA := hvLift
  let bLift := aLift⁻¹ * y
  have hcoordW (q : Fin r) :
      Multiplicative.toAdd (E w.1 (e.symm q)) = t.1 q := by
    symm
    exact evenInvolutionCycleRotations_mulEquiv_traceZero_apply x hx r e w q
  have hawi : E w.1 ci = Multiplicative.ofAdd 1 := by
    apply Multiplicative.toAdd.injective
    simpa [ci, t] using (hcoordW i).trans hi
  have hawj : E w.1 cj = Multiplicative.ofAdd 1 := by
    apply Multiplicative.toAdd.injective
    simpa [cj, t] using (hcoordW j).trans hj
  have hawk : E w.1 ck = 1 := by
    apply Multiplicative.toAdd.injective
    simpa [ck, t] using (hcoordW k).trans hk
  have hai : E a ci = Multiplicative.ofAdd 1 := by
    simpa [a, vij, E] using congrFun (E.apply_symm_apply vij) ci
  have haj : E a cj = Multiplicative.ofAdd 1 := by
    simpa [a, vij, E, hcij] using congrFun (E.apply_symm_apply vij) cj
  have hak : E a ck = 1 := by
    simpa [a, vij, E, hcik.symm, hcjk.symm] using
      congrFun (E.apply_symm_apply vij) ck
  let be : evenInvolutionCycleRotations x := ae⁻¹ * w
  let b : CycleRotationGroup x := be.1
  have hbDef : b = a⁻¹ * w.1 := rfl
  have hbi : E b ci = 1 := by
    rw [hbDef, map_mul, map_inv, Pi.mul_apply, Pi.inv_apply, hai, hawi]
    apply Multiplicative.toAdd.injective
    exact sub_self 1
  have hbk : E b ck = 1 := by
    rw [hbDef, map_mul, map_inv, Pi.mul_apply, Pi.inv_apply, hak, hawk]
    simp
  have hbDisjoint : Equiv.Perm.Disjoint
      (cycleRotationToCentralizer x b).1
      (cycleRotationToCentralizer x v).1 := by
    simpa [v, vik, E] using
      involutionRotation_disjoint_twoCycleRotation x hx b ci ck hbi hbk
  have hbImage : f bLift = evenInvolutionCycleRotationToAlternating x be := by
    rw [show f bLift = aA⁻¹ * evenInvolutionCycleRotationToAlternating x w by
      simp [bLift, haLift', hy]]
    rw [← map_inv, ← map_mul]
  have hbComm : Commute bLift vLift := by
    apply commutatorElement_eq_one_iff_commute.mp
    apply proposition_5_2_4_f_general_alternating n f hcard bLift vLift
    rw [hbImage, hvLift']
    simpa [be, b, ve, v, vA, evenInvolutionCycleRotationToAlternating] using hbDisjoint
  have haAOrder : orderOf aA = 2 := by
    simpa [aA, ae, a, vij, E, evenInvolutionCycleRotationToAlternating] using
      involutionTwoCycleRotation_orderOf x hx ci cj hcij
  have hvAOrder : orderOf vA = 2 := by
    simpa [vA, ve, v, vik, E, evenInvolutionCycleRotationToAlternating] using
      involutionTwoCycleRotation_orderOf x hx ci ck hcik
  have hcAOrder : orderOf cA = 2 := by
    simpa [cA, ce, c, vjk, E, evenInvolutionCycleRotationToAlternating] using
      involutionTwoCycleRotation_orderOf x hx cj ck hcjk
  have haOrder : orderOf (f aLift) = 2 := haLift' ▸ haAOrder
  have hvOrder : orderOf (f vLift) = 2 := hvLift' ▸ hvAOrder
  have havOrder : orderOf (f (aLift * vLift)) = 2 := by
    rw [map_mul, haLift', hvLift', haAvA]
    exact hcAOrder
  have haSupport : (f aLift).1.support.card = 4 := by
    rw [haLift']
    simpa [aA, ae, a, vij, E, evenInvolutionCycleRotationToAlternating] using
      involutionTwoCycleRotation_support_card x hx ci cj hcij
  have hvSupport : (f vLift).1.support.card = 4 := by
    rw [hvLift']
    simpa [vA, ve, v, vik, E, evenInvolutionCycleRotationToAlternating] using
      involutionTwoCycleRotation_support_card x hx ci ck hcik
  have hcSupport : cA.1.support.card = 4 := by
    simpa [cA, ce, c, vjk, E, evenInvolutionCycleRotationToAlternating] using
      involutionTwoCycleRotation_support_card x hx cj ck hcjk
  have havSupport : (f (aLift * vLift)).1.support.card = 4 := by
    rw [map_mul, haLift', hvLift', haAvA]
    exact hcSupport
  have havNot : ¬ Commute aLift vLift :=
    rootInvolutionLifts_not_commute n f hcard aLift vLift
      haOrder hvOrder havOrder haSupport hvSupport havSupport
  refine ⟨vLift, ?_, ?_⟩
  · exact ⟨ve, hvLift'.symm⟩
  · apply not_commute_of_image_eq_mul_of_central_kernel
      f.toMonoidHom f.ker_le_center y aLift bLift vLift
    · simp [bLift]
    · exact hbComm
    · exact havNot

end GLS3.Chapter5.SchurPresentation
/- END Theory.NonconstantTraceZeroRotationLift -/

/- BEGIN Theory.SchurInvolutionNoncommutingWitness -/
noncomputable section

namespace GLS3.Chapter5.SchurPresentation

/-- Every involution in the symmetric quotient of the Schur presentation has
an alternating quotient-centralizing witness that does not commute upstairs. -/
public theorem schurInvolution_noncommuting_witness
    (n : Nat) (w : SchurPresentedGroup n)
    (hx : orderOf (schurSymmetricProjection n w) = 2) :
    ∃ y : SchurAlternatingGroup n,
      Commute (schurSymmetricProjection n w)
        (schurAlternatingProjection n y).1 ∧
      ¬ Commute w y.1 := by
  let x := schurSymmetricProjection n w
  have hx' : orderOf x = 2 := by simpa [x] using hx
  by_cases hsub : Subsingleton x.cycleFactorsFinset
  · have : Subsingleton x.cycleFactorsFinset := hsub
    have hsq : x ^ 2 = 1 := by
      simpa only [hx'] using pow_orderOf_eq_one x
    have hxne : x ≠ 1 := by
      intro h
      have hone : orderOf x = 1 := orderOf_eq_one_iff.mpr h
      rw [hx'] at hone
      omega
    have hcycles : x.cycleFactorsFinset.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro h
      exact hxne (Equiv.Perm.cycleFactorsFinset_eq_empty_iff.mp h)
    obtain ⟨c, hc⟩ := hcycles
    let c' : x.cycleFactorsFinset := ⟨c, hc⟩
    have hcardCycles : Fintype.card x.cycleFactorsFinset = 1 := by
      exact Fintype.card_eq_one_iff.mpr
        ⟨c', fun b => Subsingleton.elim _ _⟩
    have hct := Equiv.Perm.cycleType_of_pow_prime_eq_one hsq
    have hsupport : x.support.card = 2 * x.cycleType.card := by
      rw [← Equiv.Perm.sum_cycleType, hct]
      simp [Nat.mul_comm]
    have hcycleTypeCard : x.cycleType.card = 1 := by
      simpa [Equiv.Perm.cycleType_def] using hcardCycles
    apply supportTwo_noncommuting_witness_for_lift n w
    simpa [x, hcycleTypeCard] using hsupport
  · have : Nontrivial x.cycleFactorsFinset :=
      not_subsingleton_iff_nontrivial.mp hsub
    obtain ⟨c, d, hcd⟩ := exists_pair_ne x.cycleFactorsFinset
    exact cyclePair_noncommuting_witness_for_lift n w hx c d hcd

end GLS3.Chapter5.SchurPresentation
/- END Theory.SchurInvolutionNoncommutingWitness -/

/- BEGIN Theory.InvolutionCycleAlternatingPreimageSplit -/
noncomputable section

namespace GLS3.Chapter5.SchurPresentation

open GLS3.Chapter5

/-- For at least five nontrivial cycles, the full preimage of the alternating
cycle-permutation factor splits over the central kernel. -/
public theorem involutionCycleAlternatingPreimage_kernel_isComplement'_commutator
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n q : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    (x : Equiv.Perm (Fin (n + 5))) (hx : orderOf x = 2)
    (eFin : x.cycleFactorsFinset ≃ Fin (q + 5)) :
    let j := involutionCycleAlternatingEmbeddingFin x hx q eFin
    let Lbar := j.range
    let E := Lbar.comap f.toMonoidHom
    let jEquiv : alternatingGroup (Fin (q + 5)) ≃* Lbar :=
      MonoidHom.ofInjective
        (involutionCycleAlternatingEmbeddingFin_injective x hx q eFin)
    let r : E →* alternatingGroup (Fin (q + 5)) :=
      jEquiv.symm.toMonoidHom.comp
        ((f.toMonoidHom.comp E.subtype).codRestrict Lbar (fun z => z.2))
    r.ker.IsComplement' (_root_.commutator E) := by
  dsimp only
  apply alternatingEmbeddingPreimage_kernel_isComplement'_commutator_of_root_support_eight
    n q f hcard (involutionCycleAlternatingEmbeddingFin x hx q eFin)
    (involutionCycleAlternatingEmbeddingFin_injective x hx q eFin)
  exact involutionCycleAlternatingEmbeddingFin_root_support_card x hx q eFin

end GLS3.Chapter5.SchurPresentation
/- END Theory.InvolutionCycleAlternatingPreimageSplit -/


/- BEGIN Theory.TraceZeroRotationPreimageCenterClassification -/
noncomputable section
namespace GLS3.Chapter5.SchurPresentation

open GLS3.Chapter5

/-- Every central element of the full preimage of the trace-zero rotation
subgroup maps either to the zero rotation or to the all-one rotation. -/
public theorem traceZeroRotationPreimage_center_classification
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    (x : Equiv.Perm (Fin (n + 5))) (hx : orderOf x = 2)
    (r : Nat) (e : x.cycleFactorsFinset ≃ Fin r) :
    let Rbar := involutionEvenRotationSubgroup x
    let R := Rbar.comap f.toMonoidHom
    ∀ z : Subgroup.center R,
      ∃ w : evenInvolutionCycleRotations x,
        f z.1.1 = evenInvolutionCycleRotationToAlternating x w ∧
        ((Multiplicative.toAdd
          (evenInvolutionCycleRotations_mulEquiv_traceZero x hx r e w)).1 = 0 ∨
         (Multiplicative.toAdd
          (evenInvolutionCycleRotations_mulEquiv_traceZero x hx r e w)).1 =
            fun _ => 1) := by
  dsimp only
  intro z
  obtain ⟨w, hw⟩ := z.1.2
  refine ⟨w, hw.symm, ?_⟩
  by_contra hcases
  push Not at hcases
  obtain ⟨q, hqR, hncomm⟩ :=
    nonconstantTraceZeroRotationLift_noncommuting_witness
      n f hcard x hx r e w z.1.1 hw.symm hcases.1 hcases.2
  have hzcomm := Subgroup.mem_center_iff.mp z.2 ⟨q, hqR⟩
  apply hncomm
  rw [commute_iff_eq]
  exact congrArg Subtype.val hzcomm.symm

end GLS3.Chapter5.SchurPresentation
/- END Theory.TraceZeroRotationPreimageCenterClassification -/

/- BEGIN Theory.proposition_5_2_8_b -/
noncomputable section

namespace GLS3.Chapter5.SchurPresentation

/-- Proposition 5.2.8(b): for an involution in the symmetric overgroup of an
alternating quotient, the fixed subgroup of any Schur double-cover lift has
image of index two and contains a twisted fiber witness. -/
public theorem proposition_5_2_8_b
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    (σ : Equiv.Perm (Fin (n + 5))) (hσ : orderOf σ = 2) :
    let beta : MulAut (alternatingGroup (Fin (n + 5))) :=
      MulAut.conjNormal (H := alternatingGroup (Fin (n + 5))) σ
    let alpha : MulAut G := doubleCoverLiftMulAut n f hcard beta
    ∃ _hle : (automorphismFixedSubgroup alpha).map f.toMonoidHom ≤
        automorphismFixedSubgroup beta,
      (((automorphismFixedSubgroup alpha).map f.toMonoidHom).subgroupOf
        (automorphismFixedSubgroup beta)).index = 2 ∧
      ∃ g : G, alpha g =
        (DoubleCoverUniqueness.kernelInvolution f.toMonoidHom hcard : G) * g := by
  dsimp only
  let beta : MulAut (alternatingGroup (Fin (n + 5))) :=
    MulAut.conjNormal (H := alternatingGroup (Fin (n + 5))) σ
  let alpha : MulAut G := doubleCoverLiftMulAut n f hcard beta
  let w := permutationLift n σ
  have hwOrder : orderOf (schurSymmetricProjection n w) = 2 := by
    simpa [w, permutationLift_projection] using hσ
  obtain ⟨y, hquot, hnoncomm⟩ :=
    schurInvolution_noncommuting_witness n w hwOrder
  let alphaA : MulAut (SchurAlternatingGroup n) :=
    doubleCoverLiftMulAut n (schurAlternatingCovering n)
      (natCard_ker_schurAlternatingCovering n) beta
  have halphaA : alphaA = schurAlternatingConj n w := by
    simpa [alphaA, beta, w, permutationLift_projection] using
      doubleCoverLiftMulAut_conjNormal_eq_schurAlternatingConj n w
  have hyNotFixedA : alphaA y ≠ y := by
    rw [halphaA]
    intro hy
    apply hnoncomm
    rw [commute_iff_eq]
    have hcoe := congrArg Subtype.val hy
    rw [schurAlternatingConj_apply_coe] at hcoe
    have h := congrArg (fun z : SchurPresentedGroup n => z * w) hcoe
    simpa [mul_assoc] using h
  obtain ⟨e, he, _⟩ := theorem_5_2_3_a_2 n f
    (schurAlternatingCovering n) hcard
    (natCard_ker_schurAlternatingCovering n)
  let g : G := e.symm y
  have he_apply (k : G) : schurAlternatingProjection n (e k) = f k := by
    exact DFunLike.congr_fun he k
  have hintertwine : ∀ k : G, e (alpha k) = alphaA (e k) := by
    exact doubleCoverLiftMulAut_intertwine n f
      (schurAlternatingCovering n) hcard
      (natCard_ker_schurAlternatingCovering n) e he beta
  have hgImage : e g = y := by simp [g]
  have hgNotFixed : alpha g ≠ g := by
    intro hg
    apply hyNotFixedA
    have h := hintertwine g
    rw [hg, hgImage] at h
    exact h.symm
  have hcompat : ∀ k : G, f (alpha k) = beta (f k) := by
    intro k
    have h := congrArg
      (fun q : Covering G (alternatingGroup (Fin (n + 5))) => q k)
      (doubleCoverLiftMulAut_fac n f hcard beta)
    exact h
  have hgFixed : beta (f g) = f g := by
    apply Subtype.ext
    change σ * (f g).1 * σ⁻¹ = (f g).1
    have hfg : f g = schurAlternatingProjection n y := by
      rw [← he_apply g, hgImage]
    rw [hfg]
    have hσw : schurSymmetricProjection n w = σ := by
      simpa [w] using permutationLift_projection n σ
    rw [← hσw, hquot.eq, mul_inv_cancel_right]
  have hgCases := doubleCoverLift_fixed_or_twisted
    f.toMonoidHom hcard alpha beta hcompat g hgFixed
  rcases hgCases with hgFixedUpstairs | hgTwist
  · exact (hgNotFixed hgFixedUpstairs).elim
  · exact involutionFixedSubgroup_index_two_of_twisted_lift
      f.toMonoidHom f.surjective f.ker_le_center hcard
      alpha beta hcompat g hgFixed hgTwist

end GLS3.Chapter5.SchurPresentation
/- END Theory.proposition_5_2_8_b -/

/- BEGIN Theory.InvolutionCycleAlternatingPreimageComplement -/
noncomputable section

namespace GLS3.Chapter5.SchurPresentation

open GLS3.Chapter5

/-- For every number of nontrivial involution cycles, the full preimage of the
alternating cycle-permutation factor splits over the covering kernel. -/
public theorem involutionCycleAlternatingPreimage_kernel_hasComplement
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    (x : Equiv.Perm (Fin (n + 5))) (hx : orderOf x = 2)
    (r : Nat) (eFin : x.cycleFactorsFinset ≃ Fin r) :
    let j := (involutionCycleAlternatingEmbedding x hx).comp
      eFin.altCongrHom.symm.toMonoidHom
    let Lbar := j.range
    let E := Lbar.comap f.toMonoidHom
    let jEquiv : alternatingGroup (Fin r) ≃* Lbar :=
      MonoidHom.ofInjective
        (involutionCycleAlternatingEmbedding_comp_altCongr_injective x hx eFin)
    let p : E →* alternatingGroup (Fin r) :=
      jEquiv.symm.toMonoidHom.comp
        ((f.toMonoidHom.comp E.subtype).codRestrict Lbar (fun z => z.2))
    ∃ S : Subgroup E, p.ker.IsComplement' S := by
  by_cases hr4 : r = 4
  · subst r
    exact involutionCycleAlternatingPreimageFour_kernel_isComplement'
      n f hcard x hx eFin
  by_cases hr5 : 5 ≤ r
  · obtain ⟨q, rfl⟩ : ∃ q, r = q + 5 := by
      exact ⟨r - 5, by omega⟩
    dsimp only
    exact ⟨_root_.commutator _,
      involutionCycleAlternatingPreimage_kernel_isComplement'_commutator
        n q f hcard x hx eFin⟩
  · have hrle : r ≤ 3 := by omega
    dsimp only
    let j := (involutionCycleAlternatingEmbedding x hx).comp
      eFin.altCongrHom.symm.toMonoidHom
    let Lbar := j.range
    let E := Lbar.comap f.toMonoidHom
    let jEquiv : alternatingGroup (Fin r) ≃* Lbar :=
      MonoidHom.ofInjective
        (involutionCycleAlternatingEmbedding_comp_altCongr_injective x hx eFin)
    let toRange : E →* Lbar :=
      (f.toMonoidHom.comp E.subtype).codRestrict Lbar (fun z => z.2)
    let p : E →* alternatingGroup (Fin r) :=
      jEquiv.symm.toMonoidHom.comp toRange
    have hp : Function.Surjective p := by
      intro a
      obtain ⟨g, hg⟩ := f.surjective (j a)
      let gE : E := ⟨g, by
        change f g ∈ j.range
        exact ⟨a, hg.symm⟩⟩
      refine ⟨gE, ?_⟩
      change jEquiv.symm (toRange gE) = a
      apply jEquiv.injective
      rw [jEquiv.apply_symm_apply]
      apply Subtype.ext
      exact hg
    have hpKer : p.ker = f.toMonoidHom.ker.comap E.subtype := by
      ext z
      constructor
      · intro hz
        have hz1 := MonoidHom.mem_ker.mp hz
        have hzRange : toRange z = 1 := by
          apply jEquiv.symm.injective
          simpa [p] using hz1
        exact MonoidHom.mem_ker.mpr (congrArg Subtype.val hzRange)
      · intro hz
        apply MonoidHom.mem_ker.mpr
        change jEquiv.symm (toRange z) = 1
        apply jEquiv.injective
        rw [jEquiv.apply_symm_apply, map_one]
        apply Subtype.ext
        exact MonoidHom.mem_ker.mp hz
    have hpKerCard : Nat.card p.ker = 2 := by
      rw [hpKer]
      let eKer : f.toMonoidHom.ker.comap E.subtype ≃* f.toMonoidHom.ker :=
        { toFun := fun z => ⟨z.1.1, z.2⟩
          invFun := fun z => ⟨⟨z.1, by
            change f z.1 ∈ Lbar
            have hz1 : f z.1 = 1 := MonoidHom.mem_ker.mp z.2
            rw [hz1]
            exact Lbar.one_mem⟩, z.2⟩
          left_inv := fun z => by ext; rfl
          right_inv := fun z => by ext; rfl
          map_mul' := fun _ _ => rfl }
      exact (Nat.card_congr eKer.toEquiv).trans hcard
    have hpIndex : p.ker.index = Nat.card (alternatingGroup (Fin r)) := by
      rw [Subgroup.index_eq_card]
      exact Nat.card_congr
        (QuotientGroup.quotientKerEquivOfSurjective p hp).toEquiv
    have hcop : Nat.Coprime (Nat.card p.ker) p.ker.index := by
      rw [hpKerCard, hpIndex]
      have hrCases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
      rcases hrCases with rfl | rfl | rfl | rfl
      · rw [Nat.card_unique]
        all_goals decide
      · rw [Nat.card_unique]
        all_goals decide
      · rw [nat_card_alternatingGroup, Nat.card_fin]
        all_goals decide
      · rw [nat_card_alternatingGroup, Nat.card_fin]
        all_goals decide
    exact Subgroup.exists_right_complement'_of_coprime hcop

end GLS3.Chapter5.SchurPresentation
/- END Theory.InvolutionCycleAlternatingPreimageComplement -/

/- BEGIN Theory.A6DoubleCoverExceptionalTwistCertificate -/
namespace GLS3.Chapter5

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

public theorem a6TwistedReflectionLift_mem_subgroup :
    a6TwistedReflectionLift ∈ a6DoubleCoverPermutationSubgroup := by
  have h1 : a6DoubleCoverGen1 ∈ a6DoubleCoverPermutationSubgroup :=
    Subgroup.subset_closure (by left; rfl)
  have h2 : a6DoubleCoverGen2 ∈ a6DoubleCoverPermutationSubgroup :=
    Subgroup.subset_closure (by right; rfl)
  have h12 := (a6DoubleCoverPermutationSubgroup).mul_mem h1 h2
  rw [a6TwistedReflectionLift]
  exact (a6DoubleCoverPermutationSubgroup).mul_mem
    ((a6DoubleCoverPermutationSubgroup).mul_mem h1
      ((a6DoubleCoverPermutationSubgroup).pow_mem h12 2))
    ((a6DoubleCoverPermutationSubgroup).inv_mem h1)


@[expose] public def a6TwistedReflectionLiftSub :
    a6DoubleCoverPermutationSubgroup :=
  ⟨a6TwistedReflectionLift, a6TwistedReflectionLift_mem_subgroup⟩


public theorem a6TwistedReflectionLiftSub_sq :
    a6TwistedReflectionLiftSub ^ 2 = a6DoubleCoverCentralSub := by
  apply Subtype.ext
  exact a6TwistedReflectionLift_sq

public theorem a6TwistedReflectionLiftSub_conj :
    a6ExceptionalConjugator⁻¹ * a6TwistedReflectionLiftSub *
        a6ExceptionalConjugator =
      a6DoubleCoverCentralSub * a6TwistedReflectionLiftSub := by
  exact a6TwistedReflectionLift_conj

public theorem a6ExceptionalConjugatorLiftAut_twistsReflection :
    a6ExceptionalConjugatorLiftAut a6TwistedReflectionLiftSub =
      a6DoubleCoverCentralSub * a6TwistedReflectionLiftSub := by
  apply Subtype.ext
  rw [a6ExceptionalConjugatorLiftAut_apply]
  exact a6TwistedReflectionLift_conj

end GLS3.Chapter5

namespace GLS3.Chapter5

@[reducible, expose] public def a6CanonicalReflection : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 1 4 * Equiv.swap 2 5, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide⟩

set_option maxHeartbeats 800000 in
public theorem a6TwistedReflectionLiftSub_blockCoverHom :
    a6DoubleCoverBlockCoverHom a6TwistedReflectionLiftSub =
      a6CanonicalReflection := by
  apply Subtype.ext
  have hsub : a6TwistedReflectionLiftSub =
      a6DoubleCoverGen1Sub * (a6DoubleCoverGen1Sub *
        a6DoubleCoverGen2Sub) ^ 2 * a6DoubleCoverGen1Sub⁻¹ := by
    apply Subtype.ext
    rfl
  simp only [hsub, map_mul, map_pow, map_inv, a6DoubleCoverBlockCoverHom_gen1, a6DoubleCoverBlockCoverHom_gen2]
  decide +kernel

end GLS3.Chapter5
/- END Theory.A6DoubleCoverExceptionalTwistCertificate -/


/- BEGIN Theory.TraceZeroRotationPreimageEvenCenter -/
noncomputable section
namespace GLS3.Chapter5.SchurPresentation

open GLS3.Chapter5

/-- For an even number of involution cycles, the center of the full trace-zero
rotation preimage is the preimage of the subgroup generated by the involution. -/
public theorem traceZeroRotationPreimage_center_eq_fullInvolutionPreimage_of_even
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    (xA : alternatingGroup (Fin (n + 5))) (hx : orderOf xA.1 = 2)
    (r : Nat) (e : xA.1.cycleFactorsFinset ≃ Fin r) (hr : Even r) :
    let Rbar := involutionEvenRotationSubgroup xA.1
    let R := Rbar.comap f.toMonoidHom
    Subgroup.center R =
      ((Subgroup.zpowers xA).comap f.toMonoidHom).comap R.subtype := by
  dsimp only
  let Rbar := involutionEvenRotationSubgroup xA.1
  let R := Rbar.comap f.toMonoidHom
  let E := evenInvolutionCycleRotations_mulEquiv_traceZero xA.1 hx r e
  obtain ⟨wx, hwxImage, hwxCoord⟩ :=
    exists_evenInvolutionFullRotation xA.1 hx r e hr
  apply le_antisymm
  · intro z hz
    obtain ⟨w, hw, hzero | hall⟩ :=
      traceZeroRotationPreimage_center_classification
        n f hcard xA.1 hx r e ⟨z, hz⟩
    · have hEw : E w = 1 := by
        have hadd : Multiplicative.toAdd (E w) = 0 := Subtype.ext hzero
        exact congrArg Multiplicative.ofAdd hadd
      have hw1 : w = 1 := E.injective (by simpa using hEw)
      change f z.1 ∈ Subgroup.zpowers xA
      rw [hw, hw1, map_one]
      exact Subgroup.one_mem _
    · have hE : E w = E wx := by
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        exact hall.trans hwxCoord.symm
      have hwwx : w = wx := E.injective hE
      have hwxA : evenInvolutionCycleRotationToAlternating xA.1 wx = xA :=
        Subtype.ext hwxImage
      change f z.1 ∈ Subgroup.zpowers xA
      rw [hw, hwwx, hwxA]
      exact Subgroup.mem_zpowers xA
  · intro z hz
    apply Subgroup.mem_center_iff.mpr
    intro y
    obtain ⟨a, ha⟩ := y.2
    obtain ⟨u, hu⟩ := f.surjective xA
    change f u = xA at hu
    have huy : Commute u y.1 :=
      involutionLift_commutes_evenRotationLift
        n f hcard xA hx a u y.1 hu ha.symm
    obtain ⟨k, hk⟩ := hz
    have huky : Commute (u ^ k) y.1 := huy.zpow_left k
    have himage : f z.1 = f (u ^ k * 1) := by
      rw [map_mul, map_zpow, map_one, mul_one, hu]
      exact hk.symm
    exact Subtype.ext (commute_of_image_eq_mul_of_central_kernel
      f.toMonoidHom f.ker_le_center z.1 (u ^ k) 1 y.1 himage
      huky (Commute.one_left y.1)).eq.symm

end GLS3.Chapter5.SchurPresentation
/- END Theory.TraceZeroRotationPreimageEvenCenter -/

/- BEGIN Theory.TraceZeroRotationPreimageEvenCenterEquiv -/
namespace GLS3.Chapter5.SchurPresentation

open GLS3.Chapter5

/-- For even cycle count, the center of the trace-zero rotation preimage is
canonically equivalent to the full preimage of the involution subgroup. -/
public theorem traceZeroRotationPreimage_centerMulEquiv_fullInvolutionPreimage
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    (xA : alternatingGroup (Fin (n + 5))) (hx : orderOf xA.1 = 2)
    (r : Nat) (e : xA.1.cycleFactorsFinset ≃ Fin r) (hr : Even r) :
    let Rbar := involutionEvenRotationSubgroup xA.1
    let R := Rbar.comap f.toMonoidHom
    let X := (Subgroup.zpowers xA).comap f.toMonoidHom
    Nonempty (Subgroup.center R ≃* X) := by
  dsimp only
  let Rbar := involutionEvenRotationSubgroup xA.1
  let R := Rbar.comap f.toMonoidHom
  let X := (Subgroup.zpowers xA).comap f.toMonoidHom
  obtain ⟨wx, hwxImage, _⟩ :=
    exists_evenInvolutionFullRotation xA.1 hx r e hr
  have hxMem : xA ∈ Rbar := by
    refine ⟨wx, ?_⟩
    exact Subtype.ext hwxImage
  have hXleR : X ≤ R := by
    intro z hz
    change f z ∈ Rbar
    exact (Subgroup.zpowers_le.mpr hxMem) hz
  have hcenter :=
    traceZeroRotationPreimage_center_eq_fullInvolutionPreimage_of_even
      n f hcard xA hx r e hr
  dsimp only at hcenter
  have hcomap : X.comap R.subtype = X.subgroupOf R := rfl
  rw [hcomap] at hcenter
  exact ⟨(MulEquiv.subgroupCongr hcenter).trans
    (Subgroup.subgroupOfEquivOfLe hXleR)⟩

end GLS3.Chapter5.SchurPresentation
/- END Theory.TraceZeroRotationPreimageEvenCenterEquiv -/

/- BEGIN Theory.TraceZeroRotationPreimageOddCenter -/
noncomputable section
namespace GLS3.Chapter5.SchurPresentation

open GLS3.Chapter5

/-- For an odd number of involution cycles, the center of the full trace-zero
rotation preimage is exactly the covering kernel. -/
public theorem traceZeroRotationPreimage_center_eq_kernel_of_odd
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    (x : Equiv.Perm (Fin (n + 5))) (hx : orderOf x = 2)
    (r : Nat) (e : x.cycleFactorsFinset ≃ Fin r) (hr : Odd r) :
    let Rbar := involutionEvenRotationSubgroup x
    let R := Rbar.comap f.toMonoidHom
    Subgroup.center R = f.toMonoidHom.ker.comap R.subtype := by
  dsimp only
  let Rbar := involutionEvenRotationSubgroup x
  let R := Rbar.comap f.toMonoidHom
  let E := evenInvolutionCycleRotations_mulEquiv_traceZero x hx r e
  apply le_antisymm
  · intro z hz
    obtain ⟨w, hw, hzero | hall⟩ :=
      traceZeroRotationPreimage_center_classification
        n f hcard x hx r e ⟨z, hz⟩
    · apply MonoidHom.mem_ker.mpr
      have hEw : E w = 1 := by
        have hadd : Multiplicative.toAdd (E w) = 0 := Subtype.ext hzero
        exact congrArg Multiplicative.ofAdd hadd
      have hw1 : w = 1 := E.injective (by simpa using hEw)
      simpa [hw1] using hw
    · have hallmem : (fun _ : Fin r => (1 : ZMod 2)) ∈
          traceZeroTwoSubgroup r := by
        rw [← hall]
        exact (Multiplicative.toAdd (E w)).2
      exact ((Nat.not_even_iff_odd.mpr hr)
        ((traceZeroTwoSubgroup_allOne_mem_iff_even r).mp hallmem)).elim
  · intro z hz
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp
      (f.ker_le_center (show z.1 ∈ f.toMonoidHom.ker from hz)) y.1

end GLS3.Chapter5.SchurPresentation
/- END Theory.TraceZeroRotationPreimageOddCenter -/

/- BEGIN Theory.AlternatingSubgroupIndexTwo -/
noncomputable section

namespace GLS3.Chapter5

/-- An embedded alternating group is contained in every index-two subgroup of
its ambient group. This includes the small degrees because the proof uses
three-cycle generation rather than perfectness. -/
public theorem alternatingSubgroup_le_of_index_two
    {V α : Type*} [Group V] [Fintype α] [DecidableEq α]
    (U H : Subgroup V) (hindex : U.index = 2)
    (e : H ≃* alternatingGroup α) : H ≤ U := by
  let P : Subgroup (alternatingGroup α) :=
    U.comap (H.subtype.comp e.symm.toMonoidHom)
  have hPtop : P = ⊤ := by
    apply top_unique
    rw [← alternatingGroup.closure_isThreeCycles_eq_top]
    refine (Subgroup.closure_le P).2 ?_
    intro q hq
    change (e.symm q : H).1 ∈ U
    let a : V := (e.symm q : H).1
    have ha2 : a ^ 2 ∈ U := U.sq_mem_of_index_two hindex a
    have hqOrder : orderOf q = 3 := by
      exact (orderOf_injective (alternatingGroup α).subtype
        (Subgroup.subtype_injective _) q).symm.trans hq.orderOf
    have hq3 : q ^ 3 = 1 := by
      have h := pow_orderOf_eq_one q
      rw [hqOrder] at h
      exact h
    have heq3 : (e.symm q : H) ^ 3 = 1 := by
      apply e.injective
      simp only [map_pow, map_one, MulEquiv.apply_symm_apply, hq3]
    have ha3 : a ^ 3 = 1 := congrArg Subtype.val heq3
    have ha3mem : a ^ 3 ∈ U := by rw [ha3]; exact U.one_mem
    have hprod : a ^ 3 * (a ^ 2)⁻¹ ∈ U :=
      U.mul_mem ha3mem (U.inv_mem ha2)
    simpa [a, pow_succ] using hprod
  intro h hh
  let hH : H := ⟨h, hh⟩
  have heMem : e hH ∈ P := by rw [hPtop]; exact Subgroup.mem_top _
  simpa [P, hH] using heMem

end GLS3.Chapter5
/- END Theory.AlternatingSubgroupIndexTwo -/

/- BEGIN Theory.proposition_5_2_8_d_2 -/
noncomputable section

namespace GLS3.Chapter5.SchurPresentation

open GLS3.Chapter5

/-- Proposition 5.2.8(d)(2): once the quotient rotation factor and alternating
cycle-permutation factor are complementary, their full preimage splits over
the rotation preimage. -/
public theorem proposition_5_2_8_d_2
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    (x : Equiv.Perm (Fin (n + 5))) (hx : orderOf x = 2)
    (r : Nat) (eFin : x.cycleFactorsFinset ≃ Fin r)
    (Rbar : Subgroup (alternatingGroup (Fin (n + 5)))) :
    let j := (involutionCycleAlternatingEmbedding x hx).comp
      eFin.altCongrHom.symm.toMonoidHom
    let Lbar := j.range
    let H0bar := Rbar ⊔ Lbar
    let H0 := H0bar.comap f.toMonoidHom
    let R := Rbar.comap f.toMonoidHom
    (Rbar.subgroupOf H0bar).IsComplement' (Lbar.subgroupOf H0bar) →
      ∃ S : Subgroup H0, (R.subgroupOf H0).IsComplement' S := by
  dsimp only
  let j := (involutionCycleAlternatingEmbedding x hx).comp
    eFin.altCongrHom.symm.toMonoidHom
  let Lbar := j.range
  let H0bar := Rbar ⊔ Lbar
  let H0 := H0bar.comap f.toMonoidHom
  let R := Rbar.comap f.toMonoidHom
  let E := Lbar.comap f.toMonoidHom
  let jEquiv : alternatingGroup (Fin r) ≃* Lbar :=
    MonoidHom.ofInjective
      (involutionCycleAlternatingEmbedding_comp_altCongr_injective x hx eFin)
  let toRange : E →* Lbar :=
    (f.toMonoidHom.comp E.subtype).codRestrict Lbar (fun z => z.2)
  let p : E →* alternatingGroup (Fin r) :=
    jEquiv.symm.toMonoidHom.comp toRange
  let iE : E →* H0 := E.subtype.codRestrict H0
    (fun z => (le_sup_right : Lbar ≤ Rbar ⊔ Lbar) z.2)
  intro hbarComp
  obtain ⟨C, hC⟩ :=
    involutionCycleAlternatingPreimage_kernel_hasComplement
      n f hcard x hx r eFin
  have hpKer : p.ker = f.toMonoidHom.ker.comap E.subtype := by
    ext z
    constructor
    · intro hz
      have hz1 := MonoidHom.mem_ker.mp hz
      have hzRange : toRange z = 1 := by
        apply jEquiv.symm.injective
        simpa [p] using hz1
      exact MonoidHom.mem_ker.mpr (congrArg Subtype.val hzRange)
    · intro hz
      apply MonoidHom.mem_ker.mpr
      change jEquiv.symm (toRange z) = 1
      apply jEquiv.injective
      rw [jEquiv.apply_symm_apply, map_one]
      apply Subtype.ext
      exact MonoidHom.mem_ker.mp hz
  have hCcomap : (f.toMonoidHom.ker.comap E.subtype).IsComplement' C := by
    rw [← hpKer]
    exact hC
  refine ⟨C.map iE, ?_⟩
  exact preimageSup_isComplement'_of_rightPreimage_kernel_isComplement'
    f.toMonoidHom f.surjective Rbar Lbar C hbarComp hCcomap

end GLS3.Chapter5.SchurPresentation
/- END Theory.proposition_5_2_8_d_2 -/


/- BEGIN Theory.TraceZeroRotationPreimageEvenCenterE4 -/
noncomputable section
namespace GLS3.Chapter5.SchurPresentation

open GLS3.Chapter5

public theorem traceZeroRotationPreimage_centerMulEquiv_E4
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    (xA : alternatingGroup (Fin (n + 5))) (hx : orderOf xA.1 = 2)
    (r : Nat) (e : xA.1.cycleFactorsFinset ≃ Fin r)
    (m : Nat) (hm : 1 ≤ m) (hrm : r = 2 * m) (hmEven : Even m) :
    let Rbar := involutionEvenRotationSubgroup xA.1
    let R := Rbar.comap f.toMonoidHom
    Nonempty (Subgroup.center R ≃* Multiplicative (ZMod 2 × ZMod 2)) := by
  dsimp only
  have hrEven : Even r := ⟨m, by omega⟩
  obtain ⟨eCenter⟩ :=
    traceZeroRotationPreimage_centerMulEquiv_fullInvolutionPreimage
      n f hcard xA hx r e hrEven
  have hx2 : xA.1 ^ 2 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hx]
  have hct := Equiv.Perm.cycleType_of_pow_prime_eq_one hx2
  have hsupport : xA.1.support.card = 4 * m := by
    have hsupport' : xA.1.support.card = 2 * xA.1.cycleType.card := by
      rw [← Equiv.Perm.sum_cycleType, hct]
      simp [Nat.mul_comm]
    have hcycles : xA.1.cycleType.card = r := by
      have hcardCycles : Fintype.card xA.1.cycleFactorsFinset = r := by
        simpa using Fintype.card_congr e
      simpa [Equiv.Perm.cycleType_def] using hcardCycles
    omega
  have hxA : orderOf xA = 2 :=
    (orderOf_injective (Subgroup.subtype (alternatingGroup (Fin (n + 5))))
      Subtype.coe_injective xA).symm.trans hx
  obtain ⟨eX⟩ := proposition_5_2_4_e_E4_general
    n m f hcard xA hxA hm hsupport hmEven
  exact ⟨eCenter.trans eX⟩

end GLS3.Chapter5.SchurPresentation
/- END Theory.TraceZeroRotationPreimageEvenCenterE4 -/

/- BEGIN Theory.TraceZeroRotationPreimageEvenCenterZ4 -/
noncomputable section
namespace GLS3.Chapter5.SchurPresentation

open GLS3.Chapter5

public theorem traceZeroRotationPreimage_centerMulEquiv_Z4
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    (xA : alternatingGroup (Fin (n + 5))) (hx : orderOf xA.1 = 2)
    (r : Nat) (e : xA.1.cycleFactorsFinset ≃ Fin r)
    (m : Nat) (hm : 1 ≤ m) (hrm : r = 2 * m) (hmOdd : Odd m) :
    let Rbar := involutionEvenRotationSubgroup xA.1
    let R := Rbar.comap f.toMonoidHom
    Nonempty (Subgroup.center R ≃* Multiplicative (ZMod 4)) := by
  dsimp only
  have hrEven : Even r := ⟨m, by omega⟩
  obtain ⟨eCenter⟩ :=
    traceZeroRotationPreimage_centerMulEquiv_fullInvolutionPreimage
      n f hcard xA hx r e hrEven
  have hx2 : xA.1 ^ 2 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hx]
  have hct := Equiv.Perm.cycleType_of_pow_prime_eq_one hx2
  have hsupport : xA.1.support.card = 4 * m := by
    have hsupport' : xA.1.support.card = 2 * xA.1.cycleType.card := by
      rw [← Equiv.Perm.sum_cycleType, hct]
      simp [Nat.mul_comm]
    have hcycles : xA.1.cycleType.card = r := by
      have hcardCycles : Fintype.card xA.1.cycleFactorsFinset = r := by
        simpa using Fintype.card_congr e
      simpa [Equiv.Perm.cycleType_def] using hcardCycles
    omega
  have hxA : orderOf xA = 2 :=
    (orderOf_injective (Subgroup.subtype (alternatingGroup (Fin (n + 5))))
      Subtype.coe_injective xA).symm.trans hx
  obtain ⟨eX⟩ := proposition_5_2_4_e_Z4_general
    n m f hcard xA hxA hm hsupport hmOdd
  exact ⟨eCenter.trans eX⟩

end GLS3.Chapter5.SchurPresentation
/- END Theory.TraceZeroRotationPreimageEvenCenterZ4 -/


/- BEGIN Theory.proposition_5_2_8_e -/
noncomputable section
namespace GLS3.Chapter5.SchurPresentation

open GLS3.Chapter5

/-- Proposition 5.2.8(e): the full preimage of the trace-zero rotation subgroup
splits as a central cyclic factor times an extraspecial-or-kernel factor. -/
public theorem proposition_5_2_8_e
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    (x : Equiv.Perm (Fin (n + 5))) (hx : orderOf x = 2)
    (r : Nat) (e : x.cycleFactorsFinset ≃ Fin r) :
    let Rbar := involutionEvenRotationSubgroup x
    let R := Rbar.comap f.toMonoidHom
    ∃ Z1 R1 : Subgroup R,
      Z1 ⊔ R1 = ⊤ ∧
      (∀ z ∈ Z1, ∀ y ∈ R1, Commute z y) ∧
      f.toMonoidHom.ker.comap R.subtype ≤ R1 ∧
      (IsExtraspecialTwoSubgroup R1 ∨
        R1 = f.toMonoidHom.ker.comap R.subtype) ∧
      (f.toMonoidHom.ker.comap R.subtype) ⊓ Z1 =
        (frattini Z1).map Z1.subtype ∧
      Nat.card Z1 =
        (if r % 4 = 0 then 2 else if r % 4 = 2 then 4 else 1) ∧
      IsCyclic Z1 := by
  dsimp only
  let Rbar := involutionEvenRotationSubgroup x
  let R := Rbar.comap f.toMonoidHom
  obtain ⟨q, hqSurj, hqKer, hqCard, hRP⟩ :=
    traceZeroRotationPreimage_quotient_data n f hcard x hx r e
  have hZcenter : q.ker ≤ Subgroup.center R := by
    rw [hqKer]
    intro z hz
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp
      (f.ker_le_center (show z.1 ∈ f.toMonoidHom.ker from hz)) y.1
  by_cases hrEven : Even r
  · obtain ⟨m, hrmAdd⟩ := hrEven
    have hrm : r = 2 * m := by omega
    have hxne : x ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hx
      norm_num at hx
    have hcycles : x.cycleFactorsFinset.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro h
      exact hxne (Equiv.Perm.cycleFactorsFinset_eq_empty_iff.mp h)
    have hrpos : 0 < r := by
      have hcardPos : 0 < Fintype.card x.cycleFactorsFinset :=
        Fintype.card_pos_iff.mpr ⟨⟨hcycles.choose, hcycles.choose_spec⟩⟩
      have hcardEq : Fintype.card x.cycleFactorsFinset = r := by
        simpa using Fintype.card_congr e
      omega
    have hm : 1 ≤ m := by omega
    obtain ⟨wx, hwxImage, _⟩ :=
      exists_evenInvolutionFullRotation x hx r e ⟨m, hrmAdd⟩
    have hxsign : Equiv.Perm.sign x = 1 := by
      rw [← hwxImage]
      exact (evenInvolutionCycleRotationToAlternating x wx).2
    let xA : alternatingGroup (Fin (n + 5)) := ⟨x, hxsign⟩
    by_cases hmEven : Even m
    · obtain ⟨eCenter⟩ :=
        traceZeroRotationPreimage_centerMulEquiv_E4
          n f hcard xA hx r e m hm hrm hmEven
      have hcenterCard : Nat.card (Subgroup.center R) = 4 := by
        simpa using Nat.card_congr eCenter.toEquiv
      obtain ⟨Z1, R1, hsup, hcomm, hZR1, hR1, hinter, hZ1card, hZ1cyclic⟩ :=
        exists_klein_four_central_decomposition
          hRP q q.ker rfl hZcenter hqCard eCenter hcenterCard
      have hmod : r % 4 = 0 := by
        obtain ⟨k, hk⟩ := hmEven
        omega
      refine ⟨Z1, R1, hsup, hcomm, ?_, ?_, ?_, ?_, hZ1cyclic⟩
      · simpa [hqKer] using hZR1
      · simpa [hqKer] using hR1
      · simpa [hqKer] using hinter
      · simpa [hmod] using hZ1card
    · have hmOdd : Odd m := Nat.not_even_iff_odd.mp hmEven
      obtain ⟨eCenter⟩ :=
        traceZeroRotationPreimage_centerMulEquiv_Z4
          n f hcard xA hx r e m hm hrm hmOdd
      have hcenterCard : Nat.card (Subgroup.center R) = 4 := by
        simpa using Nat.card_congr eCenter.toEquiv
      let : IsCyclic (Subgroup.center R) :=
        isCyclic_of_surjective eCenter.symm.toMonoidHom eCenter.symm.surjective
      obtain ⟨Z1, R1, hsup, hcomm, hZR1, hR1, hinter, hZ1card, hZ1cyclic⟩ :=
        exists_cyclic_four_central_decomposition
          hRP q q.ker rfl hZcenter hqCard inferInstance hcenterCard
      have hmod : r % 4 = 2 := by
        obtain ⟨k, hk⟩ := hmOdd
        omega
      refine ⟨Z1, R1, hsup, hcomm, ?_, ?_, ?_, ?_, hZ1cyclic⟩
      · simpa [hqKer] using hZR1
      · simpa [hqKer] using hR1
      · simpa [hqKer] using hinter
      · simpa [hmod] using hZ1card
  · have hrOdd : Odd r := Nat.not_even_iff_odd.mp hrEven
    have hcenter :=
      traceZeroRotationPreimage_center_eq_kernel_of_odd
        n f hcard x hx r e hrOdd
    dsimp only at hcenter
    obtain ⟨Z1, R1, hsup, hcomm, hZR1, hR1, hinter, hZ1card, hZ1cyclic⟩ :=
      exists_odd_center_decomposition hRP q q.ker rfl
        (by simpa [hqKer] using hcenter) hqCard
    have hmod0 : r % 4 ≠ 0 := by
      obtain ⟨k, hk⟩ := hrOdd
      omega
    have hmod2 : r % 4 ≠ 2 := by
      obtain ⟨k, hk⟩ := hrOdd
      omega
    refine ⟨Z1, R1, hsup, hcomm, ?_, ?_, ?_, ?_, hZ1cyclic⟩
    · simpa [hqKer] using hZR1
    · simpa [hqKer] using hR1
    · simpa [hqKer] using hinter
    · simpa [hmod0, hmod2] using hZ1card

end GLS3.Chapter5.SchurPresentation
/- END Theory.proposition_5_2_8_e -/

/- BEGIN Theory.proposition_5_2_7_b_transport -/
namespace GLS3.Chapter5

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

/-- The cyclic order-ten fixed subgroup calculation transports from the
explicit `2·A₆` model along any equivalence intertwining the exceptional
lifts. -/
public theorem proposition_5_2_7_b_transport
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (x : MulAut K) (e : K ≃* a6DoubleCoverPermutationSubgroup)
    (hcompat : ∀ k : K,
      e (x k) = a6ExceptionalConjugatorLiftAut (e k)) :
    IsCyclic (automorphismFixedSubgroup x) := by
  let E := fixedSubgroupMulEquivOfCompat e x
    a6ExceptionalConjugatorLiftAut hcompat
  exact (E.isCyclic).mpr a6ExceptionalFixedSubgroup_isCyclic

public theorem proposition_5_2_7_b_transport_card
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (x : MulAut K) (e : K ≃* a6DoubleCoverPermutationSubgroup)
    (hcompat : ∀ k : K,
      e (x k) = a6ExceptionalConjugatorLiftAut (e k)) :
    Nat.card (automorphismFixedSubgroup x) = 10 := by
  let E := fixedSubgroupMulEquivOfCompat e x
    a6ExceptionalConjugatorLiftAut hcompat
  rw [← a6ExceptionalFixedSubgroup_card]
  exact Nat.card_congr E

end GLS3.Chapter5
/- END Theory.proposition_5_2_7_b_transport -/

/- BEGIN Theory.A6OuterAutomorphismData -/
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

noncomputable section

namespace GLS3.Chapter5

public abbrev Perm6 := Equiv.Perm (Fin 6)

@[reducible, expose] public def unpackPermCode (n : Nat) : List (Fin 6) :=
  List.ofFn fun i : Fin 6 =>
    ⟨n / (6 ^ i.val) % 6, Nat.mod_lt _ (by decide)⟩

@[reducible, expose] public def packedPermCodeArray : Array Nat := #[
  44790, 44785, 44725, 44185, 39865, 7465, 44760, 44750, 44720, 44180, 39860, 7460,
  44400, 44390, 44300, 44120, 39800, 7400, 41160, 41150, 41060, 40340, 39260, 6860,
  15240, 15230, 15140, 14420, 9020, 2540, 44610, 44605, 44515, 44155, 39835, 7435,
  44550, 44535, 44505, 44145, 39825, 7425, 44370, 44355, 44295, 44115, 39795, 7395,
  41130, 41115, 41055, 40335, 39255, 6855, 15210, 15195, 15135, 14415, 9015, 2535,
  42450, 42445, 42355, 41635, 39475, 7075, 42390, 42375, 42345, 41625, 39465, 7065,
  41850, 41835, 41715, 41535, 39375, 6975, 40770, 40755, 40635, 40275, 39195, 6795,
  14850, 14835, 14715, 14355, 8955, 2475, 23010, 23005, 22915, 22195, 16795, 3835,
  22950, 22935, 22905, 22185, 16785, 3825, 22410, 22395, 22275, 22095, 16695, 3735,
  18090, 18075, 17955, 17055, 15975, 3015, 11610, 11595, 11475, 10575, 8415, 1935,
  43710, 43705, 43645, 42925, 39685, 7285, 43680, 43670, 43640, 42920, 39680, 7280,
  43140, 43130, 43010, 42830, 39590, 7190, 40980, 40970, 40850, 40310, 39230, 6830,
  15060, 15050, 14930, 14390, 8990, 2510, 43350, 43345, 43225, 42865, 39625, 7225,
  43260, 43240, 43210, 42850, 39610, 7210, 43080, 43060, 43000, 42820, 39580, 7180,
  40920, 40900, 40840, 40300, 39220, 6820, 15000, 14980, 14920, 14380, 8980, 2500,
  42270, 42265, 42145, 41605, 39445, 7045, 42180, 42160, 42130, 41590, 39430, 7030,
  41820, 41800, 41710, 41530, 39370, 6970, 40740, 40720, 40630, 40270, 39190, 6790,
  14820, 14800, 14710, 14350, 8950, 2470, 22830, 22825, 22705, 22165, 16765, 3805,
  22740, 22720, 22690, 22150, 16750, 3790, 22380, 22360, 22270, 22090, 16690, 3730,
  18060, 18040, 17950, 17050, 15970, 3010, 11580, 11560, 11470, 10570, 8410, 1930,
  30750, 30745, 30685, 29965, 24565, 5125, 30720, 30710, 30680, 29960, 24560, 5120,
  30180, 30170, 30050, 29870, 24470, 5030, 25860, 25850, 25730, 24830, 23750, 4310,
  12900, 12890, 12770, 11870, 8630, 2150, 30390, 30385, 30265, 29905, 24505, 5065,
  30300, 30280, 30250, 29890, 24490, 5050, 30120, 30100, 30040, 29860, 24460, 5020,
  25800, 25780, 25720, 24820, 23740, 4300, 12840, 12820, 12760, 11860, 8620, 2140,
  27150, 27145, 27025, 26125, 23965, 4525, 27060, 27040, 27010, 26110, 23950, 4510,
  26340, 26320, 26170, 25990, 23830, 4390, 25260, 25240, 25090, 24730, 23650, 4210,
  12300, 12280, 12130, 11770, 8530, 2050, 20670, 20665, 20545, 19645, 16405, 3445,
  20580, 20560, 20530, 19630, 16390, 3430, 19860, 19840, 19690, 19510, 16270, 3310,
  17700, 17680, 17530, 16990, 15910, 2950, 11220, 11200, 11050, 10510, 8350, 1870,
  38310, 38305, 38245, 37705, 32305, 6385, 38280, 38270, 38240, 37700, 32300, 6380,
  37920, 37910, 37820, 37640, 32240, 6320, 33600, 33590, 33500, 32600, 31520, 5600,
  14160, 14150, 14060, 13160, 8840, 2360, 38130, 38125, 38035, 37675, 32275, 6355,
  38070, 38055, 38025, 37665, 32265, 6345, 37890, 37875, 37815, 37635, 32235, 6315,
  33570, 33555, 33495, 32595, 31515, 5595, 14130, 14115, 14055, 13155, 8835, 2355,
  34890, 34885, 34795, 33895, 31735, 5815, 34830, 34815, 34785, 33885, 31725, 5805,
  34110, 34095, 33945, 33765, 31605, 5685, 33030, 33015, 32865, 32505, 31425, 5505,
  13590, 13575, 13425, 13065, 8745, 2265, 21930, 21925, 21835, 20935, 16615, 3655,
  21870, 21855, 21825, 20925, 16605, 3645, 21150, 21135, 20985, 20805, 16485, 3525,
  17910, 17895, 17745, 17025, 15945, 2985, 11430, 11415, 11265, 10545, 8385, 1905,
  36150, 36145, 36085, 35185, 31945, 6025, 36120, 36110, 36080, 35180, 31940, 6020,
  35400, 35390, 35240, 35060, 31820, 5900, 33240, 33230, 33080, 32540, 31460, 5540,
  13800, 13790, 13640, 13100, 8780, 2300, 35610, 35605, 35455, 35095, 31855, 5935,
  35490, 35465, 35435, 35075, 31835, 5915, 35310, 35285, 35225, 35045, 31805, 5885,
  33150, 33125, 33065, 32525, 31445, 5525, 13710, 13685, 13625, 13085, 8765, 2285,
  34530, 34525, 34375, 33835, 31675, 5755, 34410, 34385, 34355, 33815, 31655, 5735,
  34050, 34025, 33935, 33755, 31595, 5675, 32970, 32945, 32855, 32495, 31415, 5495,
  13530, 13505, 13415, 13055, 8735, 2255, 21570, 21565, 21415, 20875, 16555, 3595,
  21450, 21425, 21395, 20855, 16535, 3575, 21090, 21065, 20975, 20795, 16475, 3515,
  17850, 17825, 17735, 17015, 15935, 2975, 11370, 11345, 11255, 10535, 8375, 1895,
  29670, 29665, 29605, 28705, 24385, 4945, 29640, 29630, 29600, 28700, 24380, 4940,
  28920, 28910, 28760, 28580, 24260, 4820, 25680, 25670, 25520, 24800, 23720, 4280,
  12720, 12710, 12560, 11840, 8600, 2120, 29130, 29125, 28975, 28615, 24295, 4855,
  29010, 28985, 28955, 28595, 24275, 4835, 28830, 28805, 28745, 28565, 24245, 4805,
  25590, 25565, 25505, 24785, 23705, 4265, 12630, 12605, 12545, 11825, 8585, 2105,
  26970, 26965, 26815, 26095, 23935, 4495, 26850, 26825, 26795, 26075, 23915, 4475,
  26310, 26285, 26165, 25985, 23825, 4385, 25230, 25205, 25085, 24725, 23645, 4205,
  12270, 12245, 12125, 11765, 8525, 2045, 20490, 20485, 20335, 19615, 16375, 3415,
  20370, 20345, 20315, 19595, 16355, 3395, 19830, 19805, 19685, 19505, 16265, 3305,
  17670, 17645, 17525, 16985, 15905, 2945, 11190, 11165, 11045, 10505, 8345, 1865
]

@[reducible, expose] public def permCodeList : List (List (Fin 6)) :=
  packedPermCodeArray.toList.map unpackPermCode

public theorem permCodeList_eq_permutations :
    permCodeList = (List.finRange 6).permutations' := by
  rfl

public theorem permCodeList_length : permCodeList.length = 720 := by
  calc
    permCodeList.length = (List.finRange 6).permutations.length := by
      rw [permCodeList_eq_permutations]
      exact (List.permutations_perm_permutations'
        (List.finRange 6)).length_eq.symm
    _ = Nat.factorial (List.finRange 6).length := List.length_permutations _
    _ = 720 := by decide

public abbrev PermCodeIndex := Fin 720

public theorem packedPermCodeArray_size : packedPermCodeArray.size = 720 := by
  all_goals decide
@[reducible, expose] public def packedCodeAt (i : PermCodeIndex) : Nat :=
  packedPermCodeArray[i.val]'(by
    rw [packedPermCodeArray_size]
    exact i.isLt)

@[reducible, expose] public def codeListAt (i : PermCodeIndex) : List (Fin 6) :=
  unpackPermCode (packedCodeAt i)

public theorem codeListAt_eq_get (i : PermCodeIndex) :
    codeListAt i = permCodeList.get (Fin.cast permCodeList_length.symm i) := by
  unfold codeListAt packedCodeAt permCodeList
  change unpackPermCode packedPermCodeArray[i.val] =
    (packedPermCodeArray.toList.map unpackPermCode)[i.val]
  rw [List.getElem_map, Array.getElem_toList]

public abbrev PermCode6 := {l : List (Fin 6) // l ∈ permCodeList}

public instance : Fintype PermCode6 :=
  Fintype.ofList permCodeList.attach (List.mem_attach _)

@[reducible, expose] public def permOfCode (c : PermCode6) : Perm6 := by
  have hp : c.1.Perm (List.finRange 6) :=
    List.mem_permutations'.mp (by
      rw [← permCodeList_eq_permutations]
      exact c.2)
  have hlen : c.1.length = 6 := by
    simpa using hp.length_eq
  have hnodup : c.1.Nodup :=
    hp.nodup_iff.mpr (List.nodup_finRange 6)
  have hall : ∀ x : Fin 6, x ∈ c.1 := by
    intro x
    exact hp.mem_iff.mpr (List.mem_finRange x)
  exact (finCongr hlen).symm.trans
    (hnodup.getEquivOfForallMemList c.1 hall)

@[reducible, expose] public def codeOfPerm (σ : Perm6) : PermCode6 :=
  ⟨List.ofFn σ, by
    rw [permCodeList_eq_permutations, List.mem_permutations', List.ofFn_eq_map]
    exact σ.map_finRange_perm⟩

public abbrev PermFn6 := Fin 6 → Fin 6

/-- A local transparent copy of the six pentads.  The finite certificates
below must normalize this table in the kernel; the public `pentadAt` remains
the mathematical interface used by the comparison lemma. -/
@[reducible, expose] public def pentadAtFn : Fin 6 → PentadData
  | 0 => { { {0, 1}, {2, 4}, {3, 5} }, { {0, 2}, {1, 5}, {3, 4} },
      { {0, 3}, {1, 2}, {4, 5} }, { {0, 4}, {1, 3}, {2, 5} },
      { {0, 5}, {1, 4}, {2, 3} } }
  | 1 => { { {0, 1}, {2, 5}, {3, 4} }, { {0, 2}, {1, 4}, {3, 5} },
      { {0, 3}, {1, 2}, {4, 5} }, { {0, 4}, {1, 5}, {2, 3} },
      { {0, 5}, {1, 3}, {2, 4} } }
  | 2 => { { {0, 1}, {2, 3}, {4, 5} }, { {0, 2}, {1, 5}, {3, 4} },
      { {0, 3}, {1, 4}, {2, 5} }, { {0, 4}, {1, 2}, {3, 5} },
      { {0, 5}, {1, 3}, {2, 4} } }
  | 3 => { { {0, 1}, {2, 5}, {3, 4} }, { {0, 2}, {1, 3}, {4, 5} },
      { {0, 3}, {1, 5}, {2, 4} }, { {0, 4}, {1, 2}, {3, 5} },
      { {0, 5}, {1, 4}, {2, 3} } }
  | 4 => { { {0, 1}, {2, 3}, {4, 5} }, { {0, 2}, {1, 4}, {3, 5} },
      { {0, 3}, {1, 5}, {2, 4} }, { {0, 4}, {1, 3}, {2, 5} },
      { {0, 5}, {1, 2}, {3, 4} } }
  | 5 => { { {0, 1}, {2, 4}, {3, 5} }, { {0, 2}, {1, 3}, {4, 5} },
      { {0, 3}, {1, 4}, {2, 5} }, { {0, 4}, {1, 5}, {2, 3} },
      { {0, 5}, {1, 2}, {3, 4} } }

public theorem pentadAtFn_eq (i : Fin 6) : pentadAtFn i = pentadAt i := by
  fin_cases i <;> rw [pentadAt]

@[reducible, expose] public def codeFn (c : PermCode6) : PermFn6 :=
  fun i => c.1.getD i.val 0

@[reducible, expose] public def codeFnAt (c : PermCodeIndex) : PermFn6 :=
  fun i => (codeListAt c).getD i.val 0

@[reducible, expose] public def codeIndexOfPerm (σ : Perm6) : PermCodeIndex :=
  ⟨permCodeList.idxOf (List.ofFn σ), by
    rw [← permCodeList_length]
    apply List.idxOf_lt_length_iff.mpr
    exact (codeOfPerm σ).2⟩

public theorem codeListAt_codeIndexOfPerm (σ : Perm6) :
    codeListAt (codeIndexOfPerm σ) = List.ofFn σ := by
  rw [codeListAt_eq_get, codeIndexOfPerm]
  exact List.getElem_idxOf
    (List.idxOf_lt_length_iff.mpr (codeOfPerm σ).2)

public theorem codeFnAt_codeIndexOfPerm (σ : Perm6) :
    codeFnAt (codeIndexOfPerm σ) = σ := by
  funext i
  rw [codeFnAt, codeListAt_codeIndexOfPerm]
  fin_cases i <;> rfl

public theorem codeListAt_mem (c : PermCodeIndex) :
    codeListAt c ∈ permCodeList := by
  rw [codeListAt_eq_get]
  exact List.get_mem permCodeList (Fin.cast permCodeList_length.symm c)

@[reducible, expose] public def codeAt (c : PermCodeIndex) : PermCode6 :=
  ⟨codeListAt c, codeListAt_mem c⟩

@[reducible, expose] public def permAt (c : PermCodeIndex) : Perm6 :=
  permOfCode (codeAt c)

public theorem codeFnAt_eq_permAt (c : PermCodeIndex) :
    codeFnAt c = permAt c := by
  funext i
  have hp : (codeListAt c).Perm (List.finRange 6) :=
    List.mem_permutations'.mp (by
      rw [← permCodeList_eq_permutations]
      exact codeListAt_mem c)
  have hlen : (codeListAt c).length = 6 := by
    simp
  change (codeListAt c).getD i.val 0 = (permAt c) i
  rw [List.getD_eq_getElem (codeListAt c) 0
    (by omega : i.val < (codeListAt c).length)]
  rfl

@[reducible, expose] public def compFn (f g : PermFn6) : PermFn6 :=
  fun i => f (g i)

@[reducible, expose] public def firstFin6 (p : Fin 6 → Bool) : Fin 6 :=
  if p 0 then 0 else if p 1 then 1 else if p 2 then 2 else
    if p 3 then 3 else if p 4 then 4 else 5

public theorem firstFin6_spec (p : Fin 6 → Bool)
    (h : ∃ i, p i = true) : p (firstFin6 p) = true := by
  by_cases h0 : p 0 = true
  · simp [firstFin6, h0]
  by_cases h1 : p 1 = true
  · simp [firstFin6, h0, h1]
  by_cases h2 : p 2 = true
  · simp [firstFin6, h0, h1, h2]
  by_cases h3 : p 3 = true
  · simp [firstFin6, h0, h1, h2, h3]
  by_cases h4 : p 4 = true
  · simp [firstFin6, h0, h1, h2, h3, h4]
  have h5 : p 5 = true := by
    rcases h with ⟨i, hi⟩
    fin_cases i <;> simp_all
  simp [firstFin6, h0, h1, h2, h3, h4, h5]

@[reducible, expose] public def invFn (f : PermFn6) : PermFn6 :=
  fun i => firstFin6 fun j => decide (f j = i)

public theorem invFn_equiv (σ : Perm6) : invFn σ = σ.symm := by
  funext i
  apply σ.injective
  have hex : ∃ j : Fin 6, decide (σ j = i) = true :=
    ⟨σ.symm i, by simp⟩
  change σ (firstFin6 fun j => decide (σ j = i)) = σ (σ.symm i)
  rw [σ.apply_symm_apply]
  exact of_decide_eq_true (firstFin6_spec _ hex)

@[reducible, expose] public def mapPairFn (f : PermFn6) (s : Finset (Fin 6)) :
    Finset (Fin 6) :=
  s.image f

@[reducible, expose] public def mapMatchingFn (f : PermFn6)
    (s : Finset (Finset (Fin 6))) : Finset (Finset (Fin 6)) :=
  s.image (mapPairFn f)

@[reducible, expose] public def mapPentadFn (f : PermFn6) (s : PentadData) : PentadData :=
  s.image (mapMatchingFn f)

public theorem mapPairFn_equiv (σ : Perm6) (s : Finset (Fin 6)) :
    mapPairFn σ s = σ.finsetCongr s := by
  rw [Equiv.finsetCongr_apply, Finset.map_eq_image]
  rfl

public theorem mapMatchingFn_equiv (σ : Perm6)
    (s : Finset (Finset (Fin 6))) :
    mapMatchingFn σ s = σ.finsetCongr.finsetCongr s := by
  rw [Equiv.finsetCongr_apply, Finset.map_eq_image]
  apply Finset.image_congr
  intro a ha
  exact mapPairFn_equiv σ a

public theorem mapPentadFn_equiv (σ : Perm6) (s : PentadData) :
    mapPentadFn σ s = pentadMap σ s := by
  rw [pentadMap, pentadEquiv, Equiv.finsetCongr_apply,
    Finset.map_eq_image]
  apply Finset.image_congr
  intro a ha
  exact mapMatchingFn_equiv σ a

@[reducible, expose] public def outerFn (f : PermFn6) : PermFn6 :=
  fun i =>
    firstFin6 fun j =>
      decide (pentadAtFn j = mapPentadFn f (pentadAtFn i))

public theorem outerFn_equiv (σ : Perm6) : outerFn σ = outerHom σ := by
  funext i
  change
    firstFin6 (fun j => decide
      (pentadAtFn j = mapPentadFn σ (pentadAtFn i))) = outerAct σ i
  have hex : ∃ j : Fin 6,
      decide (pentadAtFn j = mapPentadFn σ (pentadAtFn i)) = true := by
    refine ⟨outerAct σ i, ?_⟩
    simp only [mapPentadFn_equiv, decide_eq_true_eq]
    rw [pentadAtFn_eq, pentadAtFn_eq]
    exact outerAct_spec σ i
  apply pentadAt_injective
  have hfind := of_decide_eq_true (firstFin6_spec _ hex)
  calc
    pentadAt (firstFin6 fun j =>
        decide (pentadAtFn j = mapPentadFn σ (pentadAtFn i))) =
        mapPentadFn σ (pentadAtFn i) := by
      rw [← pentadAtFn_eq]
      exact hfind
    _ = pentadMap σ (pentadAtFn i) := mapPentadFn_equiv σ (pentadAtFn i)
    _ = pentadMap σ (pentadAt i) := by rw [pentadAtFn_eq]
    _ = pentadAt (outerAct σ i) := (outerAct_spec σ i).symm

@[reducible, expose] public def codeSign (f : PermFn6) : ℤˣ :=
  ∏ i, ∏ j ∈ Finset.Ioi i, if f i < f j then 1 else -1

public theorem codeSign_equiv (σ : Perm6) : codeSign σ = σ.sign := by
  exact (Equiv.Perm.sign_eq_prod_prod_Ioi σ).symm

@[reducible, expose] public def twistFn (σ g : PermFn6) : PermFn6 :=
  outerFn (compFn σ (compFn g (invFn σ)))

@[reducible, expose] public def twistPerm (σ g : Perm6) : Perm6 :=
  outerHom (σ * g * σ⁻¹)

public theorem twistFn_equiv (σ g : Perm6) :
    twistFn σ g = twistPerm σ g := by
  have harg : compFn σ (compFn g (invFn σ)) =
      (σ * g * σ⁻¹ : Perm6) := by
    funext i
    rw [invFn_equiv]
    rfl
  rw [twistFn, harg, outerFn_equiv]

@[reducible, expose] public def outerSquareConjugator : Perm6 :=
  permAt 125

@[reducible, expose] public def outerSquareConjugatorFn : PermFn6 :=
  outerSquareConjugator

public theorem outerSquare_finRotate_fn :
    outerFn (outerFn (finRotate 6)) =
      compFn outerSquareConjugatorFn
        (compFn (finRotate 6) (invFn outerSquareConjugatorFn)) := by
  funext i
  fin_cases i <;> decide +kernel

public theorem outerSquare_adjacentSwap_fn :
    outerFn (outerFn (Equiv.swap 0 (finRotate 6 0))) =
      compFn outerSquareConjugatorFn
        (compFn (Equiv.swap 0 (finRotate 6 0))
          (invFn outerSquareConjugatorFn)) := by
  funext i
  fin_cases i <;> decide +kernel

public theorem outerHom_square_eq_conj (g : Perm6) :
    outerHom (outerHom g) =
      outerSquareConjugator * g * outerSquareConjugator⁻¹ := by
  have hinv : invFn outerSquareConjugatorFn =
      outerSquareConjugator.symm := by
    simpa only [outerSquareConjugatorFn] using
      invFn_equiv outerSquareConjugator
  have hhom : outerHom.comp outerHom =
      (MulAut.conj outerSquareConjugator : MulAut Perm6).toMonoidHom := by
    apply MonoidHom.eq_of_eqOn_dense
      (Equiv.Perm.closure_cycle_adjacent_swap
        (isCycle_finRotate_of_le (by decide))
        (support_finRotate_of_le (by decide)) 0)
    rintro h (rfl | rfl)
    · apply Equiv.ext
      intro i
      change outerHom (outerHom (finRotate 6)) i =
        outerSquareConjugator
          (finRotate 6 (outerSquareConjugator.symm i))
      rw [← outerFn_equiv (outerHom (finRotate 6)),
        ← outerFn_equiv (finRotate 6)]
      have hcert := congrFun outerSquare_finRotate_fn i
      rw [hinv] at hcert
      simpa only [outerSquareConjugatorFn, compFn, MulAut.conj_apply] using hcert
    · apply Equiv.ext
      intro i
      change outerHom (outerHom (Equiv.swap 0 (finRotate 6 0))) i =
        outerSquareConjugator
          (Equiv.swap 0 (finRotate 6 0) (outerSquareConjugator.symm i))
      rw [← outerFn_equiv (outerHom (Equiv.swap 0 (finRotate 6 0))),
        ← outerFn_equiv (Equiv.swap 0 (finRotate 6 0))]
      have hcert := congrFun outerSquare_adjacentSwap_fn i
      rw [hinv] at hcert
      simpa only [outerSquareConjugatorFn, compFn, MulAut.conj_apply] using hcert
  exact DFunLike.congr_fun hhom g

@[reducible, expose] public def a6Generator (i : Fin 4) : Perm6 :=
  SchurPresentation.adjacentSwap 1 0 *
    SchurPresentation.adjacentSwap 1 i.succ

public theorem a6Generator_eq (i : Fin 4) :
    a6Generator i =
      (SchurPresentation.alternatingSuzukiGenerator 1 i).1 := by
  exact (SchurPresentation.alternatingSuzukiGenerator_val 1 i).symm

@[reducible, expose] public def a6GeneratorFn (i : Fin 4) : PermFn6 :=
  a6Generator i

@[reducible, expose] public def canonicalTwistPerm : Perm6 :=
  Equiv.swap 2 3 * Equiv.swap 2 5

@[reducible, expose] public def canonicalTwistFn : PermFn6 := canonicalTwistPerm

@[reducible, expose] public def conjugateCanonicalTwistFn (τ g : PermFn6) : PermFn6 :=
  compFn τ (compFn
    (twistFn canonicalTwistFn (compFn (invFn τ) (compFn g τ)))
    (invFn τ))

@[reducible, expose] public def conjugateCanonicalTwistPerm (τ g : Perm6) : Perm6 :=
  τ * twistPerm canonicalTwistPerm (τ⁻¹ * g * τ) * τ⁻¹

public theorem conjugateCanonicalTwistFn_equiv (τ g : Perm6) :
    conjugateCanonicalTwistFn τ g = conjugateCanonicalTwistPerm τ g := by
  rw [conjugateCanonicalTwistFn, invFn_equiv]
  have hinner : compFn (τ.symm : PermFn6) (compFn g τ) =
      (τ⁻¹ * g * τ : Perm6) := by
    rfl
  rw [hinner, canonicalTwistFn, twistFn_equiv]
  rfl

@[reducible, expose] public def exceptionalWitnessArray : Array Nat := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 79, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 107, 0, 0, 0, 0, 126, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 72, 0, 0, 0, 7, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 62, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 150, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 121, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 133, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 110, 0, 0, 0, 123, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 55, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 60, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 67, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 88, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 69, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 23, 0, 0, 0, 0, 0
]


end GLS3.Chapter5
/- END Theory.A6OuterAutomorphismData -/

/- BEGIN Theory.A6OuterAutomorphismCertificateCore -/
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

noncomputable section

namespace GLS3.Chapter5

public theorem exceptionalWitnessArray_size :
    exceptionalWitnessArray.size = 720 := by
  all_goals decide
@[reducible, expose] public def exceptionalWitnessIndex (c : PermCodeIndex) : PermCodeIndex :=
  Fin.ofNat 720 (exceptionalWitnessArray[c.val]'(by
    rw [exceptionalWitnessArray_size]
    exact c.isLt))

@[reducible, expose] public def exceptionalCodeIndexArray : Array Nat := #[
  9, 23, 40, 57, 62, 79, 96, 110, 162, 166, 185, 221, 231, 244, 268,
  283, 326, 352, 368, 378, 414, 433, 437, 487, 513, 556, 571, 595, 605,
  620, 630, 644, 675, 689, 699, 714]

@[reducible, expose] public def exceptionalCodeIndexList : List Nat :=
  exceptionalCodeIndexArray.toList

public theorem exceptionalCodeIndexArray_size :
    exceptionalCodeIndexArray.size = 36 := by
  all_goals decide
public theorem exceptionalCodeIndexList_length :
    exceptionalCodeIndexList.length = 36 := by
  all_goals decide
@[reducible, expose] public def exceptionalCodeIndexAt (j : Fin 36) : PermCodeIndex :=
  Fin.ofNat 720 (exceptionalCodeIndexArray[j.val]'(by
    rw [exceptionalCodeIndexArray_size]
    exact j.isLt))

public theorem exceptionalCodeIndexAt_injective :
    Function.Injective exceptionalCodeIndexAt := by
  decide +kernel

public theorem exceptionalCandidatePermFn_injective :
    Function.Injective
      (fun j : Fin 36 => codeFnAt (exceptionalCodeIndexAt j)) := by
  decide +kernel

set_option maxRecDepth 100000 in
public theorem exceptionalWitnessSignCertificate :
    ∀ j : Fin 36,
      codeSign (codeFnAt
        (exceptionalWitnessIndex (exceptionalCodeIndexAt j))) = 1 := by
  decide +kernel

@[reducible, expose] public def exceptionalConjugatorAt (j : Fin 36) :
    alternatingGroup (Fin 6) :=
  ⟨permAt (exceptionalWitnessIndex (exceptionalCodeIndexAt j)), by
    change (permAt
      (exceptionalWitnessIndex (exceptionalCodeIndexAt j))).sign = 1
    rw [← codeSign_equiv, ← codeFnAt_eq_permAt]
    exact exceptionalWitnessSignCertificate j⟩

public abbrev exceptionalEquation (c : PermCodeIndex) : Prop :=
  compFn (outerFn (codeFnAt c))
      (compFn outerSquareConjugatorFn (codeFnAt c)) = id

@[reducible, expose] public def codeIndexBlock (b : Fin 24) (j : Fin 30) : PermCodeIndex :=
  finProdFinEquiv (b, j)

end GLS3.Chapter5
/- END Theory.A6OuterAutomorphismCertificateCore -/

/- BEGIN Theory.A6OuterAutomorphismEquationCertificates -/
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

noncomputable section

namespace GLS3.Chapter5

set_option maxRecDepth 100000 in
public theorem exceptionalEquationCertificate_block0 :
    ∀ j : Fin 30, exceptionalEquation (codeIndexBlock 0 j) →
      (codeIndexBlock 0 j).val ∈ exceptionalCodeIndexList := by
  decide +kernel

set_option maxRecDepth 100000 in
public theorem exceptionalEquationCertificate_block1 :
    ∀ j : Fin 30, exceptionalEquation (codeIndexBlock 1 j) →
      (codeIndexBlock 1 j).val ∈ exceptionalCodeIndexList := by
  decide +kernel

set_option maxRecDepth 100000 in
public theorem exceptionalEquationCertificate_block2 :
    ∀ j : Fin 30, exceptionalEquation (codeIndexBlock 2 j) →
      (codeIndexBlock 2 j).val ∈ exceptionalCodeIndexList := by
  decide +kernel

set_option maxRecDepth 100000 in
public theorem exceptionalEquationCertificate_block3 :
    ∀ j : Fin 30, exceptionalEquation (codeIndexBlock 3 j) →
      (codeIndexBlock 3 j).val ∈ exceptionalCodeIndexList := by
  decide +kernel

set_option maxRecDepth 100000 in
public theorem exceptionalEquationCertificate_block4 :
    ∀ j : Fin 30, exceptionalEquation (codeIndexBlock 4 j) →
      (codeIndexBlock 4 j).val ∈ exceptionalCodeIndexList := by
  decide +kernel

set_option maxRecDepth 100000 in
public theorem exceptionalEquationCertificate_block5 :
    ∀ j : Fin 30, exceptionalEquation (codeIndexBlock 5 j) →
      (codeIndexBlock 5 j).val ∈ exceptionalCodeIndexList := by
  decide +kernel

set_option maxRecDepth 100000 in
public theorem exceptionalEquationCertificate_block6 :
    ∀ j : Fin 30, exceptionalEquation (codeIndexBlock 6 j) →
      (codeIndexBlock 6 j).val ∈ exceptionalCodeIndexList := by
  decide +kernel

set_option maxRecDepth 100000 in
public theorem exceptionalEquationCertificate_block7 :
    ∀ j : Fin 30, exceptionalEquation (codeIndexBlock 7 j) →
      (codeIndexBlock 7 j).val ∈ exceptionalCodeIndexList := by
  decide +kernel

set_option maxRecDepth 100000 in
public theorem exceptionalEquationCertificate_block8 :
    ∀ j : Fin 30, exceptionalEquation (codeIndexBlock 8 j) →
      (codeIndexBlock 8 j).val ∈ exceptionalCodeIndexList := by
  decide +kernel

set_option maxRecDepth 100000 in
public theorem exceptionalEquationCertificate_block9 :
    ∀ j : Fin 30, exceptionalEquation (codeIndexBlock 9 j) →
      (codeIndexBlock 9 j).val ∈ exceptionalCodeIndexList := by
  decide +kernel

set_option maxRecDepth 100000 in
public theorem exceptionalEquationCertificate_block10 :
    ∀ j : Fin 30, exceptionalEquation (codeIndexBlock 10 j) →
      (codeIndexBlock 10 j).val ∈ exceptionalCodeIndexList := by
  decide +kernel

set_option maxRecDepth 100000 in
public theorem exceptionalEquationCertificate_block11 :
    ∀ j : Fin 30, exceptionalEquation (codeIndexBlock 11 j) →
      (codeIndexBlock 11 j).val ∈ exceptionalCodeIndexList := by
  decide +kernel

set_option maxRecDepth 100000 in
public theorem exceptionalEquationCertificate_block12 :
    ∀ j : Fin 30, exceptionalEquation (codeIndexBlock 12 j) →
      (codeIndexBlock 12 j).val ∈ exceptionalCodeIndexList := by
  decide +kernel

set_option maxRecDepth 100000 in
public theorem exceptionalEquationCertificate_block13 :
    ∀ j : Fin 30, exceptionalEquation (codeIndexBlock 13 j) →
      (codeIndexBlock 13 j).val ∈ exceptionalCodeIndexList := by
  decide +kernel

set_option maxRecDepth 100000 in
public theorem exceptionalEquationCertificate_block14 :
    ∀ j : Fin 30, exceptionalEquation (codeIndexBlock 14 j) →
      (codeIndexBlock 14 j).val ∈ exceptionalCodeIndexList := by
  decide +kernel

set_option maxRecDepth 100000 in
public theorem exceptionalEquationCertificate_block15 :
    ∀ j : Fin 30, exceptionalEquation (codeIndexBlock 15 j) →
      (codeIndexBlock 15 j).val ∈ exceptionalCodeIndexList := by
  decide +kernel

set_option maxRecDepth 100000 in
public theorem exceptionalEquationCertificate_block16 :
    ∀ j : Fin 30, exceptionalEquation (codeIndexBlock 16 j) →
      (codeIndexBlock 16 j).val ∈ exceptionalCodeIndexList := by
  decide +kernel

set_option maxRecDepth 100000 in
public theorem exceptionalEquationCertificate_block17 :
    ∀ j : Fin 30, exceptionalEquation (codeIndexBlock 17 j) →
      (codeIndexBlock 17 j).val ∈ exceptionalCodeIndexList := by
  decide +kernel

set_option maxRecDepth 100000 in
public theorem exceptionalEquationCertificate_block18 :
    ∀ j : Fin 30, exceptionalEquation (codeIndexBlock 18 j) →
      (codeIndexBlock 18 j).val ∈ exceptionalCodeIndexList := by
  decide +kernel

set_option maxRecDepth 100000 in
public theorem exceptionalEquationCertificate_block19 :
    ∀ j : Fin 30, exceptionalEquation (codeIndexBlock 19 j) →
      (codeIndexBlock 19 j).val ∈ exceptionalCodeIndexList := by
  decide +kernel

set_option maxRecDepth 100000 in
public theorem exceptionalEquationCertificate_block20 :
    ∀ j : Fin 30, exceptionalEquation (codeIndexBlock 20 j) →
      (codeIndexBlock 20 j).val ∈ exceptionalCodeIndexList := by
  decide +kernel

set_option maxRecDepth 100000 in
public theorem exceptionalEquationCertificate_block21 :
    ∀ j : Fin 30, exceptionalEquation (codeIndexBlock 21 j) →
      (codeIndexBlock 21 j).val ∈ exceptionalCodeIndexList := by
  decide +kernel

set_option maxRecDepth 100000 in
public theorem exceptionalEquationCertificate_block22 :
    ∀ j : Fin 30, exceptionalEquation (codeIndexBlock 22 j) →
      (codeIndexBlock 22 j).val ∈ exceptionalCodeIndexList := by
  decide +kernel

set_option maxRecDepth 100000 in
public theorem exceptionalEquationCertificate_block23 :
    ∀ j : Fin 30, exceptionalEquation (codeIndexBlock 23 j) →
      (codeIndexBlock 23 j).val ∈ exceptionalCodeIndexList := by
  decide +kernel

public theorem exceptionalEquationCertificate
    (c : PermCodeIndex) (hc : exceptionalEquation c) :
    c.val ∈ exceptionalCodeIndexList := by
  obtain ⟨⟨b, j⟩, rfl⟩ :=
    (finProdFinEquiv : Fin 24 × Fin 30 ≃ Fin (24 * 30)).surjective c
  change exceptionalEquation (codeIndexBlock b j) at hc
  change (codeIndexBlock b j).val ∈ exceptionalCodeIndexList
  fin_cases b
  · exact exceptionalEquationCertificate_block0 j hc
  · exact exceptionalEquationCertificate_block1 j hc
  · exact exceptionalEquationCertificate_block2 j hc
  · exact exceptionalEquationCertificate_block3 j hc
  · exact exceptionalEquationCertificate_block4 j hc
  · exact exceptionalEquationCertificate_block5 j hc
  · exact exceptionalEquationCertificate_block6 j hc
  · exact exceptionalEquationCertificate_block7 j hc
  · exact exceptionalEquationCertificate_block8 j hc
  · exact exceptionalEquationCertificate_block9 j hc
  · exact exceptionalEquationCertificate_block10 j hc
  · exact exceptionalEquationCertificate_block11 j hc
  · exact exceptionalEquationCertificate_block12 j hc
  · exact exceptionalEquationCertificate_block13 j hc
  · exact exceptionalEquationCertificate_block14 j hc
  · exact exceptionalEquationCertificate_block15 j hc
  · exact exceptionalEquationCertificate_block16 j hc
  · exact exceptionalEquationCertificate_block17 j hc
  · exact exceptionalEquationCertificate_block18 j hc
  · exact exceptionalEquationCertificate_block19 j hc
  · exact exceptionalEquationCertificate_block20 j hc
  · exact exceptionalEquationCertificate_block21 j hc
  · exact exceptionalEquationCertificate_block22 j hc
  · exact exceptionalEquationCertificate_block23 j hc

public theorem exceptionalCodeIndexAt_complete :
    ∀ c : PermCodeIndex, c.val ∈ exceptionalCodeIndexList →
      ∃ j : Fin 36, exceptionalCodeIndexAt j = c := by
  intro c hc
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hc
  let j : Fin 36 := Fin.cast exceptionalCodeIndexList_length i
  refine ⟨j, ?_⟩
  apply Fin.ext
  change exceptionalCodeIndexArray[j.val]'(by
      rw [exceptionalCodeIndexArray_size]
      exact j.isLt) % 720 = c.val
  have hij : exceptionalCodeIndexArray[j.val]'(by
      rw [exceptionalCodeIndexArray_size]
      exact j.isLt) = c.val := by
    simpa [exceptionalCodeIndexList, j] using hi
  rw [hij, Nat.mod_eq_of_lt c.isLt]


end GLS3.Chapter5
/- END Theory.A6OuterAutomorphismEquationCertificates -/

/- BEGIN Theory.A6OuterAutomorphismConjugacyCertificates -/
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

noncomputable section

namespace GLS3.Chapter5

@[reducible, expose] public def exceptionalCandidateBlock (b : Fin 6) (j : Fin 6) : Fin 36 :=
  ⟨b.val * 6 + j.val, by omega⟩

set_option maxRecDepth 100000 in
public theorem exceptionalCandidateConjugacyCertificate_block0 :
    ∀ j : Fin 6, ∀ i : Fin 4,
        twistFn
            (codeFnAt (exceptionalCodeIndexAt (exceptionalCandidateBlock 0 j)))
            (a6GeneratorFn i) =
          conjugateCanonicalTwistFn
            (codeFnAt
              (exceptionalWitnessIndex
                (exceptionalCodeIndexAt (exceptionalCandidateBlock 0 j))))
            (a6GeneratorFn i) := by
  decide +kernel

set_option maxRecDepth 100000 in
public theorem exceptionalCandidateConjugacyCertificate_block1 :
    ∀ j : Fin 6, ∀ i : Fin 4,
        twistFn
            (codeFnAt (exceptionalCodeIndexAt (exceptionalCandidateBlock 1 j)))
            (a6GeneratorFn i) =
          conjugateCanonicalTwistFn
            (codeFnAt
              (exceptionalWitnessIndex
                (exceptionalCodeIndexAt (exceptionalCandidateBlock 1 j))))
            (a6GeneratorFn i) := by
  decide +kernel

set_option maxRecDepth 100000 in
public theorem exceptionalCandidateConjugacyCertificate_block2 :
    ∀ j : Fin 6, ∀ i : Fin 4,
        twistFn
            (codeFnAt (exceptionalCodeIndexAt (exceptionalCandidateBlock 2 j)))
            (a6GeneratorFn i) =
          conjugateCanonicalTwistFn
            (codeFnAt
              (exceptionalWitnessIndex
                (exceptionalCodeIndexAt (exceptionalCandidateBlock 2 j))))
            (a6GeneratorFn i) := by
  decide +kernel

set_option maxRecDepth 100000 in
public theorem exceptionalCandidateConjugacyCertificate_block3 :
    ∀ j : Fin 6, ∀ i : Fin 4,
        twistFn
            (codeFnAt (exceptionalCodeIndexAt (exceptionalCandidateBlock 3 j)))
            (a6GeneratorFn i) =
          conjugateCanonicalTwistFn
            (codeFnAt
              (exceptionalWitnessIndex
                (exceptionalCodeIndexAt (exceptionalCandidateBlock 3 j))))
            (a6GeneratorFn i) := by
  decide +kernel

set_option maxRecDepth 100000 in
public theorem exceptionalCandidateConjugacyCertificate_block4 :
    ∀ j : Fin 6, ∀ i : Fin 4,
        twistFn
            (codeFnAt (exceptionalCodeIndexAt (exceptionalCandidateBlock 4 j)))
            (a6GeneratorFn i) =
          conjugateCanonicalTwistFn
            (codeFnAt
              (exceptionalWitnessIndex
                (exceptionalCodeIndexAt (exceptionalCandidateBlock 4 j))))
            (a6GeneratorFn i) := by
  decide +kernel

set_option maxRecDepth 100000 in
public theorem exceptionalCandidateConjugacyCertificate_block5 :
    ∀ j : Fin 6, ∀ i : Fin 4,
        twistFn
            (codeFnAt (exceptionalCodeIndexAt (exceptionalCandidateBlock 5 j)))
            (a6GeneratorFn i) =
          conjugateCanonicalTwistFn
            (codeFnAt
              (exceptionalWitnessIndex
                (exceptionalCodeIndexAt (exceptionalCandidateBlock 5 j))))
            (a6GeneratorFn i) := by
  decide +kernel

public theorem exceptionalCandidateConjugacyCertificate
    (j : Fin 36) : ∀ i : Fin 4,
      twistFn (codeFnAt (exceptionalCodeIndexAt j)) (a6GeneratorFn i) =
        conjugateCanonicalTwistFn
          (codeFnAt (exceptionalWitnessIndex (exceptionalCodeIndexAt j)))
          (a6GeneratorFn i) := by
  by_cases h0 : j.val < 6
  · let k : Fin 6 := ⟨j.val, h0⟩
    have hk : exceptionalCandidateBlock 0 k = j := by
      apply Fin.ext
      simp [k]
    rw [← hk]
    exact exceptionalCandidateConjugacyCertificate_block0 k
  by_cases h1 : j.val < 12
  · let k : Fin 6 := ⟨j.val - 6, by omega⟩
    have hk : exceptionalCandidateBlock 1 k = j := by
      apply Fin.ext
      simp [k]
      omega
    rw [← hk]
    exact exceptionalCandidateConjugacyCertificate_block1 k
  by_cases h2 : j.val < 18
  · let k : Fin 6 := ⟨j.val - 12, by omega⟩
    have hk : exceptionalCandidateBlock 2 k = j := by
      apply Fin.ext
      simp [k]
      omega
    rw [← hk]
    exact exceptionalCandidateConjugacyCertificate_block2 k
  by_cases h3 : j.val < 24
  · let k : Fin 6 := ⟨j.val - 18, by omega⟩
    have hk : exceptionalCandidateBlock 3 k = j := by
      apply Fin.ext
      simp [k]
      omega
    rw [← hk]
    exact exceptionalCandidateConjugacyCertificate_block3 k
  by_cases h4 : j.val < 30
  · let k : Fin 6 := ⟨j.val - 24, by omega⟩
    have hk : exceptionalCandidateBlock 4 k = j := by
      apply Fin.ext
      simp [k]
      omega
    rw [← hk]
    exact exceptionalCandidateConjugacyCertificate_block4 k
  · let k : Fin 6 := ⟨j.val - 30, by omega⟩
    have hk : exceptionalCandidateBlock 5 k = j := by
      apply Fin.ext
      simp [k]
      omega
    rw [← hk]
    exact exceptionalCandidateConjugacyCertificate_block5 k


public theorem exceptionalConjugacyCertificate
    (c : PermCodeIndex) (hc : c.val ∈ exceptionalCodeIndexList) :
    ∀ i : Fin 4,
      twistFn (codeFnAt c) (a6GeneratorFn i) =
        conjugateCanonicalTwistFn
          (codeFnAt (exceptionalWitnessIndex c))
          (a6GeneratorFn i) := by
  obtain ⟨j, rfl⟩ := exceptionalCodeIndexAt_complete c hc
  exact exceptionalCandidateConjugacyCertificate j

public theorem exceptionalTwistWitnessCertificate
    (c : PermCodeIndex)
    (hc : exceptionalEquation c) :
    ∀ i : Fin 4,
      twistFn (codeFnAt c) (a6GeneratorFn i) =
        conjugateCanonicalTwistFn
          (codeFnAt (exceptionalWitnessIndex c))
          (a6GeneratorFn i) :=
  exceptionalConjugacyCertificate c (exceptionalEquationCertificate c hc)


end GLS3.Chapter5
/- END Theory.A6OuterAutomorphismConjugacyCertificates -/

/- BEGIN Theory.A6OuterAutomorphismNormalForm -/
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

noncomputable section

namespace GLS3.Chapter5

set_option maxRecDepth 100000 in
public theorem exceptionalTwistCertificate :
    ∀ c : PermCodeIndex,
      compFn (outerFn (codeFnAt c))
          (compFn outerSquareConjugatorFn (codeFnAt c)) = id →
      ∃ d : PermCodeIndex, ∀ i : Fin 4,
        twistFn (codeFnAt c) (a6GeneratorFn i) =
          conjugateCanonicalTwistFn (codeFnAt d) (a6GeneratorFn i) := by
  intro c hc
  exact ⟨exceptionalWitnessIndex c,
    exceptionalTwistWitnessCertificate c hc⟩

@[expose] public def exceptionalTwistAut (σ : Perm6) :
    MulAut (alternatingGroup (Fin 6)) :=
  outerAltAut * MulAut.conjNormal σ

public theorem exceptionalTwistAut_apply_val (σ : Perm6)
    (g : alternatingGroup (Fin 6)) :
    ((exceptionalTwistAut σ g).1 : Perm6) = twistPerm σ g.1 := by
  rfl

public theorem exceptionalTwistAut_square (σ : Perm6) :
    exceptionalTwistAut σ ^ 2 =
      MulAut.conjNormal
        (outerHom σ * outerSquareConjugator * σ) := by
  apply MulEquiv.ext
  intro g
  apply Subtype.ext
  change outerHom
      (σ * outerHom (σ * (g.1 : Perm6) * σ⁻¹) * σ⁻¹) =
    (outerHom σ * outerSquareConjugator * σ) * g.1 *
      (outerHom σ * outerSquareConjugator * σ)⁻¹
  simp only [map_mul]
  simp_rw [outerHom_square_eq_conj]
  rw [map_inv]
  group

@[expose] public def canonicalExceptionalAut :
    MulAut (alternatingGroup (Fin 6)) :=
  exceptionalTwistAut canonicalTwistPerm


@[reducible, expose] public def exceptionalStandardNineX : alternatingGroup (Fin 6) :=
  SchurPresentation.alternatingSuzukiGenerator 1 0

@[reducible, expose] public def exceptionalStandardNineY : alternatingGroup (Fin 6) :=
  (SchurPresentation.alternatingSuzukiGenerator 1 3)⁻¹ *
    (SchurPresentation.alternatingSuzukiGenerator 1 2)⁻¹

@[reducible, expose] public def exceptionalStandardNineInner : Perm6 :=
  permAt 4

public theorem exceptionalStandardNine_x_val :
    exceptionalStandardNineInner *
        twistPerm canonicalTwistPerm exceptionalStandardNineX.1 *
        exceptionalStandardNineInner⁻¹ =
      (exceptionalStandardNineX ^ 2 * exceptionalStandardNineY).1 := by
  apply Equiv.ext
  intro i
  change exceptionalStandardNineInner
      (twistPerm canonicalTwistPerm exceptionalStandardNineX.1
        (exceptionalStandardNineInner.symm i)) = _
  rw [← congrFun (twistFn_equiv canonicalTwistPerm
    exceptionalStandardNineX.1) (exceptionalStandardNineInner.symm i)]
  fin_cases i <;> decide +kernel

public theorem exceptionalStandardNine_y_val :
    exceptionalStandardNineInner *
        twistPerm canonicalTwistPerm exceptionalStandardNineY.1 *
        exceptionalStandardNineInner⁻¹ =
      (exceptionalStandardNineX ^ 2 * exceptionalStandardNineY ^ 2).1 := by
  apply Equiv.ext
  intro i
  change exceptionalStandardNineInner
      (twistPerm canonicalTwistPerm exceptionalStandardNineY.1
        (exceptionalStandardNineInner.symm i)) = _
  rw [← congrFun (twistFn_equiv canonicalTwistPerm
    exceptionalStandardNineY.1) (exceptionalStandardNineInner.symm i)]
  fin_cases i <;> decide +kernel

public theorem exceptionalStandardNine_x :
    ((MulAut.conjNormal exceptionalStandardNineInner :
        MulAut (alternatingGroup (Fin 6))) * canonicalExceptionalAut)
        exceptionalStandardNineX =
      exceptionalStandardNineX ^ 2 * exceptionalStandardNineY := by
  apply Subtype.ext
  exact exceptionalStandardNine_x_val

public theorem exceptionalStandardNine_y :
    ((MulAut.conjNormal exceptionalStandardNineInner :
        MulAut (alternatingGroup (Fin 6))) * canonicalExceptionalAut)
        exceptionalStandardNineY =
      exceptionalStandardNineX ^ 2 * exceptionalStandardNineY ^ 2 := by
  apply Subtype.ext
  exact exceptionalStandardNine_y_val


@[reducible, expose] public def naturalStandardNineReflection : Perm6 :=
  Equiv.swap 0 1

public theorem naturalStandardNineReflection_x :
    (MulAut.conjNormal naturalStandardNineReflection)
        exceptionalStandardNineX = exceptionalStandardNineX⁻¹ := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  fin_cases i <;> decide +kernel

public theorem naturalStandardNineReflection_y :
    (MulAut.conjNormal naturalStandardNineReflection)
        exceptionalStandardNineY = exceptionalStandardNineY := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  fin_cases i <;> decide +kernel

public theorem a6ExceptionalConjugatorLiftAut_stabilizes_kernel :
    ∀ g : a6DoubleCoverPermutationSubgroup,
      g ∈ a6DoubleCoverBlockCoverHom.ker ↔
        a6ExceptionalConjugatorLiftAut g ∈ a6DoubleCoverBlockCoverHom.ker := by
  intro g
  rw [← a6DoubleCover_center_eq_ker]
  constructor
  · intro hg
    rw [Subgroup.mem_center_iff] at hg ⊢
    intro h
    obtain ⟨k, rfl⟩ := a6ExceptionalConjugatorLiftAut.surjective h
    simpa [map_mul] using congrArg a6ExceptionalConjugatorLiftAut (hg k)
  · intro hg
    rw [Subgroup.mem_center_iff] at hg ⊢
    intro h
    have hh := hg (a6ExceptionalConjugatorLiftAut h)
    have hback := congrArg a6ExceptionalConjugatorLiftAut.symm hh
    simpa [map_mul] using hback

@[expose] public noncomputable def a6ExceptionalKernelStabilizer :
    Covering.kernelStabilizer a6DoubleCover_covering :=
  ⟨a6ExceptionalConjugatorLiftAut,
    a6ExceptionalConjugatorLiftAut_stabilizes_kernel⟩

@[expose] public noncomputable def a6ExceptionalQuotientAut :
    MulAut (alternatingGroup (Fin 6)) :=
  Covering.descendMulAut a6DoubleCover_covering a6ExceptionalKernelStabilizer

public theorem a6ExceptionalQuotientAut_compat
    (g : a6DoubleCoverPermutationSubgroup) :
    a6ExceptionalQuotientAut (a6DoubleCoverBlockCoverHom g) =
      a6DoubleCoverBlockCoverHom (a6ExceptionalConjugatorLiftAut g) := by
  have h := congrArg (fun q : a6DoubleCoverPermutationSubgroup →*
      alternatingGroup (Fin 6) => q g)
    (Covering.descendMulAut_fac a6DoubleCover_covering a6ExceptionalKernelStabilizer)
  exact h

public theorem a6ExceptionalConjugatorLiftAut_eq_quotientLift :
    a6ExceptionalConjugatorLiftAut =
      SchurPresentation.doubleCoverLiftMulAut 1 a6DoubleCover_covering
        a6DoubleCoverBlockCoverHom_kernel_card a6ExceptionalQuotientAut := by
  apply SchurPresentation.doubleCoverLiftMulAut_unique 1
    a6DoubleCover_covering a6DoubleCoverBlockCoverHom_kernel_card
    a6ExceptionalQuotientAut
  apply Covering.ext
  intro g
  exact (a6ExceptionalQuotientAut_compat g).symm

public theorem a6ExceptionalQuotientAut_gen2_not_threeCycle :
    (((a6ExceptionalQuotientAut
      (a6DoubleCoverBlockCoverHom a6DoubleCoverGen2Sub)).1 : Perm6).cycleType) ≠
      {3} := by
  rw [a6ExceptionalQuotientAut_compat]
  have hword : a6ExceptionalConjugatorLiftAut a6DoubleCoverGen2Sub =
      a6DoubleCoverGen1Sub * a6DoubleCoverGen2Sub *
        a6DoubleCoverGen1Sub * a6DoubleCoverGen2Sub⁻¹ *
        a6DoubleCoverGen1Sub⁻¹ * a6DoubleCoverGen2Sub⁻¹ := by
    apply Subtype.ext
    rw [a6ExceptionalConjugatorLiftAut_apply]
    exact a6ExceptionalConjugator_conj_gen2
  rw [hword]
  simp only [map_mul, map_inv, a6DoubleCoverBlockCoverHom_gen1,
    a6DoubleCoverBlockCoverHom_gen2]
  decide +kernel

public theorem a6ExceptionalQuotientAut_not_mem_natural :
    a6ExceptionalQuotientAut ∉ naturalAlternatingAutomorphismSubgroup := by
  intro hmem
  rcases hmem with ⟨σ, hσ⟩
  have hthree :
      (((a6ExceptionalQuotientAut
        (a6DoubleCoverBlockCoverHom a6DoubleCoverGen2Sub)).1 : Perm6).cycleType) =
        {3} := by
    rw [← hσ, a6DoubleCoverBlockCoverHom_gen2]
    change (σ * a6DoubleCoverQuotientGen2 * σ⁻¹).cycleType = {3}
    rw [Equiv.Perm.cycleType_conj]
    decide +kernel
  exact a6ExceptionalQuotientAut_gen2_not_threeCycle hthree

public theorem a6ExceptionalConjugatorLiftAut_sq :
    a6ExceptionalConjugatorLiftAut ^ 2 = 1 := by
  apply MulEquiv.ext
  intro g
  rw [pow_two, MulAut.mul_apply, MulAut.one_apply]
  apply Subtype.ext
  rw [a6ExceptionalConjugatorLiftAut_apply,
    a6ExceptionalConjugatorLiftAut_apply]
  have hu : a6ExceptionalConjugator⁻¹ = a6ExceptionalConjugator := by
    apply inv_eq_of_mul_eq_one_left
    simpa [pow_two] using a6ExceptionalConjugator_sq
  rw [hu]
  calc
    a6ExceptionalConjugator *
        (a6ExceptionalConjugator * (g : Perm144) * a6ExceptionalConjugator) *
          a6ExceptionalConjugator =
      (a6ExceptionalConjugator * a6ExceptionalConjugator) * g *
        (a6ExceptionalConjugator * a6ExceptionalConjugator) := by group
    _ = g := by
      rw [show a6ExceptionalConjugator * a6ExceptionalConjugator = 1 by
        simpa [pow_two] using a6ExceptionalConjugator_sq]
      simp

public theorem a6ExceptionalConjugatorLiftAut_ne_one :
    a6ExceptionalConjugatorLiftAut ≠ 1 := by
  intro h
  have happ : a6ExceptionalConjugatorLiftAut a6TwistedReflectionLiftSub =
      a6TwistedReflectionLiftSub := by
    rw [h]
    rfl
  rw [a6ExceptionalConjugatorLiftAut_twistsReflection] at happ
  have hcentral : a6DoubleCoverCentralSub = 1 := by
    exact mul_right_cancel (happ.trans (one_mul _).symm)
  exact a6DoubleCoverCentralSub_ne_one hcentral

public theorem a6ExceptionalConjugatorLiftAut_order :
    orderOf a6ExceptionalConjugatorLiftAut = 2 :=
  orderOf_eq_prime a6ExceptionalConjugatorLiftAut_sq
    a6ExceptionalConjugatorLiftAut_ne_one

public theorem a6ExceptionalQuotientAut_order :
    orderOf a6ExceptionalQuotientAut = 2 := by
  rw [← SchurPresentation.orderOf_doubleCoverLiftMulAut 1
    a6DoubleCover_covering a6DoubleCoverBlockCoverHom_kernel_card
    a6ExceptionalQuotientAut,
    ← a6ExceptionalConjugatorLiftAut_eq_quotientLift]
  exact a6ExceptionalConjugatorLiftAut_order

@[expose] public def conjugateCanonicalExceptionalAut (τ : Perm6) :
    MulAut (alternatingGroup (Fin 6)) :=
  MulAut.conjNormal τ * canonicalExceptionalAut * (MulAut.conjNormal τ)⁻¹

public theorem conjugateCanonicalExceptionalAut_apply_val (τ : Perm6)
    (g : alternatingGroup (Fin 6)) :
    ((conjugateCanonicalExceptionalAut τ g).1 : Perm6) =
      conjugateCanonicalTwistPerm τ g.1 := by
  rfl

public theorem exceptionalTwistAut_eq_conjugate_of_certificate
    (c d : PermCodeIndex)
    (hd : ∀ i : Fin 4,
      twistFn (codeFnAt c) (a6GeneratorFn i) =
        conjugateCanonicalTwistFn (codeFnAt d) (a6GeneratorFn i)) :
    exceptionalTwistAut (permAt c) =
      conjugateCanonicalExceptionalAut (permAt d) := by
  have hgenerator (i : Fin 4) :
      exceptionalTwistAut (permAt c)
          (SchurPresentation.alternatingSuzukiGenerator 1 i) =
        conjugateCanonicalExceptionalAut (permAt d)
          (SchurPresentation.alternatingSuzukiGenerator 1 i) := by
    apply Subtype.ext
    have hdi := hd i
    rw [codeFnAt_eq_permAt, codeFnAt_eq_permAt,
      show a6GeneratorFn i = a6Generator i by rfl,
      twistFn_equiv, conjugateCanonicalTwistFn_equiv] at hdi
    rw [exceptionalTwistAut_apply_val,
      conjugateCanonicalExceptionalAut_apply_val, ← a6Generator_eq]
    exact Equiv.ext fun j => congrFun hdi j
  apply MulEquiv.ext
  have hhom : (exceptionalTwistAut (permAt c)).toMonoidHom =
      (conjugateCanonicalExceptionalAut (permAt d)).toMonoidHom := by
    apply MonoidHom.eq_of_eqOn_dense
      (SchurPresentation.alternatingSuzukiGenerator_closure_eq_top 1)
    intro g hg
    rcases hg with ⟨i, rfl⟩
    exact hgenerator i
  intro g
  exact DFunLike.congr_fun hhom g

public theorem exceptionalCandidateAut_eq_conjugate (j : Fin 36) :
    exceptionalTwistAut (permAt (exceptionalCodeIndexAt j)) =
      conjugateCanonicalExceptionalAut (exceptionalConjugatorAt j).1 := by
  change exceptionalTwistAut (permAt (exceptionalCodeIndexAt j)) =
    conjugateCanonicalExceptionalAut
      (permAt (exceptionalWitnessIndex (exceptionalCodeIndexAt j)))
  exact exceptionalTwistAut_eq_conjugate_of_certificate
    (exceptionalCodeIndexAt j)
    (exceptionalWitnessIndex (exceptionalCodeIndexAt j))
    (exceptionalCandidateConjugacyCertificate j)

public theorem exceptionalTwistAut_injective :
    Function.Injective exceptionalTwistAut := by
  intro σ τ hστ
  apply GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6
    (by decide)
  have h := congrArg (fun α : MulAut (alternatingGroup (Fin 6)) =>
    outerAltAut⁻¹ * α) hστ
  simpa [exceptionalTwistAut] using h

public theorem mulAut_conj_transport
    {G : Type*} [Group G] (α : MulAut G) (g : G) :
    α * MulAut.conj g * α⁻¹ = MulAut.conj (α g) := by
  apply MulEquiv.ext
  intro z
  simp [MulAut.mul_apply, MulAut.conj_apply]

public theorem conjugateCanonicalExceptionalAut_eq_of_fixed_difference
    (τ υ : alternatingGroup (Fin 6))
    (hfix : canonicalExceptionalAut (υ⁻¹ * τ) = υ⁻¹ * τ) :
    conjugateCanonicalExceptionalAut τ.1 =
      conjugateCanonicalExceptionalAut υ.1 := by
  let d : alternatingGroup (Fin 6) := υ⁻¹ * τ
  have htransport := mulAut_conj_transport canonicalExceptionalAut d
  have hd : canonicalExceptionalAut d = d := hfix
  rw [hd] at htransport
  have hcomm : canonicalExceptionalAut * MulAut.conj d =
      MulAut.conj d * canonicalExceptionalAut := by
    calc
      canonicalExceptionalAut * MulAut.conj d =
          (canonicalExceptionalAut * MulAut.conj d *
            canonicalExceptionalAut⁻¹) * canonicalExceptionalAut := by group
      _ = MulAut.conj d * canonicalExceptionalAut := by rw [htransport]
  have hτ : τ = υ * d := by
    dsimp [d]
    group
  unfold conjugateCanonicalExceptionalAut
  rw [MulAut.conjNormal_val, MulAut.conjNormal_val, hτ, map_mul]
  calc
    (MulAut.conj υ * MulAut.conj d) * canonicalExceptionalAut *
          (MulAut.conj υ * MulAut.conj d)⁻¹ =
        MulAut.conj υ *
          (MulAut.conj d * canonicalExceptionalAut *
            (MulAut.conj d)⁻¹) *
          (MulAut.conj υ)⁻¹ := by group
    _ = MulAut.conj υ * canonicalExceptionalAut *
          (MulAut.conj υ)⁻¹ := by
      rw [hcomm.symm]
      group

@[expose] public def canonicalFixedPacking :
    Fin 36 × automorphismFixedSubgroup canonicalExceptionalAut →
      alternatingGroup (Fin 6) :=
  fun z => exceptionalConjugatorAt z.1 * z.2.1

public theorem canonicalFixedPacking_injective :
    Function.Injective canonicalFixedPacking := by
  rintro ⟨j, g⟩ ⟨k, h⟩ hjk
  change exceptionalConjugatorAt j * g.1 =
    exceptionalConjugatorAt k * h.1 at hjk
  have hdEq : (exceptionalConjugatorAt k)⁻¹ * exceptionalConjugatorAt j =
      h.1 * g.1⁻¹ := by
    calc
      (exceptionalConjugatorAt k)⁻¹ * exceptionalConjugatorAt j =
          (exceptionalConjugatorAt k)⁻¹ *
            (exceptionalConjugatorAt j * g.1) * g.1⁻¹ := by group
      _ = (exceptionalConjugatorAt k)⁻¹ *
            (exceptionalConjugatorAt k * h.1) * g.1⁻¹ := by
          rw [hjk]
      _ = h.1 * g.1⁻¹ := by group
  have hdFixed : canonicalExceptionalAut
      ((exceptionalConjugatorAt k)⁻¹ * exceptionalConjugatorAt j) =
        (exceptionalConjugatorAt k)⁻¹ * exceptionalConjugatorAt j := by
    rw [hdEq, map_mul, map_inv, h.2, g.2]
  have hconj :
      conjugateCanonicalExceptionalAut (exceptionalConjugatorAt j).1 =
        conjugateCanonicalExceptionalAut (exceptionalConjugatorAt k).1 :=
    conjugateCanonicalExceptionalAut_eq_of_fixed_difference
      (exceptionalConjugatorAt j) (exceptionalConjugatorAt k) hdFixed
  have haut :
      exceptionalTwistAut (permAt (exceptionalCodeIndexAt j)) =
        exceptionalTwistAut (permAt (exceptionalCodeIndexAt k)) := by
    rw [exceptionalCandidateAut_eq_conjugate,
      exceptionalCandidateAut_eq_conjugate]
    exact hconj
  have hperm : permAt (exceptionalCodeIndexAt j) =
      permAt (exceptionalCodeIndexAt k) :=
    exceptionalTwistAut_injective haut
  have hfn : codeFnAt (exceptionalCodeIndexAt j) =
      codeFnAt (exceptionalCodeIndexAt k) := by
    rw [codeFnAt_eq_permAt, codeFnAt_eq_permAt, hperm]
  have hjkeq : j = k := exceptionalCandidatePermFn_injective hfn
  subst k
  have hgh : g = h := by
    apply Subtype.ext
    exact mul_left_cancel hjk
  rw [hgh]

public theorem exceptionalTwistAut_conjugate_canonical (σ : Perm6)
    (hσsq : exceptionalTwistAut σ ^ 2 = 1) :
    ∃ τ : Perm6,
      exceptionalTwistAut σ = conjugateCanonicalExceptionalAut τ := by
  let c : PermCodeIndex := codeIndexOfPerm σ
  have hcode : codeFnAt c = σ := codeFnAt_codeIndexOfPerm σ
  have hproduct : outerHom σ * outerSquareConjugator * σ = 1 := by
    apply GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6
      (by decide)
    rw [← exceptionalTwistAut_square, hσsq, map_one]
  have hcertificate :
      compFn (outerFn (codeFnAt c))
          (compFn outerSquareConjugatorFn (codeFnAt c)) = id := by
    rw [hcode, outerFn_equiv]
    exact congrArg (fun e : Perm6 => (e : PermFn6)) hproduct
  obtain ⟨d, hd⟩ := exceptionalTwistCertificate c hcertificate
  let τ : Perm6 := permAt d
  refine ⟨τ, ?_⟩
  have hperm : permAt c = σ := by
    apply Equiv.ext
    intro i
    exact congrFun ((codeFnAt_eq_permAt c).symm.trans hcode) i
  rw [← hperm]
  exact exceptionalTwistAut_eq_conjugate_of_certificate c d hd

@[expose] public def automorphismFixedSubgroup_conjMulEquiv
    {G : Type*} [Group G] (α u : MulAut G) :
    automorphismFixedSubgroup (u * α * u⁻¹) ≃*
      automorphismFixedSubgroup α where
  toFun g := ⟨u⁻¹ g.1, by
    change α (u⁻¹ g.1) = u⁻¹ g.1
    have hg : (u * α * u⁻¹) g.1 = g.1 := g.2
    have hu := congrArg (fun z : G => u⁻¹ z) hg
    simpa [MulAut.mul_apply] using hu⟩
  invFun g := ⟨u g.1, by
    change (u * α * u⁻¹) (u g.1) = u g.1
    have hg : α g.1 = g.1 := g.2
    have hu := congrArg (fun z : G => u z) hg
    simpa [MulAut.mul_apply] using hu⟩
  left_inv g := by
    apply Subtype.ext
    exact EquivLike.apply_inv_apply u g.1
  right_inv g := by
    apply Subtype.ext
    exact EquivLike.inv_apply_apply u g.1
  map_mul' a b := by
    apply Subtype.ext
    exact map_mul u⁻¹ a.1 b.1

@[expose] public noncomputable def conjugateCanonicalFixedMulEquiv (τ : Perm6) :
    automorphismFixedSubgroup (conjugateCanonicalExceptionalAut τ) ≃*
      automorphismFixedSubgroup canonicalExceptionalAut := by
  change automorphismFixedSubgroup
      (MulAut.conjNormal τ * canonicalExceptionalAut *
        (MulAut.conjNormal τ)⁻¹) ≃*
    automorphismFixedSubgroup canonicalExceptionalAut
  exact automorphismFixedSubgroup_conjMulEquiv canonicalExceptionalAut
    (MulAut.conjNormal τ)

@[expose] public def automorphismFixedSubgroup_intertwiningMulEquiv
    {G L : Type*} [Group G] [Group L]
    (e : G ≃* L) (alpha : MulAut G) (beta : MulAut L)
    (h : ∀ g : G, e (alpha g) = beta (e g)) :
    automorphismFixedSubgroup alpha ≃* automorphismFixedSubgroup beta where
  toFun g := ⟨e g.1, by
    change beta (e g.1) = e g.1
    rw [← h, g.2]⟩
  invFun l := ⟨e.symm l.1, by
    apply e.injective
    calc
      e (alpha (e.symm l.1)) = beta (e (e.symm l.1)) := h _
      _ = beta l.1 := by rw [e.apply_symm_apply]
      _ = l.1 := l.2
      _ = e (e.symm l.1) := (e.apply_symm_apply l.1).symm⟩
  left_inv g := by
    apply Subtype.ext
    exact e.symm_apply_apply g.1
  right_inv l := by
    apply Subtype.ext
    exact e.apply_symm_apply l.1
  map_mul' g h := by
    apply Subtype.ext
    exact map_mul e g.1 h.1

public theorem outerAltAut_not_mem_natural :
    outerAltAut ∉ naturalAlternatingAutomorphismSubgroup := by
  intro hout
  rcases hout with ⟨σ, hσ⟩
  have hconjThree :
      ((((MulAut.conjNormal σ) baseThreeCycle).1 : Perm6)).IsThreeCycle := by
    change (σ * threeCyclePerm * σ⁻¹).cycleType = {3}
    rw [Equiv.Perm.cycleType_conj]
    exact baseThreeCycle_isThreeCycle
  have houtThree : (((outerAltAut baseThreeCycle).1 : Perm6)).IsThreeCycle := by
    rw [← hσ]
    exact hconjThree
  change ((outerAltAut baseThreeCycle).1 : Perm6).cycleType = {3} at houtThree
  have hbad := outerAltAut_base_cycleType.symm.trans houtThree
  have hcard := congrArg Multiset.card hbad
  norm_num at hcard

public theorem exceptionalAut_eq_twist
    (α : MulAut (alternatingGroup (Fin 6)))
    (hα : α ∉ naturalAlternatingAutomorphismSubgroup) :
    ∃ σ : Perm6, α = exceptionalTwistAut σ := by
  let N := naturalAlternatingAutomorphismSubgroup
  have hmem : outerAltAut⁻¹ * α ∈ N := by
    rw [Subgroup.mul_mem_iff_of_index_two
      naturalAlternatingAutomorphismSubgroup_index]
    simp [outerAltAut_not_mem_natural, hα]
  change outerAltAut⁻¹ * α ∈
    (MulAut.conjNormal : Perm6 →*
      MulAut (alternatingGroup (Fin 6))).range at hmem
  rcases hmem with ⟨σ, hσ⟩
  refine ⟨σ, ?_⟩
  rw [exceptionalTwistAut, hσ]
  simp


public theorem a6_noninner_involution_standardNine_normalForm
    (β : MulAut (alternatingGroup (Fin 6)))
    (hβOrder : orderOf β = 2)
    (hβNoninner : ∀ g : alternatingGroup (Fin 6), β ≠ MulAut.conj g) :
    (∃ δ : alternatingGroup (Fin 6),
      let γ := MulAut.conj δ * β
      γ exceptionalStandardNineX = exceptionalStandardNineX⁻¹ ∧
        γ exceptionalStandardNineY = exceptionalStandardNineY) ∨
    (∃ τ : Perm6,
      let γ := (MulAut.conjNormal exceptionalStandardNineInner :
          MulAut (alternatingGroup (Fin 6))) *
        (MulAut.conjNormal τ)⁻¹ * β * MulAut.conjNormal τ
      γ exceptionalStandardNineX =
          exceptionalStandardNineX ^ 2 * exceptionalStandardNineY ∧
        γ exceptionalStandardNineY =
          exceptionalStandardNineX ^ 2 * exceptionalStandardNineY ^ 2) := by
  by_cases hβNatural : β ∈ naturalAlternatingAutomorphismSubgroup
  · left
    rcases hβNatural with ⟨σ, hσ⟩
    have hsign : σ.sign = -1 := by
      rcases Int.units_eq_one_or σ.sign with hone | hneg
      · let g : alternatingGroup (Fin 6) :=
          ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hone⟩
        exfalso
        apply (hβNoninner g)
        rw [← MulAut.conjNormal_val]
        exact hσ.symm
      · exact hneg
    let δPerm : Perm6 := naturalStandardNineReflection * σ⁻¹
    have hδ : δPerm ∈ alternatingGroup (Fin 6) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      dsimp [δPerm]
      rw [map_mul, map_inv, Equiv.Perm.sign_swap (by decide), hsign]
      all_goals decide
    let δ : alternatingGroup (Fin 6) := ⟨δPerm, hδ⟩
    refine ⟨δ, ?_⟩
    have hγ : MulAut.conj δ * β =
        MulAut.conjNormal naturalStandardNineReflection := by
      rw [← hσ]
      change MulAut.conjNormal δ.1 * MulAut.conjNormal σ = _
      rw [← map_mul]
      apply congrArg MulAut.conjNormal
      dsimp [δ, δPerm]
      group
    rw [hγ]
    exact ⟨naturalStandardNineReflection_x,
      naturalStandardNineReflection_y⟩
  · right
    obtain ⟨σ, hσ⟩ := exceptionalAut_eq_twist β hβNatural
    have hsq : exceptionalTwistAut σ ^ 2 = 1 := by
      rw [← hσ, ← hβOrder]
      exact pow_orderOf_eq_one β
    obtain ⟨τ, hτ⟩ := exceptionalTwistAut_conjugate_canonical σ hsq
    refine ⟨τ, ?_⟩
    have hγ :
        (MulAut.conjNormal exceptionalStandardNineInner :
            MulAut (alternatingGroup (Fin 6))) *
          (MulAut.conjNormal τ)⁻¹ * β * MulAut.conjNormal τ =
        (MulAut.conjNormal exceptionalStandardNineInner :
            MulAut (alternatingGroup (Fin 6))) * canonicalExceptionalAut := by
      rw [hσ, hτ]
      dsimp [conjugateCanonicalExceptionalAut]
      group
    rw [hγ]
    exact ⟨exceptionalStandardNine_x, exceptionalStandardNine_y⟩

/-- A non-inner involution of `A₆` has one of the two determinant-minus-one
normal forms on the standard elementary abelian subgroup of order nine.  The
second form records both the natural conjugating permutation and the inner
factor separately, so its statement exposes no implementation-specific
permutation constants. -/
public theorem a6_noninner_standardNine_normalForm
    (β : MulAut (alternatingGroup (Fin 6)))
    (hβOrder : orderOf β = 2)
    (hβNoninner : ∀ g : alternatingGroup (Fin 6), β ≠ MulAut.conj g) :
    (∃ δ : alternatingGroup (Fin 6),
      let γ := MulAut.conj δ * β
      γ SchurPresentation.Theorem523BaseNine.a6X =
          SchurPresentation.Theorem523BaseNine.a6X⁻¹ ∧
        γ SchurPresentation.Theorem523BaseNine.a6Y =
          SchurPresentation.Theorem523BaseNine.a6Y) ∨
    (∃ τ : Equiv.Perm (Fin 6), ∃ δ : alternatingGroup (Fin 6),
      let γ := MulAut.conj δ * (MulAut.conjNormal τ)⁻¹ * β *
        MulAut.conjNormal τ
      γ SchurPresentation.Theorem523BaseNine.a6X =
          SchurPresentation.Theorem523BaseNine.a6X ^ 2 *
            SchurPresentation.Theorem523BaseNine.a6Y ∧
        γ SchurPresentation.Theorem523BaseNine.a6Y =
          SchurPresentation.Theorem523BaseNine.a6X ^ 2 *
            SchurPresentation.Theorem523BaseNine.a6Y ^ 2) := by
  obtain hnormal | hnormal :=
    a6_noninner_involution_standardNine_normalForm β hβOrder hβNoninner
  · left
    obtain ⟨δ, hX, hY⟩ := hnormal
    exact ⟨δ, hX, hY⟩
  · right
    obtain ⟨τ, hX, hY⟩ := hnormal
    let δ : alternatingGroup (Fin 6) :=
      ⟨exceptionalStandardNineInner, by
        rw [Equiv.Perm.mem_alternatingGroup]
        decide⟩
    refine ⟨τ, δ, ?_, ?_⟩
    · change ((((MulAut.conjNormal exceptionalStandardNineInner :
          MulAut (alternatingGroup (Fin 6))) *
        (MulAut.conjNormal τ)⁻¹ * β * MulAut.conjNormal τ) :
          MulAut (alternatingGroup (Fin 6))) exceptionalStandardNineX =
        exceptionalStandardNineX ^ 2 * exceptionalStandardNineY)
      exact hX
    · change ((((MulAut.conjNormal exceptionalStandardNineInner :
          MulAut (alternatingGroup (Fin 6))) *
        (MulAut.conjNormal τ)⁻¹ * β * MulAut.conjNormal τ) :
          MulAut (alternatingGroup (Fin 6))) exceptionalStandardNineY =
        exceptionalStandardNineX ^ 2 * exceptionalStandardNineY ^ 2)
      exact hY


end GLS3.Chapter5
/- END Theory.A6OuterAutomorphismNormalForm -/

/- BEGIN KGroup.GLS3.Chapter5.proposition_5_2_7 -/
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

noncomputable section

namespace GLS3.Chapter5

private theorem __ch5_proposition_5_2_7_quotientAction_order'
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    {n p : Nat} (hp : p.Prime)
    (quotientEquiv : K ⧸ Subgroup.center K ≃*
      alternatingGroup (Fin n))
    (x : MulAut K) (hx : orderOf x = p)
    (quotientAction : MulAut (alternatingGroup (Fin n)))
    (quotientAction_compat : ∀ k : K,
      quotientEquiv (QuotientGroup.mk' (Subgroup.center K) (x k)) =
        quotientAction
          (quotientEquiv (QuotientGroup.mk' (Subgroup.center K) k))) :
    orderOf quotientAction = p := by
  have hiter : ∀ m : Nat, ∀ k : K,
      (alternatingQuotientHom quotientEquiv) ((x ^ m) k) =
        (quotientAction ^ m) ((alternatingQuotientHom quotientEquiv) k) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        intro k
        rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply,
          ih (x k)]
        exact congrArg (quotientAction ^ m) (quotientAction_compat k)
  have hpow : quotientAction ^ p = 1 := by
    apply DFunLike.ext _ _
    intro a
    obtain ⟨k, rfl⟩ :=
      (quotientEquiv.surjective.comp
        (QuotientGroup.mk'_surjective (Subgroup.center K))) a
    have hit := hiter p k
    have hxpow : x ^ p = 1 := by
      rw [← hx]
      exact pow_orderOf_eq_one x
    rw [hxpow, MulAut.one_apply] at hit
    exact hit.symm
  have hdvd : orderOf quotientAction ∣ p :=
    orderOf_dvd_iff_pow_eq_one.mpr hpow
  rcases (Nat.dvd_prime hp).mp hdvd with hone | hp'
  · exfalso
    have haone : quotientAction = 1 := orderOf_eq_one_iff.mp hone
    have hxhom : x.toMonoidHom = (1 : MulAut K).toMonoidHom := by
      apply SchurPresentation.monoidHom_eq_of_isPerfect_of_comp_eq
        (alternatingQuotientHom quotientEquiv)
        (by
          intro k hk
          change (alternatingQuotientHom quotientEquiv) k = 1 at hk
          simpa [alternatingQuotientHom] using hk)
      apply MonoidHom.ext
      intro k
      change (alternatingQuotientHom quotientEquiv) (x k) =
        (alternatingQuotientHom quotientEquiv) k
      calc
        (alternatingQuotientHom quotientEquiv) (x k) =
            quotientAction ((alternatingQuotientHom quotientEquiv) k) :=
          quotientAction_compat k
        _ = (alternatingQuotientHom quotientEquiv) k := by rw [haone]; rfl
    have hxone : x = 1 := by
      apply MulEquiv.ext
      intro k
      exact DFunLike.congr_fun hxhom k
    have h : orderOf x = 1 := by rw [hxone]; exact orderOf_one
    rw [hx] at h
    exact hp.ne_one h
  · exact hp'

private theorem __ch5_proposition_5_2_7_quotientAction_not_mem_natural
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (quotientEquiv : K ⧸ Subgroup.center K ≃*
      alternatingGroup (Fin 6))
    (x : MulAut K)
    (H : Subgroup (MulAut K))
    (HEquiv : H ≃* Equiv.Perm (Fin 6))
    (quotientAction : MulAut (alternatingGroup (Fin 6)))
    (quotientAction_compat : ∀ k : K,
      quotientEquiv (QuotientGroup.mk' (Subgroup.center K) (x k)) =
        quotientAction
          (quotientEquiv (QuotientGroup.mk' (Subgroup.center K) k)))
    (H_action_compat : ∀ h : H, ∀ k : K,
      quotientEquiv (QuotientGroup.mk' (Subgroup.center K) (h.1 k)) =
        MulAut.conjNormal (HEquiv h)
          (quotientEquiv (QuotientGroup.mk' (Subgroup.center K) k)))
    (hxH : x ∉ H) :
    quotientAction ∉ naturalAlternatingAutomorphismSubgroup := by
  intro haction
  change quotientAction ∈
    (MulAut.conjNormal : Perm6 →*
      MulAut (alternatingGroup (Fin 6))).range at haction
  rcases haction with ⟨σ, hσ⟩
  let h : H := HEquiv.symm σ
  have hHequiv : HEquiv h = σ := HEquiv.apply_symm_apply σ
  have hxhom : x.toMonoidHom = h.1.toMonoidHom := by
    apply SchurPresentation.monoidHom_eq_of_isPerfect_of_comp_eq
      (alternatingQuotientHom quotientEquiv)
      (by
        intro k hk
        change (alternatingQuotientHom quotientEquiv) k = 1 at hk
        simpa [alternatingQuotientHom] using hk)
    apply MonoidHom.ext
    intro k
    change (alternatingQuotientHom quotientEquiv) (x k) =
      (alternatingQuotientHom quotientEquiv) (h.1 k)
    calc
      (alternatingQuotientHom quotientEquiv) (x k) =
          quotientAction ((alternatingQuotientHom quotientEquiv) k) :=
        quotientAction_compat k
      _ = MulAut.conjNormal σ ((alternatingQuotientHom quotientEquiv) k) := by
        rw [hσ]
      _ = MulAut.conjNormal (HEquiv h)
          ((alternatingQuotientHom quotientEquiv) k) := by rw [hHequiv]
      _ = (alternatingQuotientHom quotientEquiv) (h.1 k) :=
        (H_action_compat h k).symm
  have hxh : x = h.1 := by
    apply MulEquiv.ext
    intro k
    exact DFunLike.congr_fun hxhom k
  apply hxH
  rw [hxh]
  exact h.2

@[reducible] private def __ch5_proposition_5_2_7_canonicalRotationPerm : Perm6 :=
  Equiv.swap 0 5 * Equiv.swap 0 2 *
    Equiv.swap 0 3 * Equiv.swap 0 1

@[reducible] private def __ch5_proposition_5_2_7_canonicalReflectionPerm : Perm6 :=
  Equiv.swap 1 5 * Equiv.swap 2 3

@[reducible] private def __ch5_proposition_5_2_7_canonicalRotation : alternatingGroup (Fin 6) :=
  ⟨__ch5_proposition_5_2_7_canonicalRotationPerm, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide⟩

@[reducible] private def __ch5_proposition_5_2_7_canonicalReflection : alternatingGroup (Fin 6) :=
  ⟨__ch5_proposition_5_2_7_canonicalReflectionPerm, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide⟩

private theorem __ch5_proposition_5_2_7_canonicalRotation_fixed :
    canonicalExceptionalAut __ch5_proposition_5_2_7_canonicalRotation = __ch5_proposition_5_2_7_canonicalRotation := by
  apply Subtype.ext
  change twistPerm canonicalTwistPerm __ch5_proposition_5_2_7_canonicalRotationPerm =
    __ch5_proposition_5_2_7_canonicalRotationPerm
  apply Equiv.ext
  intro i
  rw [← twistFn_equiv canonicalTwistPerm __ch5_proposition_5_2_7_canonicalRotationPerm]
  fin_cases i <;> decide +kernel

private theorem __ch5_proposition_5_2_7_canonicalReflection_fixed :
    canonicalExceptionalAut __ch5_proposition_5_2_7_canonicalReflection = __ch5_proposition_5_2_7_canonicalReflection := by
  apply Subtype.ext
  change twistPerm canonicalTwistPerm __ch5_proposition_5_2_7_canonicalReflectionPerm =
    __ch5_proposition_5_2_7_canonicalReflectionPerm
  apply Equiv.ext
  intro i
  rw [← twistFn_equiv canonicalTwistPerm __ch5_proposition_5_2_7_canonicalReflectionPerm]
  fin_cases i <;> decide +kernel

@[reducible] private def __ch5_proposition_5_2_7_fixedRotation :
    automorphismFixedSubgroup canonicalExceptionalAut :=
  ⟨__ch5_proposition_5_2_7_canonicalRotation, __ch5_proposition_5_2_7_canonicalRotation_fixed⟩

@[reducible] private def __ch5_proposition_5_2_7_fixedReflection :
    automorphismFixedSubgroup canonicalExceptionalAut :=
  ⟨__ch5_proposition_5_2_7_canonicalReflection, __ch5_proposition_5_2_7_canonicalReflection_fixed⟩

@[reducible] private def __ch5_proposition_5_2_7_dihedralImagePerm : DihedralGroup 5 → Perm6
  | .r i => __ch5_proposition_5_2_7_canonicalRotationPerm ^ i.val
  | .sr i => __ch5_proposition_5_2_7_canonicalReflectionPerm * __ch5_proposition_5_2_7_canonicalRotationPerm ^ i.val

@[reducible] private def __ch5_proposition_5_2_7_dihedralImageFn (d : DihedralGroup 5) : PermFn6 :=
  __ch5_proposition_5_2_7_dihedralImagePerm d

@[reducible] private def __ch5_proposition_5_2_7_canonicalDihedralMap :
    DihedralGroup 5 → automorphismFixedSubgroup canonicalExceptionalAut
  | .r i => __ch5_proposition_5_2_7_fixedRotation ^ i.val
  | .sr i => __ch5_proposition_5_2_7_fixedReflection * __ch5_proposition_5_2_7_fixedRotation ^ i.val

private theorem __ch5_proposition_5_2_7_canonicalDihedralMap_apply_val (d : DihedralGroup 5) :
    (((__ch5_proposition_5_2_7_canonicalDihedralMap d).1.1 : Perm6)) = __ch5_proposition_5_2_7_dihedralImagePerm d := by
  cases d <;> rfl

private theorem __ch5_proposition_5_2_7_canonicalDihedralMap_mul (a b : DihedralGroup 5) :
    __ch5_proposition_5_2_7_canonicalDihedralMap (a * b) =
      __ch5_proposition_5_2_7_canonicalDihedralMap a * __ch5_proposition_5_2_7_canonicalDihedralMap b := by
  apply Subtype.ext
  apply Subtype.ext
  change (((__ch5_proposition_5_2_7_canonicalDihedralMap (a * b)).1.1 : Perm6)) =
    (((__ch5_proposition_5_2_7_canonicalDihedralMap a).1.1 : Perm6)) *
      (((__ch5_proposition_5_2_7_canonicalDihedralMap b).1.1 : Perm6))
  rw [__ch5_proposition_5_2_7_canonicalDihedralMap_apply_val, __ch5_proposition_5_2_7_canonicalDihedralMap_apply_val,
    __ch5_proposition_5_2_7_canonicalDihedralMap_apply_val]
  cases a <;> cases b <;> rename_i i j <;>
    fin_cases i <;> fin_cases j <;> decide

private def __ch5_proposition_5_2_7_canonicalDihedralHom :
    DihedralGroup 5 →* automorphismFixedSubgroup canonicalExceptionalAut where
  toFun := __ch5_proposition_5_2_7_canonicalDihedralMap
  map_one' := rfl
  map_mul' := __ch5_proposition_5_2_7_canonicalDihedralMap_mul

private theorem __ch5_proposition_5_2_7_canonicalDihedralHom_apply_val (d : DihedralGroup 5) :
    (((__ch5_proposition_5_2_7_canonicalDihedralHom d).1.1 : Perm6)) = __ch5_proposition_5_2_7_dihedralImagePerm d := by
  exact __ch5_proposition_5_2_7_canonicalDihedralMap_apply_val d

private theorem __ch5_proposition_5_2_7_canonicalDihedralHom_injective :
    Function.Injective __ch5_proposition_5_2_7_canonicalDihedralHom := by
  decide +kernel

private theorem __ch5_proposition_5_2_7_canonicalFixedSubgroup_card_le_ten :
    Nat.card (automorphismFixedSubgroup canonicalExceptionalAut) ≤ 10 := by
  let : Fintype (automorphismFixedSubgroup canonicalExceptionalAut) :=
    Fintype.ofFinite _
  have hpacking := Fintype.card_le_of_injective canonicalFixedPacking
    canonicalFixedPacking_injective
  have hA : Fintype.card (alternatingGroup (Fin 6)) = 360 := by
    rw [card_alternatingGroup, Fintype.card_fin]
    norm_num [Nat.factorial]
  rw [Fintype.card_prod, Fintype.card_fin, hA] at hpacking
  rw [Nat.card_eq_fintype_card]
  omega

private theorem __ch5_proposition_5_2_7_canonicalDihedralHom_surjective :
    Function.Surjective __ch5_proposition_5_2_7_canonicalDihedralHom := by
  let : Fintype (automorphismFixedSubgroup canonicalExceptionalAut) :=
    Fintype.ofFinite _
  have hlower : 10 ≤
      Fintype.card (automorphismFixedSubgroup canonicalExceptionalAut) := by
    have h := Fintype.card_le_of_injective __ch5_proposition_5_2_7_canonicalDihedralHom
      __ch5_proposition_5_2_7_canonicalDihedralHom_injective
    rw [DihedralGroup.card] at h
    norm_num at h
    exact h
  have hcodomain :
      Fintype.card (automorphismFixedSubgroup canonicalExceptionalAut) = 10 := by
    have hupper := __ch5_proposition_5_2_7_canonicalFixedSubgroup_card_le_ten
    rw [Nat.card_eq_fintype_card] at hupper
    omega
  have hdomain : Fintype.card (DihedralGroup 5) = 10 := by
    rw [DihedralGroup.card]
  exact ((Fintype.bijective_iff_injective_and_card __ch5_proposition_5_2_7_canonicalDihedralHom).2
    ⟨__ch5_proposition_5_2_7_canonicalDihedralHom_injective, hdomain.trans hcodomain.symm⟩).2

private noncomputable def canonicalFixedMulEquivDihedral :
    automorphismFixedSubgroup canonicalExceptionalAut ≃* DihedralGroup 5 :=
  (MulEquiv.ofBijective __ch5_proposition_5_2_7_canonicalDihedralHom
    ⟨__ch5_proposition_5_2_7_canonicalDihedralHom_injective, __ch5_proposition_5_2_7_canonicalDihedralHom_surjective⟩).symm

private theorem __ch5_proposition_5_2_7_a6ExceptionalQuotientAut_conjugate_canonical :
    ∃ τ : Perm6,
      a6ExceptionalQuotientAut = conjugateCanonicalExceptionalAut τ := by
  obtain ⟨σ, hσ⟩ := exceptionalAut_eq_twist a6ExceptionalQuotientAut
    a6ExceptionalQuotientAut_not_mem_natural
  have hsq : exceptionalTwistAut σ ^ 2 = 1 := by
    rw [← hσ, ← a6ExceptionalQuotientAut_order]
    exact pow_orderOf_eq_one a6ExceptionalQuotientAut
  obtain ⟨τ, hτ⟩ := exceptionalTwistAut_conjugate_canonical σ hsq
  exact ⟨τ, hσ.trans hτ⟩

private noncomputable def a6ExceptionalLiftFixedMulEquivZModTen
    (beta : MulAut (alternatingGroup (Fin 6)))
    (hbetaOrder : orderOf beta = 2)
    (hbetaOutside : beta ∉ naturalAlternatingAutomorphismSubgroup) :
    automorphismFixedSubgroup
        (SchurPresentation.doubleCoverLiftMulAut 1 a6DoubleCover_covering
          a6DoubleCoverBlockCoverHom_kernel_card beta) ≃*
      Multiplicative (ZMod 10) := by
  let σ : Perm6 := Classical.choose (exceptionalAut_eq_twist beta hbetaOutside)
  have hσ : beta = exceptionalTwistAut σ :=
    Classical.choose_spec (exceptionalAut_eq_twist beta hbetaOutside)
  have hσsq : exceptionalTwistAut σ ^ 2 = 1 := by
    rw [← hσ, ← hbetaOrder]
    exact pow_orderOf_eq_one beta
  let τ : Perm6 := Classical.choose
    (exceptionalTwistAut_conjugate_canonical σ hσsq)
  have hτ : exceptionalTwistAut σ = conjugateCanonicalExceptionalAut τ :=
    Classical.choose_spec (exceptionalTwistAut_conjugate_canonical σ hσsq)
  let υ : Perm6 := Classical.choose __ch5_proposition_5_2_7_a6ExceptionalQuotientAut_conjugate_canonical
  have hυ : a6ExceptionalQuotientAut = conjugateCanonicalExceptionalAut υ :=
    Classical.choose_spec __ch5_proposition_5_2_7_a6ExceptionalQuotientAut_conjugate_canonical
  let delta : MulAut (alternatingGroup (Fin 6)) :=
    MulAut.conjNormal τ * (MulAut.conjNormal υ)⁻¹
  have hconj : beta = delta * a6ExceptionalQuotientAut * delta⁻¹ := by
    rw [hσ, hτ, hυ]
    dsimp [delta, conjugateCanonicalExceptionalAut]
    group
  let liftHom := SchurPresentation.doubleCoverLiftMulAutHom 1
    a6DoubleCover_covering a6DoubleCoverBlockCoverHom_kernel_card
  have hlift : liftHom beta =
      liftHom delta * liftHom a6ExceptionalQuotientAut * (liftHom delta)⁻¹ := by
    rw [hconj]
    simp only [map_mul, map_inv]
  rw [show SchurPresentation.doubleCoverLiftMulAut 1 a6DoubleCover_covering
      a6DoubleCoverBlockCoverHom_kernel_card beta = liftHom beta by rfl,
    hlift]
  exact (automorphismFixedSubgroup_conjMulEquiv
      (liftHom a6ExceptionalQuotientAut) (liftHom delta)).trans
    (by
      rw [show liftHom a6ExceptionalQuotientAut =
        a6ExceptionalConjugatorLiftAut by
          exact a6ExceptionalConjugatorLiftAut_eq_quotientLift.symm]
      exact a6ExceptionalFixedSubgroupMulEquivZModTen)

private noncomputable def doubleCoverExceptionalFixedMulEquivZModTen
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (f : Covering K (alternatingGroup (Fin 6)))
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    (beta : MulAut (alternatingGroup (Fin 6)))
    (hbetaOrder : orderOf beta = 2)
    (hbetaOutside : beta ∉ naturalAlternatingAutomorphismSubgroup) :
    automorphismFixedSubgroup
        (SchurPresentation.doubleCoverLiftMulAut 1 f hcard beta) ≃*
      Multiplicative (ZMod 10) := by
  let e : K ≃* a6DoubleCoverPermutationSubgroup := Classical.choose
    (SchurPresentation.theorem_5_2_3_a_2 1 f
      a6DoubleCover_covering hcard a6DoubleCoverBlockCoverHom_kernel_card)
  have he : a6DoubleCover_covering.comp (Covering.ofMulEquiv e) = f :=
    (Classical.choose_spec (SchurPresentation.theorem_5_2_3_a_2 1 f
      a6DoubleCover_covering hcard a6DoubleCoverBlockCoverHom_kernel_card)).1
  let alphaK := SchurPresentation.doubleCoverLiftMulAut 1 f hcard beta
  let alphaA := SchurPresentation.doubleCoverLiftMulAut 1 a6DoubleCover_covering
    a6DoubleCoverBlockCoverHom_kernel_card beta
  have he_apply (g : K) : a6DoubleCoverBlockCoverHom (e g) = f g := by
    exact DFunLike.congr_fun he g
  have hintertwine : ∀ g : K, e (alphaK g) = alphaA (e g) := by
    have hhom : e.toMonoidHom.comp alphaK.toMonoidHom =
        alphaA.toMonoidHom.comp e.toMonoidHom := by
      apply SchurPresentation.monoidHom_eq_of_isPerfect_of_comp_eq
        a6DoubleCoverBlockCoverHom
        (by rw [← a6DoubleCover_center_eq_ker])
      apply MonoidHom.ext
      intro g
      have hK := congrArg
        (fun q : Covering K (alternatingGroup (Fin 6)) => q g)
        (SchurPresentation.doubleCoverLiftMulAut_fac 1 f hcard beta)
      have hA := congrArg
        (fun q : Covering a6DoubleCoverPermutationSubgroup
          (alternatingGroup (Fin 6)) => q (e g))
        (SchurPresentation.doubleCoverLiftMulAut_fac 1 a6DoubleCover_covering
          a6DoubleCoverBlockCoverHom_kernel_card beta)
      change f (alphaK g) = beta (f g) at hK
      change a6DoubleCoverBlockCoverHom (alphaA (e g)) =
        beta (a6DoubleCoverBlockCoverHom (e g)) at hA
      rw [he_apply] at hA
      exact (he_apply (alphaK g)).trans (hK.trans hA.symm)
    intro g
    exact DFunLike.congr_fun hhom g
  exact (automorphismFixedSubgroup_intertwiningMulEquiv e alphaK alphaA
    hintertwine).trans
      (a6ExceptionalLiftFixedMulEquivZModTen beta hbetaOrder hbetaOutside)

/-! Proposition 5.2.7(b): for a Schur double cover of `A₆`, the fixed
subgroup of a non-inner involution is cyclic of order ten. -/
public theorem proposition_5_2_7_b
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (quotientEquiv : K ⧸ Subgroup.center K ≃*
      alternatingGroup (Fin 6))
    (hcenter : Nat.card (Subgroup.center K) = 2)
    (x : MulAut K) (hxOrder : orderOf x = 2)
    (H : Subgroup (MulAut K))
    (HEquiv : H ≃* Equiv.Perm (Fin 6))
    (quotientAction : MulAut (alternatingGroup (Fin 6)))
    (quotientAction_compat : ∀ k : K,
      quotientEquiv (QuotientGroup.mk' (Subgroup.center K) (x k)) =
        quotientAction
          (quotientEquiv (QuotientGroup.mk' (Subgroup.center K) k)))
    (H_action_compat : ∀ h : H, ∀ k : K,
      quotientEquiv (QuotientGroup.mk' (Subgroup.center K) (h.1 k)) =
        MulAut.conjNormal (HEquiv h)
          (quotientEquiv (QuotientGroup.mk' (Subgroup.center K) k)))
    (hxH : x ∉ H) :
    Nonempty
      (automorphismFixedSubgroup x ≃* Multiplicative (ZMod 10)) := by
  let f : Covering K (alternatingGroup (Fin 6)) := {
    toMonoidHom := alternatingQuotientHom quotientEquiv
    surjective := quotientEquiv.surjective.comp
      (QuotientGroup.mk'_surjective (Subgroup.center K)) }
  have hfker : f.toMonoidHom.ker = Subgroup.center K := by
    ext k
    simp [f, alternatingQuotientHom]
  have hfcard : Nat.card f.toMonoidHom.ker = 2 := by
    rw [hfker, hcenter]
  have hbetaOrder : orderOf quotientAction = 2 :=
    @__ch5_proposition_5_2_7_quotientAction_order' K _ _ _ 6 2 Nat.prime_two quotientEquiv x hxOrder
      quotientAction quotientAction_compat
  have hbetaOutside : quotientAction ∉
      naturalAlternatingAutomorphismSubgroup :=
    __ch5_proposition_5_2_7_quotientAction_not_mem_natural quotientEquiv x H HEquiv quotientAction
      quotientAction_compat H_action_compat hxH
  let lift := SchurPresentation.doubleCoverLiftMulAut 1 f hfcard
    quotientAction
  have hxlift : x = lift := by
    apply MulEquiv.ext
    intro k
    have hhom : x.toMonoidHom = lift.toMonoidHom := by
      apply SchurPresentation.monoidHom_eq_of_isPerfect_of_comp_eq
        (alternatingQuotientHom quotientEquiv)
        (by
          intro k hk
          change (alternatingQuotientHom quotientEquiv) k = 1 at hk
          simpa [alternatingQuotientHom] using hk)
      apply MonoidHom.ext
      intro k
      have hxk := quotientAction_compat k
      have hlift := congrArg
        (fun q : Covering K (alternatingGroup (Fin 6)) => q k)
        (SchurPresentation.doubleCoverLiftMulAut_fac 1 f hfcard
          quotientAction)
      exact hxk.trans hlift.symm
    exact DFunLike.congr_fun hhom k
  rw [hxlift]
  exact Nonempty.intro
    (doubleCoverExceptionalFixedMulEquivZModTen f hfcard quotientAction
      hbetaOrder hbetaOutside)

/-- The fixed subgroup of any order-two automorphism of `A₆` outside the
natural symmetric subgroup is dihedral of order ten. -/
public theorem a6_outsideNatural_involution_fixed_equiv_dihedral
    (beta : MulAut (alternatingGroup (Fin 6)))
    (hbetaOrder : orderOf beta = 2)
    (hbetaOutside : beta ∉ naturalAlternatingAutomorphismSubgroup) :
    Nonempty (automorphismFixedSubgroup beta ≃* DihedralGroup 5) := by
  obtain ⟨sigma, haction⟩ := exceptionalAut_eq_twist beta hbetaOutside
  have hsq : exceptionalTwistAut sigma ^ 2 = 1 := by
    rw [← haction, ← hbetaOrder]
    exact pow_orderOf_eq_one beta
  obtain ⟨tau, hconj⟩ := exceptionalTwistAut_conjugate_canonical sigma hsq
  refine ⟨?_⟩
  rw [haction, hconj]
  exact (conjugateCanonicalFixedMulEquiv tau).trans
    canonicalFixedMulEquivDihedral

/-- Proposition 5.2.7(a): the fixed subgroup in `A₆` of an outer involution
outside the natural `S₆`-subgroup of `Aut(A₆)` is dihedral of order ten. -/
public theorem proposition_5_2_7_a
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (n p : Nat) (hn5 : 5 ≤ n) (hpPrime : p.Prime)
    (quotientEquiv : K ⧸ Subgroup.center K ≃*
      alternatingGroup (Fin n))
    (x : MulAut K) (hxOrder : orderOf x = p)
    (H : Subgroup (MulAut K))
    (HEquiv : H ≃* Equiv.Perm (Fin n))
    (quotientAction : MulAut (alternatingGroup (Fin n)))
    (quotientAction_compat : ∀ k : K,
      quotientEquiv (QuotientGroup.mk' (Subgroup.center K) (x k)) =
        quotientAction
          (quotientEquiv (QuotientGroup.mk' (Subgroup.center K) k)))
    (H_action_compat : ∀ h : H, ∀ k : K,
      quotientEquiv (QuotientGroup.mk' (Subgroup.center K) (h.1 k)) =
        MulAut.conjNormal (HEquiv h)
          (quotientEquiv (QuotientGroup.mk' (Subgroup.center K) k)))
    (hn6 : n = 6) (hp2 : p = 2) (hxH : x ∉ H) :
    Nonempty
      (↥(automorphismFixedSubgroup quotientAction) ≃* DihedralGroup 5) := by
  subst n
  have horder : orderOf quotientAction = 2 :=
    (__ch5_proposition_5_2_7_quotientAction_order' hpPrime quotientEquiv x hxOrder quotientAction
      quotientAction_compat).trans hp2
  have houtside :
      quotientAction ∉ naturalAlternatingAutomorphismSubgroup :=
    __ch5_proposition_5_2_7_quotientAction_not_mem_natural quotientEquiv x H HEquiv quotientAction
      quotientAction_compat H_action_compat hxH
  obtain ⟨σ, haction⟩ := exceptionalAut_eq_twist quotientAction houtside
  have hsq : exceptionalTwistAut σ ^ 2 = 1 := by
    rw [← haction, ← horder]
    exact pow_orderOf_eq_one quotientAction
  obtain ⟨τ, hconj⟩ := exceptionalTwistAut_conjugate_canonical σ hsq
  refine ⟨?_⟩
  rw [haction, hconj]
  exact (conjugateCanonicalFixedMulEquiv τ).trans
    canonicalFixedMulEquivDihedral

/-!
Clause (b) is intentionally not declared until the exceptional double-cover
fixed-subgroup calculation has a proof. The proved quotient calculation in
`proposition_5_2_7_a` is not sufficient by itself to identify the fixed
subgroup upstairs with the cyclic group of order ten.
-/

/-- A normal `3`-subgroup of an exceptional alternating covering group lies
in the center.  This is the group-theoretic reduction used before the
determinant argument in Proposition 5.2.7(c). -/
public theorem pCore_le_center_of_exceptional_alternating_quotient
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (n : Nat) (hn5 : 5 ≤ n)
    (quotientEquiv : K ⧸ Subgroup.center K ≃*
      alternatingGroup (Fin n))
    (hnExceptional : n = 6 ∨ n = 7)
    (O3 : Subgroup K) (hO3 : IsPCore 3 O3) :
    O3 ≤ Subgroup.center K := by
  let q : K →* alternatingGroup (Fin n) :=
    alternatingQuotientHom quotientEquiv
  let N : Subgroup (alternatingGroup (Fin n)) := O3.map q
  let : O3.Normal := hO3.1
  let : N.Normal := by
    dsimp [N]
    exact Subgroup.Normal.map hO3.1 q
      (quotientEquiv.surjective.comp
        (QuotientGroup.mk'_surjective (Subgroup.center K)))
  let : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using hn5)
  rcases (inferInstance : N.Normal).eq_bot_or_eq_top with hN | hN
  · have hleker : O3 ≤ q.ker := by
      apply (Subgroup.map_eq_bot_iff (H := O3) (f := q)).mp
      exact hN
    have hqker : q.ker = Subgroup.center K := by
      ext k
      simp [q, alternatingQuotientHom]
    simpa [hqker] using hleker
  · have hmapP : IsPGroup 3 N := hO3.2.1.map q
    have htopP : IsPGroup 3 (alternatingGroup (Fin n)) := by
      rw [hN] at hmapP
      exact hmapP.of_equiv Subgroup.topEquiv
    let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp htopP
    have hodd : Odd (Nat.card (alternatingGroup (Fin n))) := by
      rw [hk]
      exact (show Odd 3 from ⟨1, by norm_num⟩).pow
    rcases hnExceptional with hn6 | hn7
    · subst n
      rw [nat_card_alternatingGroup] at hodd
      norm_num [Nat.factorial] at hodd
    · subst n
      rw [nat_card_alternatingGroup] at hodd
      norm_num [Nat.factorial] at hodd

/-- In degrees six and seven, the center of any alternating covering group
has order dividing the exceptional Schur multiplier order six. -/
public theorem exceptional_alternating_center_card_dvd_six
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (n : Nat)
    (quotientEquiv : K ⧸ Subgroup.center K ≃*
      alternatingGroup (Fin n))
    (hnExceptional : n = 6 ∨ n = 7) :
    Nat.card (Subgroup.center K) ∣ 6 := by
  rcases hnExceptional with hn6 | hn7
  · subst n
    let f : Covering K (alternatingGroup (Fin 6)) := {
      toMonoidHom := alternatingQuotientHom quotientEquiv
      surjective := quotientEquiv.surjective.comp
        (QuotientGroup.mk'_surjective (Subgroup.center K)) }
    obtain ⟨L, instL, finL, qsL, f0, hf0, _hcyclic, hcard⟩ :=
      SchurPresentation.theorem_5_2_3_c_multiplier_a6
    let : Group L := instL
    let : Finite L := finL
    let : IsQuasisimple L := qsL
    have hdvd :=
      Covering.coveringKernel_card_dvd_of_universal f0 hf0 f
    have hfker : f.toMonoidHom.ker = Subgroup.center K := by
      ext k
      simp [f, alternatingQuotientHom]
    rw [hfker, hcard] at hdvd
    exact hdvd
  · subst n
    let f : Covering K (alternatingGroup (Fin 7)) := {
      toMonoidHom := alternatingQuotientHom quotientEquiv
      surjective := quotientEquiv.surjective.comp
        (QuotientGroup.mk'_surjective (Subgroup.center K)) }
    obtain ⟨L, instL, finL, qsL, f0, hf0, _hcyclic, hcard⟩ :=
      SchurPresentation.theorem_5_2_3_c_multiplier_a7
    let : Group L := instL
    let : Finite L := finL
    let : IsQuasisimple L := qsL
    have hdvd :=
      Covering.coveringKernel_card_dvd_of_universal f0 hf0 f
    have hfker : f.toMonoidHom.ker = Subgroup.center K := by
      ext k
      simp [f, alternatingQuotientHom]
    rw [hfker, hcard] at hdvd
    exact hdvd

/-- The `3`-core in Proposition 5.2.7(c) is either trivial or has order
three.  Thus the remaining nontrivial case is exactly the central `3Aₙ`
case treated by the determinant argument in the source. -/
public theorem pCore_card_eq_one_or_three
    {K : Type} [Group K] [Finite K]
    (O3 : Subgroup K) (hO3 : IsPGroup 3 O3)
    (hO3center : O3 ≤ Subgroup.center K)
    (hcenterDvd : Nat.card (Subgroup.center K) ∣ 6) :
    Nat.card O3 = 1 ∨ Nat.card O3 = 3 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hO3Dvd : Nat.card O3 ∣ 6 :=
    (Subgroup.card_dvd_of_le hO3center).trans hcenterDvd
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hO3
  have hle : Nat.card O3 ≤ 6 := Nat.le_of_dvd (by norm_num) hO3Dvd
  have hk_le : k ≤ 1 := by
    by_contra hknot
    have htwo : 2 ≤ k := by omega
    have hpow : 3 ^ 2 ≤ 3 ^ k :=
      Nat.pow_le_pow_right (by norm_num) htwo
    rw [← hk] at hpow
    omega
  interval_cases k <;> simp_all

/-- The maximal normal `p`-subgroup is preserved by every automorphism. -/
public theorem pCore_map_eq
    {G : Type*} [Group G] [Finite G]
    (p : Nat) (O : Subgroup G) (hO : IsPCore p O) (x : MulAut G) :
    O.map x.toMonoidHom = O := by
  apply Subgroup.eq_of_le_of_card_ge
  · exact hO.2.2 _ (Subgroup.Normal.map hO.1 x.toMonoidHom x.surjective)
      (hO.2.1.map x.toMonoidHom)
  · rw [Subgroup.card_map_of_injective x.injective]

/-- A nonidentity automorphism of a group of order three is inversion. -/
private theorem __ch5_proposition_5_2_7_prime_three_mulAut_inverts_of_ne_one
    {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 3) (x : MulAut G) (hx : x ≠ 1) :
    ∀ z : G, x z = z⁻¹ := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro z
  by_cases hz : z = 1
  · simp [hz]
  have hgen : Subgroup.zpowers z = ⊤ :=
    zpowers_eq_top_of_prime_card hcard hz
  have horder : orderOf z = 3 := by
    rw [orderOf_eq_card_of_zpowers_eq_top hgen, hcard]
  have hxz_ne : x z ≠ z := by
    intro hxz
    apply hx
    ext g
    have hgmem : g ∈ Subgroup.zpowers z := by
      rw [hgen]
      exact Subgroup.mem_top g
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hgmem
    simp [hxz]
  have hxz_one : x z ≠ 1 := by
    intro hxz
    exact hz (x.injective (by simpa using hxz))
  have hxz_mem : x z ∈ Submonoid.powers z :=
    mem_powers_of_prime_card hcard hz
  obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).mp hxz_mem
  have hmod : z ^ (m % 3) = x z := by
    calc
      z ^ (m % 3) = z ^ (m % orderOf z) := by rw [horder]
      _ = z ^ m := pow_mod_orderOf z m
      _ = x z := hm
  have hlt : m % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases hrem : m % 3
  · exact (hxz_one (by simpa [hrem] using hmod.symm)).elim
  · exact (hxz_ne (by simpa [hrem] using hmod.symm)).elim
  · have hz3 : z ^ 3 = 1 := by
      rw [← horder]
      exact pow_orderOf_eq_one z
    have hz2 : z ^ 2 = z⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      simpa [pow_succ] using hz3
    rw [← hz2]
    simpa [hrem] using hmod.symm

/-- Restrict an automorphism to an invariant subgroup. -/
private def __ch5_proposition_5_2_7_restrictMulAut
    {G : Type*} [Group G] (O : Subgroup G) (x : MulAut G)
    (hmap : O.map x.toMonoidHom = O) : MulAut O :=
  (x.subgroupMap O).trans (MulEquiv.subgroupCongr hmap)

/-- For an invariant subgroup of order three, failure of pointwise fixation
is exactly the input needed to deduce inversion. -/
public theorem inverts_order_three_subgroup_of_not_pointwise_fixed
    {G : Type*} [Group G] [Finite G]
    (O : Subgroup G) (x : MulAut G)
    (hmap : O.map x.toMonoidHom = O)
    (hcard : Nat.card O = 3)
    (hnotfixed : ¬ ∀ z : O, x z.1 = z.1) :
    ∀ z : O, x z.1 = z.1⁻¹ := by
  let xO : MulAut O := __ch5_proposition_5_2_7_restrictMulAut O x hmap
  have hxO_ne : xO ≠ 1 := by
    intro hxO
    apply hnotfixed
    intro z
    have hz := congrArg Subtype.val (congrArg (fun a : MulAut O ↦ a z) hxO)
    change x z.1 = z.1 at hz
    exact hz
  intro z
  have hz := __ch5_proposition_5_2_7_prime_three_mulAut_inverts_of_ne_one hcard xO hxO_ne z
  exact congrArg Subtype.val hz

private theorem __ch5_proposition_5_2_7_quotientAction_conjugate_compat
    {K : Type*} [Group K]
    (quotientEquiv : K ⧸ Subgroup.center K ≃*
      alternatingGroup (Fin 6))
    (x : MulAut K)
    (quotientAction : MulAut (alternatingGroup (Fin 6)))
    (quotientAction_compat : ∀ k : K,
      quotientEquiv (QuotientGroup.mk' (Subgroup.center K) (x k)) =
        quotientAction
          (quotientEquiv (QuotientGroup.mk' (Subgroup.center K) k)))
    (H : Subgroup (MulAut K))
    (HEquiv : H ≃* Equiv.Perm (Fin 6))
    (H_action_compat : ∀ h : H, ∀ k : K,
      quotientEquiv (QuotientGroup.mk' (Subgroup.center K) (h.1 k)) =
        MulAut.conjNormal (HEquiv h)
          (quotientEquiv (QuotientGroup.mk' (Subgroup.center K) k)))
    (h : H) :
    ∀ k : K,
      quotientEquiv (QuotientGroup.mk' (Subgroup.center K)
        ((h.1)⁻¹ (x (h.1 k)))) =
        (((MulAut.conjNormal (HEquiv h))⁻¹ * quotientAction *
          MulAut.conjNormal (HEquiv h)) : MulAut (alternatingGroup (Fin 6)))
          (quotientEquiv (QuotientGroup.mk' (Subgroup.center K) k)) := by
  intro k
  have hh := H_action_compat h k
  have hx := quotientAction_compat (h.1 k)
  change quotientEquiv (QuotientGroup.mk' (Subgroup.center K)
      ((h.1)⁻¹ (x (h.1 k)))) = _
  calc
    quotientEquiv (QuotientGroup.mk' (Subgroup.center K)
        ((h.1)⁻¹ (x (h.1 k)))) =
        (MulAut.conjNormal (HEquiv h))⁻¹
          (quotientEquiv (QuotientGroup.mk' (Subgroup.center K)
            (x (h.1 k)))) := by
      have hhinv := H_action_compat h ((h.1)⁻¹ (x (h.1 k)))
      calc
        quotientEquiv (QuotientGroup.mk' (Subgroup.center K)
            ((h.1)⁻¹ (x (h.1 k)))) =
            (MulAut.conjNormal (HEquiv h))⁻¹
              ((MulAut.conjNormal (HEquiv h))
                (quotientEquiv (QuotientGroup.mk' (Subgroup.center K)
                  ((h.1)⁻¹ (x (h.1 k)))))) := by simp
        _ = (MulAut.conjNormal (HEquiv h))⁻¹
              (quotientEquiv (QuotientGroup.mk' (Subgroup.center K)
                (h.1 ((h.1)⁻¹ (x (h.1 k)))))) := by rw [hhinv]
        _ = (MulAut.conjNormal (HEquiv h))⁻¹
              (quotientEquiv (QuotientGroup.mk' (Subgroup.center K)
                (x (h.1 k)))) := by simp
    _ = (MulAut.conjNormal (HEquiv h))⁻¹
          (quotientAction
            (quotientEquiv (QuotientGroup.mk' (Subgroup.center K)
              (h.1 k)))) := by rw [quotientAction_compat]
    _ = (((MulAut.conjNormal (HEquiv h))⁻¹ * quotientAction *
          MulAut.conjNormal (HEquiv h)) :
          MulAut (alternatingGroup (Fin 6)))
          (quotientEquiv (QuotientGroup.mk' (Subgroup.center K) k)) := by
      rw [hh]
      simp only [MulAut.mul_apply, MulAut.inv_apply]

private theorem __ch5_proposition_5_2_7_tripleCoverA6_outer_inverts_center
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (quotientEquiv : K ⧸ Subgroup.center K ≃*
      alternatingGroup (Fin 6))
    (x : MulAut K) (hxOrder : orderOf x = 2)
    (H : Subgroup (MulAut K)) (HEquiv : H ≃* Equiv.Perm (Fin 6))
    (quotientAction : MulAut (alternatingGroup (Fin 6)))
    (quotientAction_compat : ∀ k : K,
      quotientEquiv (QuotientGroup.mk' (Subgroup.center K) (x k)) =
        quotientAction
          (quotientEquiv (QuotientGroup.mk' (Subgroup.center K) k)))
    (H_action_compat : ∀ h : H, ∀ k : K,
      quotientEquiv (QuotientGroup.mk' (Subgroup.center K) (h.1 k)) =
        MulAut.conjNormal (HEquiv h)
          (quotientEquiv (QuotientGroup.mk' (Subgroup.center K) k)))
    (hxH : x ∉ H)
    (hcenter : Nat.card (Subgroup.center K) = 3) :
    ∀ z : K, z ∈ Subgroup.center K → x z = z⁻¹ := by
  let f : Covering K (alternatingGroup (Fin 6)) := {
    toMonoidHom := alternatingQuotientHom quotientEquiv
    surjective := quotientEquiv.surjective.comp
      (QuotientGroup.mk'_surjective (Subgroup.center K)) }
  have hfker : f.toMonoidHom.ker = Subgroup.center K := by
    ext k
    simp [f, alternatingQuotientHom]
  have hfcard : Nat.card f.toMonoidHom.ker = 3 := by
    rw [hfker, hcenter]
  have hbetaOrder : orderOf quotientAction = 2 :=
    __ch5_proposition_5_2_7_quotientAction_order' (K := K) (n := 6) (p := 2) Nat.prime_two
      quotientEquiv x hxOrder quotientAction quotientAction_compat
  have hbetaOutside : quotientAction ∉
      naturalAlternatingAutomorphismSubgroup :=
      __ch5_proposition_5_2_7_quotientAction_not_mem_natural quotientEquiv x H HEquiv quotientAction
      quotientAction_compat H_action_compat hxH
  have hbetaNoninner : ∀ g : alternatingGroup (Fin 6),
      quotientAction ≠ MulAut.conj g := by
    intro g hconj
    apply hbetaOutside
    change quotientAction ∈
      (MulAut.conjNormal : Perm6 →*
        MulAut (alternatingGroup (Fin 6))).range
    refine ⟨g.1, ?_⟩
    rw [MulAut.conjNormal_val]
    exact hconj.symm
  obtain hnormal | hnormal :=
    a6_noninner_involution_standardNine_normalForm quotientAction
      hbetaOrder hbetaNoninner
  · obtain ⟨δ, hX, hY⟩ := hnormal
    exact tripleCoverA6_center_inverted_of_reflection_normalForm
      f hfcard x quotientAction quotientAction_compat δ hX hY
  · obtain ⟨τ, hX, hY⟩ := hnormal
    let h : H := HEquiv.symm τ
    have hτ : HEquiv h = τ := HEquiv.apply_symm_apply τ
    let α : MulAut K := h.1⁻¹ * x * h.1
    let β : MulAut (alternatingGroup (Fin 6)) :=
      (MulAut.conjNormal τ)⁻¹ * quotientAction * MulAut.conjNormal τ
    have hαcompat : ∀ k : K, f (α k) = β (f k) := by
      intro k
      change quotientEquiv (QuotientGroup.mk' (Subgroup.center K)
          (h.1⁻¹ (x (h.1 k)))) =
        β (quotientEquiv (QuotientGroup.mk' (Subgroup.center K) k))
      simpa [β, hτ] using
        (__ch5_proposition_5_2_7_quotientAction_conjugate_compat quotientEquiv x quotientAction
          quotientAction_compat H HEquiv H_action_compat h k)
    have hγ :
        (MulAut.conjNormal exceptionalStandardNineInner :
            MulAut (alternatingGroup (Fin 6))) * β =
          (MulAut.conjNormal exceptionalStandardNineInner :
            MulAut (alternatingGroup (Fin 6))) *
            (MulAut.conjNormal τ)⁻¹ * quotientAction *
              MulAut.conjNormal τ := by
      rfl
    have hX' :
        ((MulAut.conjNormal exceptionalStandardNineInner :
            MulAut (alternatingGroup (Fin 6))) * β)
          SchurPresentation.Theorem523BaseNine.a6X =
          SchurPresentation.Theorem523BaseNine.a6X ^ 2 *
            SchurPresentation.Theorem523BaseNine.a6Y := by
      exact hX
    have hY' :
        ((MulAut.conjNormal exceptionalStandardNineInner :
            MulAut (alternatingGroup (Fin 6))) * β)
          SchurPresentation.Theorem523BaseNine.a6Y =
          SchurPresentation.Theorem523BaseNine.a6X ^ 2 *
            SchurPresentation.Theorem523BaseNine.a6Y ^ 2 := by
      exact hY
    let δ : alternatingGroup (Fin 6) :=
      ⟨exceptionalStandardNineInner, by
        rw [Equiv.Perm.mem_alternatingGroup]
        decide⟩
    have hinv := tripleCoverA6_center_inverted_of_matrix_normalForm
      f hfcard α β hαcompat δ hX' hY'
    exact center_inversion_of_conjugate x h.1 (by
      intro z hz
      exact hinv z hz)

end GLS3.Chapter5
/- END KGroup.GLS3.Chapter5.proposition_5_2_7 -/

/- BEGIN KGroup.GLS3.Chapter5.proposition_5_2_8 -/
set_option maxHeartbeats 800000

noncomputable section

namespace GLS3.Chapter5

end GLS3.Chapter5
/- END KGroup.GLS3.Chapter5.proposition_5_2_8 -/


module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityHigherTensorAxes
public import Theory.GroupTheory.PrimeRankNormalPair
public import Theory.SpecificGroups.BinaryLinear.SmallCubicRank

/-!
# Cubic order, dimension four, and the actual higher parabolic complement

Assume the component-normalizer step Y ◁ N_G(C_T(U)). The earlier source
centralizer calculation eliminates C_T(L), gives C_G(U)=U, and puts Y in
N_G(U). The marked double from HigherTensorAxes embeds the original P in
the centralizer of the diagonal natural action. That centralizer has order
six, so the odd prime |P| equals three.

If d=5, Y/O₂(Y)≃SL₄(2) contributes three-rank at least two. The mutually
normalizing pair PU contributes another cubic, and Y∩PU=U is a two-group:
P∩Y is trivial by the original escape hypothesis. Additivity of odd ranks
contradicts the SQTK bound in the literal normalizer N_G(U). Thus d=4.
The canonical parabolic factors and Gaschütz splitting now follow from
the proved construction, without any cubic, dimension, or complement input.

The component normality premise remains with qt-d-12213-local-rigidity.
These conditional applications do not complete original 12.2.25; its full
normalizer quotient and tensor-factor markings also remain with that owner.

Source: Aschbacher--Smith, original 12.2.25--26, printed pp.805--806.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G} {d : ℕ}

/-- The odd-prime pair actor embeds in the actual doubled-natural centralizer. -/
theorem cubic_of_residual_normal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d)
    (hn : normalizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G) ≤
      normalizer (rigidityHyperplaneResidual L U V : Set G)) : Nat.card P = 3 := by
  let := C.elementary
  let n := d-1
  let : NeZero n := ⟨by dsimp [n]; omega⟩
  let B := RigidityKernel.source_centralizers h D structural A C hnone
  have hz := higher_component_centralizer_eq_bot_of_residual_normal h D A C B hn
    (RigidityResidual.radical_fixed_eq_component_centralizer h D structural A C B)
  have hs := higher_kernel_vanishing_consequences D B hz
  have hCU := (higher_selfCentralizing_of_kernel_vanishing h D structural A C B hz).2
  have hYU : rigidityHyperplaneResidual L U V ≤ normalizer (U : Set G) := by
    simpa only [hs.2.2.2] using B.residual_normalizes
  have hPY : P ≤ normalizer (rigidityHyperplaneResidual L U V : Set G) :=
    (le_sup_left.trans le_sup_left : P ≤ cyclicPairJoin P U V).trans
      ((higher_pair_normalizes_sylow_centralizer D A C).trans hn)
  have hPU : P ≤ normalizer (U : Set G) :=
    (show P ≤ H by rw [C.overgroup]; exact le_sup_left).trans C.overgroup_normalizes_core
  have hdis : Disjoint P U := disjoint_of_coprime_natCard (by
    rw [C.dimension]; exact C.odd_order.coprime_two_right.pow_right _)
  let r := U.normalizerMonoidHom.comp (inclusion hPU)
  have hr : Function.Injective r := by
    apply (MonoidHom.ker_eq_bot_iff r).mp
    apply eq_bot_iff.mpr
    intro p hp
    have hc : (⟨p,hPU p.property⟩ : normalizer (U : Set G)) ∈
        U.normalizerMonoidHom.ker := hp
    rw [normalizerMonoidHom_ker] at hc
    have hpU : (p : G) ∈ U := hCU ▸ hc
    exact Subtype.ext (disjoint_def.mp hdis p.property hpU)
  obtain ⟨q,hq,e,he⟩ := exists_natural_double D A C hd hYU hPY
  let ψ : MulAut U ≃* Representation.BinaryDoubledNatural.Ambient n :=
    (BinaryFixedLine.linearAutEquiv.trans
      (BinaryLinear.SmallParabolicLevi.linearGroupCongr e)).trans
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
          (Representation.BinaryDoubledNatural.Space n)).symm
  have hψ (y : rigidityHyperplaneResidual L U V) :
      ψ (U.normalizerMonoidHom ⟨y,hYU y.property⟩) =
        (Representation.BinaryDoubledNatural.representation n).asGroupHom (q y) := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    change e (Additive.ofMul (U.normalizerMonoidHom ⟨y,hYU y.property⟩
      (e.symm v).toMul)) = _
    rw [he]
    change Representation.BinaryDoubledNatural.representation n (q y) (e (e.symm v)) = _
    rw [e.apply_symm_apply]
    rfl
  let f := ψ.toMonoidHom.comp r
  have hf (p : P) : f p ∈ Subgroup.centralizer
      (Representation.BinaryDoubledNatural.component n :
        Set (Representation.BinaryDoubledNatural.Ambient n)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro a ⟨g,rfl⟩
    obtain ⟨y,rfl⟩ := hq g
    rw [← hψ]
    exact ((pair_action_commutes D A C hYU hPY p y).map ψ.toMonoidHom).eq.symm
  let j := f.codRestrict _ hf
  have hj : Function.Injective j := fun a b heq =>
    hr (ψ.injective (congrArg Subtype.val heq))
  have hdiv := Subgroup.card_dvd_of_injective j hj
  rw [Representation.BinaryDoubledNatural.card_centralizer (by dsimp [n]; omega)] at hdiv
  have hp := C.prime_order
  have ho := C.odd_order
  have hcases := hp.dvd_mul.mp (show Nat.card P ∣ 2*3 from hdiv)
  rcases hcases with h2 | h3
  · have he := (Nat.dvd_prime Nat.prime_two).mp h2
    rcases he with he | he
    · exact (hp.ne_one he).elim
    · rw [he] at ho
      exact (by decide : ¬ Odd (2 : ℕ)) ho |>.elim
  · exact ((Nat.dvd_prime Nat.prime_three).mp h3).resolve_left hp.ne_one

/-- The canonical parabolic factors now require only the component normality
argument; their cubic-order premise is discharged by the marked double. -/
theorem parabolic_factors_of_residual_normal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d)
    (hn : normalizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G) ≤
      normalizer (rigidityHyperplaneResidual L U V : Set G)) :
    ParabolicFactorization L V U P := by
  let B := RigidityKernel.source_centralizers h D structural A C hnone
  have hz := higher_component_centralizer_eq_bot_of_residual_normal h D A C B hn
    (RigidityResidual.radical_fixed_eq_component_centralizer h D structural A C B)
  have hs := higher_kernel_vanishing_consequences D B hz
  exact RigidityParabolic.factorization_of_cubic_and_pair_normalized D A C
    (cubic_of_residual_normal h D structural A C hnone hd hn)
    (C.core_le_sylow.trans hs.1)
    (RigidityParabolic.parabolic_normalizes_pair_of_residual_normal h D structural A C hn)


/-- The two-rank-two cubic witness in SL₄(2) and the independent pair cubic
exclude dimension five in the actual two-local normalizer. -/
theorem dimension_four_of_residual_normal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d)
    (hn : normalizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G) ≤
      normalizer (rigidityHyperplaneResidual L U V : Set G)) : d = 4 := by
  have hd5 : d = 4 ∨ d = 5 := by have := A.dimension.2; omega
  rcases hd5 with he | rfl
  · exact he
  exfalso
  let := C.elementary
  let Y := rigidityHyperplaneResidual L U V
  let J := P ⊔ U
  let B := RigidityKernel.source_centralizers h D structural A C hnone
  have hz := higher_component_centralizer_eq_bot_of_residual_normal h D A C B hn
    (RigidityResidual.radical_fixed_eq_component_centralizer h D structural A C B)
  have hs := higher_kernel_vanishing_consequences D B hz
  have hYU : Y ≤ normalizer (U : Set G) := by
    simpa only [hs.2.2.2] using B.residual_normalizes
  have hPY : P ≤ normalizer (Y : Set G) :=
    (le_sup_left.trans le_sup_left : P ≤ cyclicPairJoin P U V).trans
      ((higher_pair_normalizes_sylow_centralizer D A C).trans hn)
  have hUY : U ≤ Y := core_le_residual_of_pair_normalizes D A C hd hPY
  have hPU : P ≤ normalizer (U : Set G) :=
    (show P ≤ H by rw [C.overgroup]; exact le_sup_left).trans C.overgroup_normalizes_core
  have hYL : Y ≤ L := (map_subtype_le _).trans inf_le_left
  have hPJ : Disjoint P Y := by
    let : Fact (Nat.card P).Prime := ⟨C.prime_order⟩
    rcases (Y.subgroupOf P).eq_bot_or_eq_top_of_prime_card with hb | ht
    · apply disjoint_def.mpr
      intro x hxP hxY
      have hx : (⟨x,hxP⟩ : P) ∈ Y.subgroupOf P := hxY
      rw [hb] at hx
      have he : (⟨x,hxP⟩ : P) = 1 := mem_bot.mp hx
      exact congrArg (fun a : P => (a : G)) he
    · have hPY' : P ≤ Y := (subgroupOf_eq_top).mp ht
      exact (C.escapes (hPY'.trans (hYL.trans L.le_normalizer))).elim
  have hJY : J ≤ normalizer (Y : Set G) := sup_le hPY (hUY.trans Y.le_normalizer)
  have hYJ : Y ≤ normalizer (J : Set G) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    have hc := RigidityParabolic.residual_pair_commutator D A C hPY
    exact ((commutator_mono le_sup_left le_rfl).trans hc).trans le_sup_right
  have hInt : Y ⊓ J = U := by
    apply le_antisymm ?_ (le_inf hUY le_sup_right)
    intro x hx
    have hxprod : x ∈ (P : Set G) * (U : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right P U hPU]
      exact hx.2
    obtain ⟨p,hp,u,hu,rfl⟩ := hxprod
    have hpY : p ∈ Y := by
      simpa only [mul_inv_cancel_right] using Y.mul_mem hx.1 (Y.inv_mem (hUY hu))
    change p*u ∈ U
    rw [disjoint_def.mp hPJ hp hpY,one_mul]
    exact hu
  have hlow := primeRank_add_le_of_normalizes_of_twoGroup_intersection
    (p := 3) (by decide) Y J hYJ hJY (by
      rw [hInt]; exact IsElementaryAbelian.isPGroup 2 U)
  have hYrank : 2 ≤ primeRank 3 Y := by
    let : IsElementaryAbelian 2 (U ⊓ V : Subgroup G) :=
      IsElementaryAbelian.of_injective (inclusion (show U ⊓ V ≤ U from inf_le_left))
        (inclusion_injective _)
    let e : (Y ⧸ pCore 2 Y) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) := (residualQuotientAutEquiv D A C hd).trans (hyperplaneAutEquiv C)
    have he : primeRank 3 (Y ⧸ pCore 2 Y) =
        primeRank 3 (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) := primeRank_equiv 3 e
    rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 Y) pCore_isPGroup] at he
    rw [he]
    exact BinaryLinear.SmallCubicRank.four
  have hJrank : 1 ≤ primeRank 3 J := by
    have hp := cubic_of_residual_normal h D structural A C hnone hd hn
    have hnz : primeRank 3 P ≠ 0 := by
      intro he
      have hh := PrimeRank.eq_zero_iff_not_dvd_card.mp he
      rw [hp] at hh
      exact hh dvd_rfl
    exact (by omega : 1 ≤ primeRank 3 P).trans (primeRank_mono 3 le_sup_left)
  have hJN : J ≤ normalizer (U : Set G) := sup_le hPU U.le_normalizer
  have hlocal : IsTwoLocal (normalizer (U : Set G)) :=
    ⟨U,C.core_ne_bot (by decide),IsElementaryAbelian.isPGroup 2 U,rfl⟩
  have hupper : primeRank 3 (Y ⊔ J : Subgroup G) ≤ 2 :=
    (primeRank_mono 3 (sup_le hYU hJN)).trans
      ((h.simpleQTKE.twoLocal_sqtk hlocal).stronglyQuasithin 3 (by decide) (by decide))
  omega

/-- Complete higher-dimensional rigidity conditional only on the source
component-normalizer step. Final discharge stays with qt-d-12213-local-rigidity. -/
theorem source_rigidity_step_of_residual_normal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d)
    (hn : normalizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G) ≤
      normalizer (rigidityHyperplaneResidual L U V : Set G)) :
    (d = 3 ∨ d = 4) ∧ normalizer (L : Set G) = L ∧ L.pCoreIn 2 = V ∧
      ParabolicSplitting T L V U :=
  RigidityParabolic.source_rigidity_of_residual_normal_and_cubic h D structural A C hnone
    (Or.inr (dimension_four_of_residual_normal h D structural A C hnone hd hn))
    (cubic_of_residual_normal h D structural A C hnone hd hn) hn


/-- Application of the derived higher-dimensional parabolic factors to the
existing Gaschütz promotion, with no dimension or complement premise. -/
theorem source_split_of_residual_normal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d)
    (hn : normalizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G) ≤
      normalizer (rigidityHyperplaneResidual L U V : Set G)) :
    SplitLinearConfiguration L V d := by
  have hs := source_rigidity_step_of_residual_normal h D structural A C hnone hd hn
  exact splitLinearConfiguration_of_cyclic_factorization D A C hs.1 hs.2.1 hs.2.2.1
    (parabolic_factors_of_residual_normal h D structural A C hnone hd hn)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity

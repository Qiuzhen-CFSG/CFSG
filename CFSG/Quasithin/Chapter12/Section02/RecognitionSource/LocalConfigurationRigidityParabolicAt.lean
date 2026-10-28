module

public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityHigherNormalizerTensor
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityKernelAt

/-!
# Residual, parabolic and tensor consequences at G and T

Specialize the residual fixed-space and kernel-vanishing applications to
the local structural input. The original parabolic, its complement, and the
actual normalizer quotient and tensor conjugation equations are retained.

These are additive specializations of the corresponding rigidity modules;
public results independent of the universal inputs are reused directly.
Source: Aschbacher–Smith, original 12.2.25–26, printed pp.804–806
(PDF pp.821–823), with 12.2.2(3) and A.3.12 for containing components.
-/

public noncomputable section

section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V U P H : Subgroup G} {d : ℕ}

private theorem centralizer_eq_of_sylow_centralizer_at
    (hE : IsEvenCharacteristicAt T) {W : Subgroup G}
    (hne : W ≠ ⊥) (hTW : (T : Subgroup G) ≤ normalizer (W : Set G))
    (he : (T : Subgroup G) ⊓ centralizer (W : Set G) = W) :
    centralizer (W : Set G) = W := by
  have hWT : W ≤ (T : Subgroup G) := he.symm.le.trans inf_le_left
  have hWC : W ≤ centralizer (W : Set G) := he.symm.le.trans inf_le_right
  have hN : normalizer (W : Set G) ∈ Chapter1.He G :=
    Chapter1.twoLocal_mem_He_of_sylow_le T hE
      ⟨W, hne, T.isPGroup'.to_le hWT, rfl⟩ hTW
  have hCN : centralizer (W : Set G) ≤ normalizer (W : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hC : centralizer (W : Set G) ∈ Chapter1.He G :=
    Chapter1.lemma_1_1_3_1 hN (ne_bot_of_le_ne_bot hne hWC) hCN
      (normal_subgroupOf_centralizer_normalizer (W : Set G)).isSubnormal
  have hcoreT : (normalizer (W : Set G)).pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTW] using
      pCoreIn_le_sylow (normalizer (W : Set G)) (T.subtype hTW)
  have hcoreW : (centralizer (W : Set G)).pCoreIn 2 ≤ W := by
    apply (le_inf ?_ (pCoreIn_le 2 _)).trans he.le
    exact (pCoreIn_mono_of_normalizes hCN (normalizer_le_normalizer_centralizer W)).trans hcoreT
  apply le_antisymm ?_ hWC
  exact (le_inf le_rfl (centralizer_le hcoreW)).trans (hC.trans hcoreW)

theorem higher_selfCentralizing_of_kernel_vanishing_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P)
    (hzero : (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥) :
    centralizer (V : Set G) = V ∧ centralizer (U : Set G) = U := by
  have hs := higher_kernel_vanishing_consequences D B hzero
  exact ⟨centralizer_eq_of_sylow_centralizer_at (h.simpleQTKE.evenCharacteristic T)
      D.ne_bot (((structural L h).2.2 V D).1) hs.2.2.1,
    centralizer_eq_of_sylow_centralizer_at (h.simpleQTKE.evenCharacteristic T)
      (C.core_ne_bot (by have := A.dimension.1; omega)) C.sylow_normalizes_core hs.2.2.2⟩

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
end

section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V U P H : Subgroup G} {d : ℕ}

omit [Finite G] in
private theorem natural_normalizer_le_of_centralizer_at
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hcentral : centralizer (V : Set G) = V) : normalizer (V : Set G) ≤ L := by
  obtain ⟨e, f, hf⟩ := A.natural
  intro g hg
  let a : MulAut V := V.normalizerMonoidHom ⟨g, hg⟩
  obtain ⟨x, hx⟩ := Representation.specialLinearNatural_binary_full d
    ((f.symm.trans a).trans f)
  obtain ⟨l, hl⟩ := (QuotientGroup.mk'_surjective (pCore 2 L)) (e.symm x)
  have hel : e (QuotientGroup.mk' (pCore 2 L) l) = x := by rw [hl, e.apply_symm_apply]
  have ha : V.normalizerMonoidHom ⟨l, D.normalizes l.property⟩ = a := by
    ext v
    have hact := hf l v
    rw [hel] at hact
    have heq := hx (f v)
    simp only [MulEquiv.trans_apply, f.symm_apply_apply] at heq
    rw [heq, f.symm_apply_apply] at hact
    exact hact.symm
  have hk : (⟨l, D.normalizes l.property⟩⁻¹ * (⟨g, hg⟩ : normalizer (V : Set G))) ∈
      V.normalizerMonoidHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ha]
    exact inv_mul_cancel a
  rw [normalizerMonoidHom_ker] at hk
  have hm : (l : G)⁻¹ * g ∈ L := D.le_component (hcentral ▸ hk)
  simpa only [mul_inv_cancel_left] using L.mul_mem l.property hm

theorem higher_normalizer_eq_of_kernel_vanishing_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P)
    (hzero : (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥) :
    normalizer (L : Set G) = L := by
  have hc := (higher_kernel_vanishing_consequences D B hzero).2.1
  have hN : normalizer (L : Set G) ≤ normalizer (V : Set G) := by
    rw [← hc]
    exact normalizer_le_normalizer_characteristic_image L (pCore 2 L)
  exact le_antisymm (hN.trans (natural_normalizer_le_of_centralizer_at D A
    (higher_selfCentralizing_of_kernel_vanishing_at h D structural A C B hzero).1)) L.le_normalizer

namespace HigherRigidity

end HigherRigidity

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
end

section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.RigidityParabolic
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U : Subgroup G} {d : ℕ}

/-- Both dimension branches feed the existing complement consumer through
actual pair normality. The remaining central-factor and cubic conclusions
are still owned by qt-d-12213-local-rigidity. -/
theorem source_parabolic_of_cubic_pair_normalized_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V)
    (hzero : (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥)
    (hp : Nat.card P = 3)
    (hn : L ⊓ normalizer (U : Set G) ≤ normalizer (cyclicPairJoin P U V : Set G)) :
    ParabolicSplitting T L V U := by
  let B := RigidityKernel.source_centralizers_at h D structural A C hnone
  have hs := higher_kernel_vanishing_consequences D B hzero
  exact parabolicSplitting_of_cyclic_factorization D C
    (higher_normalizer_eq_of_kernel_vanishing_at h D structural A C B hzero)
    (factorization_of_cubic_and_pair_normalized D A C hp (C.core_le_sylow.trans hs.1) hn)

/-- The parabolic lies in YT, so residual normality supplies pair normality. -/
theorem parabolic_normalizes_pair_of_residual_normal_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hn : normalizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G) ≤
      normalizer (rigidityHyperplaneResidual L U V : Set G)) :
    L ⊓ normalizer (U : Set G) ≤ normalizer (cyclicPairJoin P U V : Set G) := by
  let Y := rigidityHyperplaneResidual L U V
  let F := L ⊓ normalizer ((U ⊓ V : Subgroup G) : Set G)
  have hPN : P ≤ normalizer (Y : Set G) :=
    (le_sup_left.trans le_sup_left : P ≤ cyclicPairJoin P U V).trans
      ((higher_pair_normalizes_sylow_centralizer D A C).trans hn)
  have hYI : Y ≤ normalizer (cyclicPairJoin P U V : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr
      ((residual_pair_commutator D A C hPN).trans (le_sup_right.trans le_sup_left))
  have hTV := ((structural L h).2.2 V D).1
  have hTW : (T : Subgroup G) ≤ normalizer ((U ⊓ V : Subgroup G) : Set G) :=
    (le_inf C.sylow_normalizes_core hTV).trans inf_normalizer_le_normalizer_inf
  have hTF : (T : Subgroup G) ≤ normalizer (F : Set G) :=
    (le_inf D.sylow_normalizes_component (hTW.trans (normalizer _).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hJF : L ⊓ normalizer (U : Set G) ≤ F :=
    le_inf inf_le_left ((le_inf inf_le_right (inf_le_left.trans D.normalizes)).trans
      inf_normalizer_le_normalizer_inf)
  exact (hJF.trans (le_embedded_pResidual_sup_sylow_of_normalizes T F hTF)).trans
    (sup_le hYI (C.sylow_le_overgroup.trans C.pair_normal))

/-- The exact rigidityStep output, with parabolic factors constructed. The
residual normality, cubic order and dimension bound remain with this task;
this conditional application does not prove the two source branches. -/
theorem source_rigidity_of_residual_normal_and_cubic_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : d = 3 ∨ d = 4) (hp : Nat.card P = 3)
    (hn : normalizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G) ≤
      normalizer (rigidityHyperplaneResidual L U V : Set G)) :
    (d = 3 ∨ d = 4) ∧ normalizer (L : Set G) = L ∧ L.pCoreIn 2 = V ∧
      ParabolicSplitting T L V U := by
  let B := RigidityKernel.source_centralizers_at h D structural A C hnone
  have hzero := higher_component_centralizer_eq_bot_of_residual_normal h D A C B hn
    (RigidityResidual.radical_fixed_eq_component_centralizer_at h D structural A C B)
  exact ⟨hd,higher_normalizer_eq_of_kernel_vanishing_at h D structural A C B hzero,
    RigidityResidual.component_core_of_centralizers D B,
    source_parabolic_of_cubic_pair_normalized_at h D structural A C hnone hzero hp
      (parabolic_normalizes_pair_of_residual_normal_at h D structural A C hn)⟩

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.RigidityParabolic
end

section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G} {d : ℕ}

/-- The odd-prime pair actor embeds in the actual doubled-natural centralizer. -/
theorem cubic_of_residual_normal_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d)
    (hn : normalizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G) ≤
      normalizer (rigidityHyperplaneResidual L U V : Set G)) : Nat.card P = 3 := by
  let := C.elementary
  let n := d-1
  let : NeZero n := ⟨by dsimp [n]; omega⟩
  let B := RigidityKernel.source_centralizers_at h D structural A C hnone
  have hz := higher_component_centralizer_eq_bot_of_residual_normal h D A C B hn
    (RigidityResidual.radical_fixed_eq_component_centralizer_at h D structural A C B)
  have hs := higher_kernel_vanishing_consequences D B hz
  have hCU := (higher_selfCentralizing_of_kernel_vanishing_at h D structural A C B hz).2
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

/-- The two-rank-two cubic witness in SL₄(2) and the independent pair cubic
exclude dimension five in the actual two-local normalizer. -/
theorem dimension_four_of_residual_normal_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
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
  let B := RigidityKernel.source_centralizers_at h D structural A C hnone
  have hz := higher_component_centralizer_eq_bot_of_residual_normal h D A C B hn
    (RigidityResidual.radical_fixed_eq_component_centralizer_at h D structural A C B)
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
    have hp := cubic_of_residual_normal_at h D structural A C hnone hd hn
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
theorem source_rigidity_step_of_residual_normal_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d)
    (hn : normalizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G) ≤
      normalizer (rigidityHyperplaneResidual L U V : Set G)) :
    (d = 3 ∨ d = 4) ∧ normalizer (L : Set G) = L ∧ L.pCoreIn 2 = V ∧
      ParabolicSplitting T L V U :=
  RigidityParabolic.source_rigidity_of_residual_normal_and_cubic_at h D structural A C hnone
    (Or.inr (dimension_four_of_residual_normal_at h D structural A C hnone hd hn))
    (cubic_of_residual_normal_at h D structural A C hnone hd hn) hn

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
end

section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
open Representation
namespace TensorModel

end TensorModel
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G}

private theorem centralizer_eq_of_pair_orders_at
    {X : Type*} [Group X] [Finite X]
    (φ : X →* TensorModel.Ambient) (J PP VV : Subgroup X)
    (hPJ : PP ≤ J) (hVJ : VV ≤ J)
    (hcentral : J.map φ ≤ centralizer (TensorModel.component : Set TensorModel.Ambient))
    (hP : Nat.card (PP.map φ) = 3) (hV : Nat.card (VV.map φ) = 2) :
    J.map φ = centralizer (TensorModel.component : Set TensorModel.Ambient) := by
  let : Finite TensorModel.Ambient := Finite.of_injective
    (fun a : TensorModel.Ambient => fun v : TensorModel.Space =>
      (a : Module.End (ZMod 2) TensorModel.Space) v)
    (fun _ _ he => Units.ext (LinearMap.ext (congrFun he)))
  apply eq_of_le_of_card_ge hcentral
  have hthree : Nat.card (PP.map φ) ∣ Nat.card (J.map φ) := card_dvd_of_le (map_mono hPJ)
  have htwo : Nat.card (VV.map φ) ∣ Nat.card (J.map φ) := card_dvd_of_le (map_mono hVJ)
  rw [hP] at hthree
  rw [hV] at htwo
  have hsix : 6 ∣ Nat.card (J.map φ) :=
    (show Nat.Coprime 2 3 by decide).mul_dvd_of_dvd_of_dvd htwo hthree
  have he : TensorModel.component = BinaryDoubledNatural.component 3 := rfl
  rw [he,BinaryDoubledNatural.card_centralizer (by decide : 2 ≤ 3)]
  exact Nat.le_of_dvd Nat.card_pos hsix

theorem source_tensor_normalizer_of_residual_normal_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V 4) (C : CyclicLocalAnalysis T L V 4 H P U)
    (hnone : NoEscape L V)
    (hn : normalizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G) ≤
      normalizer (rigidityHyperplaneResidual L U V : Set G)) :
    normalizer (U : Set G) = rigidityHyperplaneResidual L U V ⊔ cyclicPairJoin P U V ∧
      letI := C.elementary
      ∃ e : Additive U ≃ₗ[ZMod 2] TensorModel.Space,
      ∃ f : NormalizerQuotient U ≃* TensorModel.Factors,
        ∀ (g : normalizer (U : Set G)) (u : U),
          e (Additive.ofMul (U.normalizerMonoidHom g u)) =
            TensorModel.tensor (f (quotient U g)) (e (Additive.ofMul u)) := by
  let := C.elementary
  let B := RigidityKernel.source_centralizers_at h D structural A C hnone
  let Y := rigidityHyperplaneResidual L U V
  let I := cyclicPairJoin P U V
  let N := normalizer (U : Set G)
  have hz := higher_component_centralizer_eq_bot_of_residual_normal h D A C B hn
    (RigidityResidual.radical_fixed_eq_component_centralizer_at h D structural A C B)
  have hs := higher_kernel_vanishing_consequences D B hz
  have hCU := (higher_selfCentralizing_of_kernel_vanishing_at h D structural A C B hz).2
  have hNY : N ≤ normalizer (Y : Set G) := by simpa only [hs.2.2.2] using hn
  have hYN : Y ≤ N := by simpa only [hs.2.2.2] using B.residual_normalizes
  have hIN : I ≤ N := by
    simpa only [hs.2.2.2] using higher_pair_normalizes_sylow_centralizer D A C
  have hPN : P ≤ N := (le_sup_left.trans le_sup_left).trans hIN
  have hVN : V ≤ N := le_sup_right.trans hIN
  have hPY : P ≤ normalizer (Y : Set G) := hPN.trans hNY
  have hUY : U ≤ Y := core_le_residual_of_pair_normalizes D A C (by decide) hPY
  obtain ⟨q,hq,e,he⟩ := exists_natural_double D A C (by decide) hYN hPY
  let ψ : MulAut U ≃* TensorModel.Ambient :=
    (BinaryFixedLine.linearAutEquiv.trans
      (BinaryLinear.SmallParabolicLevi.linearGroupCongr e)).trans
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) TensorModel.Space).symm
  let φ : N →* TensorModel.Ambient := ψ.toMonoidHom.comp U.normalizerMonoidHom
  have hφ (g : N) (u : U) :
      (φ g : Module.End (ZMod 2) TensorModel.Space) (e (Additive.ofMul u)) =
        e (Additive.ofMul (U.normalizerMonoidHom g u)) := by
    change e (Additive.ofMul (U.normalizerMonoidHom g
      (e.symm (e (Additive.ofMul u))).toMul)) = _
    rw [e.symm_apply_apply]
    rfl
  have hker : φ.ker = U.subgroupOf N := by
    ext g
    change ψ (U.normalizerMonoidHom g) = 1 ↔ (g : G) ∈ U
    rw [← map_one ψ,ψ.injective.eq_iff]
    change g ∈ U.normalizerMonoidHom.ker ↔ _
    rw [normalizerMonoidHom_ker,hCU]
    rfl
  have hφY (y : Y) : φ (inclusion hYN y) =
      (SL3DoubledNaturalOffenders.representation (ZMod 2)).asGroupHom (q y) := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    obtain ⟨u,rfl⟩ := e.surjective v
    exact (hφ _ u.toMul).trans (he y u.toMul)
  have hYimage : (Y.subgroupOf N).map φ = TensorModel.component := by
    apply le_antisymm
    · rintro b ⟨y,hy,rfl⟩
      exact ⟨q ⟨y,hy⟩, (hφY ⟨y,hy⟩).symm⟩
    · rintro b ⟨a,rfl⟩
      obtain ⟨y,rfl⟩ := hq a
      exact ⟨inclusion hYN y,y.property,hφY y⟩
  have hφN : ∀ g : N, φ g ∈ TensorModel.normalizer := by
    intro g
    change φ g ∈ normalizer (TensorModel.component : Set TensorModel.Ambient)
    rw [← hYimage]
    apply (Y.subgroupOf N).le_normalizer_map φ
    apply mem_map_of_mem φ
    rw [←subgroupOf_normalizer_eq hYN]
    exact hNY g.property
  have hIcentral : (I.subgroupOf N).map φ ≤
      centralizer (TensorModel.component : Set TensorModel.Ambient) := by
    rintro b ⟨i,hi,rfl⟩
    rw [mem_centralizer_iff,←hYimage]
    rintro a ⟨y,hy,rfl⟩
    have hk : ⁅i,y⁆ ∈ φ.ker := by
      rw [hker]
      exact RigidityParabolic.residual_pair_commutator D A C hPY
        (commutator_mem_commutator hi hy)
    have hh := MonoidHom.mem_ker.mp hk
    rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm] at hh
    exact hh.symm
  have hcard (K : Subgroup G) (hKN : K ≤ N) :
      Nat.card ((K.subgroupOf N).map φ) = U.relIndex K := by
    rw [←relIndex_ker,hker,relIndex_subgroupOf hKN]
  have hPcard : Nat.card ((P.subgroupOf N).map φ) = 3 := by
    rw [hcard P hPN,←inf_relIndex_left]
    have hd : Disjoint U P := disjoint_of_coprime_natCard (by
      rw [C.dimension]; exact C.odd_order.coprime_two_left.pow_left _)
    rw [hd.symm.eq_bot,relIndex_bot_left]
    exact cubic_of_residual_normal_at h D structural A C hnone (by decide) hn
  have hVcard : Nat.card ((V.subgroupOf N).map φ) = 2 := by
    rw [hcard V hVN,←inf_relIndex_left]
    rw [inf_comm V U]
    exact RigidityResidual.hyperplane_index A C
  have hIimage : (I.subgroupOf N).map φ =
      centralizer (TensorModel.component : Set TensorModel.Ambient) := by
    exact centralizer_eq_of_pair_orders_at φ (I.subgroupOf N) (P.subgroupOf N) (V.subgroupOf N)
      (subgroupOf_mono N (le_sup_left.trans le_sup_left))
      (subgroupOf_mono N le_sup_right) hIcentral hPcard hVcard
  have hjoin : ((Y ⊔ I).subgroupOf N).map φ = TensorModel.normalizer := by
    rw [subgroupOf_sup hYN hIN,Subgroup.map_sup,hYimage,hIimage,
      ←SL3DoubledNaturalOffenders.binary_normalizer_eq_sup]
  have hsurj : Function.Surjective (φ.codRestrict TensorModel.normalizer hφN) := by
    intro b
    have hb : (b : TensorModel.Ambient) ∈ ((Y ⊔ I).subgroupOf N).map φ :=
      hjoin.symm ▸ b.property
    obtain ⟨g,hg,hgb⟩ := mem_map.mp hb
    exact ⟨g,Subtype.ext hgb⟩
  have hgen : N = Y ⊔ I := by
    apply le_antisymm ?_ (sup_le hYN hIN)
    intro g hg
    obtain ⟨k,hk,hkg⟩ := mem_map.mp (hjoin.symm ▸ hφN ⟨g,hg⟩)
    have hdiff : k⁻¹ * (⟨g,hg⟩ : N) ∈ φ.ker := by
      rw [MonoidHom.mem_ker,map_mul,map_inv,hkg,inv_mul_cancel]
    have hU : (k : G)⁻¹ * g ∈ U := by
      change k⁻¹ * (⟨g,hg⟩ : N) ∈ U.subgroupOf N
      rwa [←hker]
    have hh : (k : G) * ((k : G)⁻¹ * g) ∈ Y ⊔ I :=
      (Y ⊔ I).mul_mem hk (mem_sup_left (hUY hU))
    simpa only [mul_inv_cancel_left] using hh
  let fN := φ.codRestrict TensorModel.normalizer hφN
  have hkN : fN.ker = U.subgroupOf N := by
    exact (MonoidHom.ker_codRestrict φ _ _).trans hker
  let f := ((QuotientGroup.quotientMulEquivOfEq hkN.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective fN hsurj)).trans
      SL3DoubledNaturalOffenders.binaryNormalizerEquiv
  refine ⟨hgen,e,f,?_⟩
  intro g u
  exact (hφ g u).symm.trans
    (SL3DoubledNaturalOffenders.binaryNormalizerEquiv_action (fN g) (e (Additive.ofMul u)))

/-- Frattini gives the source complement in the full normalizer, with the
original P retained. This uses only normality of PU and its fixed-free action. -/
private theorem full_normalizer_complement_at
    {d : ℕ} (C : CyclicLocalAnalysis T L V d H P U)
    (hNP : normalizer (U : Set G) ≤ normalizer ((U ⊔ P : Subgroup G) : Set G)) :
    (U.subgroupOf (normalizer (U : Set G))).IsComplement'
      ((normalizer (P : Set G)).subgroupOf (normalizer (U : Set G))) := by
  let := C.elementary
  let : Fact (Nat.card P).Prime := ⟨C.prime_order⟩
  let N := normalizer (U : Set G)
  let J := U ⊔ P
  have hPN : P ≤ N :=
    (show P ≤ H by rw [C.overgroup]; exact le_sup_left).trans C.overgroup_normalizes_core
  have hJN : J ≤ N := sup_le U.le_normalizer hPN
  have hcop : (Nat.card U).Coprime (Nat.card P) := by
    rw [C.dimension]
    exact C.odd_order.coprime_two_left.pow_left _
  have hd : Disjoint U P := disjoint_of_coprime_natCard hcop
  have hp : IsPGroup (Nat.card P) P := IsPGroup.of_card (n := 1) (by simp)
  have hc := card_sup_eq_mul_of_normalizes_of_disjoint U P hPN hd
  have hi := relIndex_mul_relIndex (⊥ : Subgroup G) P J bot_le le_sup_right
  rw [relIndex_bot_left,relIndex_bot_left,hc,mul_comm (Nat.card U)] at hi
  have he : (P.subgroupOf J).index = Nat.card U := Nat.eq_of_mul_eq_mul_left Nat.card_pos hi
  have hPi : IsPGroup (Nat.card P) (P.subgroupOf J) :=
    hp.of_equiv (subgroupOfEquivOfLe le_sup_right).symm
  let S : Sylow (Nat.card P) J := hPi.toSylow (by
    rw [he]; exact C.prime_order.coprime_iff_not_dvd.mp hcop.symm)
  have hS : (S : Subgroup J).map J.subtype = P := by
    rw [IsPGroup.toSylow_coe]
    exact map_subgroupOf_eq_of_le le_sup_right
  let J' := J.subgroupOf N
  let : J'.Normal := (normal_subgroupOf_iff_le_normalizer hJN).mpr hNP
  let e : J ≃* J' := (subgroupOfEquivOfLe hJN).symm
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hmap : (S' : Subgroup J').map J'.subtype = P.subgroupOf N := by
    apply map_injective N.subtype_injective
    change (((S : Subgroup J).map e.toMonoidHom).map J'.subtype).map N.subtype = _
    rw [map_map,map_map,map_subgroupOf_eq_of_le hPN]
    exact hS
  have hfr := S'.normalizer_sup_eq_top
  rw [hmap,←subgroupOf_normalizer_eq hPN] at hfr
  have hs : U.subgroupOf N ⊔ (normalizer (P : Set G)).subgroupOf N = ⊤ := by
    change (normalizer (P : Set G)).subgroupOf N ⊔ (U ⊔ P).subgroupOf N = ⊤ at hfr
    rw [subgroupOf_sup U.le_normalizer hPN,sup_left_comm,
      sup_eq_left.mpr (subgroupOf_mono N P.le_normalizer)] at hfr
    exact hfr
  have hd' : Disjoint (U.subgroupOf N) ((normalizer (P : Set G)).subgroupOf N) := by
    rw [disjoint_iff]
    change (U ⊓ normalizer (P : Set G)).subgroupOf N = ⊥
    rw [SylowThreeNormalizer.normalizer_inf_eq_centralizer_inf U P hPN hd,C.fixed]
    exact bot_subgroupOf _
  apply isComplement'_of_disjoint_and_mul_eq_univ hd'
  rw [←coe_mul_of_right_le_normalizer_left _ _
    (by rw [(U.subgroupOf N).normalizer_eq_top]; exact le_top),hs]
  rfl

/-- The actual full-normalizer complement from original 12.2.26. The module
marking is supplied by the previous theorem, not inferred from its group type. -/
theorem source_normalizer_complement_of_residual_normal_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V 4) (C : CyclicLocalAnalysis T L V 4 H P U)
    (hnone : NoEscape L V)
    (hn : normalizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G) ≤
      normalizer (rigidityHyperplaneResidual L U V : Set G)) :
    (U.subgroupOf (normalizer (U : Set G))).IsComplement'
      ((normalizer (P : Set G)).subgroupOf (normalizer (U : Set G))) ∧
    Nonempty ((normalizer (U : Set G) ⊓ normalizer (P : Set G) : Subgroup G) ≃*
      TensorModel.Factors) := by
  obtain ⟨hgen,e,f,hact⟩ := source_tensor_normalizer_of_residual_normal_at h D structural A C hnone hn
  let Y := rigidityHyperplaneResidual L U V
  let I := cyclicPairJoin P U V
  let N := normalizer (U : Set G)
  let B := RigidityKernel.source_centralizers_at h D structural A C hnone
  have hz := higher_component_centralizer_eq_bot_of_residual_normal h D A C B hn
    (RigidityResidual.radical_fixed_eq_component_centralizer_at h D structural A C B)
  have hR := (higher_kernel_vanishing_consequences D B hz).2.2.2
  have hNY : N ≤ normalizer (Y : Set G) := by simpa only [hR] using hn
  have hPN : P ≤ N := (le_sup_left.trans le_sup_left).trans (le_sup_right.trans hgen.ge)
  have hNI : N ≤ normalizer (I : Set G) := by
    change normalizer (U : Set G) ≤ normalizer (I : Set G)
    rw [hgen]
    apply sup_le ?_ I.le_normalizer
    apply le_normalizer_iff_commutator_le_left.mpr
    exact (RigidityParabolic.residual_pair_commutator D A C (hPN.trans hNY)).trans
      (le_sup_right.trans le_sup_left)
  have hNP : N ≤ normalizer ((U ⊔ P : Subgroup G) : Set G) := by
    rw [sup_comm U P,←RigidityParabolic.pair_residual D C]
    exact hNI.trans (normalizer_le_normalizer_characteristic_image I (pResidual 2 I))
  have hcomp := full_normalizer_complement_at C hNP
  refine ⟨hcomp,?_⟩
  let k : ((normalizer (P : Set G)).subgroupOf N) ≃*
      (N ⊓ normalizer (P : Set G) : Subgroup G) := {
    toFun x := ⟨x, x.val.property, x.property⟩
    invFun x := ⟨⟨x,x.property.1⟩,x.property.2⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  exact ⟨(k.symm.trans hcomp.symm.QuotientMulEquiv.symm).trans f⟩

/-- Both source normalizer conclusions for every higher-dimensional input.
The dimension cutoff is discharged by the previous cubic-rank argument;
only the containing-component normality step remains with this owner. -/
theorem source_higher_normalizer_of_residual_normal_at
    {d : ℕ} (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d)
    (hn : normalizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G) ≤
      normalizer (rigidityHyperplaneResidual L U V : Set G)) :
    d = 4 ∧
      normalizer (U : Set G) =
        rigidityHyperplaneResidual L U V ⊔ cyclicPairJoin P U V ⊔ (T : Subgroup G) ∧
      (U.subgroupOf (normalizer (U : Set G))).IsComplement'
        ((normalizer (P : Set G)).subgroupOf (normalizer (U : Set G))) ∧
      Nonempty ((normalizer (U : Set G) ⊓ normalizer (P : Set G) : Subgroup G) ≃*
        (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) × Equiv.Perm (Fin 3))) ∧
      letI := C.elementary
      ∃ e : Additive U ≃ₗ[ZMod 2] TensorModel.Space,
      ∃ f : NormalizerQuotient U ≃* TensorModel.Factors,
        ∀ (g : normalizer (U : Set G)) (u : U),
          e (Additive.ofMul (U.normalizerMonoidHom g u)) =
            TensorModel.tensor (f (quotient U g)) (e (Additive.ofMul u)) := by
  have hd4 := dimension_four_of_residual_normal_at h D structural A C hnone hd hn
  subst d
  obtain ⟨hgen,e,f,hact⟩ := source_tensor_normalizer_of_residual_normal_at h D structural A C hnone hn
  obtain ⟨hcomp,⟨k⟩⟩ := source_normalizer_complement_of_residual_normal_at h D structural A C hnone hn
  refine ⟨rfl,?_,hcomp,?_,e,f,hact⟩
  · rw [←hgen,sup_eq_left.mpr C.sylow_normalizes_core]
  · exact ⟨k.trans (MulEquiv.prodCongr (MulEquiv.refl _)
      (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three))⟩

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
end

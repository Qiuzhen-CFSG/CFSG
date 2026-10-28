module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicExclusionNumericalDimension
public import Theory.Representation.ExtraspecialCubicDisplacement

/-!
# The order of the extraspecial orbit module

Coprime splitting and the two conjugate axes identify U=[W,⟨g⟩] and
W=U⊕C_W(g). The chosen rotation is noncentral in P: a central rotation
would normalize V and contradict disjointness of the original TI pair.
The existing extraspecial cubic-action formula gives dim W=3 dim C_W(g).
Since |U|=16 when d=3, the literal splitting forces dim W=6 and |W|=64.

Together with the prime and dimension calculation this completes the
numerical branch of 12.2.23. NumericalAssembly discharges that premise in
the original cyclic-block consumer. Nonprime selection and the terminal
component-module contradiction remain with qt-d-12213-cyclic-block.
Source: Aschbacher–Smith, 12.2.23, printed pp.803–804; the cubic fixed-space
formula is proved in Theory/Representation/ExtraspecialCubicDisplacement.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U W : Subgroup G} {d p : ℕ} {g v : G}
namespace InvariantOddLocalAnalysis
variable (S : InvariantOddLocalAnalysis T L V d p H P U W g v)
include S

private theorem rotation_coprime_module : Nat.Coprime (Nat.card (zpowers g)) (Nat.card W) := by
  let := S.elementary
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 W).exists_card_eq
  rw [Nat.card_zpowers, S.generator_order, hn]
  exact S.odd_prime.coprime_two_right.pow_right n

/-- The original pair core is the displacement of W under its rotation. -/
theorem module_commutator_rotation : ⁅W, zpowers g⁆ = U := by
  let := S.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le S.core_le_module
  let I := cyclicPairJoin (zpowers g) U V
  let B := V.map (MulAut.conj g).toMonoidHom
  have hIn : I ≤ normalizer (U : Set G) := by
    rw [← S.pair_core]
    exact I.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  have hgI : zpowers g ≤ I := le_sup_left.trans le_sup_left
  have hgW : g ∈ normalizer (W : Set G) :=
    S.normalizes ((S.overgroup ▸ le_sup_left) S.generator_mem)
  have hmapW : W.map (MulAut.conj g).toMonoidHom = W :=
    mem_normalizer_iff_map_conj_eq.mp hgW
  have hmapU : U.map (MulAut.conj g).toMonoidHom = U :=
    mem_normalizer_iff_map_conj_eq.mp (hIn (hgI (mem_zpowers g)))
  have hWV : ⁅W, V⁆ ≤ U := S.transvections.le.trans inf_le_left
  have hWB : ⁅W, B⁆ ≤ U := by
    rw [← hmapW, ← map_commutator, ← hmapU]
    exact map_mono hWV
  have hWI : ⁅W, I⁆ ≤ U := by
    rw [commutator_comm]
    change ⁅cyclicPairJoin (zpowers g) U V, W⁆ ≤ U
    rw [S.pair_generated]
    exact commutator_sup_le_of_relative_normal I V B W U hIn
      (show V ≤ I from le_sup_right)
      (le_sup_right.trans S.pair_generated.ge)
      (by rwa [commutator_comm]) (by rwa [commutator_comm])
  have hc : Nat.Coprime (Nat.card (zpowers g)) (Nat.card U) :=
    S.rotation_coprime_module.of_dvd_right (card_dvd_of_le S.core_le_module)
  have hU : ⁅U, zpowers g⁆ = U := by
    have hh := eq_commutator_sup_centralizer_of_solvable_coprime U (zpowers g)
      (hgI.trans hIn) (Group.isSolvable_of_comm fun x y => mul_comm x y) hc
    simpa only [S.pair_fixed, sup_bot_eq] using hh.symm
  exact le_antisymm ((commutator_mono le_rfl hgI).trans hWI)
    (hU.ge.trans (commutator_mono S.core_le_module le_rfl))

/-- The literal module splits as the pair core and the rotation centralizer. -/
theorem module_split_rotation :
    W = U ⊔ (W ⊓ centralizer (zpowers g : Set G)) ∧
      Disjoint U (W ⊓ centralizer (zpowers g : Set G)) := by
  let := S.elementary
  have hn : zpowers g ≤ normalizer (W : Set G) :=
    (zpowers_le.mpr S.generator_mem).trans
      ((S.overgroup ▸ le_sup_left).trans S.normalizes)
  have hm := S.module_commutator_rotation
  constructor
  · simpa only [hm] using eq_commutator_sup_centralizer_of_solvable_coprime W
      (zpowers g) hn (Group.isSolvable_of_comm fun x y => mul_comm x y)
      S.rotation_coprime_module
  · simpa only [hm] using commutator_disjoint_centralizer_of_coprime W
      (zpowers g) hn S.rotation_coprime_module

/-- The chosen rotation is noncentral in the extraspecial odd group. -/
theorem generator_not_mem_center
    (A : NaturalLocalAnalysis T L V d) (he : IsExtraspecial p P) :
    (⟨g,S.generator_mem⟩ : P) ∉ center P := by
  let : Fact p.Prime := ⟨S.prime⟩
  let := he
  intro hgZ
  have hgΦ : g ∈ (frattini P).map P.subtype := by
    exact mem_map_of_mem P.subtype (show (⟨g,S.generator_mem⟩ : P) ∈ frattini P from by
      rwa [IsExtraspecial.frattini_eq_center (p := p)])
  have hgV : V.map (MulAut.conj g).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp (S.frattini_normalizes hgΦ)
  have hVV := S.pair_disjoint
  rw [hgV] at hVV
  have hV : V = ⊥ := disjoint_self.mp hVV
  exact S.hyperplane_ne_bot A (by rw [hV, inf_bot_eq])

omit [Finite G] in
/-- Fixed vectors of the literal P-representation are the ambient rotation centralizer. -/
theorem rotation_fixedSpace_card :
    letI := S.elementary
    Nat.card (Representation.BinaryOffender.fixedSpace S.oddModuleRepresentation
      (zpowers (⟨g,S.generator_mem⟩ : P))) =
      Nat.card (W ⊓ centralizer (zpowers g : Set G) : Subgroup G) := by
  let := S.elementary
  let x : P := ⟨g,S.generator_mem⟩
  let F := Representation.BinaryOffender.fixedSpace S.oddModuleRepresentation (zpowers x)
  let C := W ⊓ centralizer (zpowers g : Set G)
  have hmem (w : Additive W) : w ∈ F ↔ w.toMul.val ∈ C := by
    rw [Representation.BinaryOffender.mem_fixedSpace_zpowers_iff]
    constructor
    · intro hw
      refine ⟨w.toMul.property, ?_⟩
      have hh := congrArg (fun z : Additive W => z.toMul.val) hw
      change g * w.toMul.val * g⁻¹ = w.toMul.val at hh
      intro z hz
      obtain ⟨n,rfl⟩ := mem_zpowers_iff.mp hz
      exact (show Commute g w.toMul.val from mul_inv_eq_iff_eq_mul.mp hh).zpow_left n
    · rintro ⟨_, hw⟩
      apply Additive.toMul.injective
      apply Subtype.ext
      change g * w.toMul.val * g⁻¹ = w.toMul.val
      exact mul_inv_eq_iff_eq_mul.mpr (hw g (mem_zpowers g))
  let e : F ≃ C := {
    toFun := fun w => ⟨w.val.toMul.val, (hmem w).mp w.property⟩
    invFun := fun w => ⟨Additive.ofMul ⟨w,w.property.1⟩, (hmem _).mpr w.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  exact Nat.card_congr e

/-- The cubic rotation formula and the actual pair splitting give |W|=64. -/
theorem extraspecial_module_card_sixtyFour
    (A : NaturalLocalAnalysis T L V d)
    (he : IsExtraspecial p P)
    (hf : W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥)
    (hp : p = 3) (hd : d = 3) : Nat.card W = 64 := by
  subst p
  let := S.elementary
  let := he
  let x : P := ⟨g,S.generator_mem⟩
  let F := Representation.BinaryOffender.fixedSpace S.oddModuleRepresentation (zpowers x)
  let C := W ⊓ centralizer (zpowers g : Set G)
  have hdim := Representation.BinaryCoprimeDegree.extraspecial_cubic_fixed_finrank
    S.oddModuleRepresentation (S.oddModuleRepresentation_center_invariants he hf)
    ((Subgroup.orderOf_coe x).symm.trans S.generator_order)
    (S.generator_not_mem_center A he)
  have hs := S.module_split_rotation
  have hn : C ≤ normalizer (U : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro c hc u hu
    exact le_centralizer W hc.1 u (S.core_le_module hu)
  have hprod : Nat.card W = 16 * Nat.card C := by
    conv_lhs => rw [hs.1]
    rw [card_sup_eq_mul_of_normalizes_of_disjoint U C hn hs.2, S.core_card, hd]
    norm_num
  have hcardC : Nat.card C = 2 ^ Module.finrank (ZMod 2) F := by
    rw [← S.rotation_fixedSpace_card, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hcardW := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
  change Nat.card W = _ at hcardW
  rw [Nat.card_zmod] at hcardW
  have hexp : Module.finrank (ZMod 2) (Additive W) = 4 + Module.finrank (ZMod 2) F := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    change 2 ^ Module.finrank (ZMod 2) (Additive W) = 2 ^ (4 + Module.finrank (ZMod 2) F)
    rw [← hcardW, hprod, hcardC, pow_add]
    rfl
  have hdim6 : Module.finrank (ZMod 2) (Additive W) = 6 := by
    change Module.finrank (ZMod 2) (Additive W) = 3 * Module.finrank (ZMod 2) F at hdim
    omega
  rw [hcardW, hdim6]
  norm_num

/-- The complete numerical reduction of the extraspecial branch in source 12.2.23. -/
theorem extraspecial_numerical_reduction
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (he : IsExtraspecial p P)
    (hf : W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥) :
    p = 3 ∧ d = 3 ∧ Nat.card W = 64 := by
  obtain ⟨hp,hd⟩ := S.extraspecial_prime_dimension_eq_three D A hTV he hf
  exact ⟨hp,hd,S.extraspecial_module_card_sixtyFour A he hf hp hd⟩

end InvariantOddLocalAnalysis
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicExclusion
public import Theory.GroupAction.SmallQuotientCentralization
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms

/-!
# The Frattini displacement and fixed line in the extraspecial branch

The fixed-point-free Frattini action on W restricts to its invariant
hyperplane W ∩ V. The quotient V/(W ∩ V) has order two and hence trivial
action, giving [V,Φ(P)] = W ∩ V. Coprime splitting supplies the fixed
complement of order two. In the extraspecial case Φ(P) has prime order;
its nontrivial hyperplane action is therefore faithful on the original V.

These are inputs to the numerical reduction in 12.2.23. The application
in LocalConfigurationCyclicExclusionCoreAssembly retains the outstanding
numerical and terminal source proofs with qt-d-12213-cyclic-block.
Source: Aschbacher–Smith, printed pp.803–804.
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

omit [Finite G] in
/-- The canonical binary orbit contains the nonzero pair core. -/
theorem module_ne_bot (A : NaturalLocalAnalysis T L V d) : W ≠ ⊥ := by
  intro hW
  have hU : U = ⊥ := bot_unique (hW ▸ S.core_le_module)
  have hc := S.core_card
  rw [hU, card_bot] at hc
  have hd := A.dimension.1
  have hpow : 1 < 2 ^ (2 * (d - 1)) := one_lt_pow₀ (by decide) (by omega)
  omega

omit [Finite G] in
/-- The intersection W ∩ V has positive rank. -/
theorem hyperplane_ne_bot (A : NaturalLocalAnalysis T L V d) : W ⊓ V ≠ ⊥ := by
  intro he
  have hc := S.hyperplane
  rw [← S.intersection, he, card_bot] at hc
  have hd := A.dimension.1
  have hpow : 1 < 2 ^ (d - 1) := one_lt_pow₀ (by decide) (by omega)
  omega

omit [Finite G] in
/-- The original intersection W ∩ V has index two in V. -/
theorem module_intersection_relIndex (A : NaturalLocalAnalysis T L V d) :
    (W ⊓ V).relIndex V = 2 := by
  have hcV : Nat.card V = 2 ^ d := by
    obtain ⟨e, f, hf⟩ := A.natural
    rw [Nat.card_congr f.toEquiv]
    simp
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) (W ⊓ V) V bot_le inf_le_right
  rw [relIndex_bot_left, relIndex_bot_left, hcV, S.intersection, S.hyperplane] at hc
  have hd : d = (d - 1) + 1 := by have := A.dimension.1; omega
  conv_rhs at hc => rw [hd, pow_succ]
  rw [S.intersection]
  exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ (d - 1)) hc

omit [Finite G] in
/-- The embedded Frattini subgroup preserves the original W. -/
theorem frattini_normalizes_module :
    (frattini P).map P.subtype ≤ normalizer (W : Set G) :=
  (map_subtype_le _).trans ((S.overgroup ▸ le_sup_left).trans S.normalizes)

omit [Finite G] in
/-- The embedded Frattini subgroup preserves W ∩ V. -/
theorem frattini_normalizes_hyperplane :
    (frattini P).map P.subtype ≤ normalizer ((W ⊓ V : Subgroup G) : Set G) :=
  (le_inf S.frattini_normalizes_module S.frattini_normalizes).trans
    inf_normalizer_le_normalizer_inf

/-- Vanishing Frattini fixed points on W implies full displacement on W ∩ V. -/
theorem frattini_moves_hyperplane
    (hf : W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥) :
    ⁅W ⊓ V, (frattini P).map P.subtype⁆ = W ⊓ V := by
  let Φ := (frattini P).map P.subtype
  let E := W ⊓ V
  let : Fact p.Prime := ⟨S.prime⟩
  let : IsElementaryAbelian 2 W := S.elementary
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le (show E ≤ W from inf_le_left)
  have hzero : E ⊓ centralizer (Φ : Set G) = ⊥ := bot_unique
    ((inf_le_inf_right _ inf_le_left).trans hf.le)
  have hc : Nat.Coprime (Nat.card Φ) (Nat.card E) := by
    obtain ⟨a, ha⟩ := (S.pgroup.to_le (map_subtype_le (frattini P))).exists_card_eq
    obtain ⟨b, hb⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
    rw [ha, hb]
    exact S.odd_prime.coprime_two_right.pow a b
  have he := eq_commutator_sup_centralizer_of_solvable_coprime E Φ
    S.frattini_normalizes_hyperplane
    (Group.isSolvable_of_comm fun x y => mul_comm x y) hc
  simpa only [hzero, sup_bot_eq] using he.symm

/-- The actual Frattini displacement on V is exactly W ∩ V. -/
theorem frattini_moves_chosen
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hf : W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥) :
    ⁅V, (frattini P).map P.subtype⁆ = W ⊓ V := by
  let := D.elementary
  have hn : ((W ⊓ V).subgroupOf V).Normal := inferInstance
  have hc : Nat.card (V ⧸ (W ⊓ V).subgroupOf V) ≤ 2 := by
    simpa only [relIndex, index_eq_card] using (S.module_intersection_relIndex A).le
  apply le_antisymm
  · exact commutator_le_of_normalized_quotient_card_le_two _ V (W ⊓ V)
      S.frattini_normalizes S.frattini_normalizes_hyperplane hn hc
  · rw [← S.frattini_moves_hyperplane hf]
    exact commutator_mono inf_le_right le_rfl

/-- The Frattini-fixed subgroup of V is a complement of order two. -/
theorem chosen_split_frattini
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hf : W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥) :
    let C := V ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G)
    V = (W ⊓ V) ⊔ C ∧ Disjoint (W ⊓ V) C ∧ Nat.card C = 2 := by
  let Φ := (frattini P).map P.subtype
  let C := V ⊓ centralizer (Φ : Set G)
  let := D.elementary
  let : Fact p.Prime := ⟨S.prime⟩
  have hc : Nat.Coprime (Nat.card Φ) (Nat.card V) := by
    obtain ⟨a, ha⟩ := (S.pgroup.to_le (map_subtype_le (frattini P))).exists_card_eq
    obtain ⟨b, hb⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [ha, hb]
    exact S.odd_prime.coprime_two_right.pow a b
  have hm : ⁅V, Φ⁆ = W ⊓ V := S.frattini_moves_chosen D A hf
  have hs : V = (W ⊓ V) ⊔ C := by
    simpa only [hm] using eq_commutator_sup_centralizer_of_solvable_coprime V Φ
      S.frattini_normalizes (Group.isSolvable_of_comm fun x y => mul_comm x y) hc
  have hd : Disjoint (W ⊓ V) C := by
    simpa only [hm] using commutator_disjoint_centralizer_of_coprime V Φ
      S.frattini_normalizes hc
  have hn : C ≤ normalizer ((W ⊓ V : Subgroup G) : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro c hc x hx
    exact le_centralizer V hc.1 x hx.2
  have hprod := card_sup_eq_mul_of_normalizes_of_disjoint (W ⊓ V) C hn hd
  have hidx := relIndex_mul_relIndex (⊥ : Subgroup G) (W ⊓ V) V bot_le inf_le_right
  rw [relIndex_bot_left, relIndex_bot_left, S.module_intersection_relIndex A] at hidx
  have he : Nat.card (W ⊓ V : Subgroup G) * Nat.card C =
      Nat.card (W ⊓ V : Subgroup G) * 2 := hprod.symm.trans (congrArg (fun B : Subgroup G => Nat.card B) hs.symm |>.trans hidx.symm)
  exact ⟨hs, hd, Nat.eq_of_mul_eq_mul_left Nat.card_pos he⟩

/-- The literal embedded Frattini subgroup has order p. -/
theorem frattini_card_of_extraspecial (he : IsExtraspecial p P) :
    Nat.card ((frattini P).map P.subtype) = p := by
  let : Fact p.Prime := ⟨S.prime⟩
  let := he
  rw [card_map_of_injective P.subtype_injective, IsExtraspecial.frattini_eq_center (p := p)]
  exact IsExtraspecial.center_order_p p P

/-- The Frattini conjugation action on the original V is faithful. -/
theorem frattini_chosen_action_faithful
    (A : NaturalLocalAnalysis T L V d) (he : IsExtraspecial p P)
    (hf : W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥) :
    Function.Injective (V.normalizerMonoidHom.comp (inclusion S.frattini_normalizes)) := by
  let Φ := (frattini P).map P.subtype
  let a := V.normalizerMonoidHom.comp (inclusion S.frattini_normalizes)
  have hc : Nat.card Φ = p := S.frattini_card_of_extraspecial he
  let : Fact (Nat.card Φ).Prime := ⟨hc ▸ S.prime⟩
  apply (MonoidHom.ker_eq_bot_iff a).mp
  rcases a.ker.eq_bot_or_eq_top_of_prime_card with hk | hk
  · exact hk
  · exfalso
    apply S.hyperplane_ne_bot A
    apply bot_unique
    intro w hw
    apply hf.le
    refine ⟨hw.1, ?_⟩
    intro z hz
    have hzker : (⟨z, hz⟩ : Φ) ∈ a.ker := hk ▸ mem_top _
    have hh := congrArg (fun f : MulAut V => (f ⟨w, hw.2⟩ : G)) hzker
    change z * w * z⁻¹ = w at hh
    exact mul_inv_eq_iff_eq_mul.mp hh

/-- A Frattini-fixed involution in V lies outside the pair core. -/
theorem exists_frattini_fixed_outside_core
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hf : W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥) :
    ∃ v' ∈ V, v' ∉ U ∧ v' ∈ centralizer
      (((frattini P).map P.subtype : Subgroup G) : Set G) := by
  let C := V ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G)
  obtain ⟨hs, hd, hc⟩ := S.chosen_split_frattini D A hf
  have hC : C ≠ ⊥ := by
    intro he
    change Nat.card C = 2 at hc
    rw [he, card_bot] at hc
    omega
  let : Nontrivial C := (Subgroup.nontrivial_iff_ne_bot _).mpr hC
  obtain ⟨x, hx1⟩ := exists_ne (1 : C)
  refine ⟨x, x.property.1, ?_, x.property.2⟩
  intro hxU
  exact hx1 (Subtype.ext (mem_bot.mp (hd.le_bot
    ⟨⟨S.core_le_module hxU, x.property.1⟩, x.property⟩)))


end InvariantOddLocalAnalysis
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

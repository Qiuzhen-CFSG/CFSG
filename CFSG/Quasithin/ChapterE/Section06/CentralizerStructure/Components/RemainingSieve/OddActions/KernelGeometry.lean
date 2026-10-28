module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.SourceInputs
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# Kernel and Sylow fixed-space geometry in E.6.8

Write W = C_V(L) and Z = C_V(T). The residual condition defining the
obstruction family passes from U to W, and relative subnormality keeps L
a component of C_G(W). If the actual V-action has corank at most one,
then W has index two in V. E.6.6 gives W ∩ Z = 1, while the normal
p-group fixed-point argument gives Z ≠ 1. Consequently |Z| = 2 and
V = W × Z.

These deductions do not prove U = W. Equality is equivalent to m(V/U) = 1.
Moreover, any strict inclusion U < W supplies an intermediate obstruction
A < W of corank two in V, with the same component L. A binary linear
functional on W annihilating U constructs A; the residual condition and
relative subnormality pass to every subgroup between U and W. It therefore
suffices to exclude this corank-two configuration, without assuming maximality.
In particular these exports must not be used as the complete kernel
assertion of E.6.8(5). The direct odd-model hypothesis is not needed for
the deductions proved here; its use in excluding U < W remains open.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.1–8,
printed pp.244–248, especially the displayed inequality (*) on p.247
and the odd-case paragraph on p.248.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve.OddActions.KernelGeometry
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G}

private theorem relIndex_eq_pow_corank [IsElementaryAbelian 2 V] (A : Subgroup G) :
    A.relIndex V = 2 ^ subgroupCorank V A := by
  rw [subgroupCorank_eq_quotient_finrank]
  exact Subgroup.relIndex_eq_two_pow_quotient_finrank V A

/-- Every intermediate subspace up to the full kernel remains in the source
obstruction family. Its residual is computed in its own centralizer in M. -/
theorem intermediate_mem_obstruction (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    {A : Subgroup G} (hUA : U ≤ A) (hAW : A ≤ V ⊓ centralizer (L : Set G)) :
    A ∈ obstructionFamily M V := by
  have hLC : L ≤ centralizer (A : Set G) :=
    le_centralizer_iff.mpr (hAW.trans inf_le_right)
  refine ⟨hAW.trans inf_le_left, fun he => hU.2.1 (le_bot_iff.mp (he ▸ hUA)), ?_, ?_⟩
  · exact fun hc => component_not_le h earlier hU hL (hLC.trans hc)
  · have hr := component_intersection_residual hU (Subgroup.centralizer_le hUA)
    have hr' := hr.trans inf_le_right
    rw [inf_comm] at hr'
    exact le_inf ((map_subtype_le _).trans inf_le_left) hr'

omit [Finite G] in
/-- Restriction of relative subnormality preserves the component at every
intermediate subspace between U and its action kernel. -/
theorem componentIn_intermediateCentralizer (hL : ComponentIn (centralizer (U : Set G)) L)
    {A : Subgroup G} (hUA : U ≤ A) (hAW : A ≤ V ⊓ centralizer (L : Set G)) :
    ComponentIn (centralizer (A : Set G)) L := by
  have hLC : L ≤ centralizer (A : Set G) :=
    le_centralizer_iff.mpr (hAW.trans inf_le_right)
  let e := (subgroupOfEquivOfLe hL.1).trans (subgroupOfEquivOfLe hLC).symm
  let _ := hL.2.2
  let _ := IsQuasisimple.of_mulEquiv e
  exact ⟨hLC, hL.2.1.comap (inclusion (Subgroup.centralizer_le hUA)), inferInstance⟩

/-- The whole action kernel is again an obstruction, with the residual
computed inside its own local centralizer. -/
theorem kernel_mem_obstruction (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) :
    V ⊓ centralizer (L : Set G) ∈ obstructionFamily M V :=
  intermediate_mem_obstruction h earlier hU hL (fixedSpace_contains hU.1 hL.1) le_rfl

omit [Finite G] in
/-- Restricting to the centralizer of the full kernel preserves the
component, since relative subnormality restricts to intermediate subgroups. -/
theorem componentIn_kernelCentralizer (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) :
    ComponentIn (centralizer ((V ⊓ centralizer (L : Set G) : Subgroup G) : Set G)) L :=
  componentIn_intermediateCentralizer hL (fixedSpace_contains hU.1 hL.1) le_rfl

/-- The supplied one-dimensional action bound makes the actual kernel a
hyperplane. Its index is two, not merely bounded by three via a logarithm. -/
theorem kernel_relIndex (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hd : actionCorank V L ≤ 1) :
    (V ⊓ centralizer (L : Set G)).relIndex V = 2 := by
  let _ := h.elementary
  have he := (rank_one_of_action_bound h (component_not_le h earlier hU hL) hd).1
  rw [relIndex_eq_pow_corank]
  change 2 ^ actionCorank V L = 2
  rw [he, pow_one]

/-- The full source fixed space Z has order two when the component action
has dimension at most one. -/
theorem sylowFixed_card (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hd : actionCorank V L ≤ 1) :
    Nat.card (sylowFixedSpace (T : Subgroup G) V) = 2 := by
  let W := V ⊓ centralizer (L : Set G)
  let Z := sylowFixedSpace (T : Subgroup G) V
  have hi := kernel_relIndex h earlier hU hL hd
  have hdis := component_fixedSpace_disjoint_sylowFixed h earlier hU hL
  have hle : Nat.card Z ≤ 2 := by
    have hh := Subgroup.relIndex_le_of_le_right
      (show Z ≤ V from inf_le_left) (W.subgroupOf V).index_ne_zero_of_finite
    rw [← inf_relIndex_right W Z, hdis, relIndex_bot_left, hi] at hh
    exact hh
  have hne : Nat.card Z ≠ 1 := by
    intro hc
    obtain ⟨z, hz, hzne⟩ := exists_sylow_fixed h
    exact hzne (mem_bot.mp ((Z.eq_bot_iff_card.mpr hc) ▸ hz))
  have hp : 0 < Nat.card Z := Nat.card_pos
  change Nat.card Z = 2
  omega

/-- The fixed space of T complements the component kernel inside V.
This does not identify the given U with that kernel. -/
theorem kernel_directDecomposition (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hd : actionCorank V L ≤ 1) :
    DirectDecomposition V (V ⊓ centralizer (L : Set G))
      (sylowFixedSpace (T : Subgroup G) V) := by
  let _ := h.elementary
  let W := V ⊓ centralizer (L : Set G)
  let Z := sylowFixedSpace (T : Subgroup G) V
  have hdis : W ⊓ Z = ⊥ := component_fixedSpace_disjoint_sylowFixed h earlier hU hL
  obtain ⟨z, hz, hzne⟩ := exists_sylow_fixed h
  have hzW : z ∉ W := fun hw => hzne (mem_bot.mp (hdis ▸ (show z ∈ W ⊓ Z from ⟨hw, hz⟩)))
  have hi : (W.subgroupOf V).index = 2 := kernel_relIndex h earlier hU hL hd
  refine ⟨le_antisymm (sup_le inf_le_left inf_le_left) ?_, hdis, ?_⟩
  · intro v hv
    by_cases hvW : v ∈ W
    · exact mem_sup_left hvW
    · have hm : v * z ∈ W :=
        (Subgroup.mul_mem_iff_of_index_two hi (a := (⟨v, hv⟩ : V))
          (b := (⟨z, hz.1⟩ : V))).mpr (iff_of_false hvW hzW)
      have hh : (v * z) * z⁻¹ ∈ W ⊔ Z :=
        (W ⊔ Z).mul_mem (mem_sup_left hm) (mem_sup_right (Z.inv_mem hz))
      simpa only [mul_inv_cancel_right] using hh
  · apply commutator_eq_bot_iff_le_centralizer.mpr
    exact (show W ≤ V from inf_le_left).trans
      (V.le_centralizer.trans (Subgroup.centralizer_le (show Z ≤ V from inf_le_left)))

/-- Equality with the kernel is equivalent to a separate bound on V/U.
The given action bound controls V/kernel; the bound on V/U remains separate. -/
theorem eq_kernel_iff_corank_one (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hd : actionCorank V L ≤ 1) :
    U = V ⊓ centralizer (L : Set G) ↔ subgroupCorank V U = 1 := by
  let _ := h.elementary
  have hUW := fixedSpace_contains hU.1 hL.1
  have hi := kernel_relIndex h earlier hU hL hd
  constructor
  · intro he
    rw [he]
    exact (rank_one_of_action_bound h (component_not_le h earlier hU hL) hd).1
  · intro hc
    have hUi : U.relIndex V = 2 := by rw [relIndex_eq_pow_corank, hc, pow_one]
    have hm := relIndex_mul_relIndex U (V ⊓ centralizer (L : Set G)) V hUW inf_le_left
    rw [hi, hUi] at hm
    have h1 : U.relIndex (V ⊓ centralizer (L : Set G)) = 1 := by omega
    exact le_antisymm hUW (relIndex_eq_one.mp h1)

omit [Finite G] in
private theorem exists_hyperplane_between {W : Subgroup G}
    [IsElementaryAbelian 2 W] (hUW : U < W) :
    ∃ A : Subgroup G, U ≤ A ∧ A ≤ W ∧ A.relIndex W = 2 := by
  let P : Submodule (ZMod 2) (Additive W) :=
    AddSubgroup.toZModSubmodule 2 (U.subgroupOf W).toAddSubgroup
  have hP : P < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro he
    apply hUW.not_ge
    intro w hw
    have hh : Additive.ofMul (⟨w, hw⟩ : W) ∈ P := by rw [he]; trivial
    exact hh
  obtain ⟨f, hf, hPf⟩ := P.exists_le_ker_of_lt_top hP
  have hs : Function.Surjective f.toAddMonoidHom := by
    obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp hf
    have hv1 : f v = 1 := by
      have hb : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide +kernel
      exact (hb _).resolve_left (by simpa using hv)
    intro c
    have hb : c = 0 ∨ c = 1 := by revert c; decide +kernel
    rcases hb with rfl | rfl
    · exact ⟨0, map_zero _⟩
    · exact ⟨v, hv1⟩
  let B : Subgroup W := f.toAddMonoidHom.ker.toSubgroup
  refine ⟨B.map W.subtype, ?_, map_subtype_le _, ?_⟩
  · intro u hu
    have hb : (⟨u, hUW.le hu⟩ : W) ∈ B :=
      hPf (show Additive.ofMul (⟨u, hUW.le hu⟩ : W) ∈ P from hu)
    exact mem_map_of_mem W.subtype hb
  · rw [relIndex, subgroupOf, comap_map_eq, W.ker_subtype, sup_bot_eq]
    change f.toAddMonoidHom.ker.index = 2
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hs, AddSubgroup.card_top]
    exact Nat.card_zmod 2

/-- Any failure of the requested equality already occurs at an intermediate
obstruction of corank two, with the same actual component and action kernel.
The odd-model exclusion of this configuration is still required. -/
theorem exists_corank_two_obstruction_of_kernel_ne (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hd : actionCorank V L ≤ 1) (hne : U ≠ V ⊓ centralizer (L : Set G)) :
    ∃ A : Subgroup G, U ≤ A ∧ A < V ⊓ centralizer (L : Set G) ∧
      A ∈ obstructionFamily M V ∧ ComponentIn (centralizer (A : Set G)) L ∧
      subgroupCorank V A = 2 := by
  let _ := h.elementary
  let W := V ⊓ centralizer (L : Set G)
  let _ : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (show W ≤ V from inf_le_left)
  obtain ⟨A, hUA, hAW, hi⟩ := exists_hyperplane_between
    (show U < W from lt_of_le_of_ne (fixedSpace_contains hU.1 hL.1) hne)
  have hAWlt : A < W := by
    apply lt_of_le_of_ne hAW
    intro he
    rw [he, relIndex_self] at hi
    norm_num at hi
  refine ⟨A, hUA, hAWlt, intermediate_mem_obstruction h earlier hU hL hUA hAW,
    componentIn_intermediateCentralizer hL hUA hAW, ?_⟩
  have hm := relIndex_mul_relIndex A W V hAW inf_le_left
  rw [hi, kernel_relIndex h earlier hU hL hd] at hm
  change Nat.log 2 (A.relIndex V) = 2
  rw [← hm]
  decide

end CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve.OddActions.KernelGeometry

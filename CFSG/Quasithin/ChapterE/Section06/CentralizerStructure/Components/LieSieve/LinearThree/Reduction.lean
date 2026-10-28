module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve
public import Theory.GroupTheory.PResidual.PrimeToAction
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Residual and coprime-action reductions for the PSL₃ branches of E.6.8

The obstruction residual kills the actual action of L ∩ M on V, so that
image has odd order. Coprime action therefore splits V into the commutator
and C_V(L ∩ M), without assuming the Borel alternative. Once the model
calculation identifies this fixed subgroup with C_V(L), both the source
direct decomposition and its displacement dimension follow.

The normalizer of the marked Sylow subgroup is the preimage of the
normalizer in the central quotient whenever Z(L) is a two-group. This
constructs the Borel candidate; it does not place that candidate in M.
Borel containment, exclusion of a larger parabolic, and the cyclic action
and exact corank remain separate model obligations. The conditional
assembly below is not an assertion of either source PSL₃ branch.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248 (PDF pp.258–259), and Definition E.6.4, printed p.245.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.LinearThree
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G}

/-- The TI condition identifies the intersection with the actual normalizer
of V inside L. -/
theorem intersection_eq_normalizer
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) :
    L ⊓ M = L ⊓ normalizer (V : Set G) :=
  le_antisymm (le_inf inf_le_left (component_intersection_normalizes h hU hL.1))
    (inf_le_inf_left L h.normalizer_le)

/-- The residual centralization in Definition E.6.4 kills the actual
conjugation homomorphism from L ∩ M. -/
theorem residual_le_action_kernel
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) :
    primeToResidual 2 ↥(L ⊓ M) ≤
      (V.normalizerMonoidHom.comp
        (inclusion (component_intersection_normalizes h hU hL.1))).ker := by
  intro x hx
  have hc := (component_intersection_residual hU hL.1
    (mem_map_of_mem (L ⊓ M).subtype hx)).2
  change V.normalizerMonoidHom ⟨x, _⟩ = 1
  rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker]
  exact hc

/-- The marked Sylow normalizer is the full preimage of its quotient
Borel whenever the center is a two-group, including the trivial center. -/
theorem borelPreimage_sylow_normalizer (S : Sylow 2 L)
    (hz : IsPGroup 2 (center L)) :
    BorelPreimage L ((normalizer (S : Set L)).map L.subtype) := by
  let q := QuotientGroup.mk' (center L)
  let R := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  refine ⟨map_subtype_le _, R, ?_⟩
  rw [← comap_subtype, comap_map_eq_self_of_injective L.subtype_injective]
  change normalizer (S : Set L) =
    (normalizer ((S : Subgroup L).map q : Set (L ⧸ center L))).comap q
  rw [comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective _)]
  rw [comap_map_eq_self (show q.ker ≤ (S : Subgroup L) by
    simpa only [q, QuotientGroup.ker_mk'] using hz.le_sylow_of_normal S)]
  rfl


/-- The candidate Borel is marked by the actual Sylow subgroup of L. -/
@[expose] def markedBorel (L : Subgroup G) (S : Sylow 2 L) : Subgroup G :=
  (normalizer (S : Set L)).map L.subtype

/-- No model or ambient placement is needed for this quotient-preimage identity. -/
theorem markedBorel_is_preimage (S : Sylow 2 L) (hz : IsPGroup 2 (center L)) :
    BorelPreimage L (markedBorel L S) := borelPreimage_sylow_normalizer S hz

omit [Finite G] in
private theorem action_card (V B : Subgroup G) (hB : B ≤ normalizer (V : Set G)) :
    Nat.card (inducedAutomizer V B) =
      Nat.card (V.normalizerMonoidHom.comp (inclusion hB)).range := by
  rw [inducedAutomizer, ← relIndex_ker, MonoidHom.ker_rangeRestrict,
    normalizerMonoidHom_ker, relIndex_subgroupOf hB, ← index_ker,
    ← MonoidHom.comap_ker, normalizerMonoidHom_ker]
  rfl

/-- The residual condition makes the actual induced action odd, before any
Borel placement or cyclicity calculation. -/
theorem intersection_action_odd
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) :
    Odd (Nat.card (inducedAutomizer V (L ⊓ M))) := by
  rw [action_card V (L ⊓ M) (component_intersection_normalizes h hU hL.1)]
  exact Nat.coprime_two_left.mp
    (coprime_card_range_of_primeToResidual_le_ker 2 _ (residual_le_action_kernel h hU hL))

/-- Coprime splitting follows already from the obstruction condition. Its
fixed factor is C_V(L ∩ M); identifying it with C_V(L) is still required. -/
theorem intersection_decomposition
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) :
    DirectDecomposition V ⁅V, L ⊓ M⁆ (V ⊓ centralizer ((L ⊓ M : Subgroup G) : Set G)) := by
  let _ := h.elementary
  have hn := component_intersection_normalizes h hU hL.1
  let f := V.normalizerMonoidHom.comp (inclusion hn)
  have hc : Nat.Coprime 2 (Nat.card f.range) :=
    coprime_card_range_of_primeToResidual_le_ker 2 f (residual_le_action_kernel h hU hL)
  obtain ⟨d, hd⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
  have hcop : Nat.Coprime (Nat.card f.range) (Nat.card V) := by
    rw [hd]
    exact hc.symm.pow_right d
  obtain ⟨hgen, hdis⟩ := commutator_centralizer_decomposition_of_coprime_image V (L ⊓ M) hn hcop
  refine ⟨hgen, hdis, commutator_eq_bot_iff_le_centralizer.mpr ?_⟩
  have hWV : ⁅V, L ⊓ M⁆ ≤ V := le_normalizer_iff_commutator_le_left.mp hn
  exact hWV.trans (V.le_centralizer.trans (centralizer_le inf_le_left))

/-- Once the model identifies the two fixed subgroups, the source direct
product follows from the residual condition alone. -/
theorem decomposition_of_fixedSpace_eq
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hfixed : V ⊓ centralizer ((L ⊓ M : Subgroup G) : Set G) =
      V ⊓ centralizer (L : Set G)) :
    DirectDecomposition V ⁅V, L ⊓ M⁆ (V ⊓ centralizer (L : Set G)) := by
  simpa only [hfixed] using intersection_decomposition h hU hL

/-- The order of the moving direct factor is the index of the fixed factor.
Taking binary logarithms gives the displacement dimension. -/
theorem displacement_corank_of_decomposition
    (hd : DirectDecomposition V ⁅V, L ⊓ M⁆ (V ⊓ centralizer (L : Set G))) :
    subgroupCorank ⁅V, L ⊓ M⁆ ⊥ = actionCorank V L := by
  let C := V ⊓ centralizer (L : Set G)
  let W := ⁅V, L ⊓ M⁆
  have hnorm : W ≤ normalizer (C : Set G) :=
    (commutator_eq_bot_iff_le_centralizer.mp hd.2.2).trans (Subgroup.centralizer_le_normalizer _)
  have hdis : Disjoint C W := disjoint_iff.mpr (inf_comm W C ▸ hd.2.1)
  have hcard : Nat.card V = Nat.card C * Nat.card W := by
    calc
      Nat.card V = Nat.card (C ⊔ W : Subgroup G) := by
        rw [sup_comm]
        exact congrArg (fun A : Subgroup G => Nat.card A) hd.1.symm
      _ = _ := card_sup_eq_mul_of_normalizes_of_disjoint C W hnorm hdis
  have hi := relIndex_mul_relIndex (⊥ : Subgroup G) C V bot_le inf_le_left
  simp only [relIndex_bot_left] at hi
  rw [hcard] at hi
  have he : C.relIndex V = Nat.card W := Nat.eq_of_mul_eq_mul_left Nat.card_pos hi
  change Nat.log 2 ((⊥ : Subgroup G).relIndex W) = Nat.log 2 (C.relIndex V)
  rw [relIndex_bot_left, he]

/-- Conditional assembly for a marked Borel calculation. The Borel placement,
cyclic induced action, exact action corank and fixed-space comparison are
explicit unproved inputs here. This is not the source PSL₃ theorem. -/
theorem borelAlternative_of_calculations
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    {n : ℕ} (model : BorelComponentModel L n)
    (S : Sylow 2 L) (hz : IsPGroup 2 (center L))
    (hplace : L ⊓ M = markedBorel L S)
    (haction : Nonempty (inducedAutomizer V (L ⊓ M) ≃* Multiplicative (ZMod (2 ^ n - 1))))
    (hdimension : n = actionCorank V L)
    (hfixed : 1 < n → V ⊓ centralizer ((L ⊓ M : Subgroup G) : Set G) =
      V ⊓ centralizer (L : Set G)) :
    BorelAlternative M V U L n := by
  have hd (hn : 1 < n) := decomposition_of_fixedSpace_eq h hU hL (hfixed hn)
  refine ⟨model, ?_, haction, hdimension, ?_, hd, ?_⟩
  · rw [hplace]
    exact markedBorel_is_preimage S hz
  · rw [hdimension]
    exact fixedSpace_corank_le hU.1 hL.1
  · intro hn
    exact (displacement_corank_of_decomposition (hd hn)).trans hdimension.symm

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.LinearThree

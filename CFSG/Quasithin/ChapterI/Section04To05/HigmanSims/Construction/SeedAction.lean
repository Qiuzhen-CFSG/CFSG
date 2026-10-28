module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.LocalCores
public import Theory.GroupTheory.PGroup.HomocyclicOmegaFrattini
public import Theory.GroupTheory.PGroup.OmegaCoprimeAction
public import Theory.ElementaryAbelian.AutomorphismCardEight

/-!
# The actual seed action in type HS

The elementary eight V is the first omega subgroup of O₂(N_G(V)): the
homocyclic model gives its order, and the source containment identifies it.
Restriction to omega of an abelian two-group has two-group kernel. Together
with the self-centralizing core this proves C_G(V) = O₂(N_G(V)), with the
right-hand subgroup mapped into G. The order 168 of the quotient then shows
that the literal normalizer action induces every automorphism of V.

These results use HS1--HS2 without ambient simplicity, group order, or a
permutation realization. They supply the local fusion input for the
construction of the L₃(4) and M₂₂ subgroups; they do not assert that construction.

Source: Aschbacher--Smith, type HS and I.4.8, printed p.418; the elementary
normalizer-action step in the local-recognition route cited there.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

private noncomputable def coreCoordinates (h : TypeAt z V) :
    pCore 2 (normalizer (V : Set G)) ≃* StandardHomocyclicCover (Fin 3) (2^2) :=
  (MulEquiv.subgroupCongr h.normalizer_fitting.symm).trans
    (h.normalizer_core.some.trans (MulEquiv.funMultiplicative (Fin 3) (ZMod 4)).symm)

private theorem core_comm (h : TypeAt z V) :
    IsMulCommutative (pCore 2 (normalizer (V : Set G))) := by
  let e := coreCoordinates h
  exact ⟨⟨fun x y => e.injective (by simp only [map_mul, mul_comm])⟩⟩

private theorem omega_core_card (h : TypeAt z V) :
    Nat.card (omega (pCore 2 (normalizer (V : Set G))) (p := 2) 1) = 8 := by
  let e := coreCoordinates h
  let eQ := (QuotientGroup.congr _ _ e (frattini_map_equiv e)).trans
    (standardHomocyclicCoverFrattiniQuotientEquiv (Fin 3) 2 2 (by decide))
  have hc := Nat.card_congr ((HomocyclicOmegaFrattini.equiv (by decide : 1 ≤ 2) e).symm.trans eQ).toEquiv
  simpa [StandardHomocyclicCover, Nat.card_eq_fintype_card] using hc

/-- Inside the actual normalizer, the seed is precisely omega of its two-core. -/
theorem TypeAt.seed_eq_omega_normalizer_core (h : TypeAt z V) :
    V.subgroupOf (normalizer (V : Set G)) =
      (omega (pCore 2 (normalizer (V : Set G))) (p := 2) 1).map
        (pCore 2 (normalizer (V : Set G))).subtype := by
  let := h.elementary
  have hc : Nat.card (V.subgroupOf (normalizer (V : Set G))) = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe V.le_normalizer).toEquiv).trans h.seed_card
  apply eq_of_le_of_card_ge ?_ ?_
  · intro v hv
    have hq : v ∈ pCore 2 (normalizer (V : Set G)) := by
      have hh := h.seed_le_normalizer_core hv
      obtain ⟨q, hq, he⟩ := hh
      have heq : q = v := Subtype.ext he
      rw [← h.normalizer_fitting, ← heq]
      exact hq
    refine ⟨⟨v, hq⟩, subset_closure ?_, rfl⟩
    change (⟨v, hq⟩ : pCore 2 (normalizer (V : Set G))) ^ (2^1) = 1
    apply Subtype.ext
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (v : G) hv
  · rw [card_map_of_injective (pCore 2 (normalizer (V : Set G))).subtype_injective,
      omega_core_card h, hc]

/-- The ambient centralizer of the seed is the embedded normalizer two-core. -/
theorem TypeAt.seed_centralizer (h : TypeAt z V) :
    centralizer (V : Set G) = (pCore 2 (normalizer (V : Set G))).map
      (normalizer (V : Set G)).subtype := by
  let M := normalizer (V : Set G)
  let Q := pCore 2 M
  let := core_comm h
  have hd := OmegaAction.centralizer_omegaOne_pCore_le
    h.normalizer_twoCore_selfCentralizing
  rw [← h.seed_eq_omega_normalizer_core] at hd
  apply le_antisymm
  · intro x hx
    have hn : x ∈ M := centralizer_le_normalizer (V : Set G) hx
    refine ⟨⟨x, hn⟩, hd ?_, rfl⟩
    intro v hv
    exact Subtype.ext (hx (v : G) hv)
  · rintro x ⟨q, hq, rfl⟩ v hv
    have hvQ : (⟨v, V.le_normalizer hv⟩ : M) ∈ Q := by
      have hh := h.seed_le_normalizer_core hv
      obtain ⟨w, hw, he⟩ := hh
      have heq : w = ⟨v, V.le_normalizer hv⟩ := Subtype.ext he
      change (⟨v, V.le_normalizer hv⟩ : normalizer (V : Set G)) ∈ pCore 2 (normalizer (V : Set G))
      rw [← h.normalizer_fitting, ← heq]
      exact hw
    exact congrArg (fun x : Q => (x.val : G)) (mul_comm ⟨_, hvQ⟩ ⟨q, hq⟩)

/-- Every automorphism of the elementary eight comes from its actual normalizer. -/
theorem TypeAt.seed_action_surjective (h : TypeAt z V) :
    Function.Surjective V.normalizerMonoidHom := by
  let := h.elementary
  apply MonoidHom.surjective_of_card_ker_le_div
  rw [normalizerMonoidHom_ker, h.seed_centralizer,
    show ((pCore 2 (normalizer (V : Set G))).map (normalizer (V : Set G)).subtype).subgroupOf (normalizer (V : Set G)) = pCore 2 (normalizer (V : Set G)) from
      comap_map_eq_self_of_injective (normalizer (V : Set G)).subtype_injective _,
    card_mulAut_of_elementary_eight V h.seed_card,
    h.normalizer_card, ← h.normalizer_fitting, h.normalizer_core_card]
end CFSG.Quasithin.HigmanSims

module

public import Theory.PGroupCore
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Sylow

/-!
# Transporting the original elementary two-core bound

A faithful homomorphism identifies an original centralizer preimage
with the actual image restricted to the target centralizer. The explicit
isomorphism transports the original two-core, Sylow normality and
elementary cardinal bound, retaining the literal subgroup maps.
Source application: Aschbacher–Smith E.2.7, printed pp.218–219.
-/

public section
open Subgroup
namespace Theory.GroupTheory
/-- The literal elementary two-core/Sylow-normal bound transports along an actual group isomorphism. -/
theorem elementary_core_bound_of_equiv
    {G X : Type*} [Group G] [Group X] [Finite G] (e : G ≃* X)
    (hb : ∀ T : Sylow 2 X, ∀ V : Subgroup X, V ≤ pCore 2 X →
      (T : Subgroup X) ≤ normalizer (V : Set X) → (∀ v ∈ V, v ^ 2 = 1) → Nat.card V ≤ 2)
    (T : Sylow 2 G) (V : Subgroup G) (hV : V ≤ pCore 2 G)
    (hVN : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hpow : ∀ v ∈ V, v ^ 2 = 1) : Nat.card V ≤ 2 := by
  let T' := T.mapSurjective (f := e.toMonoidHom) e.surjective
  let V' := V.map e.toMonoidHom
  have hV' : V' ≤ pCore 2 X := by
    rw [← pCore_map_iso 2 e]
    exact map_mono hV
  have hVN' : (T' : Subgroup X) ≤ normalizer (V' : Set X) := by
    rw [← map_normalizer_eq_of_bijective V e.bijective]
    change (T : Subgroup G).map e.toMonoidHom ≤ _
    exact map_mono hVN
  have hh := hb T' V' hV' hVN' (by
    rintro _ ⟨v, hv, rfl⟩
    rw [← map_pow, hpow v hv, map_one])
  rwa [card_map_of_injective e.injective] at hh
end Theory.GroupTheory

open Subgroup
namespace Theory.GroupTheory
 theorem elementary_core_bound_of_faithful_centralizer
    {H G : Type*} [Group H] [Group G] [Finite H]
    (f : H →* G) (hf : Function.Injective f)
    (M : Subgroup H) (C : Subgroup G) (hM : C.comap f = M)
    (hb : ∀ T : Sylow 2 (f.range.subgroupOf C), ∀ V : Subgroup (f.range.subgroupOf C),
      V ≤ pCore 2 (f.range.subgroupOf C) →
      (T : Subgroup (f.range.subgroupOf C)) ≤ normalizer (V : Set (f.range.subgroupOf C)) →
      (∀ v ∈ V, v ^ 2 = 1) → Nat.card V ≤ 2)
    (T : Sylow 2 H) (hTM : (T : Subgroup H) ≤ M)
    (V : Subgroup H) (hV : IsElementaryAbelian 2 V)
    (hVM : V ≤ (pCore 2 M).map M.subtype)
    (hVN : (T : Subgroup H) ≤ normalizer (V : Set H)) : Nat.card V ≤ 2 := by
  let B := f.range.subgroupOf C
  let q : M →* B := {
    toFun m := ⟨⟨f m, show m.val ∈ C.comap f by rw [hM]; exact m.property⟩, ⟨m, rfl⟩⟩
    map_one' := by apply Subtype.ext; apply Subtype.ext; exact map_one f
    map_mul' a b := by apply Subtype.ext; apply Subtype.ext; exact map_mul f (a : H) (b : H) }
  have hq : Function.Bijective q := by
    constructor
    · intro a b he
      exact Subtype.ext (hf (congrArg (fun x : B => x.val.val) he))
    · intro b
      obtain ⟨a, ha⟩ := b.property
      have ham : a ∈ M := by
        rw [← hM]
        change f a ∈ C
        rw [ha]
        exact b.val.property
      exact ⟨⟨a, ham⟩, Subtype.ext (Subtype.ext ha)⟩
  let e : M ≃* B := MulEquiv.ofBijective q hq
  let T₀ := T.subtype hTM
  let V₀ := V.subgroupOf M
  have hVMle : V ≤ M := hVM.trans (map_subtype_le _)
  have hV₀ : V₀ ≤ pCore 2 M := by
    intro v hv
    obtain ⟨w, hw, he⟩ := hVM hv
    exact (Subtype.ext he : w = v) ▸ hw
  have hVN₀ : (T₀ : Subgroup M) ≤ normalizer (V₀ : Set M) := by
    rw [← subgroupOf_normalizer_eq hVMle]
    intro a ha
    exact hVN ha
  have hpow : ∀ v ∈ V₀, v ^ 2 = 1 := by
    let := hV
    intro v hv
    exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian v.val hv)
  have hh := elementary_core_bound_of_equiv e hb T₀ V₀ hV₀ hVN₀ hpow
  rwa [Nat.card_congr (subgroupOfEquivOfLe hVMle).toEquiv] at hh
end Theory.GroupTheory

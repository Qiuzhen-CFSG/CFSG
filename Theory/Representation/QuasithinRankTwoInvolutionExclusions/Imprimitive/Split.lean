module

public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Basic
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Displacement ranks on two summands

A swapping involution on `V × W` has displacement space isomorphic to `V`.
Its displacement is the graph of the negative of the isomorphism from `V` to
`W`. A block diagonal operator has the sum of the two displacement ranks.
Commutation with the swap identifies the two block actions, so their ranks
agree. In equal coordinates it forces the two operators themselves to agree.

These are the linear algebra steps for Aschbacher–Smith, *The Classification
of Quasithin Groups*, G.11.2(8),(12), printed p.364 (PDF p.375), and the
exclusions in 6.2.19, printed p.691 (PDF p.708). They do not supply the
four-dimensional component representations or identify a source group with a
concrete model.
-/

@[expose] public section

namespace Representation.RankTwo.Imprimitive
variable {k V W : Type*} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

def swap (e : V ≃ₗ[k] W) : Module.End k (V × W) :=
  (e.symm.toLinearMap.comp (LinearMap.snd k V W)).prod
    (e.toLinearMap.comp (LinearMap.fst k V W))

@[simp] lemma swap_apply (e : V ≃ₗ[k] W) (z : V × W) :
    swap e z = (e.symm z.2, e z.1) := rfl

def swapRangeEquiv (e : V ≃ₗ[k] W) :
    V ≃ₗ[k] LinearMap.range (swap e - 1) where
  toFun v := ⟨(v, - e v), ⟨(0, e v), by simp [swap]⟩⟩
  invFun z := z.val.1
  left_inv v := rfl
  right_inv z := by
    apply Subtype.ext
    rcases z with ⟨z, ⟨⟨v,w⟩, rfl⟩⟩
    change (e.symm w - v, -e (e.symm w - v)) = (e.symm w - v, e v - w)
    rw [map_sub, e.apply_symm_apply, neg_sub]
  map_add' v w := by
    apply Subtype.ext
    change (v + w, -e (v + w)) = (v + w, -e v + -e w)
    rw [map_add, neg_add]
  map_smul' c v := by apply Subtype.ext; simp

lemma finrank_swap (e : V ≃ₗ[k] W) :
    Module.finrank k (LinearMap.range (swap e - 1)) = Module.finrank k V :=
  (swapRangeEquiv e).finrank_eq.symm

lemma intertwine_of_commute_swap (e : V ≃ₗ[k] W)
    (a : Module.End k V) (b : Module.End k W)
    (h : Commute (a.prodMap b) (swap e)) :
    ∀ v, b (e v) = e (a v) := by
  intro v
  have he := congrArg (fun f : Module.End k (V × W) => (f (v, 0)).2) h.eq
  exact he

noncomputable def blockRangeEquiv (a : Module.End k V) (b : Module.End k W) :
    LinearMap.range (a.prodMap b - 1) ≃ₗ[k]
      (LinearMap.range (a - 1) × LinearMap.range (b - 1)) where
  toFun z := ⟨⟨z.val.1, by
    obtain ⟨v, hv⟩ := z.property
    exact ⟨v.1, congrArg Prod.fst hv⟩⟩,
    ⟨z.val.2, by
    obtain ⟨v, hv⟩ := z.property
    exact ⟨v.2, congrArg Prod.snd hv⟩⟩⟩
  invFun z := ⟨(z.1.val,z.2.val), by
    obtain ⟨v, hv⟩ := z.1.property
    obtain ⟨w, hw⟩ := z.2.property
    exact ⟨(v,w), Prod.ext hv hw⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma finrank_block [FiniteDimensional k V] [FiniteDimensional k W]
    (a : Module.End k V) (b : Module.End k W) :
    Module.finrank k (LinearMap.range (a.prodMap b - 1)) =
      Module.finrank k (LinearMap.range (a - 1)) +
      Module.finrank k (LinearMap.range (b - 1)) := by
  rw [(blockRangeEquiv a b).finrank_eq, Module.finrank_prod]

/-- A swapping involution has half the dimension as its displacement rank. -/
lemma finrank_of_exchanges
    (t : Module.End k (V × W)) (a : V →ₗ[k] W) (b : W →ₗ[k] V)
    (ht : ∀ v w, t (v,w) = (b w, a v)) (ht2 : t * t = 1) :
    Module.finrank k (LinearMap.range (t - 1)) = Module.finrank k V := by
  let e : V ≃ₗ[k] W :=
    { toFun := fun v => a v
      map_add' := a.map_add
      map_smul' := a.map_smul
      invFun := b
      left_inv := by
        intro v
        have h := congrArg (fun f : Module.End k (V × W) => (f (v,0)).1) ht2
        simpa only [Module.End.mul_apply, ht, Module.End.one_apply] using h
      right_inv := by
        intro w
        have h := congrArg (fun f : Module.End k (V × W) => (f (0,w)).2) ht2
        simpa only [Module.End.mul_apply, ht, Module.End.one_apply] using h }
  have he : t = swap e := by
    apply LinearMap.ext
    rintro ⟨v,w⟩
    exact ht v w
  rw [he]
  exact finrank_swap e

/-- An intertwiner identifies displacement spaces, without a group-level model. -/
def displacementRangeEquiv (e : V ≃ₗ[k] W)
    (a : Module.End k V) (b : Module.End k W)
    (h : ∀ v, b (e v) = e (a v)) :
    LinearMap.range (a - 1) ≃ₗ[k] LinearMap.range (b - 1) where
  toFun z := ⟨e z.val, by
    obtain ⟨v, hv⟩ := z.property
    refine ⟨e v, ?_⟩
    change b (e v) - e v = e z.val
    rw [h, ← map_sub]
    exact congrArg e hv⟩
  invFun z := ⟨e.symm z.val, by
    obtain ⟨w, hw⟩ := z.property
    refine ⟨e.symm w, e.injective ?_⟩
    change e (a (e.symm w) - e.symm w) = e (e.symm z.val)
    rw [map_sub, ← h, e.apply_symm_apply, e.apply_symm_apply]
    exact hw⟩
  left_inv z := Subtype.ext (e.symm_apply_apply z.val)
  right_inv z := Subtype.ext (e.apply_symm_apply z.val)
  map_add' z w := Subtype.ext (e.map_add z.val w.val)
  map_smul' c z := Subtype.ext (e.map_smul c z.val)

/-- Commutation with the swapping element forces equal block ranks. -/
lemma finrank_commuting_block [FiniteDimensional k V] [FiniteDimensional k W]
    (e : V ≃ₗ[k] W) (a : Module.End k V) (b : Module.End k W)
    (h : Commute (a.prodMap b) (swap e)) :
    Module.finrank k (LinearMap.range (a.prodMap b - 1)) =
      2 * Module.finrank k (LinearMap.range (a - 1)) := by
  have hr := (displacementRangeEquiv e a b (intertwine_of_commute_swap e a b h)).finrank_eq
  rw [finrank_block, ← hr]
  omega

/-- For equal coordinate spaces, commutation with plain swapping means diagonal action. -/
lemma eq_of_commute_swap (a b : Module.End k V)
    (h : Commute (a.prodMap b) (swap (LinearEquiv.refl k V))) : a = b := by
  ext v
  exact (intertwine_of_commute_swap (LinearEquiv.refl k V) a b h v).symm

end Representation.RankTwo.Imprimitive

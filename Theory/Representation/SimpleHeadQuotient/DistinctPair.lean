module
public import Theory.Representation.SimpleHeadQuotient.Independent

/-!
# Invariant subspaces of two distinct simple modules

The only submodules of a sum of two inequivalent simple representations are
zero, the two coordinate summands, and the full sum. Each coordinate projection
is zero or onto; when both are onto, independence of simple quotients makes
the pair onto. The natural–dual fixed-generation argument in Aschbacher–Smith
10.2.9, printed p.751, consumes this elementary module fact.
-/

public section
open Representation
namespace Representation.SimpleHeadQuotient
variable {k G V W : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  (σ : Representation k G V) (τ : Representation k G W)

theorem distinct_pair_submodules [IsIrreducible σ] [IsIrreducible τ]
    (hne : ¬ Nonempty (σ.Equiv τ)) (K : Submodule k (V × W))
    (hK : ∀ g x, x ∈ K → (σ.prod τ) g x ∈ K) :
    K = ⊥ ∨ K = (⊤ : Submodule k V).prod ⊥ ∨
      K = (⊥ : Submodule k V).prod ⊤ ∨ K = ⊤ := by
  let S : Subrepresentation (σ.prod τ) := ⟨K, fun g _ hx => hK g _ hx⟩
  let f : S.toRepresentation.IntertwiningMap σ :=
    (LinearMap.fst k V W ∘ₗ K.subtype).intertwiningMap_of_isIntertwiningMap
      _ _ (fun _ _ => rfl)
  let g : S.toRepresentation.IntertwiningMap τ :=
    (LinearMap.snd k V W ∘ₗ K.subtype).intertwiningMap_of_isIntertwiningMap
      _ _ (fun _ _ => rfl)
  rcases IsIrreducible.surjective_or_eq_zero f with hf | hf <;>
    rcases IsIrreducible.surjective_or_eq_zero g with hg | hg
  · right; right; right
    apply top_unique
    intro x _
    obtain ⟨y,hy⟩ := surjective_prod_of_inequivalent_simple_quotients f g hf hg hne x
    change (y : V × W) = x at hy
    exact hy ▸ y.property
  · right; left
    apply le_antisymm
    · intro x hx
      exact ⟨Submodule.mem_top, show x.2 = 0 from congrArg (fun h => h ⟨x,hx⟩) hg⟩
    · rintro ⟨v,w⟩ ⟨_,hw⟩
      obtain ⟨y,hy⟩ := hf v
      have hz : (y : V × W).2 = 0 := congrArg (fun h => h y) hg
      have he : (y : V × W) = (v,w) := Prod.ext hy (hz.trans hw.symm)
      exact he ▸ y.property
  · right; right; left
    apply le_antisymm
    · intro x hx
      exact ⟨show x.1 = 0 from congrArg (fun h => h ⟨x,hx⟩) hf, Submodule.mem_top⟩
    · rintro ⟨v,w⟩ ⟨hv,_⟩
      obtain ⟨y,hy⟩ := hg w
      have hz : (y : V × W).1 = 0 := congrArg (fun h => h y) hf
      have he : (y : V × W) = (v,w) := Prod.ext (hz.trans hv.symm) hy
      exact he ▸ y.property
  · left
    apply bot_unique
    intro x hx
    exact Prod.ext (congrArg (fun h => h ⟨x,hx⟩) hf)
      (congrArg (fun h => h ⟨x,hx⟩) hg)
end Representation.SimpleHeadQuotient

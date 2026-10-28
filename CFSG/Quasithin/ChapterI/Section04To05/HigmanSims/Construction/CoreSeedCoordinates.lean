module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CoreMatrixAction

/-!
# Compatible binary and cyclic-four coordinates on the original HS seed

Doubling each binary coordinate embeds the binary cube in C₄³. Transport
through any coordinates on the whole normalizer core gives exactly the
original seed: all images have square one, and both groups have order eight.
This chooses the dual-plane generators inside the original group while
keeping the matrix action and its binary restriction in the same basis.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims

/-- The additive inclusion of a binary scalar as the two-torsion of Z/4. -/
@[expose] def binaryDouble : ZMod 2 →+ ZMod 4 where
  toFun x := 2 * (x.val : ZMod 4)
  map_zero' := by decide
  map_add' := by decide +kernel

private theorem binaryDouble_injective : Function.Injective binaryDouble := by decide +kernel

private def doubleCube : Multiplicative (Fin 3 → ZMod 2) →*
    Multiplicative (Fin 3 → ZMod 4) where
  toFun v := Multiplicative.ofAdd (fun i => binaryDouble (v.toAdd i))
  map_one' := by ext i; exact binaryDouble.map_zero
  map_mul' a b := by ext i; exact binaryDouble.map_add _ _

private theorem doubleCube_injective : Function.Injective doubleCube := by
  intro a b he
  apply Multiplicative.toAdd.injective
  funext i
  exact binaryDouble_injective (congrArg (fun v => v.toAdd i) he)

variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

private def coreSeedMap (h : TypeAt z V)
    (e : pCore 2 (normalizer (V : Set G)) ≃* Multiplicative (Fin 3 → ZMod 4)) :
    Multiplicative (Fin 3 → ZMod 2) →* V := by
  let M := normalizer (V : Set G)
  let P := pCore 2 M
  let f := M.subtype.comp (P.subtype.comp (e.symm.toMonoidHom.comp doubleCube))
  refine f.codRestrict V ?_
  intro v
  let q : P := e.symm (doubleCube v)
  have hq : q ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, map_one, e.apply_symm_apply]
    have hv : (doubleCube v) ^ 2 = 1 := by
      rw [pow_two]
      ext i
      change binaryDouble (v.toAdd i) + binaryDouble (v.toAdd i) = 0
      exact (by decide +kernel : ∀ x : ZMod 2, binaryDouble x + binaryDouble x = 0) (v.toAdd i)
    exact hv
  have hw : (q : M) ∈ (omega P (p := 2) 1).map P.subtype :=
    ⟨q, subset_closure (show q ^ (2^1) = 1 from hq), rfl⟩
  rw [← h.seed_eq_omega_normalizer_core] at hw
  exact hw

/-- Coordinates on the actual seed induced by coordinates on its full
normalizer core, with no independent choice of binary basis. -/
def TypeAt.seedCoordinates (h : TypeAt z V)
    (e : pCore 2 (normalizer (V : Set G)) ≃* Multiplicative (Fin 3 → ZMod 4)) :
    V ≃* Multiplicative (Fin 3 → ZMod 2) := by
  let f := coreSeedMap h e
  have hf : Function.Injective f := by
    intro a b he
    apply doubleCube_injective
    apply e.symm.injective
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun v : V => (v : G)) he
  have hc : Nat.card (Multiplicative (Fin 3 → ZMod 2)) = Nat.card V := by
    rw [h.seed_card]
    simp [Nat.card_eq_fintype_card]
  exact (MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf, hc⟩)).symm

/-- The inverse binary coordinate map is literally the doubled cube inside
the original intrinsic normalizer core. -/
theorem TypeAt.seedCoordinates_symm_apply (h : TypeAt z V)
    (e : pCore 2 (normalizer (V : Set G)) ≃* Multiplicative (Fin 3 → ZMod 4))
    (v : Multiplicative (Fin 3 → ZMod 2)) :
    ((h.seedCoordinates e).symm v : G) =
      ((e.symm (Multiplicative.ofAdd (fun i => binaryDouble (v.toAdd i))) :
        pCore 2 (normalizer (V : Set G))) : normalizer (V : Set G)) := by rfl

end CFSG.Quasithin.HigmanSims

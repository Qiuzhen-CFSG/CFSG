module

public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic.Geometry
public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic.Quotient
public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic.Perfectness

/-!
# The long local subgroup of the split G₂ model

The long-Weyl local group in characteristic two is the first-vector stabilizer.
It is normal in the singular-point parabolic, which is its literal product with
the Borel. Its action on the distinguished plane modulo the first-vector line
has image SL₂ and kernel the five-root subgroup omitting root E. Since SL₂ has
trivial two-core, this kernel is exactly the local two-core, of order q⁵; the
quotient is PSL₂. Over F₂ the local core has order 32 inside full G₂(2).

The common Sylow subgroup lies in the local group, so the source's `L₂ S` is
literally `L₂`. The equalities below also express its core and order in this
source convention. For q > 2, local torus and root commutators prove perfectness
and equality with the solvable residual. The concrete quotient map and its
coefficientwise field compatibility are re-exported from `Quotient`.

This establishes the long-local clauses; the other local group and the full
amalgam identification belong to their respective source assembly modules.

Source: Aschbacher--Smith, F.1.12(I)(3) and (II), printed pp. 262--264.
-/

public section

open scoped Pointwise

namespace Atlas.G2.LieParabolicSetup

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The marked ambient Sylow subgroup is contained in the long local group. -/
theorem sylow_le_local₂ : (sylow (F := F) : Subgroup (Model F)) ≤ local₂ :=
  unipotent_le_local₂

/-- Adjoining the common Sylow subgroup leaves the long local group unchanged. -/
theorem local₂_sup_sylow :
    local₂ (F := F) ⊔ (sylow (F := F) : Subgroup (Model F)) = local₂ :=
  sup_eq_left.mpr sylow_le_local₂

/-- The product `L₂ S` in F.1.12 is the literal set product. -/
theorem local₂_mul_sylow :
    (local₂ (F := F) : Set (Model F)) *
      ((sylow (F := F) : Subgroup (Model F)) : Set (Model F)) =
        (local₂ (F := F) : Set (Model F)) := by
  ext g
  constructor
  · rintro ⟨l, hl, s, hs, rfl⟩
    exact local₂.mul_mem hl (sylow_le_local₂ hs)
  · intro hg
    exact ⟨g, hg, 1, (sylow (F := F)).one_mem, mul_one g⟩

/-- The source's `O₂(L₂ S)`, embedded in the full G₂ model. -/
theorem local₂_sylow_pCoreIn :
    (local₂ (F := F) ⊔ (sylow (F := F) : Subgroup (Model F))).pCoreIn 2 = radical₂ := by
  rw [local₂_sup_sylow, local₂_pCoreIn]

/-- The order assertion in F.1.12(I)(3), with the marked Sylow adjoined. -/
theorem card_local₂_sylow_pCore :
    Nat.card (pCore 2
      (local₂ ⊔ (sylow (F := F) : Subgroup (Model F)) : Subgroup (Model F))) =
        Nat.card F ^ 5 := by
  rw [local₂_sup_sylow, card_local₂_pCore]

/-- In the full binary model the source's second core has order 32. -/
theorem card_local₂_sylow_pCore_binary :
    Nat.card (pCore 2 (local₂ ⊔ (sylow (F := ZMod 2) : Subgroup (Model (ZMod 2))) :
      Subgroup (Model (ZMod 2)))) = 32 := by
  rw [local₂_sup_sylow]
  exact card_local₂_pCore_binary

end Atlas.G2.LieParabolicSetup

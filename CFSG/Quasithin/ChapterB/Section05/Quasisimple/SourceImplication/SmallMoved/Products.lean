module

public import Theory.Representation.BinaryOffender.SmallMovedProducts
public import Theory.Representation.GeneralLinearNatural
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Geometry

/-!
# Small moved spaces exclude the reducible B.5.1 models

An actual offender on the original module remains an offender on an invariant
submodule. The two faithful natural summands in the doubled and natural-dual
models therefore contradict the plane bound. For a repeated natural module,
two coordinate summands give the same obstruction, forcing multiplicity one.
All embeddings and subgroup maps retain the original action.

Source: Aschbacher–Smith 13.7.15(1–2), printed pp.943–944, applying B.5.1(1).
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SmallMoved
variable {G D V W : Type*} [Group G] [Group D]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) D W)

/-- The matrix representation remains faithful after restriction of scalars. -/
theorem linearNatural_faithful (F : BinaryField) (n : ℕ) :
    Function.Injective (linearNatural F n) := by
  intro a b hab
  apply specialLinearNatural_injective n
  apply LinearMap.ext
  intro v
  exact LinearMap.congr_fun hab v

set_option backward.isDefEq.respectTransparency false in
/-- A source model on an invariant section supplies an actual embedding into V. -/
theorem not_product_section [Finite D]
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]
    (τ : Representation (ZMod 2) D X)
    (hf : Function.Injective σ) (hg : Function.Injective τ)
    (U : Subrepresentation ρ) (e : ActionEquiv U.toRepresentation (σ.prod τ))
    {A : Subgroup G} (hA : IsOffender ρ A)
    (hd : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) ≤ 2) : False := by
  let j := U.toSubmodule.subtype.comp e.linearEquiv.symm.toLinearMap
  apply not_offender_faithful_product_embedding ρ σ τ hf hg e.groupEquiv.toMonoidHom
    e.groupEquiv.injective j (U.toSubmodule.subtype_injective.comp e.linearEquiv.symm.injective)
    ?_ hA hd
  intro g v
  have he := e.intertwines g (e.linearEquiv.symm v)
  apply_fun e.linearEquiv.symm at he
  simpa [j, Subrepresentation.toRepresentation] using
    congrArg Subtype.val he

private def twoCoordinates (r : ℕ) : W × W →ₗ[ZMod 2] (Fin r → W) where
  toFun v i := if i.val = 0 then v.1 else v.2
  map_add' v w := by ext i; by_cases hi : i.val = 0 <;> simp only [hi, ↓reduceIte, Pi.add_apply, Prod.fst_add, Prod.snd_add]
  map_smul' c v := by ext i; by_cases hi : i.val = 0 <;> simp only [hi, ↓reduceIte, Pi.smul_apply, RingHom.id_apply] <;> rfl

omit [FiniteDimensional (ZMod 2) W] in
private theorem twoCoordinates_injective (r : ℕ) (hr : 2 ≤ r) :
    Function.Injective (twoCoordinates (W := W) r) := by
  intro v w h
  apply Prod.ext
  · have hh := congrFun h ⟨0,by omega⟩
    simpa [twoCoordinates] using hh
  · have hh := congrFun h ⟨1,by omega⟩
    simpa [twoCoordinates] using hh

set_option backward.isDefEq.respectTransparency false in
/-- Two coordinate copies already contradict the plane bound. -/
theorem repeated_multiplicity_le_one [Finite D]
    (hf : Function.Injective σ) (U : Subrepresentation ρ) {r : ℕ}
    (e : ActionEquiv U.toRepresentation (repeated σ r))
    {A : Subgroup G} (hA : IsOffender ρ A)
    (hd : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) ≤ 2) : r ≤ 1 := by
  by_contra! hn
  let j := U.toSubmodule.subtype.comp
    (e.linearEquiv.symm.toLinearMap.comp (twoCoordinates (W := W) r))
  apply not_offender_faithful_product_embedding ρ σ σ hf hf e.groupEquiv.toMonoidHom
    e.groupEquiv.injective j
    (U.toSubmodule.subtype_injective.comp
      (e.linearEquiv.symm.injective.comp (twoCoordinates_injective r hn))) ?_ hA hd
  intro g v
  have he := e.intertwines g (e.linearEquiv.symm (twoCoordinates r v))
  apply_fun e.linearEquiv.symm at he
  have hcoord : repeated σ r (e.groupEquiv g) (twoCoordinates r v) =
      twoCoordinates r ((σ.prod σ) (e.groupEquiv g) v) := by
    ext i
    change σ (e.groupEquiv g) (if i.val = 0 then v.1 else v.2) =
      if i.val = 0 then σ (e.groupEquiv g) v.1 else σ (e.groupEquiv g) v.2
    split <;> rfl
  simp only [e.linearEquiv.symm_apply_apply, e.linearEquiv.apply_symm_apply] at he
  rw [hcoord] at he
  simpa [j, Subrepresentation.toRepresentation] using congrArg Subtype.val he

/-- A full component restriction uses the original acting group. -/
noncomputable def actionOfWhole {τ : Representation (ZMod 2) G V}
    {L : Subgroup G} (hL : L = ⊤) (e : ActionEquiv (τ.comp L.subtype) σ) :
    ActionEquiv τ σ where
  groupEquiv := (topEquiv.symm.trans (MulEquiv.subgroupCongr hL.symm)).trans e.groupEquiv
  linearEquiv := e.linearEquiv
  intertwines g v := e.intertwines
    ((topEquiv.symm.trans (MulEquiv.subgroupCongr hL.symm)) g) v
end CFSG.Quasithin.ChapterB.QuasisimpleSource.SmallMoved

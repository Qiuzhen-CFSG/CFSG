module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Cyclotomic.Coordinates
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.F4ChevalleySplitTorus
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Cyclic subgroups in the algebraic F4 torus and conditional Ree descent

The coordinate solution is inserted into the actual split torus of the closed
root-generated F4 carrier. In characteristic two its order is odd, so an
algebraically closed field contains all the required roots of unity. The
resulting map from `Multiplicative (ZMod n)` is injective, by recovery of the
four diagonal parameters and then coordinate 1.

The final construction conjugates this literal torus by a supplied Lang
solution and proves membership in the fixed subgroup. Transport to the finite
`ReeF4.Model` uses a supplied multiplicative equivalence. These are conditional
constructions: neither the Weyl/twist action, the Lang solutions, nor the
comparison of fixed points with the finite model is asserted to exist here.

`HasReeRootAction`, `weylMinus` and `weylPlus` specify the exact remaining
geometric calculations. The chosen words are `s₀s₁` and
`(s₀s₁s₂s₃)^6 s₀s₁`, in zero-based standard F4 numbering.

Sources: GLS3 §§2.1–2.4 and §4.10, especially the conjugation convention in
2.1.5(d); `refs/KGroup/GLS3/chapter2.tex` and `chapter4.tex`.
-/

public section

namespace ReeF4.CentralCovers.OddPrimary.Cyclotomic
open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem
noncomputable section
variable {F : Type*} [Field F] [IsAlgClosed F]

abbrev AlgebraicCarrier (F : Type*) [Field F] [IsAlgClosed F] :=
  F4Chevalley.Carrier (k := F)

abbrev AlgebraicPoints (F : Type*) [Field F] [IsAlgClosed F] :=
  Variety.Point (AlgebraicCarrier F)

/-- The existing four-parameter torus in the actual closed F4 carrier. -/
@[expose] def diagonal : (Fin 4 → Fˣ) →* AlgebraicPoints F :=
  (F4Chevalley.splitTorusMorphism (k := F)).onPoints.comp
    { toFun := (dPointEquiv 4).symm
      map_one' := by apply (dPointEquiv 4).injective; rw [Equiv.apply_symm_apply, dPointEquiv_one]
      map_mul' u v := by
        apply (dPointEquiv 4).injective
        rw [Equiv.apply_symm_apply, dPointEquiv_mul]
        simp }

theorem diagonal_injective : Function.Injective (diagonal (F := F)) :=
  F4Chevalley.splitTorusMorphism_injective.comp (dPointEquiv 4).symm.injective

omit [IsAlgClosed F] in
theorem order_cast_one [CharP F 2] (a : ℤ) : (torusOrder a : F) = 1 := by
  have hc := congrArg (Int.castRingHom F) (torusOrder_cast a)
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hfour : (4 : F) = 0 := by rw [show (4:F) = 2*2 by norm_num, htwo, zero_mul]
  change ((torusOrder a : ℤ) : F) = (orderPolynomial a : F) at hc
  norm_num [orderPolynomial, htwo, hfour] at hc
  simpa only [htwo, hfour, zero_mul, sub_zero, zero_sub, neg_zero, zero_add] using hc

/-- An odd-order cyclic group identified with all roots of unity of that order. -/
def rootsEquiv [CharP F 2] (a : ℤ) :
    Multiplicative (ZMod (torusOrder a)) ≃* rootsOfUnity (torusOrder a) F := by
  have : NeZero (torusOrder a) := ⟨(torusOrder_pos a).ne'⟩
  have : NeZero (torusOrder a : F) := ⟨by rw [order_cast_one]; exact one_ne_zero⟩
  apply mulEquivOfCyclicCardEq
  change Nat.card (ZMod (torusOrder a)) = _
  rw [Nat.card_zmod, HasEnoughRootsOfUnity.natCard_rootsOfUnity]

/-- The one-parameter cyclic subgroup of the concrete algebraic F4 torus. -/
def algebraicTorus [CharP F 2] (a : ℤ) :
    Multiplicative (ZMod (torusOrder a)) →* AlgebraicPoints F :=
  diagonal.comp ((rootsCoordinates a).comp (rootsEquiv (F := F) a).toMonoidHom)

theorem algebraicTorus_injective [CharP F 2] (a : ℤ) :
    Function.Injective (algebraicTorus (F := F) a) :=
  diagonal_injective.comp ((rootsCoordinates_injective a).comp (rootsEquiv a).injective)

@[expose] def rootPoint (r : F4Chevalley.Root) (t : F) : AlgebraicPoints F :=
  (F4Chevalley.rootMorphism r).onPoints (kPlusPoint t)

/-- The exact exceptional root formula, using the integer field-size convention. -/
@[expose] def HasReeRootAction (m : ℕ)
    (σ : Theory.AlgebraicGroup.Morphism
      (AlgebraicCarrier F) (AlgebraicCarrier F)) : Prop := by
  classical
  exact ∀ (r : F4Chevalley.Root) (t : F), σ.onPoints (rootPoint r t) =
    rootPoint (exceptionalRootPermutation r)
      (if IsLongRoot r then t^(2^m) else t^(2^(m+1)))

local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

@[expose] def simpleWeyl (i : Fin 4) : AlgebraicPoints F :=
  rootPoint (typeF4SimpleRootIndex i) 1 *
    rootPoint (-typeF4SimpleRootIndex i) (-1) * rootPoint (typeF4SimpleRootIndex i) 1

@[expose] def weylMinus : AlgebraicPoints F := simpleWeyl 0 * simpleWeyl 1

@[expose] def weylPlus : AlgebraicPoints F :=
  (simpleWeyl 0 * simpleWeyl 1 * simpleWeyl 2 * simpleWeyl 3)^6 * weylMinus

@[expose] def algebraicFixed (σ : AlgebraicPoints F →* AlgebraicPoints F) : Subgroup (AlgebraicPoints F) :=
  MonoidHom.eqLocus σ (MonoidHom.id _)

theorem conjugated_fixed (σ : AlgebraicPoints F →* AlgebraicPoints F)
    (n g t : AlgebraicPoints F) (hg : g * (σ g)⁻¹ = n)
    (ht : n * σ t * n⁻¹ = t) : g⁻¹ * t * g ∈ algebraicFixed σ := by
  have hs : σ g = n⁻¹ * g := by rw [← hg]; group
  change σ (g⁻¹ * t * g) = g⁻¹ * t * g
  simp only [map_mul, map_inv]
  calc
    (σ g)⁻¹ * σ t * σ g = g⁻¹ * (n * σ t * n⁻¹) * g := by rw [hs]; group
    _ = g⁻¹ * t * g := by rw [ht]

/-- Conjugation by a Lang solution embeds the cyclic group in the fixed subgroup. -/
def descendedTorus [CharP F 2] (a : ℤ)
    (σ : AlgebraicPoints F →* AlgebraicPoints F) (n g : AlgebraicPoints F)
    (hg : g * (σ g)⁻¹ = n)
    (haction : ∀ u, n * σ (diagonal u) * n⁻¹ = diagonal (twistedAction a u)) :
    Multiplicative (ZMod (torusOrder a)) →* algebraicFixed σ :=
  (((MulAut.conj g⁻¹).toMonoidHom).comp (algebraicTorus a)).codRestrict
    (algebraicFixed σ) (fun z => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      apply conjugated_fixed σ n g _ hg
      change n * σ (diagonal (rootsCoordinates a (rootsEquiv a z))) * n⁻¹ = _
      rw [haction, rootsCoordinates_fixed]
      rfl)

theorem descendedTorus_injective [CharP F 2] (a : ℤ)
    (σ : AlgebraicPoints F →* AlgebraicPoints F) (n g : AlgebraicPoints F)
    (hg : g * (σ g)⁻¹ = n)
    (haction : ∀ u, n * σ (diagonal u) * n⁻¹ = diagonal (twistedAction a u)) :
    Function.Injective (descendedTorus a σ n g hg haction) := by
  intro x y h
  apply algebraicTorus_injective (F := F) a
  apply (MulAut.conj g⁻¹).injective
  exact congrArg Subtype.val h

/-- Transport to the literal finite model, retaining every geometric premise. -/
def cyclicEmbeddingOfDescent [CharP F 2] {m : ℕ} (a : ℤ)
    (σ : AlgebraicPoints F →* AlgebraicPoints F) (n g : AlgebraicPoints F)
    (hg : g * (σ g)⁻¹ = n)
    (haction : ∀ u, n * σ (diagonal u) * n⁻¹ = diagonal (twistedAction a u))
    (e : algebraicFixed σ ≃* Model m) : CyclicTorusEmbedding m (torusOrder a) where
  map := e.toMonoidHom.comp (descendedTorus a σ n g hg haction)
  injective := e.injective.comp (descendedTorus_injective a σ n g hg haction)
end
end ReeF4.CentralCovers.OddPrimary.Cyclotomic

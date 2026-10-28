module
public import CFSG.Quasithin.Chapter12.Section06.Setup
public import CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup

/-!
# Full coordinates from the vanishing original fixed space

When the original fixed space C_V(L) vanishes, the quotient projection
V → V/C_V(L) is an isomorphism. Compose its inverse with the given
orthogonal marking to obtain coordinates on the unchanged full V.
The action formula retains the original conjugation-kernel quotient,
and nonsingularity agrees with the original quotient-form predicate.
These coordinates connect the original source setup to the later local
geometry without identifying two distinct action quotients by convention.

Source: Aschbacher--Smith, 12.6.23 and the setup following it, printed
pp.830--831 (PDF pp.847--848). The vanishing premise is explicit here;
this module does not prove 12.6.23.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06.OrthogonalMarking
variable {G : Type*} [Group G] {L V : Subgroup G} [IsElementaryAbelian 2 V]
  {hn : L ≤ normalizer (V : Set G)} (D : OrthogonalMarking L V hn)

private theorem fixedSeed_eq_bot (hZ : ZV L V = ⊥) :
    (fixedSeed L V hn).toSubmodule = ⊥ := by
  apply le_bot_iff.mp
  intro v hv
  have he : (v.toMul : G) = 1 := mem_bot.mp
    (hZ ▸ (mem_fixedSeed_iff L V hn v).mp hv)
  exact congrArg Additive.ofMul (show v.toMul = 1 from Subtype.ext he)

/-- The full six-space coordinates after the original fixed space vanishes. -/
@[expose] noncomputable def fullLinearCoordinates (hZ : ZV L V = ⊥) :
    Additive V ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8) :=
  ((fixedSeed L V hn).toSubmodule.quotEquivOfEqBot (by exact fixedSeed_eq_bot hZ)).symm.trans
    D.coordinates

theorem fullLinearCoordinates_apply (hZ : ZV L V = ⊥) (v : Additive V) :
    D.fullLinearCoordinates hZ v = D.coordinates (Submodule.Quotient.mk v) := by
  simp only [fullLinearCoordinates,LinearEquiv.trans_apply,Submodule.quotEquivOfEqBot_symm_apply]

/-- Multiplicative coordinates on the unchanged original subgroup V. -/
@[expose] noncomputable def fullCoordinates (hZ : ZV L V = ⊥) :
    V ≃* Multiplicative (BinaryPermutation.natural (Fin 8)) where
  toFun v := Multiplicative.ofAdd (D.fullLinearCoordinates hZ (Additive.ofMul v))
  invFun v := ((D.fullLinearCoordinates hZ).symm v.toAdd).toMul
  left_inv v := (D.fullLinearCoordinates hZ).symm_apply_apply (Additive.ofMul v)
  right_inv v := (D.fullLinearCoordinates hZ).apply_symm_apply v.toAdd
  map_mul' v w := (D.fullLinearCoordinates hZ).map_add (Additive.ofMul v) (Additive.ofMul w)

theorem fullCoordinates_apply (hZ : ZV L V = ⊥) (v : V) :
    (D.fullCoordinates hZ v).toAdd =
      D.coordinates (Submodule.Quotient.mk (Additive.ofMul v)) :=
  D.fullLinearCoordinates_apply hZ (Additive.ofMul v)

/-- The action still factors through the original conjugation-kernel quotient. -/
theorem fullCoordinates_equivariant (hZ : ZV L V = ⊥) (l : L) (v : V) :
    (D.fullCoordinates hZ (conjugation L V hn l v)).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 8)
        (D.groupEquiv (QuotientGroup.mk' (conjugation L V hn).ker l)).val
        (D.fullCoordinates hZ v).toAdd := by
  rw [D.fullCoordinates_apply,D.fullCoordinates_apply]
  exact D.equivariant l (Submodule.Quotient.mk (Additive.ofMul v))

/-- Nonsingularity is exactly the original quotient-form predicate. -/
theorem fullCoordinates_nonsingular_iff (hZ : ZV L V = ⊥) (v : V) :
    BinaryPermutation.TerminalOrthogonal.Eight.form (D.fullCoordinates hZ v).toAdd ≠ 0 ↔
      D.Nonsingular v := by
  rw [D.fullCoordinates_apply]
  rfl

/-- The later setup uses the same T, L, V and selected point. Its full
coordinates are obtained from the actual fixed-space quotient map. -/
@[expose] noncomputable def fullSetup (hZ : ZV L V = ⊥) (T : Sylow 2 G) (z : V) :
    Nonabelian.Setup G :=
  ⟨T,L,M L,V,D.fullCoordinates hZ,z⟩

end CFSG.Quasithin.Chapter12.Section06.OrthogonalMarking

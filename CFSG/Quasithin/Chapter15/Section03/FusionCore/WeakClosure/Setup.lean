module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.QuadraticGeometry

/-!
# Earlier inputs for the orthogonal weak-closure argument

The quadratic form is on the actual elementary abelian subgroup `V`, as in
`FusionCore.NaturalOrthogonalAction`. A definite plane has order four and all
three of its nonidentity vectors are nonsingular. Thus the choice of plane
used in `S = N_T(P)` and `Z_S = C_V(S)` is tied to this form.

`EarlierFusionInputs` lists the preceding source conclusions used in
15.3.46–47. In particular, the residual alternative uses `O²(X)`, the full
action-image alternative is expressed modulo `C_M(V)`, and the centralizer
bound is exactly 15.3.45(3) for the chosen definite plane. It contains no
fusion-control or weak-closure-centralization premise. The section assembly
must construct these inputs from the earlier theorems.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1121–1122, 1140–1141, especially 15.3.2(2,4) and 15.3.45(3).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore

open Subgroup
open scoped IsMulCommutative

variable {G : Type*} [Group G]

/-- A definite plane in the specified quadratic space, with its ambient embedding. -/
def IsDefinitePlane {V : Subgroup G} [IsElementaryAbelian 2 V]
    (Q : QuadraticForm (ZMod 2) (Additive V)) (P : Subgroup G) : Prop :=
  P ≤ V ∧ Nat.card P = 4 ∧
    ∀ v : V, (v : G) ∈ P → v ≠ 1 → Q (Additive.ofMul v) ≠ 0

/-- Exactly the residual/action-image dichotomy in 15.3.2(4).
The join equality says that `X` has full image in `M/C_M(V)`. -/
def ResidualUniquenessDichotomy (T : Sylow 2 G) (M V : Subgroup G) : Prop :=
  ∀ X : Subgroup G, (T : Subgroup G) ≤ X → X ≤ M →
    Stellmacher.twoResidualAmbient X ≤ M ⊓ centralizer (V : Set G) ∨
      (X ⊔ (M ⊓ centralizer (V : Set G)) = M ∧
        Chapter4.UniqueMaximalOvergroup X M)

/-- The standing local setup, 15.3.2(2,4), and the instance of 15.3.45(3)
used by the fusion proof. Natural action and definiteness are separate inputs. -/
structure EarlierFusionInputs (T : Sylow 2 G) (M V P : Subgroup G) : Prop where
  normalizer_eq : M = normalizer (V : Set G)
  module_eq : V = localModule T M
  module_le_sylow : V ≤ T
  sylow_le : (T : Subgroup G) ≤ M
  central_fixed : centralInvolutions T = fixedPlane V T
  central_order : Nat.card (centralInvolutions T) = 2
  residual_uniqueness : ResidualUniquenessDichotomy T M V
  plane_fixed_centralizer :
    centralizer (fixedPlane P (planeStabilizer T P) : Set G) ≤ M

/-- The finite natural-module calculations needed to separate the two orbits.

This is an intermediate contract, not an earlier-source hypothesis and not an
assertion of 15.3.46. Its constructor must be proved from the full natural
action and `EarlierFusionInputs`. In particular the Sylow group is relative
to the full centralizer, and its ambient image is the actual plane stabilizer.
No global fusion separation or weak-closure centralization is a field. -/
structure OrthogonalFusionCalculations (T : Sylow 2 G) (M V P : Subgroup G)
    [IsElementaryAbelian 2 V] (Q : QuadraticForm (ZMod 2) (Additive V)) where
  z : V
  z_ne_one : z ≠ 1
  z_central : (z : G) ∈ centralInvolutions T
  z_singular : Q (Additive.ofMul z) = 0
  v : V
  v_ne_one : v ≠ 1
  fixed_line : fixedPlane P (planeStabilizer T P) = zpowers (v : G)
  singular_orbit : ∀ u : V, u ≠ 1 → Q (Additive.ofMul u) = 0 →
    ConjugateBy M (z : G) (u : G)
  nonsingular_orbit : ∀ u : V, Q (Additive.ofMul u) ≠ 0 →
    ConjugateBy M (v : G) (u : G)
  centralizer_sylow : Sylow 2 (centralizer ({(v : G)} : Set G))
  sylow_image : (centralizer_sylow : Subgroup (centralizer ({(v : G)} : Set G))).map
    (centralizer ({(v : G)} : Set G)).subtype = planeStabilizer T P
  stabilizer_index : (planeStabilizer T P).relIndex T = 2

end CFSG.Quasithin.Chapter15.Section03.FusionCore

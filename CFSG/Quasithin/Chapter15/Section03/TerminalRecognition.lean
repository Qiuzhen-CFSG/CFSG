module

public import Stellmacher.CentralizerQuotientRepresentation
public import Theory.GroupTheory.NormalClosureCentralizerCore
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.GroupTheory.ConjugateSpanOrder
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Action and lifting steps in the terminal proof of Theorem 15.3.1

Work intrinsically in `H = G₀`; its two-core is `Q₀`, and the module is the
actual normal closure `V₀ = ⟨Vᴴ⟩`. The conclusions of 15.3.67–68 give
`V ≤ Z(Q₀)` and a two-group centralizer of `V`. We prove that `V₀` is
elementary abelian and that its centralizer is exactly `Q₀`, then construct
the faithful binary action of `H/Q₀`.

For `T = T_E` and `E = X_E`, the identity `E = [E,J(T)]`, together with
`E` escaping the two-core, makes `J(T)` act nontrivially on `V₀`. The
maximum-elementary-subgroup bound supplies an actual FF-offender. We also
prove the normal-closure commutator identity used in the non-`S₃` branch
and the conjugate-span centralization step used in the `S₃` branch.

Finally a surjection from the stabilizer of the actual plane in the action
image lifts to a surjection from its actual normalizer in `X`. This step
does not require the quotient map to be injective on `X`.

The F.6.18/B.5.6 intersection, elimination of the nonexceptional actions,
and the exceptional plane-stabilizer calculation are separate recognition
inputs. None is asserted here. In the source, `Â₆` is the nonsplit triple
cover (A.3.5); `Ŝ₆` extends its three-dimensional `𝔽₄` representation by a
field involution (K.1.3), not by a central double-cover construction.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), printed pp.1154–1155, PDF pp.1171–1172;
covering-group conventions on printed pp.43 and 453.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition

variable {H : Type*} [Group H]

/-- The actual normal closure `V₀ = ⟨Vᴳ⁰⟩`, formed inside `G₀`. -/
abbrev moduleClosure (V : Subgroup H) : Subgroup H := normalClosure (V : Set H)

/-- The quotient by the intrinsic two-core of the local group. -/
abbrev coreQuotient (H : Type*) [Group H] := H ⧸ pCore 2 H

/-- The actual quotient homomorphism, retaining its nontrivial kernel. -/
def coreProjection : H →* coreQuotient H := QuotientGroup.mk' (pCore 2 H)

/-- Normality of the two-core puts every conjugate of `V` inside it. -/
theorem moduleClosure_le_twoCore (V : Subgroup H) (hV : V ≤ pCore 2 H) :
    moduleClosure V ≤ pCore 2 H := normalClosure_le_normal hV

/-- Centralization of `V` by the normal two-core extends to its normal closure. -/
theorem moduleClosure_le_coreCentralizer (V : Subgroup H)
    (hcore : pCore 2 H ≤ centralizer (V : Set H)) :
    moduleClosure V ≤ centralizer (pCore 2 H : Set H) :=
  normalClosure_le_normal (le_centralizer_iff.mp hcore)

/-- The normal closure of the elementary subgroup inside `Z(Q₀)` is elementary. -/
theorem moduleClosure_elementary (V : Subgroup H) [IsElementaryAbelian 2 V]
    (hV : V ≤ pCore 2 H) (hcore : pCore 2 H ≤ centralizer (V : Set H)) :
    IsElementaryAbelian 2 (moduleClosure V) := by
  let _ : IsMulCommutative (moduleClosure V) :=
    le_centralizer_iff_isMulCommutative.mp
      ((moduleClosure_le_coreCentralizer V hcore).trans
        (centralizer_le (moduleClosure_le_twoCore V hV)))
  exact IsElementaryAbelian.normalClosure_of_isMulCommutative V

/-- The faithful-action kernel in the final proof is exactly `O₂(G₀)`. -/
theorem moduleClosure_centralizer (V : Subgroup H)
    (hC : IsPGroup 2 (centralizer (V : Set H)))
    (hcore : pCore 2 H ≤ centralizer (V : Set H)) :
    centralizer (moduleClosure V : Set H) = pCore 2 H :=
  centralizer_normalClosure_eq_pCore_of_isPGroup 2 V hC hcore

/-- Kernel equality in the form needed by the descended conjugation action. -/
theorem coreProjection_ker (V : Subgroup H)
    (hC : IsPGroup 2 (centralizer (V : Set H)))
    (hcore : pCore 2 H ≤ centralizer (V : Set H)) :
    (coreProjection (H := H)).ker = centralizer (moduleClosure V : Set H) :=
  (QuotientGroup.ker_mk' _).trans (moduleClosure_centralizer V hC hcore).symm

open Representation.BinaryOffender
open Representation.NormalElementaryQuotient

variable (V : Subgroup H) [IsElementaryAbelian 2 (moduleClosure V)]
    (hC : IsPGroup 2 (centralizer (V : Set H)))
    (hcore : pCore 2 H ≤ centralizer (V : Set H))

/-- The faithful quotient acts by genuine conjugation on the binary module `V₀`. -/
noncomputable def quotientAction :
    Representation (ZMod 2) (coreQuotient H) (Additive (moduleClosure V)) :=
  representation (moduleClosure V) coreProjection (QuotientGroup.mk'_surjective _)
    (coreProjection_ker V hC hcore)

/-- Compatibility of the quotient representation with ambient multiplication. -/
theorem quotientAction_apply (g : H) (v : Additive (moduleClosure V)) :
    ((quotientAction V hC hcore (coreProjection g) v).toMul : H) =
      g * (v.toMul : H) * g⁻¹ :=
  representation_apply (moduleClosure V) coreProjection (QuotientGroup.mk'_surjective _)
    (coreProjection_ker V hC hcore) g v

/-- The quotient representation is faithful. -/
theorem quotientAction_injective : Function.Injective (quotientAction V hC hcore) :=
  representation_injective (moduleClosure V) coreProjection (QuotientGroup.mk'_surjective _)
    (coreProjection_ker V hC hcore)

variable [Finite H]

/-- The source identity `X_E = [X_E,J(T_E)]` forces an actual FF-offender. -/
theorem quotientAction_isFFModule (T : Sylow 2 H) (E : Subgroup H)
    (hV : V ≤ pCore 2 H)
    (hE : E = ⁅E, Stellmacher.elementaryAbelianMaxJ (T : Subgroup H)⁆)
    (hEnot : ¬ E ≤ pCore 2 H) : IsFFModule (quotientAction V hC hcore) := by
  apply isFFModule_of_thompson_not_le (moduleClosure V) coreProjection
    (QuotientGroup.mk'_surjective _) (coreProjection_ker V hC hcore) (T : Subgroup H)
  · exact (moduleClosure_le_twoCore V hV).trans (pCore_isPGroup.le_sylow_of_normal T)
  · intro hJ
    have hJcore : Stellmacher.elementaryAbelianMaxJ (T : Subgroup H) ≤ pCore 2 H := by
      simpa only [coreProjection, QuotientGroup.ker_mk'] using hJ
    apply hEnot
    calc
      E = ⁅E, Stellmacher.elementaryAbelianMaxJ (T : Subgroup H)⁆ := hE
      _ ≤ ⁅E, pCore 2 H⁆ := commutator_mono le_rfl hJcore
      _ ≤ pCore 2 H := commutator_le_right _ _

omit [Finite H] [IsElementaryAbelian 2 (moduleClosure V)] in
/-- In the non-`S₃` branch, `V = [V,Y_F]` and `Y_F ≤ X` imply `V₀ = [V₀,X]`. -/
theorem moduleClosure_eq_commutator (X Y : Subgroup H) [X.Normal]
    (hYX : Y ≤ X) (hVY : V = ⁅V, Y⁆) :
    moduleClosure V = ⁅moduleClosure V, X⁆ := by
  apply le_antisymm
  · apply normalClosure_le_normal
    exact hVY.le.trans (commutator_mono le_normalClosure hYX)
  · exact commutator_le_left _ _

omit [Finite H] [IsElementaryAbelian 2 (moduleClosure V)] in
/-- The `S₃` branch propagation: `Z ≤ C(X)` implies `⟨Z^{Y_F}⟩ ≤ C(X)`. -/
theorem conjugateSpan_centralizes_normal (Z Y X : Subgroup H) [X.Normal]
    (hZX : Z ≤ centralizer (X : Set H)) :
    conjugateSpanBy Z Y ≤ centralizer (X : Set H) := by
  apply conjugateSpanBy_le hZX
  rw [normalizer_eq_top]
  exact le_top

/-- The binary subspace coming from the specified subgroup `V₁ ≤ V₀`. -/
noncomputable def planeSubspace (P : Subgroup H) :
    Submodule (ZMod 2) (Additive (moduleClosure V)) :=
  subspace (moduleClosure V) (P.subgroupOf (moduleClosure V))

omit [Finite H] in
/-- Lift an `A₅` quotient of the plane stabilizer through the action kernel. -/
theorem exists_surjective_planeNormalizer_to_A5 (X P : Subgroup H)
    (hP : P ≤ moduleClosure V)
    (f : (X.map coreProjection ⊓
      subspaceStabilizer (quotientAction V hC hcore) (planeSubspace V P) :
        Subgroup (coreQuotient H)) →* alternatingGroup (Fin 5))
    (hf : Function.Surjective f) :
    ∃ F : (X ⊓ normalizer (P : Set H) : Subgroup H) →* alternatingGroup (Fin 5),
      Function.Surjective F := by
  have h := exists_surjective_normalizer_hom (moduleClosure V) coreProjection
    (QuotientGroup.mk'_surjective _) (coreProjection_ker V hC hcore)
    X (P.subgroupOf (moduleClosure V)) f hf
  have hmap : (P.subgroupOf (moduleClosure V)).map (moduleClosure V).subtype = P :=
    map_subgroupOf_eq_of_le hP
  rw [hmap] at h
  exact h

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition

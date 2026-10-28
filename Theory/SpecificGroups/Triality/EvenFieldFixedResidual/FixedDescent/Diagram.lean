module

public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.Twist
public import Theory.GroupAction.AutomorphismFixedResidualTransport
/-!
# Reversing the pinned D4 cycle

The transposition of arms 2 and 3 preserves the actual D4 Cartan matrix.
Its extension to the root pairing and integral Geck matrices intertwines the
inverse triality cycle with the canonical cycle. It commutes with entrywise
coefficient maps, hence identifies the two half-parameter fixed groups by a
multiplicative equivalence on the original split matrices.

This is the explicit diagram comparison in GLS3 Remark 2.2.5(b), used in
Aschbacher–Smith 16.1.4(4), printed p.1171. Sources:
`refs/KGroup/GLS3/chapter2.tex` and `refs/quasithin.pdf`.
-/

public section
noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.SimpleGeckGroup
namespace Triality.Standard.EvenField

private def armSwap : Equiv.Perm (Fin 4) := Equiv.swap 2 3
private theorem armSwap_cartan (i j : Fin 4) :
    typeDCartanMatrix 2 (armSwap i) (armSwap j) = typeDCartanMatrix 2 i j := by
  fin_cases i <;> fin_cases j <;> decide
private def armSwapBase : Equiv.Perm (typeDRootPairing_base 2).support :=
  (typeDRootPairing_baseEquiv 2).symm.trans (armSwap.trans (typeDRootPairing_baseEquiv 2))
private theorem armSwapBase_numbered (i : Fin 4) :
    armSwapBase (typeDRootPairing_baseEquiv 2 i) = typeDRootPairing_baseEquiv 2 (armSwap i) := by
  simp [armSwapBase]
private theorem armSwapBase_cartan (i j : (typeDRootPairing_base 2).support) :
    (typeDRootPairing_base 2).cartanMatrix (armSwapBase i) (armSwapBase j) =
      (typeDRootPairing_base 2).cartanMatrix i j := by
  obtain ⟨i, rfl⟩ := (typeDRootPairing_baseEquiv 2).surjective i
  obtain ⟨j, rfl⟩ := (typeDRootPairing_baseEquiv 2).surjective j
  simpa only [armSwapBase_numbered, typeDRootPairing_base_cartanMatrix] using armSwap_cartan i j
private def armSwapRoot : (typeDRootPairing 2).Equiv (typeDRootPairing 2) :=
  (typeDRootPairing_base 2).equivOfCartanMatrixEq (typeDRootPairing_base 2)
    armSwapBase armSwapBase_cartan
private theorem armSwapRoot_simple (i : (typeDRootPairing_base 2).support) :
    armSwapRoot.indexEquiv i = armSwapBase i := by
  apply (typeDRootPairing 2).root.injective
  rw [← RootPairing.Hom.root_weightMap_apply]
  change ((typeDRootPairing_base 2).toWeightBasis.equiv
    (typeDRootPairing_base 2).toWeightBasis armSwapBase) ((typeDRootPairing 2).root i) = _
  simpa using Module.Basis.equiv_apply (typeDRootPairing_base 2).toWeightBasis i
    (typeDRootPairing_base 2).toWeightBasis armSwapBase

/-- The pinned automorphism swapping arms 2 and 3. -/
def reverseDiagram (P : Parameters) : MulAut (SplitGroup P) :=
  diagramEquiv armSwapRoot armSwapBase armSwapRoot_simple

private theorem split_hom_ext {P : Parameters} {H : Type*} [Group H]
    (f g : SplitGroup P →* H)
    (hpos : ∀ i t, f (positive i t) = g (positive i t))
    (hneg : ∀ i t, f (negative i t) = g (negative i t)) : f = g := by
  apply MonoidHom.ext
  rintro ⟨x,hx⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨⟨s,i⟩,t,rfl⟩ := hx
      cases s
      · exact hneg i t
      · exact hpos i t
  | one => exact f.map_one.trans g.map_one.symm
  | mul x y hx hy h1 h2 =>
      exact (f.map_mul ⟨x,hx⟩ ⟨y,hy⟩).trans
        ((congrArg₂ (· * ·) h1 h2).trans (g.map_mul ⟨x,hx⟩ ⟨y,hy⟩).symm)
  | inv x hx h =>
      exact (map_inv f ⟨x,hx⟩).trans ((congrArg Inv.inv h).trans (map_inv g ⟨x,hx⟩).symm)

private theorem armSwapBase_cycle (i : (typeDRootPairing_base 2).support) :
    armSwapBase (typeD4DiagramBasePermutation (typeD4DiagramBasePermutation i)) =
      typeD4DiagramBasePermutation (armSwapBase i) := by
  obtain ⟨i, rfl⟩ := (typeDRootPairing_baseEquiv 2).surjective i
  simp only [typeD4DiagramBasePermutation_numbered, armSwapBase_numbered]
  congr 1
  fin_cases i <;> decide

/-- Swapping two arms conjugates the inverse triality cycle to the canonical cycle. -/
theorem reverseDiagram_cycle (P : Parameters) (x : SplitGroup P) :
    reverseDiagram P (diagramAutomorphism P (diagramAutomorphism P x)) =
      diagramAutomorphism P (reverseDiagram P x) := by
  have h := split_hom_ext
    ((reverseDiagram P).toMonoidHom.comp
      ((diagramAutomorphism P).toMonoidHom.comp (diagramAutomorphism P).toMonoidHom))
    ((diagramAutomorphism P).toMonoidHom.comp (reverseDiagram P).toMonoidHom)
    (fun i t => by
      change reverseDiagram P (diagramAutomorphism P (diagramAutomorphism P (positive i t))) =
        diagramAutomorphism P (reverseDiagram P (positive i t))
      simp only [diagramAutomorphism_positive, reverseDiagram, diagramEquiv_positive,
        armSwapBase_cycle])
    (fun i t => by
      change reverseDiagram P (diagramAutomorphism P (diagramAutomorphism P (negative i t))) =
        diagramAutomorphism P (reverseDiagram P (negative i t))
      simp only [diagramAutomorphism_negative, reverseDiagram, diagramEquiv_negative,
        armSwapBase_cycle])
  exact DFunLike.congr_fun h x

/-- The canonical diagram cycle with the smaller Frobenius exponent over the larger field. -/
@[expose] def forwardGraphHalf (n : ℕ) (hn : 0 < n) (m : ℕ) :
    MulAut (SplitGroup (binaryParameters n hn)) :=
  diagramAutomorphism (binaryParameters n hn) * splitFrobenius n hn m

/-- The arm swap intertwines the two literal half-parameter twists. -/
theorem reverseDiagram_half (n : ℕ) (hn : 0 < n) (m : ℕ)
    (x : SplitGroup (binaryParameters n hn)) :
    reverseDiagram _ (inverseGraphHalf n hn m x) =
      forwardGraphHalf n hn m (reverseDiagram _ x) := by
  change reverseDiagram _ (diagramAutomorphism _ (diagramAutomorphism _ (splitFrobenius n hn m x))) = _
  rw [reverseDiagram_cycle]
  change diagramAutomorphism _ (reverseDiagram _ (equiv _ x)) =
    diagramAutomorphism _ (equiv _ (reverseDiagram _ x))
  exact congrArg (diagramAutomorphism _) (diagramEquiv_equiv _ _ _ _ x)

/-- Actual fixed-group equivalence induced by the pinned arm swap. -/
def inverseGraphFixedEquivForward (n : ℕ) (hn : 0 < n) (m : ℕ) :
    (inverseGraphHalf n hn m).fixedSubgroup ≃* (forwardGraphHalf n hn m).fixedSubgroup :=
  MulAut.fixedSubgroupEquivOfCompatible (reverseDiagram _) _ _ (reverseDiagram_half n hn m)
private theorem forward_cube {A : Type*} [Group A] (d f : A)
    (hc : Commute d f) (hd : d^3 = 1) : (d*f)^3 = f^3 := by
  rw [hc.mul_pow, hd, one_mul]

/-- The forward half twist has cube equal to the coefficient involution. -/
theorem forwardGraphHalf_cube (n : ℕ) (hn : 0 < n) (m : ℕ) :
    forwardGraphHalf n hn m ^ 3 = splitFrobenius n hn (3*m) := by
  have hc : Commute (diagramAutomorphism (binaryParameters n hn)) (splitFrobenius n hn m) := by
    apply MulEquiv.ext
    intro x
    exact RootPairing.SimpleGeckGroup.diagramEquiv_equiv _ _ _ _ x
  have hd : diagramAutomorphism (binaryParameters n hn) ^ 3 = 1 := by
    apply MulEquiv.ext
    exact diagramAutomorphism_three _
  exact (forward_cube _ _ hc hd).trans
    ((splitFrobenius_mul n hn m 3).symm.trans
      (congrArg (splitFrobenius n hn) (Nat.mul_comm m 3)))

/-- Every forward half-twist fixed matrix has entries in the smaller coefficient field. -/
theorem forwardGraphHalf_fixed_coefficient (n : ℕ) (hn : 0 < n) (m : ℕ)
    (x : SplitGroup (binaryParameters n hn)) (hx : forwardGraphHalf n hn m x = x) :
    splitFrobenius n hn (3*m) x = x := by
  have h : (forwardGraphHalf n hn m ^ 3) x = x :=
    (congrArg (forwardGraphHalf n hn m) (congrArg (forwardGraphHalf n hn m) hx)).trans
      ((congrArg (forwardGraphHalf n hn m) hx).trans hx)
  exact (congrArg (fun a : MulAut (SplitGroup (binaryParameters n hn)) => a x)
    (forwardGraphHalf_cube n hn m).symm).trans h


end Triality.Standard.EvenField

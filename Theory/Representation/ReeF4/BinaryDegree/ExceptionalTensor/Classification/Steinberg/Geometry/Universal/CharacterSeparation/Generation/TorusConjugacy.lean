module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.Characters
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Basic
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.TorusConjugacy.MatrixSupport
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.TorusConjugacy.BorelReduction
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.TorusConjugacy.Centralizer
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.TorusConjugacy.BorelAssembly

/-!
# Concrete F4 torus maximality and arbitrary-model conjugacy

A carrier matrix commuting with every literal torus matrix is forced onto the
Cartan block and the root diagonal by `MatrixSupport`. In characteristic two,
`Centralizer` proves that these remaining entries are exactly a torus matrix.
Thus the split torus is self-centralizing and maximal. This also identifies
the previously chosen containing maximal torus with the literal split torus.

Geometric Borel conjugacy and torus conjugacy inside connected solvable Borel
carriers supply ambient maximal-torus conjugacy through `BorelAssembly`.
The final results therefore have no extra geometric premises. They apply to
any supplied actual F4 root model, without constraining its base, over any
algebraically closed field of characteristic two. In particular they apply
over the algebraic closure of the finite field in the Ree F4 construction;
semisimplicity is not needed for this step. The earlier conditional reductions
remain available with their original interfaces.

Sources: GLS3, Theorems 1.4.3(b) and 1.9.5(c). In this library
`T.conjugate g` means `g T g⁻¹`, opposite to the book's exponent notation;
existence of a conjugating element is unaffected.
-/

public section

open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.F4Chevalley
namespace Theory.AlgebraicGroup.F4Chevalley.TorusConjugacy
variable {k : Type*} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private theorem subtorus_commute {G : Variety k} [AlgebraicGroup G]
    (T : ClosedSubgroup G) (hT : IsSubtorus T)
    {x y : Variety.Point G} (hx : x ∈ T.toSubgroup) (hy : y ∈ T.toSubgroup) :
    x * y = y * x := by
  let a := T.pointEquiv.symm ⟨x, hx⟩
  let b := T.pointEquiv.symm ⟨y, hy⟩
  have he := congrArg T.inclusion.onPoints
    (isMulCommutative_iff.mp hT.isMulCommutative a b)
  have ha : T.inclusion.onPoints a = x :=
    congrArg Subtype.val (T.pointEquiv.apply_symm_apply _)
  have hb : T.inclusion.onPoints b = y :=
    congrArg Subtype.val (T.pointEquiv.apply_symm_apply _)
  simpa only [map_mul, ha, hb] using he

variable (hmat : ∀ A : (Matrix BasisIndex BasisIndex k)ˣ,
  matrixToAmbient A ∈ ambientCarrierSubgroup (k := k) →
  (∀ u : Fin 4 → kˣ, Commute A (torusElement u)) →
  ∃ u : Fin 4 → kˣ, A = torusElement u)

include hmat

/-- The literal matrix centralizer calculation identifies the closed-torus centralizer. -/
theorem splitTorus_centralizer_eq_of_matrix_centralizer :
    (splitTorus (k := k)).centralizer.toSubgroup = (splitTorus (k := k)).toSubgroup := by
  apply le_antisymm
  · intro g hg
    obtain ⟨A, hA⟩ := matrixToAmbient_bijective.2
      ((ambientClosedCarrier (k := k)).inclusion.onPoints g)
    have hmem : matrixToAmbient A ∈ ambientCarrierSubgroup (k := k) := by
      rw [hA]
      exact ((ambientClosedCarrier (k := k)).pointEquiv g).property
    obtain ⟨u, rfl⟩ := hmat A hmem
      (TorusConjugacy.matrix_commutes_torus_of_centralizes g hg A hA)
    refine ⟨(dPointEquiv 4).symm u, ?_⟩
    apply (ambientClosedCarrier (k := k)).inclusion_injective
    rw [splitTorusMorphism_inclusion_apply, torusAmbientMorphism_matrix,
      Equiv.apply_symm_apply]
    exact hA
  · intro g hg
    apply Subgroup.mem_centralizer_iff.mpr
    intro t ht
    exact subtorus_commute _ splitTorus_isSubtorus ht hg

/-- A torus containing the split torus centralizes it, so the matrix calculation forces equality. -/
theorem splitTorus_isMaximal_of_matrix_centralizer :
    IsMaximalTorus (splitTorus (k := k)) := by
  refine ⟨splitTorus_isSubtorus, ?_⟩
  intro S hS hTS
  apply SetLike.coe_injective
  apply Set.Subset.antisymm _ hTS
  intro x hx
  have hc : x ∈ (splitTorus (k := k)).centralizer.toSubgroup := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro t ht
    exact subtorus_commute S hS (hTS ht) hx
  rw [splitTorus_centralizer_eq_of_matrix_centralizer hmat] at hc
  exact hc

/-- The previously chosen containing maximal torus is the split torus once the calculation is supplied. -/
theorem maximalTorus_eq_splitTorus_of_matrix_centralizer :
    maximalTorus (k := k) = splitTorus (k := k) :=
  (splitTorus_isMaximal_of_matrix_centralizer hmat).2 _
    maximalTorus_isSubtorus splitTorus_le_maximalTorus

/-- Conditional assembly for an arbitrary actual root model and its arbitrary chosen base. -/
theorem model_torus_conjugate_of_matrix_centralizer_and_borel_conjugacy
    (hBorel : ∀ B C : ClosedSubgroup (Carrier (k := k)),
      IsBorelSubgroup B → IsBorelSubgroup C →
      ∃ g : Variety.Point (Carrier (k := k)), C = B.conjugate g)
    (hsolv : ∀ B : ClosedSubgroup (Carrier (k := k)), IsBorelSubgroup B →
      letI := B.carrierAlgebraicGroup
      ∀ T₁ T₂ : ClosedSubgroup B.carrierVariety,
        IsMaximalTorus T₁ → IsMaximalTorus T₂ →
        ∃ b : Variety.Point B.carrierVariety, T₂ = T₁.conjugate b)
    (M : RootSystemModel StandardRootSystem.typeF4RootPairingULift (Carrier (k := k))) :
    IsMaximalTorus (splitTorus (k := k)) ∧
      ∃ g : Variety.Point (Carrier (k := k)),
        M.torus = (splitTorus (k := k)).conjugate g := by
  have hT := splitTorus_isMaximal_of_matrix_centralizer hmat
  exact ⟨hT, TorusConjugacy.maximalTori_conjugate_of_borel_and_solvable_conjugacy
    hBorel hsolv _ _ hT M.maximalTorus⟩

omit hmat in
/-- In characteristic two the literal split torus is self-centralizing. -/
theorem splitTorus_centralizer_eq [CharP k 2] :
    (splitTorus (k := k)).centralizer.toSubgroup = (splitTorus (k := k)).toSubgroup :=
  splitTorus_centralizer_eq_of_matrix_centralizer matrix_centralizer_eq_torusElement

omit hmat in
/-- The literal rank-four split torus is maximal in the concrete F4 carrier. -/
theorem splitTorus_isMaximal [CharP k 2] :
    IsMaximalTorus (splitTorus (k := k)) :=
  splitTorus_isMaximal_of_matrix_centralizer matrix_centralizer_eq_torusElement

omit hmat in
/-- The selected containing maximal torus equals the literal split torus. -/
theorem maximalTorus_eq_splitTorus [CharP k 2] :
    maximalTorus (k := k) = splitTorus (k := k) :=
  maximalTorus_eq_splitTorus_of_matrix_centralizer matrix_centralizer_eq_torusElement

omit hmat in
/-- Every supplied F4 root model has torus conjugate to the literal split torus.
No restriction is imposed on the model's chosen base. This supplies the torus
conjugator used to transport root subgroups in GLS3 1.9.5(c). -/
theorem model_torus_conjugate [CharP k 2]
    (M : RootSystemModel StandardRootSystem.typeF4RootPairingULift (Carrier (k := k))) :
    ∃ g : Variety.Point (Carrier (k := k)),
      M.torus = (splitTorus (k := k)).conjugate g :=
  maximalTori_conjugate _ _ splitTorus_isMaximal M.maximalTorus

end Theory.AlgebraicGroup.F4Chevalley.TorusConjugacy

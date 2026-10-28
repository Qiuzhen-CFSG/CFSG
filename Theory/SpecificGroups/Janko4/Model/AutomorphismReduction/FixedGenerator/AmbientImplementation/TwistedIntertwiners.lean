module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.AmbientImplementation.Intertwiners
public import Theory.Representation.PRegularTrace

/-!
# A trace criterion for nonzero twisted J₄ intertwiners

For the literal ATLAS representation, invariance of binary matrix traces on
odd-order elements suffices to produce a nonzero intertwiner with an
automorphism twist. Irreducibility remains an explicit hypothesis.

The comparison argument works over an arbitrary field. If two irreducible
modules are inequivalent, Jacobson density supplies an algebra element acting
as the identity on the first and zero on the second. Equal trace characters
then force the first character to vanish everywhere. Here the certified product
`matrixA * matrixB` has trace one, excluding that possibility. The characteristic
two power decomposition reduces trace equality to odd-order elements, and the
resulting representation equivalence gives the required matrix equations.

This module proves a conditional criterion, not the unconditional
`generatorIntertwiners_ne_bot`: trace invariance under automorphisms fixing `a`
remains a concrete model obligation. In particular no uniqueness assertion is
inferred from GLS3, Table 5.3i, which only asserts existence of an absolutely
irreducible representation of dimension 112. The matrix data are ATLAS
`J4G1-f2r112B0`, attributed in `Janko4.Model.Data`. The source motivation is the
J₄ entry of the SQTK list and the outer-automorphism inspection in
Aschbacher–Smith, printed pp.33 and 510 of `refs/quasithin.pdf`.

The abstract comparison uses Mathlib's semisimple `jacobson_density`; the
odd-order reduction is `Representation.exists_pRegular_same_character`.
-/

open scoped MonoidAlgebra

namespace Module

variable {F A V W : Type*} [Field F] [Ring A] [Algebra F A]
  [AddCommGroup V] [AddCommGroup W] [Module F V] [Module F W]
  [Module A V] [Module A W] [IsScalarTower F A V] [IsScalarTower F A W]
  [FiniteDimensional F V] [FiniteDimensional F W]
  [IsSimpleModule A V] [IsSimpleModule A W]

include F in
/-- Inequivalent simple modules can be separated by an element of their
acting algebra, without requiring an algebraically closed scalar field. -/
private theorem exists_separating_element (hne : IsEmpty (V ≃ₗ[A] W)) :
    ∃ a : A, (∀ v : V, a • v = v) ∧ ∀ w : W, a • w = 0 := by
  classical
  have hVW (f : V →ₗ[A] W) : f = 0 := by
    by_contra hf
    exact hne.false (LinearEquiv.ofBijective f (LinearMap.bijective_of_ne_zero hf))
  have hWV (f : W →ₗ[A] V) : f = 0 := by
    by_contra hf
    exact hne.false (LinearEquiv.ofBijective f (LinearMap.bijective_of_ne_zero hf)).symm
  let : IsSemisimpleModule A (V × W) := by
    have h := IsSemisimpleModule.sup
      (IsSemisimpleModule.range (LinearMap.inl A V W))
      (IsSemisimpleModule.range (LinearMap.inr A V W))
    rw [LinearMap.sup_range_inl_inr] at h
    exact IsSemisimpleModule.congr Submodule.topEquiv.symm
  let p : Module.End F (V × W) := (LinearMap.id : V →ₗ[F] V).prodMap 0
  have hcomm (T : Module.End A (V × W)) (x : V × W) : p (T x) = T (p x) := by
    have h₁ := hWV ((LinearMap.fst A V W).comp (T.comp (LinearMap.inr A V W)))
    have h₂ := hVW ((LinearMap.snd A V W).comp (T.comp (LinearMap.inl A V W)))
    have h₁' : (T (0, x.2)).1 = 0 := DFunLike.congr_fun h₁ x.2
    have h₂' : (T (x.1, 0)).2 = 0 := DFunLike.congr_fun h₂ x.1
    have hx : x = (x.1, 0) + (0, x.2) := by simp
    change ((T x).1, 0) = T (x.1, 0)
    apply Prod.ext
    · conv_lhs => rw [hx, map_add]
      simpa using h₁'
    · exact h₂'.symm
  let p' : Module.End (Module.End A (V × W)) (V × W) :=
    { p.toAddHom with map_smul' T x := hcomm T x }
  let basis := Module.finBasis F (V × W)
  obtain ⟨a, ha⟩ := jacobson_density p' (Finset.univ.image basis)
  have he : p = (Module.toModuleEnd F (S := A) (V × W)) a := by
    apply basis.ext
    intro i
    exact ha (basis i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  refine ⟨a, fun v => ?_, fun w => ?_⟩
  · exact (congrArg Prod.fst (DFunLike.congr_fun he (v, 0))).symm
  · exact (congrArg Prod.snd (DFunLike.congr_fun he (0, w))).symm

end Module

namespace Representation

variable {F G V W : Type*} [Field F] [Monoid G]
  [AddCommGroup V] [AddCommGroup W] [Module F V] [Module F W]
  [FiniteDimensional F V] [FiniteDimensional F W]
  (ρ : Representation F G V) (σ : Representation F G W)
  [IsIrreducible ρ] [IsIrreducible σ]

/-- An equal nonzero trace character distinguishes irreducible modules even
when the characteristic divides their dimension or the group order. -/
private theorem equiv_of_equal_nonzero_trace
    (hchar : ρ.character = σ.character) (htrace : ∃ g, ρ.character g ≠ 0) :
    Nonempty (ρ.Equiv σ) := by
  classical
  by_contra hne
  have hne' : IsEmpty (ρ.asModule ≃ₗ[F[G]] σ.asModule) := by
    refine ⟨fun e => ?_⟩
    let f := (IntertwiningMap.equivLinearMapAsModule ρ σ).symm e.toLinearMap
    have hf : Function.Bijective f := e.bijective
    exact hne ⟨f.ofBijective hf⟩
  obtain ⟨a, ha, hb⟩ := Module.exists_separating_element (F := F) hne'
  have hρ : ρ.asAlgebraHom a = 1 := by
    ext v
    have h := congrArg ρ.asModuleEquiv (ha (ρ.asModuleEquiv.symm v))
    simpa only [asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply, Module.End.one_apply] using h
  have hσ : σ.asAlgebraHom a = 0 := by
    ext w
    have h := congrArg σ.asModuleEquiv (hb (σ.asModuleEquiv.symm w))
    simpa only [asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply, map_zero,
      LinearMap.zero_apply] using h
  have hlinear :
      (LinearMap.trace F V).comp ρ.asAlgebraHom.toLinearMap =
        (LinearMap.trace F W).comp σ.asAlgebraHom.toLinearMap := by
    apply MonoidAlgebra.lhom_ext'
    intro g
    apply LinearMap.ext
    intro c
    simpa only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      MonoidAlgebra.lsingle_apply, asAlgebraHom_single, map_smul, character] using congrArg (c • ·) (congrFun hchar g)
  obtain ⟨g, hg⟩ := htrace
  apply hg
  have h := DFunLike.congr_fun hlinear (a * MonoidAlgebra.single g 1)
  simpa only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul,
    asAlgebraHom_single_one, hρ, hσ, one_mul, zero_mul, map_zero, character] using h

end Representation

namespace Janko4.OuterReduction.FixedGenerator


private noncomputable def binaryRepresentation :
    Representation (ZMod 2) Model BinaryVector :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp toMatrix

set_option maxRecDepth 2048 in
private theorem binaryRepresentation_apply (g : Model) (v : BinaryVector) :
    binaryRepresentation g v = (toMatrix g).mulVec v := rfl

private theorem binaryRepresentation_character (g : Model) :
    binaryRepresentation.character g = Matrix.trace (toMatrix g) :=
  Matrix.trace_toLin'_eq _

private noncomputable def twistedRepresentation (α : MulAut Model) :
    Representation (ZMod 2) Model BinaryVector :=
  binaryRepresentation.comp α.toMonoidHom

private theorem twistedRepresentation_apply (α : MulAut Model) (g : Model) :
    twistedRepresentation α g = binaryRepresentation (α g) := rfl

private theorem twistedRepresentation_character (α : MulAut Model) (g : Model) :
    (twistedRepresentation α).character g = Matrix.trace (toMatrix (α g)) := by
  rw [Representation.character, twistedRepresentation_apply]
  exact binaryRepresentation_character (α g)

private theorem binaryRepresentation_comp_irreducible (hirr : GeneratorIrreducible)
    (α : MulAut Model) : Representation.IsIrreducible
      (twistedRepresentation α) := by
  change IsSimpleOrder (Subrepresentation (binaryRepresentation.comp α.toMonoidHom))
  refine { exists_pair_ne := ?_, eq_bot_or_eq_top := ?_ }
  · refine ⟨⊥, ⊤, ?_⟩
    intro h
    have he := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top he
  · intro S
    have hs := hirr S.toSubmodule
      (fun v hv => by
        have h := S.apply_mem_toSubmodule (α.symm a) hv
        simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          α.apply_symm_apply, binaryRepresentation_apply, toMatrix_a] using h)
      (fun v hv => by
        have h := S.apply_mem_toSubmodule (α.symm b) hv
        simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          α.apply_symm_apply, binaryRepresentation_apply, toMatrix_b] using h)
    exact hs.imp (fun h => Subrepresentation.toSubmodule_injective h)
      (fun h => Subrepresentation.toSubmodule_injective h)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
/-- A nonzero trace value in the actual binary representation, checked from
the already certified packed product of the two generators. -/
public theorem trace_matrixA_mul_matrixB : Matrix.trace (matrixA * matrixB) = 1 := by
  have h : decodeRows GeneratorCertificates.cRows = matrixA * matrixB := by
    rw [← GeneratorCertificates.product_a_b, GeneratorCertificates.decode_packedMul]
    rfl
  rw [← h]
  decide +kernel

/-- Binary trace invariance produces a nonzero intertwiner. The irreducibility
of the twist follows from that of the source and surjectivity of `α`. -/
public theorem generatorIntertwiners_ne_bot_of_trace_eq
    (hirr : GeneratorIrreducible) (α : MulAut Model)
    (htrace : ∀ g : Model, Matrix.trace (toMatrix (α g)) = Matrix.trace (toMatrix g)) :
    generatorIntertwiners α ≠ ⊥ := by
  let : Representation.IsIrreducible binaryRepresentation := by
    have h := binaryRepresentation_comp_irreducible hirr (1 : MulAut Model)
    change Representation.IsIrreducible (binaryRepresentation.comp (MonoidHom.id Model)) at h
    rwa [MonoidHom.comp_id] at h
  let : Representation.IsIrreducible (twistedRepresentation α) :=
    binaryRepresentation_comp_irreducible hirr α
  have hchar : binaryRepresentation.character =
      (twistedRepresentation α).character := by
    funext g
    rw [binaryRepresentation_character, twistedRepresentation_character]
    exact (htrace g).symm
  have hnonzero : ∃ g, binaryRepresentation.character g ≠ 0 := by
    refine ⟨a * b, ?_⟩
    rw [binaryRepresentation_character, map_mul, toMatrix_a, toMatrix_b,
      trace_matrixA_mul_matrixB]
    exact one_ne_zero
  obtain ⟨e⟩ := Representation.equiv_of_equal_nonzero_trace binaryRepresentation
    (twistedRepresentation α) hchar hnonzero
  let U : BinaryMatrix := Matrix.toLin'.symm e.toLinearEquiv.toLinearMap
  have hUL : Matrix.toLin' U = e.toLinearEquiv.toLinearMap :=
    Matrix.toLin'.apply_symm_apply _
  have hU (g : Model) : U * toMatrix g = toMatrix (α g) * U := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, hUL]
    change e.toLinearEquiv.toLinearMap * binaryRepresentation g =
      binaryRepresentation (α g) * e.toLinearEquiv.toLinearMap
    exact e.isIntertwining' g
  have hmem : U ∈ generatorIntertwiners α := by
    constructor
    · simpa only [toMatrix_a] using hU a
    · simpa only [toMatrix_b] using hU b
  have hne : U ≠ 0 := by
    intro hz
    have he : e.toLinearEquiv.toLinearMap = 0 := by
      have he := Matrix.toLin'.apply_symm_apply e.toLinearEquiv.toLinearMap
      change Matrix.toLin' U = e.toLinearEquiv.toLinearMap at he
      rw [hz, map_zero] at he
      exact he.symm
    have hz' := DFunLike.congr_fun he (1 : BinaryVector)
    have h1 : (1 : BinaryVector) = 0 := e.toLinearEquiv.injective
      (hz'.trans (e.toLinearEquiv.map_zero).symm)
    exact one_ne_zero h1
  intro hbot
  exact hne ((Submodule.mem_bot (R := ZMod 2)).mp (hbot ▸ hmem))

/-- It suffices to establish trace invariance on odd-order elements of the
actual carrier. This does not assume absolute irreducibility or a Brauer table. -/
public theorem generatorIntertwiners_ne_bot_of_odd_trace_eq
    (hirr : GeneratorIrreducible) (α : MulAut Model)
    (htrace : ∀ g : Model, Odd (orderOf g) →
      Matrix.trace (toMatrix (α g)) = Matrix.trace (toMatrix g)) :
    generatorIntertwiners α ≠ ⊥ := by
  apply generatorIntertwiners_ne_bot_of_trace_eq hirr α
  intro g
  obtain ⟨h, hreg, heq⟩ := Representation.exists_pRegular_same_character (F := ZMod 2) 2 g
  have hodd : Odd (orderOf h) :=
    Nat.not_even_iff_odd.mp (fun heven => hreg (even_iff_two_dvd.mp heven))
  calc
    Matrix.trace (toMatrix (α g)) = (twistedRepresentation α).character g :=
      (twistedRepresentation_character α g).symm
    _ = (twistedRepresentation α).character h := heq BinaryVector (twistedRepresentation α)
    _ = Matrix.trace (toMatrix (α h)) := twistedRepresentation_character α h
    _ = Matrix.trace (toMatrix h) := htrace h hodd
    _ = binaryRepresentation.character h := (binaryRepresentation_character h).symm
    _ = binaryRepresentation.character g := (heq BinaryVector binaryRepresentation).symm
    _ = Matrix.trace (toMatrix g) := binaryRepresentation_character g

end Janko4.OuterReduction.FixedGenerator

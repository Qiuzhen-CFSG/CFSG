module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Setup
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Module.Model
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.LocalCatalogue.SmallConstituents


/-!
# A natural submodule of the faithful long local action

Restrict the actual action to SL₃(4), identify its coefficient field with the
concrete quadratic field, and view the fixed space as a binary module. The
nontrivial central cubic acts nontrivially by faithfulness. Its quadratic
kernel contains a nonzero displacement and is invariant, so it contains a
minimal nonzero submodule. That submodule has binary dimension at most twelve
and satisfies the central quadratic relation.

The proved small binary SL₃(4) catalogue identifies it with the natural or
dual module, retaining an actual intertwining equivalence. Coordinatewise
field comparison transports this additive embedding to the prescribed F.
For the dual case, the literal graph element and its coordinate permutation
supply the natural embedding. No semisimplicity or decomposition is assumed.
The output is exactly the input of `Long.Module.longFrameOfNatural`; its
faithfulness premise is left to the separate source-assembly owner.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284
(PDF147–148). The reused binary catalogue proves the tensor-word and descent
steps from GLS III, §2.8; despite its historical Mathieu path, it has no
Mathieu or classification-certificate hypothesis.
-/

open Matrix
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long
open OctonionLocals ModuleModel
open PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight
open Representation
noncomputable section

private abbrev Q := Representation.SL3FourLocalCatalogue.F
private abbrev SLQ := Representation.SL3FourLocalCatalogue.SL
private abbrev z := Representation.SL3FourLocalCatalogue.z

private theorem central_cube : z ^ 3 = 1 := by decide +kernel
private theorem central_ne_one : z ≠ 1 := by
  intro h
  exact Representation.SL3FourNaturalDual.omega_ne_one
    (congrArg (fun A : SLQ => A.val 0 0) h)

private def quadraticSpace {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SLQ V) : Subrepresentation ρ where
  toSubmodule := (ρ z ^ 2 + ρ z + 1).ker
  apply_mem_toSubmodule g := by
    intro v hv
    change ρ z (ρ z v) + ρ z v + v = 0 at hv
    change ρ z (ρ z (ρ g v)) + ρ z (ρ g v) + ρ g v = 0
    have hc (w : V) : ρ z (ρ g w) = ρ g (ρ z w) := by
      change (ρ z * ρ g) w = (ρ g * ρ z) w
      rw [← map_mul, ← map_mul, Representation.SL3FourNaturalDual.centralScalar_commute]
    rw [hc, hc, ← map_add, ← map_add, hv, map_zero]

private theorem exists_small_constituent {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) SLQ V)
    (hz : ρ z ≠ 1) (hd : Module.finrank (ZMod 2) V ≤ 12) :
    ∃ (a : Representation.SL3FourLocalCatalogue.Constituent)
      (n : (Fin 3 → Q) →+ V), Function.Injective n ∧
      ∀ g v, ρ g (n v) = n (Representation.SL3FourLocalCatalogue.constituent a g v) := by
  classical
  have hex : ∃ v : V, ρ z v ≠ v := by
    by_contra! h
    exact hz (LinearMap.ext h)
  obtain ⟨v, hv⟩ := hex
  have hc : ρ z (ρ z (ρ z v)) = v := by
    change (ρ z ^ 3) v = v
    rw [← map_pow, central_cube, map_one]
    rfl
  have hne : quadraticSpace ρ ≠ ⊥ := by
    intro he
    have hmem : ρ z v - v ∈ quadraticSpace ρ := by
      change ρ z (ρ z (ρ z v - v)) + ρ z (ρ z v - v) + (ρ z v - v) = 0
      simp only [map_sub, hc]
      abel
    rw [he] at hmem
    exact hv (sub_eq_zero.mp hmem)
  obtain ⟨N, hN, hNle⟩ := (eq_bot_or_exists_atom_le (quadraticSpace ρ)).resolve_left hne
  let : IsIrreducible N.toRepresentation := (Subrepresentation.irreducible_iff_isAtom N).mpr hN
  have hq : Representation.SL3FourLocalCatalogue.CentralQuadratic N.toRepresentation := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    exact hNle w.property
  obtain ⟨a, ⟨e⟩⟩ := Representation.SL3FourLocalCatalogue.exists_constituent_equiv
    N.toRepresentation hq ((Submodule.finrank_le N.toSubmodule).trans hd)
  let n : (Fin 3 → Q) →+ V := N.toSubmodule.subtype.toAddMonoidHom.comp
    e.symm.toLinearEquiv.toAddEquiv.toAddMonoidHom
  refine ⟨a, n, Subtype.val_injective.comp e.symm.toLinearEquiv.injective, ?_⟩
  intro g w
  exact congrArg Subtype.val (LinearMap.congr_fun (e.symm.isIntertwining' g) w).symm


private theorem blockIn_injective : Function.Injective (blockIn (F := F)) := by
  intro A B h
  apply Subtype.ext
  have he := congrArg (fun x : longLocal (F := F) => peirceMatrix x.val) h
  change peirceMatrix (BlockRealization.blockHom A) =
    peirceMatrix (BlockRealization.blockHom B) at he
  simpa only [BlockRealization.peirceMatrix_blockHom] using he

private def binaryLongAction (E : LocalEmbedding) :
    Representation (ZMod 2) (longLocal (F := F)) fixedSpace where
  toFun g := (E.action g).toAddEquiv.toAddMonoidHom.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro v
    change E.action 1 v = v
    rw [map_one]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    change E.action (g * h) v = E.action g (E.action h v)
    rw [map_mul]
    rfl

private def binaryAction (E : LocalEmbedding) : Representation (ZMod 2) SLQ fixedSpace :=
  (binaryLongAction E).comp
    (blockIn.comp (Matrix.SpecialLinearGroup.map scalarFieldEquiv.symm.toRingHom))

private theorem binaryAction_injective (E : LocalEmbedding) (hf : Function.Injective E.action) :
    Function.Injective (binaryAction E) := by
  intro A B h
  have he : E.action (blockIn (Matrix.SpecialLinearGroup.map scalarFieldEquiv.symm.toRingHom A)) =
      E.action (blockIn (Matrix.SpecialLinearGroup.map scalarFieldEquiv.symm.toRingHom B)) := by
    apply LinearEquiv.ext
    intro v
    exact LinearMap.congr_fun h v
  have hm := blockIn_injective (hf he)
  apply Subtype.ext
  funext i j
  apply scalarFieldEquiv.symm.injective
  exact congrArg (fun g : SL(3,F) => g.val i j) hm

private def catalogueCoordinates : (Fin 3 → F) ≃+ (Fin 3 → Q) where
  toFun u i := scalarFieldEquiv (u i)
  invFun u i := scalarFieldEquiv.symm (u i)
  left_inv u := by funext i; exact scalarFieldEquiv.symm_apply_apply (u i)
  right_inv u := by funext i; exact scalarFieldEquiv.apply_symm_apply (u i)
  map_add' u v := by funext i; exact map_add scalarFieldEquiv (u i) (v i)

private theorem catalogueCoordinates_mulVec (A : Matrix (Fin 3) (Fin 3) F) (u : Fin 3 → F) :
    catalogueCoordinates (A *ᵥ u) = A.map scalarFieldEquiv *ᵥ catalogueCoordinates u := by
  funext i
  exact scalarFieldEquiv.toRingHom.map_mulVec A u i

private theorem scalarSL_roundtrip (A : SL(3,F)) :
    Matrix.SpecialLinearGroup.map scalarFieldEquiv.symm.toRingHom
      (Matrix.SpecialLinearGroup.map scalarFieldEquiv.toRingHom A) = A := by
  apply Subtype.ext
  funext i j
  exact scalarFieldEquiv.symm_apply_apply (A.val i j)

private theorem catalogueCoordinates_dual (A : SL(3,F)) (u : Fin 3 → F) :
    Representation.SL3FourNaturalDual.dualCoordinates
      (Matrix.SpecialLinearGroup.map scalarFieldEquiv.toRingHom A) (catalogueCoordinates u) =
        catalogueCoordinates (BlockRealization.cofactor A.val *ᵥ u) := by
  rw [catalogueCoordinates_mulVec]
  change BlockRealization.cofactor (A.val.map scalarFieldEquiv) *ᵥ catalogueCoordinates u =
    (BlockRealization.cofactor A.val).map scalarFieldEquiv *ᵥ catalogueCoordinates u
  congr 1
  rw [BlockRealization.cofactor, BlockRealization.cofactor, Matrix.transpose_map]
  exact congrArg Matrix.transpose (scalarFieldEquiv.toRingHom.map_adjugate A.val).symm

/-- Faithfulness forces an additive natural submodule with the exact block marking. -/
public theorem exists_naturalInjection_of_faithful (E : LocalEmbedding)
    (hf : Function.Injective E.action) :
    ∃ n : (Fin 3 → F) →+ fixedSpace, Function.Injective n ∧
      ∀ (A : SL(3,F)) (u : Fin 3 → F), E.action (ModuleModel.blockIn A) (n u) =
        n (A.val *ᵥ u) := by
  have hz : binaryAction E z ≠ 1 := fun h =>
    central_ne_one (binaryAction_injective E hf (h.trans (map_one (binaryAction E)).symm))
  obtain ⟨a, n, hn, he⟩ := exists_small_constituent (binaryAction E) hz
    fixedSpace_finrank_le_twelve
  let m : (Fin 3 → F) →+ fixedSpace := n.comp catalogueCoordinates.toAddMonoidHom
  have hm : Function.Injective m := hn.comp catalogueCoordinates.injective
  have hmact (A : SL(3,F)) (u : Fin 3 → F) :
      E.action (blockIn A) (m u) = n (Representation.SL3FourLocalCatalogue.constituent a
        (Matrix.SpecialLinearGroup.map scalarFieldEquiv.toRingHom A) (catalogueCoordinates u)) := by
    have h := he (Matrix.SpecialLinearGroup.map scalarFieldEquiv.toRingHom A)
      (catalogueCoordinates u)
    change E.action (blockIn (Matrix.SpecialLinearGroup.map scalarFieldEquiv.symm.toRingHom
      (Matrix.SpecialLinearGroup.map scalarFieldEquiv.toRingHom A))) (m u) = _ at h
    rwa [scalarSL_roundtrip] at h
  cases a with
  | natural =>
    refine ⟨m, hm, ?_⟩
    intro A u
    rw [hmact]
    change n (A.val.map scalarFieldEquiv *ᵥ catalogueCoordinates u) =
      n (catalogueCoordinates (A.val *ᵥ u))
    rw [catalogueCoordinates_mulVec]
  | dual =>
    have hd (A : SL(3,F)) (u : Fin 3 → F) :
        E.action (blockIn A) (m u) = m (BlockRealization.cofactor A.val *ᵥ u) := by
      rw [hmact]
      exact congrArg n (catalogueCoordinates_dual A u)
    exact ⟨graphNatural E.action m, graphNatural_injective E.action m hm,
      graphNatural_equivariant E.action m hd⟩

end
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long

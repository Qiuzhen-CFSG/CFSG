module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.ParabolicPairs.InvariantGeometry.MiddleRadical
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.ParabolicPairs.InvariantGeometry.SylowDerivedCenter.Coordinates
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.ParabolicPairs.InvariantGeometry.SylowDerivedCenter.DerivedEntries
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.ParabolicPairs.InvariantGeometry.SylowDerivedCenter.UpperSylow
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.HeckeAction.FixedSpace

/-!
# Transport of the binary degree-five Sylow derived center

Conjugation carries a subspace radical to the radical of the image subspace.
Thus a calculation of the center of the derived subgroup for one Sylow
subgroup gives the corresponding flag for every Sylow subgroup. The final
transport uses the published SL/PSL equivalences and the actual linear model
of the component.

The matrix inputs are proved in `UpperSylow` and `DerivedEntries`: the
positive-root subgroup is Sylow, and its derived center has exactly the four
rectangular entries described by `FiveRectangle`. The final theorem
`exists_middle_pair_of_five_sylow` combines them with the geometric transport
to identify Z(T′) with the radical intersection for a two-space contained
in a three-space, for every Sylow two-subgroup of the component.

Source: Aschbacher–Smith 2.3.9(7), printed pp.525–526; the invariant-parabolic
convention appears on printed p.216.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary
open Subgroup

theorem conjugate_radical_five (a : BinaryLinear.GL (Vector 5)) (W : Space 5) :
    (BinaryLinear.radical W).map (MulAut.conj a).toMonoidHom =
      BinaryLinear.radical (W.map a.toLinearMap) := by
  calc
    _ = (BinaryLinear.radical W).comap (MulAut.conj a).symm.toMonoidHom :=
      Subgroup.map_equiv_eq_comap_symm (MulAut.conj a) _
    _ = _ := ?_
  ext g
  change ((∀ v ∈ W, a.symm (g (a v)) = v) ∧
    ∀ v, a.symm (g (a v)) - v ∈ W) ↔
    ((∀ v ∈ W.map a.toLinearMap, g v = v) ∧
    ∀ v, g v - v ∈ W.map a.toLinearMap)
  constructor
  · rintro ⟨hf, hd⟩
    constructor
    · rintro v ⟨w, hw, rfl⟩
      simpa using congrArg a (hf w hw)
    · intro v
      rw [Submodule.mem_map_equiv]
      simpa using hd (a.symm v)
  · rintro ⟨hf, hd⟩
    constructor
    · intro v hv
      have h := hf (a v) (Submodule.mem_map_of_mem hv)
      simpa using congrArg a.symm h
    · intro v
      have h := hd (a v)
      rw [Submodule.mem_map_equiv] at h
      simpa using h

/-- Sylow conjugacy transports the standard rectangular derived-center calculation. -/
theorem exists_middle_pair_of_linear_sylow
    (U S : Sylow 2 (BinaryLinear.GL (Vector 5)))
    (hU : derivedCenter (U : Subgroup _) =
      BinaryLinear.radical (fivePrefix 2) ⊓ BinaryLinear.radical (fivePrefix 3)) :
    ∃ W₂ W₃ : Space 5, Module.finrank (ZMod 2) W₂ = 2 ∧
      Module.finrank (ZMod 2) W₃ = 3 ∧ W₂ ≤ W₃ ∧
      derivedCenter (S : Subgroup _) = BinaryLinear.radical W₂ ⊓ BinaryLinear.radical W₃ := by
  let : Finite (BinaryLinear.GL (Vector 5)) :=
    Finite.of_injective (fun g : BinaryLinear.GL (Vector 5) => (g : Vector 5 → Vector 5))
      DFunLike.coe_injective
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq (BinaryLinear.GL (Vector 5)) U S
  refine ⟨(fivePrefix 2).map a.toLinearMap, (fivePrefix 3).map a.toLinearMap, ?_, ?_, ?_, ?_⟩
  · rw [a.finrank_map_eq, fivePrefix_finrank 2 (by decide)]
  · rw [a.finrank_map_eq, fivePrefix_finrank 3 (by decide)]
  · exact Submodule.map_mono (fivePrefix_mono (by decide : 2 ≤ 3))
  · have hs : (S : Subgroup _) = (U : Subgroup _).map (MulAut.conj a).toMonoidHom := by
      rw [← ha]
      rfl
    rw [hs, ← derivedCenter_map, hU,
      Subgroup.map_inf _ _ _ (MulAut.conj a).injective,
      conjugate_radical_five, conjugate_radical_five]

/-- Conditional assembly from the Sylow property and the four-entry matrix calculation. -/
theorem exists_middle_pair_of_five_matrix_calculation
    {G : Type*} [Group G] {L : Subgroup G} (e : L ≃* PSL 5) (T : Sylow 2 L)
    (U : Sylow 2 (SL 5))
    (hU : (U : Subgroup (SL 5)) =
      Representation.SL5TenDimensional.Classification.HeckeAction.upperRootSubgroup)
    (hZ : ∀ A : SL 5, A ∈ derivedCenter
      Representation.SL5TenDimensional.Classification.HeckeAction.upperRootSubgroup ↔
        FiveRectangle A) :
    ∃ W₂ W₃ : Space 5, Module.finrank (ZMod 2) W₂ = 2 ∧
      Module.finrank (ZMod 2) W₃ = 3 ∧ W₂ ≤ W₃ ∧
      derivedCenter (T : Subgroup L) = subspaceRadical e W₂ ⊓ subspaceRadical e W₃ := by
  let : Finite L := Finite.of_injective e e.injective
  let U' := U.mapSurjective (f := (slEquivLinear 5).toMonoidHom) (slEquivLinear 5).surjective
  let T' := T.mapSurjective (f := (linearModel e).toMonoidHom) (linearModel e).surjective
  have hU' : derivedCenter (U' : Subgroup _) =
      BinaryLinear.radical (fivePrefix 2) ⊓ BinaryLinear.radical (fivePrefix 3) := by
    change derivedCenter ((U : Subgroup (SL 5)).map (slEquivLinear 5).toMonoidHom) = _
    rw [← derivedCenter_map, hU]
    ext g
    rw [Subgroup.mem_map_equiv, hZ, fiveRectangle_iff_radical, MulEquiv.apply_symm_apply]
  obtain ⟨W₂, W₃, h₂, h₃, h₂₃, hQ⟩ := exists_middle_pair_of_linear_sylow U' T' hU'
  refine ⟨W₂, W₃, h₂, h₃, h₂₃, ?_⟩
  have hm : (derivedCenter (T : Subgroup L)).map (linearModel e).toMonoidHom =
      BinaryLinear.radical W₂ ⊓ BinaryLinear.radical W₃ := by
    rw [derivedCenter_map]
    exact hQ
  ext x
  change (x ∈ derivedCenter (T : Subgroup L)) ↔
    linearModel e x ∈ BinaryLinear.radical W₂ ⊓ BinaryLinear.radical W₃
  have h := congrArg (fun K : Subgroup (BinaryLinear.GL (Vector 5)) => linearModel e x ∈ K) hm
  simpa only [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] using Iff.of_eq h

/-- Every Sylow two-subgroup of a component isomorphic to PSL₅(2) has derived
center equal to the radical intersection of a two-space and a containing
three-space in its actual linear model. -/
theorem exists_middle_pair_of_five_sylow
    {G : Type*} [Group G] {L : Subgroup G} (e : L ≃* PSL 5) (T : Sylow 2 L) :
    ∃ W₂ W₃ : Space 5, Module.finrank (ZMod 2) W₂ = 2 ∧
      Module.finrank (ZMod 2) W₃ = 3 ∧ W₂ ≤ W₃ ∧
      derivedCenter (T : Subgroup L) = subspaceRadical e W₂ ⊓ subspaceRadical e W₃ := by
  obtain ⟨U, hU⟩ := exists_five_upperRoot_sylow
  exact exists_middle_pair_of_five_matrix_calculation e T U hU
    mem_derivedCenter_upperRootSubgroup_iff_fiveRectangle

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary

end

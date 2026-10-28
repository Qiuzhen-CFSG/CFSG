module

public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceFourActors.Marking
/-!
# The two source outer-involution classes and their diagonal modules

The exceptional comparison transports the actual relative centralizers
C_L(t), giving S₆ and C₂ × S₄. Restriction of the same module equivalence
constructs the literal map u ↦ u + t.u on the original natural summand.
It is equivariant for the source layer centralizer, and its image equals
the actual displacement image [V,t].

Source: Aschbacher–Smith, H.9.3(1–2), printed p.391.
-/

@[expose] public section
open BinaryNaturalDual BinaryNaturalDual.ModelOrbits Theory.GroupTheory
namespace CFSG.Quasithin.ChapterH.NaturalDual.SourceFourActors
variable {M V : Type*} [Group M] [AddCommGroup V] [Module (ZMod 2) V]
  (S : SourceSetup 4 M V) (T : Sylow 2 M)
noncomputable def transposition : M := (group S T).symm BinaryNaturalDual.FourActors.transposition
noncomputable def tripleTransposition : M := (group S T).symm BinaryNaturalDual.FourActors.tripleTransposition

def innerCentralizer (a : M) : Subgroup M :=
  componentLayer M ⊓ Subgroup.centralizer ({a} : Set M)

theorem innerCentralizer_map (a : M) :
    (innerCentralizer a).map (group S T).toMonoidHom = BinaryNaturalDual.FourActors.innerCentralizer (group S T a) := by
  ext b
  constructor
  · rintro ⟨g,hg,rfl⟩
    refine ⟨(group_inner_iff S T g).mpr hg.1, ?_⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    change group S T g * group S T a = group S T a * group S T g
    simpa only [map_mul] using congrArg (group S T) (Subgroup.mem_centralizer_singleton_iff.mp hg.2)
  · intro hb
    refine ⟨(group S T).symm b, ?_, (group S T).apply_symm_apply b⟩
    constructor
    · exact (group_inner_iff S T _).mp (by simpa using hb.1)
    · apply Subgroup.mem_centralizer_singleton_iff.mpr
      apply (group S T).injective
      simpa only [map_mul, MulEquiv.apply_symm_apply] using Subgroup.mem_centralizer_singleton_iff.mp hb.2

noncomputable def innerCentralizerEquiv (a : M) :
    innerCentralizer a ≃* BinaryNaturalDual.FourActors.innerCentralizer (group S T a) :=
  ((group S T).subgroupMap (innerCentralizer a)).trans
    (MulEquiv.subgroupCongr (innerCentralizer_map S T a))

theorem outer_involution_catalogue :
    (orderOf (transposition S T) = 2 ∧ transposition S T ∉ componentLayer M) ∧
    (orderOf (tripleTransposition S T) = 2 ∧ tripleTransposition S T ∉ componentLayer M) ∧
    (∀ a : M, orderOf a = 2 → a ∉ componentLayer M →
      IsConj a (transposition S T) ∨ IsConj a (tripleTransposition S T)) ∧
    ¬ IsConj (transposition S T) (tripleTransposition S T) ∧
    Nonempty (innerCentralizer (transposition S T) ≃* Equiv.Perm (Fin 6)) ∧
    Nonempty (innerCentralizer (tripleTransposition S T) ≃*
      (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))) := by
  have ht : group S T (transposition S T) = BinaryNaturalDual.FourActors.transposition := (group S T).apply_symm_apply _
  have hu : group S T (tripleTransposition S T) = BinaryNaturalDual.FourActors.tripleTransposition := (group S T).apply_symm_apply _
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [← (group S T).orderOf_eq, ht]; exact BinaryNaturalDual.FourActors.transposition_order
  · intro h; exact BinaryNaturalDual.FourActors.transposition_outer (ht ▸ (group_inner_iff S T _).mpr h)
  · rw [← (group S T).orderOf_eq, hu]; exact BinaryNaturalDual.FourActors.tripleTransposition_order
  · intro h; exact BinaryNaturalDual.FourActors.tripleTransposition_outer (hu ▸ (group_inner_iff S T _).mpr h)
  · intro a ha hout
    have hc := BinaryNaturalDual.FourActors.outer_involution_conjugacy (group S T a)
      (((group S T).orderOf_eq a).trans ha)
      (fun h => hout ((group_inner_iff S T a).mp h))
    rcases hc with h | h
    · exact Or.inl (by simpa [transposition] using (group S T).symm.toMonoidHom.map_isConj h)
    · exact Or.inr (by simpa [tripleTransposition] using (group S T).symm.toMonoidHom.map_isConj h)
  · intro h
    exact BinaryNaturalDual.FourActors.not_isConj_representatives (by simpa only [MulEquiv.coe_toMonoidHom, ht,hu] using (group S T).toMonoidHom.map_isConj h)
  · exact ⟨(innerCentralizerEquiv S T _).trans
      ((MulEquiv.subgroupCongr (congrArg BinaryNaturalDual.FourActors.innerCentralizer ht)).trans BinaryNaturalDual.FourActors.PermutationCatalogue.transpositionCentralizerEquiv)⟩
  · exact ⟨(innerCentralizerEquiv S T _).trans
      ((MulEquiv.subgroupCongr (congrArg BinaryNaturalDual.FourActors.innerCentralizer hu)).trans BinaryNaturalDual.FourActors.PermutationCatalogue.tripleTranspositionCentralizerEquiv)⟩

theorem outer_involution_cycleType (a : M) (ha : orderOf a = 2) (hout : a ∉ componentLayer M) :
    (permutation S T a).cycleType = {2} ∨ (permutation S T a).cycleType = {2,2,2} :=
  BinaryNaturalDual.FourActors.outer_involution_cycleType _ (((group S T).orderOf_eq a).trans ha)
    (fun h => hout ((group_inner_iff S T a).mp h))

noncomputable def diagonalEquiv (a : M) (ha : orderOf a = 2) (hout : a ∉ componentLayer M) :
    S.natural ≃ₗ[ZMod 2] elementFixed S a := by
  have h2 : (group S T a)^2 = 1 := by
    rw [← map_pow, show a^2 = 1 by simpa only [ha] using pow_orderOf_eq_one a, map_one]
  exact (naturalCoordinates S T).trans
    ((BinaryNaturalDual.FourActors.outerDiagonalEquiv (AutomorphismModel.coordinateAction S.degree) (group S T a) h2
      (fun h => hout ((group_inner_iff S T a).mp h))).trans
      ((coordinates S T).ofSubmodules _ _ (elementFixed_map S T a)).symm)

theorem diagonalEquiv_apply (a : M) (ha : orderOf a = 2) (hout : a ∉ componentLayer M)
    (u : S.natural) : (diagonalEquiv S T a ha hout u : V) = u + S.representation a u := by
  apply (coordinates S T).injective
  simp only [diagonalEquiv, LinearEquiv.trans_apply, LinearEquiv.ofSubmodules_symm_apply,
    LinearEquiv.apply_symm_apply, BinaryNaturalDual.FourActors.outerDiagonalEquiv_apply, map_add,
    equivariant, natural_marking]

theorem diagonalEquiv_equivariant (a : M) (ha : orderOf a = 2) (hout : a ∉ componentLayer M)
    (l : componentLayer M) (hl : Commute (l : M) a) (u : S.natural) :
    (diagonalEquiv S T a ha hout
      ((naturalCoordinates S T).symm (layerCoordinates S T l (naturalCoordinates S T u))) : V) =
      S.representation l (diagonalEquiv S T a ha hout u : V) := by
  rw [diagonalEquiv_apply, diagonalEquiv_apply, ← natural_action S T, map_add]
  congr 1
  exact congrArg (fun f : Module.End (ZMod 2) V => f u) (hl.map S.representation).eq.symm

include T in
theorem outer_fixed_eq_displacement (a : M) (ha : orderOf a = 2) (hout : a ∉ componentLayer M) :
    elementFixed S a = LinearMap.range (S.representation a - LinearMap.id) := by
  have h2 : (group S T a)^2 = 1 := by
    rw [← map_pow, show a^2 = 1 by simpa only [ha] using pow_orderOf_eq_one a, map_one]
  have hc := BinaryNaturalDual.FourActors.outer_fixedSpace_eq_displacement (AutomorphismModel.coordinateAction S.degree)
    (group S T a) h2 (fun h => hout ((group_inner_iff S T a).mp h))
  ext v
  have he : v ∈ elementFixed S a ↔ coordinates S T v ∈
      BinaryNaturalDual.fixedSpace (BinaryNaturalDual.FourActors.action (AutomorphismModel.coordinateAction S.degree) (group S T a)) := by
    rw [← elementFixed_map, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
  rw [he,hc]
  constructor
  · rintro ⟨w,hw⟩
    refine ⟨(coordinates S T).symm w, ?_⟩
    apply (coordinates S T).injective
    simpa only [LinearMap.sub_apply, LinearMap.id_apply, map_sub, equivariant,
      LinearEquiv.apply_symm_apply] using hw
  · rintro ⟨w,rfl⟩
    refine ⟨coordinates S T w, ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub, equivariant]

include T in
theorem outer_fixed_finrank (a : M) (ha : orderOf a = 2) (hout : a ∉ componentLayer M) :
    Module.finrank (ZMod 2) (elementFixed S a) = 4 := by
  rw [← (diagonalEquiv S T a ha hout).finrank_eq, (naturalCoordinates S T).finrank_eq]
  simp [BinaryNaturalDual.FourActors.X, BinaryLinear.OuterCyclic.Space]
end CFSG.Quasithin.ChapterH.NaturalDual.SourceFourActors

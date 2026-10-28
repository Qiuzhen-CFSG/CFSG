module

public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.SylowOvergroups.Sylow
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.SylowOvergroups.Bruhat
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.SylowOvergroups.StandardOvergroups

/-!
# Sylow overgroups are actual binary five-dimensional flag stabilizers

Every Sylow two-subgroup is the stabilizer of a complete flag in an actual
basis: conjugate the explicit standard Sylow and transport that basis.
Concrete Bruhat factorization and standard Borel overgroup exhaustion then
show that every subgroup containing a Sylow two-subgroup is the stabilizer
of a partial flag in the transported basis. The empty partial flag handles
the whole group, so no properness or maximality hypothesis is required.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), A.3.12,
printed pp.47--48, especially the characteristic-two parabolic argument on
p.48, and the L₅(2) branch of 1.3.9, printed p.514.
-/

@[expose] public section

namespace BinaryLinear.FiveFlagGeometry
open OuterCyclic SylowOvergroups

/-- Every Sylow two-subgroup stabilizes a complete flag in an actual basis. -/
theorem sylow_eq_flagStabilizer (T : Sylow 2 (LinearGroup 5)) :
    ∃ b : FiveBasis, (T : Subgroup (LinearGroup 5)) = flagStabilizer b Set.univ := by
  let : Finite (LinearGroup 5) :=
    Finite.of_injective (fun g : LinearGroup 5 => (g : Space 5 → Space 5))
      DFunLike.coe_injective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (LinearGroup 5) standardSylow T
  have hmap : standardBorel.map (MulAut.conj g).toMonoidHom =
      (T : Subgroup (LinearGroup 5)) := by
    change ((g • standardSylow : Sylow 2 (LinearGroup 5)) : Subgroup (LinearGroup 5)) = _
    rw [hg]
  refine ⟨standardBasis.map g, ?_⟩
  exact hmap.symm.trans (flagStabilizer_map_conj standardBasis Set.univ g)

/-- The empty flag accounts for the whole group. -/
theorem isFlagParabolic_top : IsFlagParabolic (⊤ : Subgroup (LinearGroup 5)) :=
  ⟨standardBasis, ∅, (flagStabilizer_empty standardBasis).symm⟩

/-- Transport standard-coordinate exhaustion to arbitrary Sylow overgroups. -/
theorem isFlagParabolic_of_standard_overgroups
    (hstandard : ∀ Q : Subgroup (LinearGroup 5), standardBorel ≤ Q →
      ∃ cuts : Set (Fin 4), Q = flagStabilizer standardBasis cuts)
    (T : Sylow 2 (LinearGroup 5)) (P : Subgroup (LinearGroup 5))
    (hTP : (T : Subgroup (LinearGroup 5)) ≤ P) : IsFlagParabolic P := by
  let : Finite (LinearGroup 5) :=
    Finite.of_injective (fun g : LinearGroup 5 => (g : Space 5 → Space 5))
      DFunLike.coe_injective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (LinearGroup 5) standardSylow T
  have hmap : standardBorel.map (MulAut.conj g).toMonoidHom =
      (T : Subgroup (LinearGroup 5)) := by
    change ((g • standardSylow : Sylow 2 (LinearGroup 5)) : Subgroup (LinearGroup 5)) = _
    rw [hg]
  let Q := P.map (MulAut.conj g).symm.toMonoidHom
  have hBQ : standardBorel ≤ Q := by
    intro u hu
    apply Subgroup.mem_map_equiv.mpr
    apply hTP
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
  obtain ⟨cuts, hQ⟩ := hstandard Q hBQ
  have hPQ : Q.map (MulAut.conj g).toMonoidHom = P :=
    (Subgroup.map_symm_eq_iff_map_eq Q (e := MulAut.conj g) (H := P)).mp rfl
  refine ⟨standardBasis.map g, cuts, ?_⟩
  rw [← hPQ, hQ, flagStabilizer_map_conj]

/-- Every subgroup containing a Sylow two-subgroup is the stabilizer of an
actual partial flag. The empty flag includes the whole group. -/
theorem isFlagParabolic_of_sylow_le
    (T : Sylow 2 (LinearGroup 5)) (P : Subgroup (LinearGroup 5))
    (hTP : (T : Subgroup (LinearGroup 5)) ≤ P) : IsFlagParabolic P :=
  isFlagParabolic_of_standard_overgroups
    (standard_overgroups_of_bruhat hasBruhatDecomposition) T P hTP

end BinaryLinear.FiveFlagGeometry

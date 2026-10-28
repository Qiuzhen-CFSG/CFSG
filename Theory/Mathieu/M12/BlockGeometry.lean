module

public import Theory.Mathieu.M12.BlockGeometry.Defs
public import Theory.Mathieu.M12.BlockGeometry.SecondSquareControl
public import Theory.Mathieu.M12.SmallParabolicPair.NormalFour
public import Theory.Mathieu.M12.ValueBoundParabolics
public import Theory.Mathieu.M12.Properties.AutCover
public import Theory.Quasithin.EvenCharacteristic

/-!
# Invariant second-parabolic geometry in M₁₂

The unique normal elementary four in the marked Sylow subgroup is preserved
by every automorphism stabilizing that Sylow subgroup. Its normalizer, the
literal second parabolic, is therefore invariant as well. The established
square control supplies its self-centralizing two-core.

An automorphism fixing the marked Sylow subgroup pointwise is either the
identity or conjugation by the distinguished involution. In the latter case
its fixed subgroup is the first parabolic, which generates M₁₂ with the
second. Sylow conjugacy transports the subgroup, its model isomorphism,
stabilizer invariance and fixed-subgroup generation together. This constructs
`Geometry` without a block-obstruction premise; central-cover and component
orbit transport remain with its consumers.

Source: Aschbacher–Smith, 2.3.9(7), printed p.526, and GLS3, Table 5.3b.
The existing marked permutations and their checked local calculations are
reused from `SmallParabolicPair`, which retains their source attribution.
-/

public section
open Subgroup
namespace Sporadic.Mathieu.M12SmallPair.BlockGeometry
noncomputable section

/-- The Sylow stabilizer preserves the actual natural four, by its uniqueness
as a normal elementary subgroup of order four in the marked Sylow subgroup. -/
theorem natural_invariant (β : MulAut M12)
    (hβ : sylowCandidate.map β.toMonoidHom = sylowCandidate) :
    natural.map β.toMonoidHom = natural := by
  let : IsKleinFour natural := natural_kleinFour
  let : IsElementaryAbelian 2 natural :=
    { toIsMulCommutative := IsKleinFour.isMulCommutative
      exponent_dvd_p := by simp }
  let : IsElementaryAbelian 2 (natural.map β.toMonoidHom) :=
    IsElementaryAbelian.map β.toMonoidHom
  apply normal_four_eq_natural
  · exact (Nat.card_congr (β.subgroupMap natural).toEquiv).symm.trans card_natural
  · rw [← hβ]
    exact map_mono (natural_le_core.trans core_le_sylowCandidate)
  · rw [← hβ]
    exact (map_mono (show sylowCandidate ≤ normalizer (natural : Set M12)
      from inf_le_right)).trans (le_normalizer_map β.toMonoidHom)

/-- The full automorphism stabilizer of the marked Sylow subgroup preserves
the second parabolic, the normalizer of the natural four. -/
theorem secondParabolic_invariant (β : MulAut M12)
    (hβ : sylowCandidate.map β.toMonoidHom = sylowCandidate) :
    secondParabolic.map β.toMonoidHom = secondParabolic := by
  change (normalizer (natural : Set M12)).map β.toMonoidHom =
    normalizer (natural : Set M12)
  rw [map_equiv_normalizer_eq, natural_invariant β hβ]

/-- The fixed subgroup of every pointwise Sylow fixer generates M₁₂ with
the second parabolic. For the nonidentity fixer this is the marked pair. -/
theorem marked_generated (α : MulAut M12)
    (hα : ∀ r ∈ sylowCandidate, α r = r) :
    α.fixedSubgroup ⊔ secondParabolic = ⊤ := by
  rcases SylowAutomorphisms.eq_one_or_conj_of_fixes_sylow α hα with rfl | rfl
  · have htop : (1 : MulAut M12).fixedSubgroup = ⊤ := by
      ext x
      simp
    rw [htop, top_sup_eq]
  · have hfixed : (MulAut.conj z).fixedSubgroup = firstParabolic := by
      ext x
      rw [MulAut.mem_fixedSubgroup]
      change z * x * z⁻¹ = x ↔ x ∈ centralizer ({z} : Set M12)
      rw [mem_centralizer_singleton_iff]
      exact mul_inv_eq_iff_eq_mul.trans eq_comm
    rw [hfixed, ValueBoundParabolics.parabolic_sup_eq_top]

private theorem map_pullback (e β : MulAut M12) (U : Subgroup M12) :
    U.map (e.trans (β.trans e.symm)).toMonoidHom =
      ((U.map e.toMonoidHom).map β.toMonoidHom).map e.symm.toMonoidHom := by
  rw [map_map, map_map]
  rfl

/-- The invariant seed for any prescribed Sylow subgroup and pointwise fixer.
The subgroup and all its markings are transported by the same conjugation. -/
theorem seed_of_fixes_sylow (R : Sylow 2 M12) (α : MulAut M12)
    (hα : ∀ r ∈ (R : Subgroup M12), α r = r) : Nonempty (LocalSeed R α) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M12 commonSylow R
  let e := MulAut.conj g
  have hR : sylowCandidate.map e.toMonoidHom = (R : Subgroup M12) := by
    change ((g • commonSylow : Sylow 2 M12) : Subgroup M12) = R
    rw [hg]
  have hRinv : (R : Subgroup M12).map e.symm.toMonoidHom = sylowCandidate := by
    rw [← hR]
    simp [map_map]
  let a : MulAut M12 := e.trans (α.trans e.symm)
  have ha : ∀ r ∈ sylowCandidate, a r = r := by
    intro r hr
    have hm : e r ∈ (R : Subgroup M12) := hR ▸ mem_map_of_mem e.toMonoidHom hr
    change e.symm (α (e r)) = r
    rw [hα _ hm, e.symm_apply_apply]
  refine ⟨{
    localSubgroup := secondParabolic.map e.toMonoidHom
    modelIso := (e.subgroupMap secondParabolic).symm
    sylow_le := ?_
    invariant := ?_
    selfCentralizing := ?_
    generated := ?_
  }⟩
  · rw [← hR]
    exact map_mono (show sylowCandidate ≤ secondParabolic from inf_le_right)
  · intro β hβ
    let b : MulAut M12 := e.trans (β.trans e.symm)
    have hb : sylowCandidate.map b.toMonoidHom = sylowCandidate := by
      rw [map_pullback, hR, hβ, hRinv]
    apply map_injective (f := e.symm.toMonoidHom) e.symm.injective
    calc
      ((secondParabolic.map e.toMonoidHom).map β.toMonoidHom).map e.symm.toMonoidHom =
          secondParabolic.map b.toMonoidHom := (map_pullback e β secondParabolic).symm
      _ = secondParabolic := secondParabolic_invariant b hb
      _ = (secondParabolic.map e.toMonoidHom).map e.symm.toMonoidHom := by simp [map_map]
  · exact (Theory.Quasithin.centralizer_pCore_map_le_iff 2 e secondParabolic).mpr
      SecondSquareControl.control.selfCentralizingCore
  · have hfixed : a.fixedSubgroup.map e.toMonoidHom = α.fixedSubgroup := by
      ext x
      rw [mem_map_equiv, MulAut.mem_fixedSubgroup, MulAut.mem_fixedSubgroup]
      change e.symm (α (e (e.symm x))) = e.symm x ↔ α x = x
      rw [e.apply_symm_apply]
      exact e.symm.injective.eq_iff
    rw [← hfixed, ← Subgroup.map_sup, marked_generated a ha,
      map_top_of_surjective _ e.surjective]

/-- The unconditional M₁₂ model geometry for the source block argument. -/
theorem geometry : Geometry where
  center_eq_bot := m12_center_eq_bot
  seed R α _ _ hα := seed_of_fixes_sylow R α hα

end
end Sporadic.Mathieu.M12SmallPair.BlockGeometry

end

module
public import Theory.GroupAction.HexagonReflections
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# Reflections normalizing the actual apartment fixer

Agreement on seven successive edges of a twelve-cycle forces agreement on
the whole cycle. Thus its pointwise fixer is exactly the seven-path fixer.
The Schur--Zassenhaus lift of the cycle action normalizes this same subgroup;
the two lifted reflections retain this information along with their orders
and endpoint action. This is the common subgroup needed to compare their
preimages in a marked amalgam.

Source: Aschbacher--Smith F.4.15--16, printed pp.281--282.
-/

@[expose] public noncomputable section
open SimpleGraph SimpleGraph.PathTransitivePolygon Fin.NatCast Subgroup
namespace GroupAction.HexagonReflections
variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

/-- The pointwise fixer of the actual labelled twelve-cycle. -/
def cycleFixer (f : Fin 12 → V) : Subgroup G :=
  fixingSubgroup G (Set.range f)

@[simp] theorem mem_cycleFixer (f : Fin 12 → V) (g : G) :
    g ∈ cycleFixer (G := G) f ↔ ∀ i, g • f i = f i := by
  simp only [cycleFixer, mem_fixingSubgroup_iff, Set.forall_mem_range]

/-- Seven consecutive edges determine the entire pointwise cycle fixer. -/
theorem mem_cycleFixer_iff_seven
    (act : GraphAction Γ G)
    (hg : ∀ v (p : Γ.Walk v v), p.IsCycle → 12 ≤ p.length)
    (f : cycleGraph 12 →g Γ) (hf : Function.Injective f) (g : G) :
    g ∈ cycleFixer (G := G) f ↔
      ∀ i : Fin 8, g • f (↑i.val : Fin 12) = f (↑i.val : Fin 12) := by
  rw [mem_cycleFixer]
  constructor
  · intro h i
    exact h _
  · intro h
    apply extend_agreement act hg f f hf hf 0 g
    simpa only [zero_add] using h

/-- Every permutation of this cycle normalizes its pointwise fixer. -/
theorem normalizes_cycleFixer (f : Fin 12 → V) (r : Equiv.Perm (Fin 12))
    (g : G) (hg : ∀ i, g • f i = f (r i)) :
    g ∈ normalizer (cycleFixer (G := G) f : Set G) := by
  have hi (i : Fin 12) : g⁻¹ • f i = f (r.symm i) := by
    rw [inv_smul_eq_iff, hg, r.apply_symm_apply]
  apply mem_normalizer_iff.mpr
  intro x
  simp only [mem_cycleFixer]
  constructor
  · intro hx i
    rw [mul_smul, mul_smul, hi, hx, hg, r.apply_symm_apply]
  · intro hx i
    have h := hx (r i)
    rw [mul_smul, mul_smul, hi, r.symm_apply_apply, ← hg] at h
    exact (MulAction.injective g) h

/-- The lifted dihedral action retains normalization of the same pointwise
cycle fixer, not just its action on the two endpoint vertices. -/
theorem exists_normalizing_reflections
    (act : GraphAction Γ G)
    (hg : ∀ v (p : Γ.Walk v v), p.IsCycle → 12 ≤ p.length)
    (htrans : ∀ v, RootPathTransitive Γ G v 7)
    (f : cycleGraph 12 →g Γ) (hf : Function.Injective f)
    (hcop : (Nat.card (cycleFixer (G := G) f)).Coprime 12) :
    ∃ s t : G, s^2=1 ∧ t^2=1 ∧ (s*t)^6=1 ∧
      s • f 0=f 0 ∧ s • f 1≠f 1 ∧ t • f 1=f 1 ∧ t • f 0≠f 0 ∧
      s ∈ normalizer (cycleFixer (G := G) f : Set G) ∧
      t ∈ normalizer (cycleFixer (G := G) f : Set G) := by
  have hlift (a : ZMod 6) (i : Fin 12) (hi : polygonAction (.sr a) i=i) :
      ∃ g : G, ∀ j, g • f j=f (polygonAction (.sr a) j) :=
    lift_fixed_cycle_automorphism act hg htrans f hf
      (GroupAction.DihedralPolygon.CycleAutomorphisms.graphAutEquivIso _
        (GroupAction.DihedralPolygon.CycleAutomorphisms.dihedralHom (by decide) (.sr a)).val) i hi
  obtain ⟨d,hd⟩ := exists_dihedral_lift (G := G) f
    (hlift 0 0 rfl) (hlift (-1) 1 (by decide +kernel))
    (cycleFixer f) (fun g h => (mem_cycleFixer f g).mpr h) hcop
  refine ⟨d (.sr 0),d (.sr (-1)),?_,?_,?_,?_,?_,?_,?_,
    normalizes_cycleFixer f _ _ (hd (.sr 0)),
    normalizes_cycleFixer f _ _ (hd (.sr (-1)))⟩
  · rw [←map_pow]; simp only [DihedralGroup.sr_mul_sr,sub_self,DihedralGroup.r_zero,pow_two,map_one]
  · rw [←map_pow]; simp only [DihedralGroup.sr_mul_sr,sub_self,DihedralGroup.r_zero,pow_two,map_one]
  · rw [←map_mul,←map_pow]
    have h : ((DihedralGroup.sr 0 : DihedralGroup 6)*.sr (-1))^6=1 := by decide +kernel
    rw [h,map_one]
  · exact hd (.sr 0) 0
  · rw [hd]
    exact hf.ne (by decide : polygonAction (.sr 0) 1≠1)
  · simpa only [show polygonAction (.sr (-1)) 1=1 from by decide +kernel] using hd (.sr (-1)) 1
  · rw [hd]
    exact hf.ne (by decide : polygonAction (.sr (-1)) 0≠0)

end GroupAction.HexagonReflections

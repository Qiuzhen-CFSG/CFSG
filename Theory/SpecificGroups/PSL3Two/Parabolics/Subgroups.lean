module

public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups.Bruhat
public import Mathlib.Algebra.Group.Subgroup.Order
/-!
# The parabolic subgroup lattice of PSL₃(2)

The stabilizers of the incident flag e₀ ⊂ {v | v₂ = 0} are distinct maximal
subgroups of order 24. Their intersection has order eight and is a Sylow
2-subgroup. They are exactly the maximal overgroups of this Sylow subgroup.
Conjugation transports this description to every Sylow 2-subgroup.

The proof uses the binary Bruhat decomposition: an overgroup of the upper
triangular subgroup escaping both parabolics contains both simple reflections,
and hence the whole group. The quotient map SL₃(2) → PSL₃(2) is the actual
isomorphism used to transport all coordinate subgroups.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.5.3–4,
printed pp. 419–420 (the rank-two projective-plane local model).
-/

@[expose] public section

namespace Matrix.PSL3Two

private theorem point_reflection_of_not_le (H : Subgroup SL) (hB : borelSL ≤ H)
    (hP : ¬ H ≤ pointParabolicSL) : Bruhat.perm 2 ∈ H := by
  classical
  obtain ⟨g, hg, hgp⟩ := SetLike.not_le_iff_exists.mp hP
  obtain ⟨i, j, k, h⟩ := Bruhat.decomposition g
  have hi := hB (Bruhat.upper_mem i)
  have hk := hB (Bruhat.upper_mem k)
  have hj : Bruhat.perm j ∈ H :=
    (H.mul_mem_cancel_left hi).mp ((H.mul_mem_cancel_right hk).mp (h ▸ hg))
  apply Bruhat.point_reflection_mem H hB j hj
  intro hp
  apply hgp
  rw [h]
  exact pointParabolicSL.mul_mem
    (pointParabolicSL.mul_mem (Bruhat.upper_mem i).1 hp) (Bruhat.upper_mem k).1

private theorem line_reflection_of_not_le (H : Subgroup SL) (hB : borelSL ≤ H)
    (hP : ¬ H ≤ lineParabolicSL) : Bruhat.perm 1 ∈ H := by
  classical
  obtain ⟨g, hg, hgp⟩ := SetLike.not_le_iff_exists.mp hP
  obtain ⟨i, j, k, h⟩ := Bruhat.decomposition g
  have hi := hB (Bruhat.upper_mem i)
  have hk := hB (Bruhat.upper_mem k)
  have hj : Bruhat.perm j ∈ H :=
    (H.mul_mem_cancel_left hi).mp ((H.mul_mem_cancel_right hk).mp (h ▸ hg))
  apply Bruhat.line_reflection_mem H hB j hj
  intro hp
  apply hgp
  rw [h]
  exact lineParabolicSL.mul_mem
    (lineParabolicSL.mul_mem (Bruhat.upper_mem i).2 hp) (Bruhat.upper_mem k).2

theorem overgroup_borelSL (H : Subgroup SL) (hB : borelSL ≤ H) (hH : H ≠ ⊤) :
    H ≤ pointParabolicSL ∨ H ≤ lineParabolicSL := by
  classical
  by_contra h
  obtain ⟨hp, hl⟩ := not_or.mp h
  exact hH (Bruhat.eq_top H hB (line_reflection_of_not_le H hB hl)
    (point_reflection_of_not_le H hB hp))

theorem pointParabolicSL_not_le_line : ¬ pointParabolicSL ≤ lineParabolicSL := by
  intro h
  have hp : Bruhat.perm 1 ∈ pointParabolicSL := by
    rw [mem_pointParabolicSL_iff]; decide
  have hl : Bruhat.perm 1 ∉ lineParabolicSL := by
    rw [mem_lineParabolicSL_iff]; decide
  exact hl (h hp)

theorem lineParabolicSL_not_le_point : ¬ lineParabolicSL ≤ pointParabolicSL := by
  intro h
  have hl : Bruhat.perm 2 ∈ lineParabolicSL := by
    rw [mem_lineParabolicSL_iff]; decide
  have hp : Bruhat.perm 2 ∉ pointParabolicSL := by
    rw [mem_pointParabolicSL_iff]; decide
  exact hp (h hl)

theorem pointParabolicSL_ne_line : pointParabolicSL ≠ lineParabolicSL :=
  fun h => pointParabolicSL_not_le_line h.le

theorem pointParabolicSL_ne_top : pointParabolicSL ≠ ⊤ :=
  fun h => lineParabolicSL_not_le_point (h.symm ▸ le_top)

theorem lineParabolicSL_ne_top : lineParabolicSL ≠ ⊤ :=
  fun h => pointParabolicSL_not_le_line (h.symm ▸ le_top)

theorem isCoatom_pointParabolicSL : IsCoatom pointParabolicSL := by
  refine ⟨pointParabolicSL_ne_top, ?_⟩
  intro H hH
  by_contra hn
  rcases overgroup_borelSL H (le_trans inf_le_left hH.le) hn with hp | hl
  · exact hH.not_ge hp
  · exact pointParabolicSL_not_le_line (hH.le.trans hl)

theorem isCoatom_lineParabolicSL : IsCoatom lineParabolicSL := by
  refine ⟨lineParabolicSL_ne_top, ?_⟩
  intro H hH
  by_contra hn
  rcases overgroup_borelSL H (le_trans inf_le_right hH.le) hn with hp | hl
  · exact lineParabolicSL_not_le_point (hH.le.trans hp)
  · exact hH.not_ge hl

theorem coatoms_over_borelSL (H : Subgroup SL) :
    IsCoatom H ∧ borelSL ≤ H ↔ H = pointParabolicSL ∨ H = lineParabolicSL := by
  constructor
  · rintro ⟨hH, hB⟩
    rcases overgroup_borelSL H hB hH.1 with hp | hl
    · exact Or.inl (eq_of_le_of_not_lt hp (fun h => pointParabolicSL_ne_top (hH.2 _ h)))
    · exact Or.inr (eq_of_le_of_not_lt hl (fun h => lineParabolicSL_ne_top (hH.2 _ h)))
  · rintro (rfl | rfl)
    · exact ⟨isCoatom_pointParabolicSL, inf_le_left⟩
    · exact ⟨isCoatom_lineParabolicSL, inf_le_right⟩
end Matrix.PSL3Two
namespace Matrix.PSL3Two

def pointParabolic : Subgroup PSL := pointParabolicSL.map project
def lineParabolic : Subgroup PSL := lineParabolicSL.map project
def borel : Subgroup PSL := borelSL.map project

theorem mem_pointParabolic_project (g : SL) : project g ∈ pointParabolic ↔
    g.val 1 0 = 0 ∧ g.val 2 0 = 0 := by
  rw [pointParabolic, Subgroup.mem_map_iff_mem project_injective, mem_pointParabolicSL_iff]
theorem mem_lineParabolic_project (g : SL) : project g ∈ lineParabolic ↔
    g.val 2 0 = 0 ∧ g.val 2 1 = 0 := by
  rw [lineParabolic, Subgroup.mem_map_iff_mem project_injective, mem_lineParabolicSL_iff]
theorem mem_borel_project (g : SL) : project g ∈ borel ↔
    g.val 1 0 = 0 ∧ g.val 2 0 = 0 ∧ g.val 2 1 = 0 := by
  rw [borel, Subgroup.mem_map_iff_mem project_injective, mem_borelSL_iff]

theorem card_pointParabolic : Nat.card pointParabolic = 24 := by
  unfold pointParabolic
  rw [← Nat.card_congr (pointParabolicSL.equivMapOfInjective project project_injective).toEquiv]
  exact card_pointParabolicSL
theorem card_lineParabolic : Nat.card lineParabolic = 24 := by
  unfold lineParabolic
  rw [← Nat.card_congr (lineParabolicSL.equivMapOfInjective project project_injective).toEquiv]
  exact card_lineParabolicSL
theorem card_borel : Nat.card borel = 8 := by
  unfold borel
  rw [← Nat.card_congr (borelSL.equivMapOfInjective project project_injective).toEquiv]
  exact card_borelSL

private theorem equiv_hom : equiv.toMonoidHom = project := by
  ext g
  exact equiv_apply g

theorem isCoatom_pointParabolic : IsCoatom pointParabolic := by
  unfold pointParabolic
  rw [← equiv_hom]
  exact (equiv.mapSubgroup.isCoatom_iff _).mpr isCoatom_pointParabolicSL

theorem isCoatom_lineParabolic : IsCoatom lineParabolic := by
  unfold lineParabolic
  rw [← equiv_hom]
  exact (equiv.mapSubgroup.isCoatom_iff _).mpr isCoatom_lineParabolicSL

theorem pointParabolic_ne_line : pointParabolic ≠ lineParabolic := by
  intro h
  exact pointParabolicSL_ne_line (Subgroup.map_injective project_injective h)

theorem pointParabolic_inf_line : pointParabolic ⊓ lineParabolic = borel :=
  (Subgroup.map_inf pointParabolicSL lineParabolicSL project project_injective).symm

theorem coatoms_over_borel (H : Subgroup PSL) :
    IsCoatom H ∧ borel ≤ H ↔ H = pointParabolic ∨ H = lineParabolic := by
  constructor
  · rintro ⟨hH, hB⟩
    have hc : IsCoatom (H.comap project) :=
      Subgroup.isCoatom_comap_of_surjective project_surjective hH
    have hb : borelSL ≤ H.comap project := by
      intro g hg
      exact hB (Subgroup.mem_map_of_mem project hg)
    have he := (coatoms_over_borelSL _).mp ⟨hc, hb⟩
    have hm : (H.comap project).map project = H :=
      Subgroup.map_comap_eq_self_of_surjective project_surjective H
    rcases he with he | he
    · exact Or.inl (hm.symm.trans (congrArg (Subgroup.map project) he))
    · exact Or.inr (hm.symm.trans (congrArg (Subgroup.map project) he))
  · rintro (rfl | rfl)
    · exact ⟨isCoatom_pointParabolic, pointParabolic_inf_line ▸ inf_le_left⟩
    · exact ⟨isCoatom_lineParabolic, pointParabolic_inf_line ▸ inf_le_right⟩

noncomputable def borelSylow : Sylow 2 PSL := Sylow.ofCard borel (by
  rw [card_borel, card_PSL]
  decide +kernel)

@[simp] theorem coe_borelSylow : (borelSylow : Subgroup PSL) = borel := rfl

open scoped Pointwise

theorem sylow_parabolics (S : Sylow 2 PSL) :
    ∃ P L : Subgroup PSL,
      IsCoatom P ∧ IsCoatom L ∧ P ≠ L ∧ P ⊓ L = (S : Subgroup PSL) ∧
      Nat.card P = 24 ∧ Nat.card L = 24 ∧
      ∀ H : Subgroup PSL, IsCoatom H →
        ((S : Subgroup PSL) ≤ H ↔ H = P ∨ H = L) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL borelSylow S
  let e := (MulAut.conj g).mapSubgroup
  have hs : e borel = (S : Subgroup PSL) := by
    rw [← hg]
    rfl
  refine ⟨e pointParabolic, e lineParabolic,
    (e.isCoatom_iff _).mpr isCoatom_pointParabolic,
    (e.isCoatom_iff _).mpr isCoatom_lineParabolic,
    fun h => pointParabolic_ne_line (e.injective h), ?_, ?_, ?_, ?_⟩
  · rw [← e.map_inf, pointParabolic_inf_line, hs]
  · exact (Nat.card_congr ((MulAut.conj g).subgroupMap pointParabolic).toEquiv).symm.trans
      card_pointParabolic
  · exact (Nat.card_congr ((MulAut.conj g).subgroupMap lineParabolic).toEquiv).symm.trans
      card_lineParabolic
  · intro H hH
    constructor
    · intro hS
      have hc : IsCoatom (e.symm H) := (e.symm.isCoatom_iff _).mpr hH
      have hb : borel ≤ e.symm H := by
        apply e.le_iff_le.mp
        simpa only [e.apply_symm_apply, hs] using hS
      rcases (coatoms_over_borel _).mp ⟨hc, hb⟩ with hp | hl
      · exact Or.inl (by simpa using congrArg e hp)
      · exact Or.inr (by simpa using congrArg e hl)
    · rintro (rfl | rfl)
      · rw [← hs]
        exact e.monotone (pointParabolic_inf_line ▸ inf_le_left)
      · rw [← hs]
        exact e.monotone (pointParabolic_inf_line ▸ inf_le_right)
end Matrix.PSL3Two

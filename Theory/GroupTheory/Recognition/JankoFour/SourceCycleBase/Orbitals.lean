module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.RelationChain
/-!
# Symmetry of the native transported orbitals

The literal coset action is transitive on the lines through a point. Together
with the retained orbital transitivity, it is transitive on pairs of a fixed
native type. Reversing pairs pairs the orbitals and preserves their total
cardinality. Since the five valencies 1, 42, 56, 1008, 2688 are distinct, each
orbital is self-paired. This proves symmetry of the δ₃ step needed for B1
without enumerating the ambient group or replacing the native labels.

Source: AS91 (5.4) and the opening relation filtration of §7, p.603.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
open Subgroup GraphUniquenessSystem
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}

/-- The native-label witnesses retain incidence of both ambient lines. -/
theorem lineType_incident {P : LocalGeometry.LocalSubgroups.PointData z}
    {L : LocalGeometry.LocalSubgroups.LineData z P} {r : ResidueChart P L}
    {i : Fin 5} {x : Point P} {l k : Line L} (ht : LineType r i x l k) :
    OnLine L x l ∧ OnLine L x k := by
  obtain ⟨g, a, b, rfl, rfl, rfl, _⟩ := ht
  simpa only [OnLine, Cosets.smul_vertex, mul_one] using
    And.intro (incident_smul g a.property) (incident_smul g b.property)

namespace Input
variable (d : Input h)

theorem incident_lines_transitive {x : Point d.P} {l k : Line d.L}
    (hl : OnLine d.L x l) (hk : OnLine d.L x k) :
    ∃ g : G, g • x = x ∧ g • l = k := by
  obtain ⟨a, hax, hal⟩ := hl
  obtain ⟨b, hbx, hbk⟩ := hk
  refine ⟨b * a⁻¹, ?_, ?_⟩
  · rw [← hax, Cosets.smul_vertex, inv_mul_cancel_right]
    exact hbx.trans hax.symm
  · rw [← hal, Cosets.smul_vertex, inv_mul_cancel_right]
    exact hbk

theorem lineType_pair_transitive {x : Point d.P} {l k a b : Line d.L} {i : Fin 5}
    (hlk : LineType d.residue i x l k) (hab : LineType d.residue i x a b) :
    ∃ g : G, g • x = x ∧ g • l = a ∧ g • k = b := by
  obtain ⟨g, hgx, hgl⟩ := d.incident_lines_transitive
    (lineType_incident hlk).1 (lineType_incident hab).1
  have ht : LineType d.residue i x a (g • k) := by
    simpa only [hgx, hgl] using lineType_smul g hlk
  obtain ⟨f, hfx, hfa, hfg⟩ := d.orbital_transitive x a (g • k) b i ht hab
  exact ⟨f * g, by rw [mul_smul, hgx, hfx],
    by rw [mul_smul, hgl, hfa], by rw [mul_smul, hfg]⟩

/-- Reversal transports one complete orbital to its paired orbital. -/
theorem lineType_reverse_orbital {x : Point d.P} {l k : Line d.L} {i j : Fin 5}
    (hlk : LineType d.residue i x l k) (hkl : LineType d.residue j x k l)
    {a b : Line d.L} (hab : LineType d.residue i x a b) :
    LineType d.residue j x b a := by
  obtain ⟨g, hgx, hgl, hgk⟩ := d.lineType_pair_transitive hlk hab
  simpa only [hgx, hgl, hgk] using lineType_smul g hkl

/-- The five orbital lengths are distinct, so pairing forces every native
transported orbital to be self-paired. The finite count is symbolic. -/
theorem lineType_symm {x : Point d.P} {l k : Line d.L} {i : Fin 5}
    (hlk : LineType d.residue i x l k) : LineType d.residue i x k l := by
  classical
  have hxl := (lineType_incident hlk).1
  have hxk := (lineType_incident hlk).2
  obtain ⟨j, hkl, _⟩ := d.orbital_partition x k l hxk hxl
  let X := {a : Line d.L // OnLine d.L x a}
  let valency : Fin 5 → ℕ := ![1,42,56,1008,2688]
  let pairs (t : Fin 5) := Σ a : X, {b : X // LineType d.residue t x a.val b.val}
  let swap : pairs i ≃ pairs j :=
    { toFun := fun p => ⟨p.2.val, ⟨p.1, d.lineType_reverse_orbital hlk hkl p.2.property⟩⟩
      invFun := fun p => ⟨p.2.val, ⟨p.1, d.lineType_reverse_orbital hkl hlk p.2.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let : Fintype X := Fintype.ofFinite X
  have fiber (t : Fin 5) (a : X) :
      Nat.card {b : X // LineType d.residue t x a.val b.val} = valency t := by
    let e : {b : X // LineType d.residue t x a.val b.val} ≃
        {b : Line d.L // LineType d.residue t x a.val b} :=
      { toFun := fun b => ⟨b.val.val, b.property⟩
        invFun := fun b => ⟨⟨b.val, (lineType_incident b.property).2⟩, b.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact (Nat.card_congr e).trans (d.delta_card x a.val a.property t)
  have card (t : Fin 5) : Nat.card (pairs t) = Nat.card X * valency t := by
    change Nat.card (Σ a : X, {b : X // LineType d.residue t x a.val b.val}) = _
    rw [Nat.card_sigma]
    simp only [fiber, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]
  have he : Nat.card X * valency i = Nat.card X * valency j := by
    rw [← card i, ← card j]
    exact Nat.card_congr swap
  let : Nonempty X := ⟨⟨l, hxl⟩⟩
  have he' : valency i = valency j := Nat.eq_of_mul_eq_mul_left Nat.card_pos he
  have hij : i = j := by
    fin_cases i <;> fin_cases j <;> first | rfl | norm_num [valency] at he'
  exact hij ▸ hkl

/-- Symmetry of the only nontrivial orbital step in the section 7 chain. -/
theorem ternary_two_symm {x u y : Point d.P} (ht : d.ternary 2 x u y) :
    d.ternary 2 y u x := by
  obtain ⟨hxu, huy, hc | hd⟩ := ht
  · exact d.ternary_one_le_two (d.ternary_one_symm ⟨hxu, huy, hc⟩)
  · obtain ⟨l, k, hul, hxl, huk, hyk, htype⟩ := hd
    exact ⟨adj_symm huy, adj_symm hxu,
      Or.inr ⟨k, l, huk, hyk, hul, hxl, d.lineType_symm htype⟩⟩

end Input
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase

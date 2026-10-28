module

public import Theory.Representation.PSL3Two.FourGroupGeometry
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Calculations
/-!
# Coverage of binary elementary four-groups

Sylow conjugacy places an elementary four-group in the standard order-eight
Borel. Its eight explicit upper-triangular matrices give a small checked test:
an involution outside the point translation group has all commuting Borel
involutions in the line translation group. Equal orders give the two classes;
the fixed diagram automorphism interchanges them.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the model
geometry used in the final paragraph of 15.3.61(2), printed p.1151.
-/

public section
open Subgroup Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
open scoped Pointwise
namespace BinaryLinearThree.FourGroupGeometry.Normalizers
private theorem upper_injective : Function.Injective Bruhat.upper := by decide +kernel

private theorem exists_upper (g : SL) (hg : g ∈ borelSL) :
    ∃ i : Fin 8, Bruhat.upper i = g := by
  let f : Fin 8 → borelSL := fun i => ⟨Bruhat.upper i, Bruhat.upper_mem i⟩
  have hi : Function.Injective f := fun i j h => upper_injective (congrArg Subtype.val h)
  have hc : Nat.card (Fin 8) = Nat.card borelSL := by rw [card_borelSL]; simp
  obtain ⟨i, hi⟩ := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hi, hc⟩).2 ⟨g, hg⟩
  exact ⟨i, congrArg Subtype.val hi⟩

private theorem upper_four_test : ∀ i j : Fin 8,
    Bruhat.upper i ^ 2 = 1 → Bruhat.upper i ∉ pointV →
    Bruhat.upper j ^ 2 = 1 →
    Bruhat.upper i * Bruhat.upper j = Bruhat.upper j * Bruhat.upper i →
    Bruhat.upper j ∈ lineV := by decide +kernel

theorem card_lineV : Nat.card lineV = 4 := by
  have he := Nat.card_congr (diagram.subgroupMap pointV).toEquiv
  change Nat.card pointV = Nat.card (pointV.map diagram.toMonoidHom) at he
  rw [pointV_map_diagram, card_pointV] at he
  exact he.symm

theorem fourGroup_le_borel (B : Subgroup SL) [IsElementaryAbelian 2 B]
    (hc : Nat.card B = 4) (hB : B ≤ borelSL) : B = pointV ∨ B = lineV := by
  by_cases hp : B ≤ pointV
  · exact Or.inl (eq_of_le_of_card_ge hp (by rw [hc, card_pointV]))
  · right
    apply eq_of_le_of_card_ge _ (by rw [hc, card_lineV])
    obtain ⟨g, hg, hgp⟩ := SetLike.not_le_iff_exists.mp hp
    intro h hh
    obtain ⟨i, rfl⟩ := exists_upper g (hB hg)
    obtain ⟨j, rfl⟩ := exists_upper h (hB hh)
    apply upper_four_test i j (elemPow_eq_one_of_isElementaryAbelian _ hg) hgp
      (elemPow_eq_one_of_isElementaryAbelian _ hh)
    exact congrArg Subtype.val
      (IsMulCommutative.is_comm.comm (⟨_, hg⟩ : B) ⟨_, hh⟩)

/-- The two inner conjugacy classes are the actual point and line translation groups. -/
theorem fourGroup_coverage (B : Subgroup SL) [IsElementaryAbelian 2 B]
    (hc : Nat.card B = 4) :
    ∃ g : SL, B.map (MulAut.conj g).toMonoidHom = pointV ∨
      B.map (MulAut.conj g).toMonoidHom = lineV := by
  let T : Sylow 2 SL := Sylow.ofCard borelSL (by
    rw [card_borelSL, card_SL]; decide +kernel)
  obtain ⟨S, hS⟩ := (IsElementaryAbelian.isPGroup 2 B).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL S T
  refine ⟨g, ?_⟩
  let C := B.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.map _
  apply fourGroup_le_borel C
  · exact (Nat.card_congr ((MulAut.conj g).subgroupMap B).toEquiv).symm.trans hc
  · have h : (S : Subgroup SL).map (MulAut.conj g).toMonoidHom = borelSL := by
      change (↑(g • S) : Subgroup SL) = borelSL
      rw [hg]
      rfl
    exact (map_mono hS).trans_eq h

/-- Allowing the fixed graph automorphism joins the two inner conjugacy classes. -/
theorem fourGroup_map_point (B : Subgroup SL) [IsElementaryAbelian 2 B]
    (hc : Nat.card B = 4) : ∃ e : MulAut SL, B.map e.toMonoidHom = pointV := by
  obtain ⟨g, hg | hg⟩ := fourGroup_coverage B hc
  · exact ⟨MulAut.conj g, hg⟩
  · refine ⟨(MulAut.conj g).trans diagram.symm, ?_⟩
    change B.map (diagram.symm.toMonoidHom.comp (MulAut.conj g).toMonoidHom) = _
    rw [← map_map, hg, ← pointV_map_diagram, map_map]
    simp
end BinaryLinearThree.FourGroupGeometry.Normalizers

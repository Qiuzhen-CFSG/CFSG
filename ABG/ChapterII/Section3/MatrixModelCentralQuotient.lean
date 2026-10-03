module
public import ABG.ChapterII.Section3.CentralSylowDihedralQuotient
public import ABG.ChapterII.Section1.Noncommutative
public import Theory.SpecificGroups.GL2.DeterminantCentralizer

/-!
# The central quotient of an actual matrix Sylow model

Suppose a finite group embeds in a determinant two-power level of GL2
over a field. If a chosen Sylow two-subgroup is semidihedral or wreathed
and its mapped center is central in the whole group, then the full group
center is exactly that mapped Sylow center, and quotienting by it gives
dihedral Sylow two-subgroups.

The given Sylow shape makes the group noncommutative. The matrix
determinant-centralizer theorem therefore makes its center a two-group.
As a normal two-subgroup it lies in the chosen Sylow, and ambient
centrality puts it in the Sylow center. The opposite inclusion is the
hypothesis. The established central-Sylow-quotient theorem now applies.

This is the actual model quotient in Alperin--Brauer--Gorenstein II.3
Proposition 3, article p26, before recognizing the quotient as PGL2.
It applies uniformly to the proved linear and unitary determinant models
through their original matrix inclusions; no scalar-cardinality formula,
abstract matrix recognition or quotient classification is assumed.
-/

namespace ABG
open Matrix.GeneralLinearGroup

public theorem hasDihedralSylowTwo_quotient_center_of_matrix_model
    {G F : Type*} [Group G] [Finite G] [Field F]
    (j : G →* GL (Fin 2) F) (hj : Function.Injective j) (m : ℕ)
    (hlevel : j.range ≤ determinantTwoPower F m)
    (P : Sylow 2 G) (hP : Stellmacher.IsSemidihedralGroup P ∨ IsWreathedGroup P)
    (hcenter : subgroupCenter (P : Subgroup G) ≤ Subgroup.center G) :
    Subgroup.center G = subgroupCenter (P : Subgroup G) ∧
      GorensteinWalter.HasDihedralSylowTwo (G ⧸ Subgroup.center G) := by
  have hPnc : ¬ IsMulCommutative P := by
    rcases hP with hP | hP
    · exact QuasiDihedral.not_isMulCommutative hP
    · obtain ⟨n, hn⟩ := hP
      obtain ⟨W⟩ := Wreathed.nonempty_presentation hn
      intro hc
      have hcard := W.card_center
      rw [Subgroup.center_eq_top_iff.mpr hc, Subgroup.card_top, W.card] at hcard
      have he := Nat.pow_right_injective (by decide : 1 < 2) hcard
      omega
  have hGnc : ¬ IsMulCommutative G := by
    intro h
    exact hPnc ⟨⟨fun a b => Subtype.ext (h.is_comm.comm a.val b.val)⟩⟩
  have hjnc : ¬ IsMulCommutative j.range := by
    intro h
    apply hGnc
    apply IsMulCommutative.of_comm
    intro a b
    apply hj
    rw [j.map_mul, j.map_mul]
    exact congrArg Subtype.val (h.is_comm.comm (⟨j a, ⟨a, rfl⟩⟩ : j.range) ⟨j b, ⟨b, rfl⟩⟩)
  let C := Subgroup.centralizer (j.range : Set (GL (Fin 2) F)) ⊓ determinantTwoPower F m
  have hC : IsPGroup 2 C := isPGroup_centralizer_inf_determinantTwoPower j.range hjnc m
  have hmem (c : Subgroup.center G) : j c.val ∈ C := by
    refine ⟨?_, hlevel ⟨c.val, rfl⟩⟩
    change j c.val ∈ Subgroup.centralizer (j.range : Set (GL (Fin 2) F))
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨g, rfl⟩
    exact (j.map_mul g c.val).symm.trans
      ((congrArg j (Subgroup.mem_center_iff.mp c.property g)).trans (j.map_mul c.val g))
  let f : Subgroup.center G →* C := (j.comp (Subgroup.center G).subtype).codRestrict C hmem
  have hf : Function.Injective f := by
    intro a b h
    exact Subtype.ext (hj (congrArg Subtype.val h))
  have hc2 : IsPGroup 2 (Subgroup.center G) := hC.of_injective f hf
  have hcP : Subgroup.center G ≤ (P : Subgroup G) := hc2.le_sylow_of_normal P
  have heq : Subgroup.center G = subgroupCenter (P : Subgroup G) := by
    apply le_antisymm ?_ hcenter
    intro c hc
    refine ⟨⟨c, hcP hc⟩, ?_, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro p
    exact Subtype.ext (Subgroup.mem_center_iff.mp hc p)
  exact ⟨heq, hasDihedralSylowTwo_quotient_sylow_center P (Subgroup.center G) heq hP⟩

end ABG


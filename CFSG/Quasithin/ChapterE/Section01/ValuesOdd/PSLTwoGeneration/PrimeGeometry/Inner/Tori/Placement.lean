module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.Reduction
public import GorensteinWalter.PSL2InvolutionFusion

/-!
# Placing a dihedral torus through a prescribed four-group

Involution fusion places a central involution of the dihedral subgroup at the
specified actor involution. Inside its centralizer, Sylow conjugacy then moves
a subgroup of order four onto the actor. All subgroup maps are the literal
conjugation maps and inclusions, so this second move preserves centralization.

This supplies the placement step for the torus route in Aschbacher--Smith
E.1.14(6), citing Aschbacher (1982), Lemma 4.10.
-/

public section

open Subgroup GorensteinWalter
open scoped Pointwise

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.Tori

variable {G : Type*} [Group G] [Finite G]

/-- In a group with Sylow two-subgroups of order four and a single involution
class, a dihedral subgroup with a central involution can be placed through any
specified four-group in the centralizer of any of its involutions. -/
theorem place_dihedral_through_four
    (T : Sylow 2 G) (hT : Nat.card T = 4)
    (hfusion : ∀ x y : G, IsInvolution x → IsInvolution y →
      ∃ g : G, g * x * g⁻¹ = y)
    (A : Subgroup G) (hA : IsKleinFour A) (hAT : A ≤ (T : Subgroup G))
    (z : G) (hzA : z ∈ A) (hz : z ≠ 1)
    {r : ℕ} (D : Subgroup G) (t : G) (ht : IsInvolution t)
    (hDC : D ≤ centralizer ({t} : Set G)) (eD : D ≃* DihedralGroup (2 * r)) :
    ∃ H : Subgroup G, A ≤ H ∧ H ≤ centralizer ({z} : Set G) ∧
      Nonempty (H ≃* DihedralGroup (2 * r)) := by
  classical
  let : IsKleinFour A := hA
  let : CommGroup A := { (inferInstance : Group A) with
    mul_comm := IsKleinFour.isMulCommutative.is_comm.comm }
  have hz2 : z ^ 2 = 1 := by
    rw [pow_two]
    exact congrArg Subtype.val (IsKleinFour.mul_self (⟨z, hzA⟩ : A))
  obtain ⟨g, hg⟩ := hfusion t z ht ⟨hz, hz2⟩
  let f : G ≃* G := MulAut.conj g
  have hft : f t = z := hg
  let D₁ := D.map f.toMonoidHom
  let C := centralizer ({z} : Set G)
  have hD₁C : D₁ ≤ C := by
    rintro x ⟨d, hd, rfl⟩
    rw [mem_centralizer_singleton_iff, ← hft]
    change f d * f t = f t * f d
    simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp (hDC hd))
  let L : Subgroup C := D₁.subgroupOf C
  let eL : L ≃* DihedralGroup (2 * r) :=
    (subgroupOfEquivOfLe hD₁C).trans
      ((D.equivMapOfInjective f.toMonoidHom f.injective).symm.trans eD)
  have hLc : Nat.card L = 4 * r := by
    rw [Nat.card_congr eL.toEquiv, DihedralGroup.nat_card]
    ring
  have hAC : A ≤ C := by
    intro a ha
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : A) ⟨z, hzA⟩)
  have hATeq : A = (T : Subgroup G) :=
    eq_of_le_of_card_ge hAT (by rw [hT, hA.card_four])
  have hTC : (T : Subgroup G) ≤ C := hATeq ▸ hAC
  let P : Sylow 2 C := T.subtype hTC
  have hPc : Nat.card P = 4 := by
    change Nat.card ((T : Subgroup G).subgroupOf C) = 4
    rw [Nat.card_congr (subgroupOfEquivOfLe hTC).toEquiv, hT]
  obtain ⟨B, hBc⟩ := Sylow.exists_subgroup_card_pow_prime (G := L) 2 (n := 2) (by
    rw [hLc]
    exact dvd_mul_right (2 ^ 2) r)
  let B' : Subgroup C := B.map L.subtype
  have hB'c : Nat.card B' = 4 := by
    rw [← Nat.card_congr (B.equivMapOfInjective L.subtype L.subtype_injective).toEquiv]
    exact hBc
  let Q : Sylow 2 C := Sylow.ofCard B' (hB'c.trans (hPc.symm.trans P.card_eq_multiplicity))
  have hQL : (Q : Subgroup C) ≤ L := by
    change B.map L.subtype ≤ L
    exact map_subtype_le B
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C Q P
  let K : Subgroup C := L.map (MulAut.conj c).toMonoidHom
  have hPK : (P : Subgroup C) ≤ K := by
    rw [← hc]
    change (Q : Subgroup C).map (MulAut.conj c).toMonoidHom ≤ K
    exact map_mono hQL
  let H : Subgroup G := K.map C.subtype
  refine ⟨H, ?_, ?_, ?_⟩
  · intro a ha
    exact mem_map.mpr ⟨⟨a, hAC ha⟩, hPK (hAT ha), rfl⟩
  · exact map_subtype_le K
  · exact ⟨(K.equivMapOfInjective C.subtype C.subtype_injective).symm.trans
      ((L.equivMapOfInjective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective).symm.trans eL)⟩

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.Tori

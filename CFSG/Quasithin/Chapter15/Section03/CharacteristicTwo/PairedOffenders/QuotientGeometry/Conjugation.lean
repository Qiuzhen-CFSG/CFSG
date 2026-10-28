module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.QuotientGeometry.Conjugation.Actions
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.QuotientGeometry.Conjugation.GL2

/-!
# Conjugation comparisons for the paired offender cases

The D8 involution geometry and the SD16 interchange are transported through
 the two actual action diagrams. The action maps are defined on S alone;
 explicit conjugation equations determine the relation between their even
 four-group markings. Outside the D8 image, the only simultaneous source
 positions are (i)/(ii), (ii)/(i), and (iv)/(iv). Equal images of S and T
 induce inner conjugation and force the cases to agree.

The final wrapper uses the original quotient map and an actual equivalence
 of the T-image with a Sylow two-subgroup of GL2(3). The proved Sylow
 presentation determines its parameter four and supplies the SD16 model.
The quotient and compatible local actions are inputs; no pairing, rank tuple,
 or four-group interchange is assumed. Source-theorem assembly stays with the
 paired-quotient owner.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
 15.3.25, printed pp.1133–1134 (PDF pp.1150–1151).
-/

public section
open Subgroup
open CFSG.Quasithin.ChapterB.Offenders
open CFSG.Quasithin.ChapterB.Offenders.Eight
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedQuotient.Conjugation

/-- The interchange for a genuine D8 subgroup of an actual Sylow subgroup of
 GL2(3), using its proved equivalence with the standard semidihedral model. -/
theorem GL2_three_interchange (P : Sylow 2 (GL (Fin 2) (ZMod 3)))
    (S E : Subgroup P) (e : S ≃* DihedralGroup 4)
    [IsElementaryAbelian 2 E] (hE : Nat.card E = 4) (t : P) (ht : t ∉ S) :
    E ≤ S ∧ E.map (MulAut.conj t).toMonoidHom ≤ S ∧
      E.map (MulAut.conj t).toMonoidHom ≠ E := by
  obtain ⟨v⟩ := GL2_three_sylow_equiv P
  exact semidihedral_interchange v S E e hE t ht

/-- The larger-image branch on the original quotient map. Only the local
 actions on S are supplied. The Sylow comparison, the interchange of markings,
 and the case pairing are derived, including both orientations of (i)/(ii). -/
theorem cases_of_GL2_three_quotient
    {G H : Type*} [Group G] [Group H]
    (S T : Subgroup G) (hST : S ≤ T) (q : G →* H) (f g : S →* Perm)
    (d : LocalCoordinates f (q.subgroupMap S))
    (e : LocalCoordinates g (q.subgroupMap S))
    (P : Sylow 2 (GL (Fin 2) (ZMod 3))) (v : T.map q ≃* P)
    (t : G) (ht : t ∈ T) (hout : q t ∉ S.map q)
    (σ : MulAut S) (hσ : ∀ s : S, (σ s : G) = t * s * t⁻¹)
    (α : MulAut (S.map q))
    (hα : ∀ x : S.map q, (α x : H) = q t * x * (q t)⁻¹)
    (r : Perm) (hact : ∀ s, g (σ s) = r * f s * r⁻¹)
    {A : Subgroup S} {c c' : EightCase}
    (hA : c.Realizes (A.map f)) (hA' : c'.Realizes (A.map g)) :
    (c = .regular ∧ c' = .transposition) ∨
    (c = .transposition ∧ c' = .regular) ∨ (c = .even ∧ c' = .even) := by
  let j : S.map q →* T.map q := Subgroup.inclusion (map_mono hST)
  let tq : T.map q := ⟨q t, mem_map_of_mem q ht⟩
  have hj : Function.Injective j := Subgroup.inclusion_injective (map_mono hST)
  have htq : tq ∉ j.range := by
    rintro ⟨x, hx⟩
    have hh : (x : H) = q t := congrArg Subtype.val hx
    exact hout (hh ▸ x.property)
  have hquot : ∀ s : S, q.subgroupMap S (σ s) = α (q.subgroupMap S s) := by
    intro s
    apply Subtype.ext
    change q (σ s : G) = (α (q.subgroupMap S s) : H)
    rw [hα, hσ, map_mul, map_mul, map_inv]
    rfl
  have hconj : ∀ x, j (α x) = tq * j x * tq⁻¹ := by
    intro x
    exact Subtype.ext (hα x)
  obtain ⟨pSD⟩ := GL2_three_sylow_equiv P
  exact d.cases_of_semidihedral e (q.subgroupMap_surjective S) σ α hquot r hact
    (v.trans pSD) j hj tq htq hconj hA hA'

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedQuotient.Conjugation
end

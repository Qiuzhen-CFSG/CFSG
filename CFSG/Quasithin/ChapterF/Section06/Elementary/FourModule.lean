module
public import CFSG.Quasithin.ChapterF.Section06.Elementary.Subnormal
public import CFSG.Quasithin.ChapterF.Section06.Elementary.Residual
public import Theory.GroupTheory.SpecificGroups.KleinFourFullAction
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Normal four-groups in a Goldschmidt triple

If a normal four-group contains a point fixed by the common Sylow subgroup
and moved by both vertices, the two vertex cores coincide. F.6.7 bounds each
local action kernel by its two-core. Its S₃ quotient then forces the full
S₃ action on the four-group. Thus each local kernel is exactly its two-core;
F.6.7's intersection identity identifies these cores with the same subgroup.

This supplies the small-support obstruction for the original paired-point
FF comparison in Aschbacher--Smith 13.2.12, printed p.882. It uses only the
literal Goldschmidt hypotheses from F.6.1 and F.6.7, printed pp.304--305.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterF
variable {G : Type*} [Group G] [Finite G] {A B : Subgroup G}

private theorem onto_three_of_two_kernel {D : Type*} [Group D] [Finite D]
    (f : D →* Equiv.Perm (Fin 3)) (hk : IsPGroup 2 f.ker)
    (e : (D ⧸ pCore 2 D) ≃* Equiv.Perm (Fin 3)) : Function.Surjective f := by
  have hle : f.ker ≤ pCore 2 D := le_sSup ⟨inferInstance,hk⟩
  have hi : (pCore 2 D).index = 6 := by
    rw [index_eq_card,Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hd := index_dvd_of_le hle
  rw [hi,index_ker] at hd
  apply MonoidHom.range_eq_top.mp
  apply eq_top_of_card_eq
  have hc : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  apply Nat.dvd_antisymm f.range.card_subgroup_dvd_card
  rwa [hc]

/-- A normal four-group containing a common-Sylow fixed point moved by both
vertices forces equality of the two original vertex cores. -/
theorem IsGoldschmidtTriple.cores_eq_of_normal_four
    (h : IsGoldschmidtTriple A B) (E : Subgroup G) [E.Normal] [IsKleinFour E]
    (x : G) (hx : x ∈ E)
    (hcx : A ⊓ B ≤ centralizer ({x} : Set G))
    (ha : ¬ A ≤ centralizer ({x} : Set G))
    (hb : ¬ B ≤ centralizer ({x} : Set G)) :
    A.pCoreIn 2 = B.pCoreIn 2 := by
  let f : G →* Equiv.Perm (Fin 3) :=
    (IsKleinFour.autEquivPermThree E).toMonoidHom.comp MulAut.conjNormal
  have hk : f.ker = centralizer (E : Set G) := by
    ext g
    change (IsKleinFour.autEquivPermThree E) (MulAut.conjNormal g) = 1 ↔ _
    rw [←(IsKleinFour.autEquivPermThree E).map_one,
      (IsKleinFour.autEquivPermThree E).injective.eq_iff]
    constructor
    · intro he y hy
      have hh := congrArg (fun a : MulAut E => (a ⟨y,hy⟩ : G)) he
      change g*y*g⁻¹=y at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro he
      ext y
      change g*(y:G)*g⁻¹=(y:G)
      exact mul_inv_eq_iff_eq_mul.mpr (he y y.property).symm
  have hbound (C D : Subgroup G) (hCD : IsGoldschmidtTriple C D)
      (hc : C ⊓ D ≤ centralizer ({x} : Set G))
      (hm : ¬ C ≤ centralizer ({x} : Set G)) : C ⊓ f.ker ≤ C.pCoreIn 2 := by
    apply (hCD.left_subnormal_core_iff_not_residual_le _
      (inferInstance : f.ker.Normal).isSubnormal).mpr
    intro hr
    apply hm
    rw [←hCD.left_residual_sup_intersection]
    rw [hk] at hr
    exact sup_le (hr.trans (centralizer_le (Set.singleton_subset_iff.mpr hx))) hc
  have hA := hbound A B h hcx ha
  have hB := hbound B A h.symm (inf_comm A B ▸ hcx) hb
  have hker (C : Subgroup G) (hc : C ⊓ f.ker ≤ C.pCoreIn 2)
      (e : (C ⧸ pCore 2 C) ≃* Equiv.Perm (Fin 3)) : C.pCoreIn 2 ≤ f.ker := by
    let g := f.comp C.subtype
    have hp : IsPGroup 2 g.ker := by
      apply pCore_isPGroup.to_le
      intro y hy
      obtain ⟨z,hz,he⟩ := hc ⟨y.property,hy⟩
      exact (Subtype.ext he : z=y) ▸ hz
    have he := ker_eq_twoCore_of_surjective_perm_three g
      (onto_three_of_two_kernel g hp e) hp
    rintro y ⟨y,hy,rfl⟩
    change y ∈ g.ker
    rwa [he]
  have hAk := hker A hA h.quotient_left.some
  have hBk := hker B hB h.quotient_right.some
  have hAi := (h.left_intersection_eq_core_intersection f.ker hA).2
  have hBi := (h.symm.left_intersection_eq_core_intersection f.ker hB).2
  change A.pCoreIn 2 ⊓ f.ker = (A ⊓ B) ⊓ f.ker at hAi
  change B.pCoreIn 2 ⊓ f.ker = (B ⊓ A) ⊓ f.ker at hBi
  rw [inf_of_le_left hAk] at hAi
  rw [inf_of_le_left hBk,inf_comm B A] at hBi
  exact hAi.trans hBi.symm

end CFSG.Quasithin.ChapterF

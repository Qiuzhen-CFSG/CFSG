module

public import Theory.SpecificGroups.GL2.NoncommutativeCentralizer
public import Theory.GroupTheory.PerfectCentralizerLift
public import GorensteinWalter.SL2ProjectiveCover

/-!
# The characteristic linear-two block in a cubic central matrix quotient

If a faithful two-dimensional matrix group has derived subgroup SL₂, a
central quotient of exponent three is injective on that derived subgroup.
The quotient's literal commutator is therefore SL₂. Its centralizer is
exactly the center, by the scalar centralizer theorem and perfect lifting.

This retains the canonical derived subgroup in the GL₂ and GU₂ involution
centralizers used in Aschbacher--Smith 6.1.4, printed p.666.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup

private theorem central_sq_eq_one {E : Type*} [Field E] {g : SL(2,E)}
    (hg : g ∈ center SL(2,E)) : g^2=1 := by
  obtain ⟨a,ha,h⟩ := SpecialLinearGroup.mem_center_iff.mp hg
  simp only [Fintype.card_fin] at ha
  have hcase : g=1 ∨ g= -1 := by
    rcases sq_eq_one_iff.mp ha with rfl | rfl
    · left
      apply Subtype.ext
      simpa using h.symm
    · right
      apply Subtype.ext
      simpa [←Matrix.diagonal_neg] using h.symm
  rcases hcase with rfl | rfl <;> simp

/-- The same derived subgroup survives the actual cubic central quotient,
and its full centralizer in that quotient is the center. -/
theorem commutator_structure_of_cubic_central_matrix_surjection
    {G H F E : Type*} [Group G] [Group H] [Field F] [Field E] [Finite E]
    (ρ : G →* GL (Fin 2) F) (hρ : Function.Injective ρ)
    (e : commutator G ≃* SL(2,E)) (hlarge : 3 < Nat.card E)
    (f : G →* H) (hf : Function.Surjective f) (hk : f.ker ≤ center G)
    (hcube : ∀ x ∈ f.ker, x^3=1) :
    Nonempty (commutator H ≃* SL(2,E)) ∧
      centralizer (commutator H : Set H) = center H := by
  let D := commutator G
  let : Group.IsPerfect SL(2,E) := GorensteinWalter.sl2_isPerfect_of_card_gt_three E hlarge
  let : Group.IsPerfect D := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : IsSimpleGroup (SL(2,E) ⧸ center SL(2,E)) :=
    ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : Nontrivial SL(2,E) := (QuotientGroup.mk'_surjective (center SL(2,E))).nontrivial
  have hinj : Function.Injective (f.subgroupMap D) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro x hx
    have hxf : (x : G) ∈ f.ker := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have hxe : e x ∈ center SL(2,E) := by
      apply Subgroup.mem_center_iff.mpr
      intro y
      obtain ⟨y,rfl⟩ := e.surjective y
      rw [←map_mul,←map_mul]
      exact congrArg e (Subtype.ext (Subgroup.mem_center_iff.mp (hk hxf) y))
    have hs := central_sq_eq_one hxe
    have ht : e x ^ 3 = 1 := by
      rw [←map_pow]
      exact (congrArg e (show x^3=1 from Subtype.ext (hcube x hxf))).trans (map_one e)
    rw [pow_succ,hs,one_mul] at ht
    exact e.injective (ht.trans e.map_one.symm)
  let ef : D ≃* D.map f := MulEquiv.ofBijective (f.subgroupMap D)
    ⟨hinj,f.subgroupMap_surjective D⟩
  have hmap : D.map f = commutator H := by
    change (commutator G).map f = commutator H
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr hf]
    rfl
  refine ⟨⟨(MulEquiv.subgroupCongr hmap.symm).trans (ef.symm.trans e)⟩,?_⟩
  have hDC : centralizer (D : Set G) = center G := by
    apply le_antisymm
    · intro x hx
      let R := D.map ρ
      let er : D ≃* R := D.equivMapOfInjective ρ hρ
      have hnon : ¬ IsMulCommutative R := by
        intro hh
        let : IsMulCommutative SL(2,E) := IsMulCommutative.of_comm fun a b => by
          apply (e.symm.trans er).injective
          rw [map_mul,map_mul,hh.is_comm.comm]
        have : Subsingleton SL(2,E) := Group.IsPerfect.subsingleton_of_isMulCommutative
        exact not_nontrivial_iff_subsingleton.mpr this inferInstance
      have hxR : ρ x ∈ centralizer (R : Set (GL (Fin 2) F)) := by
        rintro r ⟨d,hd,rfl⟩
        simpa only [map_mul] using congrArg ρ (hx d hd)
      have hxZ := GeneralLinearGroup.centralizer_le_scalar_of_noncommutative R hnon hxR
      rw [←GeneralLinearGroup.center_eq_range_scalar] at hxZ
      apply Subgroup.mem_center_iff.mpr
      intro y
      apply hρ
      simpa only [map_mul] using Subgroup.mem_center_iff.mp hxZ (ρ y)
    · exact center_le_centralizer _
  apply le_antisymm
  · intro h hh
    obtain ⟨g,rfl⟩ := hf h
    have hg : g ∈ centralizer (D : Set G) := by
      rw [←comap_centralizer_map_eq_of_perfect f D (hk.trans (center_le_centralizer _))]
      change f g ∈ centralizer (D.map f : Set H)
      rwa [hmap]
    rw [hDC] at hg
    apply Subgroup.mem_center_iff.mpr
    intro y
    obtain ⟨y,rfl⟩ := hf y
    simpa only [map_mul] using congrArg f (Subgroup.mem_center_iff.mp hg y)
  · exact center_le_centralizer _

end Matrix.SpecialLinearGroup

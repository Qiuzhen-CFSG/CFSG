module
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.ThreeCenters
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.TransvectionProducts

/-!
# The moved plane of a noncommuting transvection product

A product of two noncommuting transvections moves exactly the sum of their
center lines. Evaluating at the second center isolates the first line;
subtracting an already-controlled first displacement then recovers the
second. Any element centralizing the product preserves this moved plane.

Consequently the third root of the actual three-center configuration cannot
be a conjugate of the first by such an element. This supplies the geometric
obstruction to the odd-dihedral lift in Aschbacher--Smith G.4.9, printed p.341.
The group-theoretic construction of a rotation conjugator through the central
kernel remains a separate input; no dihedral lifting theorem is assumed here.
-/

public noncomputable section

open Subgroup Module
namespace Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
open InvolutionTypes InvolutionCentralizers
variable {F : Type*} [Field F] [CharP F 2]

omit [CharP F 2] in
theorem movedSpace_mul_le_sup (a b : Sp F) :
    movedSpace (a*b)≤movedSpace a⊔movedSpace b := by
  rintro x ⟨v,rfl⟩
  change (a*b) • v-v∈_
  have he : (a*b) • v-v=(a • (b • v)-b • v)+(b • v-v) := by rw [mul_smul]; abel
  rw [he]
  exact Submodule.add_mem _ ((show movedSpace a≤movedSpace a⊔movedSpace b from le_sup_left) (show a • (b • v)-b • v∈movedSpace a from ⟨b • v,rfl⟩))
    ((show movedSpace b≤movedSpace a⊔movedSpace b from le_sup_right) (show b • v-v∈movedSpace b from ⟨v,rfl⟩))

/-- The product of noncommuting transvections moves precisely their two center lines. -/
theorem movedSpace_mul_eq_sup_of_noncommuting (a b : Sp F)
    (ha : IsB1 a) (hb : IsB1 b) (hab : ¬Commute a b) :
    movedSpace (a*b)=movedSpace a⊔movedSpace b := by
  obtain ⟨u,c,hu,hc,haform⟩ := rank_one_formula a ha
  obtain ⟨v,d,hv,hd,hbform⟩ := rank_one_formula b hb
  have hs (x y : Vector F) : form F x y=form F y x := by
    simpa only [CharTwo.neg_eq] using TwoLocalCover.form_alternating.neg_eq x y
  have huv : form F u v≠0 := by
    intro hz
    apply hab
    apply FaithfulSMul.eq_of_smul_eq_smul (α:=Vector F)
    intro x
    change (a*b) • x=(b*a) • x
    have hvu : form F v u=0 := (hs v u).trans hz
    rw [mul_smul,mul_smul,haform,hbform,hbform,haform]
    simp only [map_add,map_smul,smul_eq_mul,hz,hvu,mul_zero,add_zero]
    abel
  have hvu : form F v u≠0 := by rwa [hs]
  let R := movedSpace (a*b)
  have hum : u∈R := by
    have hm : (c*form F u v) • u∈R := by
      refine ⟨v,?_⟩
      change (a*b) • v-v=_
      rw [mul_smul,hbform,TwoLocalCover.form_alternating.self_eq_zero,mul_zero,
        zero_smul,add_zero,haform,add_sub_cancel_left]
    exact (Submodule.smul_mem_iff _ (mul_ne_zero hc huv)).mp hm
  have hma : movedSpace a≤R := by
    rw [movedSpace_eq_span_center a u c hu hc haform]
    apply Submodule.span_le.mpr
    intro z hz
    have hz : z=u := Set.mem_singleton_iff.mp hz
    subst z
    exact hum
  have hvm : v∈R := by
    have hm : b • u-u∈R := by
      have h1 : (a*b) • u-u∈R := ⟨u,rfl⟩
      have h2 : a • (b • u)-b • u∈R := hma ⟨b • u,rfl⟩
      have he : ((a*b) • u-u)-(a • (b • u)-b • u)=b • u-u := by rw [mul_smul]; abel
      exact he ▸ Submodule.sub_mem R h1 h2
    rw [hbform,add_sub_cancel_left] at hm
    exact (Submodule.smul_mem_iff _ (mul_ne_zero hd hvu)).mp hm
  have hmb : movedSpace b≤R := by
    rw [movedSpace_eq_span_center b v d hv hd hbform]
    apply Submodule.span_le.mpr
    intro z hz
    have hz : z=v := Set.mem_singleton_iff.mp hz
    subst z
    exact hvm
  exact le_antisymm (movedSpace_mul_le_sup a b) (sup_le hma hmb)

/-- A conjugator centralizing the odd rotation keeps a transvection center
inside the product's moved plane. -/
theorem movedSpace_conjugate_le_product (a b g : Sp F)
    (ha : IsB1 a) (hb : IsB1 b) (hab : ¬Commute a b) (hg : Commute g (a*b)) :
    movedSpace (g*a*g⁻¹)≤movedSpace (a*b) := by
  have hle : movedSpace a≤movedSpace (a*b) := by
    rw [movedSpace_mul_eq_sup_of_noncommuting a b ha hb hab]
    exact le_sup_left
  have hfix : (movedSpace (a*b)).map (toLinear g).toLinearMap=movedSpace (a*b) := by
    rw [←movedSpace_conj]
    congr 1
    rw [hg.eq,mul_assoc,mul_inv_cancel,mul_one]
  rw [movedSpace_conj,←hfix]
  exact Submodule.map_mono hle

/-- The third marked root cannot be an odd-rotation conjugate of the first.
This is the geometric obstruction used to exclude an odd-dihedral local group. -/
theorem ThreeCenterConfiguration.third_not_rotation_conjugate
    {X : Subgroup (Sp F)} {a : Sp F} (D : ThreeCenterConfiguration X a) (ha : IsB1 a)
    (g : Sp F) (hg : Commute g (a*((D.x : Sp F)*a*(D.x : Sp F)⁻¹))) :
    (D.y : Sp F)*a*(D.y : Sp F)⁻¹≠g*a*g⁻¹ := by
  intro he
  let U := Submodule.span F (Set.range ![D.center,(D.x : Sp F) • D.center])
  have hma := movedSpace_eq_span_center a D.center D.parameter D.center_ne_zero D.parameter_ne_zero D.formula
  have hcenter : D.center∈movedSpace a := by rw [hma]; exact Submodule.subset_span rfl
  have hy : (D.y : Sp F) • D.center∈movedSpace ((D.y : Sp F)*a*(D.y : Sp F)⁻¹) := by
    rw [movedSpace_conj]
    exact ⟨D.center,hcenter,rfl⟩
  have haU : movedSpace a≤U := by
    rw [hma]
    apply Submodule.span_le.mpr
    intro z hz
    have hz : z=D.center := Set.mem_singleton_iff.mp hz
    rw [hz]
    exact Submodule.subset_span ⟨0,rfl⟩
  have hbU : movedSpace ((D.x : Sp F)*a*(D.x : Sp F)⁻¹)≤U := by
    rw [movedSpace_conj,hma,Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro z ⟨u,hu,rfl⟩
    have hu : u=D.center := Set.mem_singleton_iff.mp hu
    rw [hu]
    exact Submodule.subset_span ⟨1,rfl⟩
  have hb : IsB1 ((D.x : Sp F)*a*(D.x : Sp F)⁻¹) :=
    (isB1_conj_iff (F:=F) (D.x : Sp F) a).mpr ha
  have hle := movedSpace_conjugate_le_product a _ g ha hb D.second_noncommuting hg
  rw [←he] at hle
  apply D.third_outside
  exact (movedSpace_mul_le_sup a _).trans (sup_le haU hbU) (hle hy)

end Theory.SpecificGroups.SymplecticFour.TransvectionRecognition

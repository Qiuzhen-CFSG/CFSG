module
public import Theory.GroupTheory.WeakBNPair.RegularTree.NaturalCubic
public import Theory.SpecificGroups.SL2.BorelSmallInvariant.Basic

/-!
# Cartan transitivity on a faithfully marked upper root

An upper root mapping injectively into SL₂ in characteristic two is
transitive on its nonidentity elements under a full diagonal Cartan.
The proof lifts a square root of the ratio of the two upper parameters.
Only injectivity on the root is needed; the actor kernel is retained.

The b=1 source application adjusts the whole Cartan inside the local
actor before controlling its central braid correction.
Source: DGS, Groups and Graphs (1985), (14.5), pp.213--214.
-/

@[expose] public noncomputable section
open Subgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups
namespace Theory.GroupTheory.WeakBNPair.RegularTree.NaturalCubic
variable {F X : Type*} [Field F] [Finite F] [CharP F 2] [Group X]

theorem upper_root_cartan_transitive (π : X →* SL(2,F)) (R K : Subgroup X)
    (hdis : R ⊓ π.ker=⊥) (hn : K≤normalizer (R : Set X))
    (himage : R.map π=upperUnipotent F)
    (hfull : ∀ a : F, ∀ ha : a≠0, diag2 a ha∈K.map π)
    (x y : X) (hx : x∈R) (hy : y∈R) (hxn : x≠1) (hyn : y≠1) :
    ∃ k∈K, k*x*k⁻¹=y := by
  obtain ⟨a,ha⟩ := (mem_upperUnipotent F (π x)).mp (himage ▸ mem_map_of_mem π hx)
  obtain ⟨b,hb⟩ := (mem_upperUnipotent F (π y)).mp (himage ▸ mem_map_of_mem π hy)
  have ha0 : a≠0 := by
    intro he
    apply hxn
    exact eq_one_of_root_kernel π R hdis x hx (by rw [←ha,he,transvection_coeff_zero])
  have hb0 : b≠0 := by
    intro he
    apply hyn
    exact eq_one_of_root_kernel π R hdis y hy (by rw [←hb,he,transvection_coeff_zero])
  obtain ⟨d,hd⟩ := isSquare_of_charTwo' (b/a)
  have hd0 : d≠0 := by
    intro he
    simp [he,div_eq_zero_iff,ha0,hb0] at hd
  obtain ⟨k,hk,hπk⟩ := hfull d hd0
  refine ⟨k,hk,?_⟩
  have he : π (k*x*k⁻¹)=π y := by
    rw [map_mul,map_mul,map_inv,hπk,←ha,←hb,diag_conj_upper]
    congr 1
    rw [sq,←hd,div_mul_cancel₀ _ ha0]
  have hmem := R.mul_mem ((mem_normalizer_iff.mp (hn hk) x).mp hx) (R.inv_mem hy)
  have hz := eq_one_of_root_kernel π R hdis _ hmem (by rw [map_mul,map_inv,he,mul_inv_cancel])
  exact mul_inv_eq_one.mp hz

end Theory.GroupTheory.WeakBNPair.RegularTree.NaturalCubic

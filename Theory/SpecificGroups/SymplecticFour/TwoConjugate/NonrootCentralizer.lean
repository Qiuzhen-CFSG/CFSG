module
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.Geometry

/-!
# Centralizers of nonroot central symplectic involutions

For nonzero long and short parameters, commuting with the actual central-root
matrix forces the lower-left block to vanish. The symplectic equations then
force the two diagonal entries to be one and preserve the standard flag.
Thus the centralizer is exactly the standard unipotent subgroup. Restriction
to any literal subgroup preserves the marked intersection, including the
opposite pair used in E.2.7.

Source: Aschbacher--Smith, E.2.7, printed p.220. This proves the required
centralizer calculation for the explicit nonroot matrix; it does not assert
the separate subgroup-recognition or involution-normal-form theorem.
-/

public section
open Matrix Subgroup
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.TwoConjugate
variable {F : Type*} [Field F] [CharP F 2]
local notation "a" => (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "b" => (Sum.inl (1 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "c" => (Sum.inr (0 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "d" => (Sum.inr (1 : Fin 2) : Fin 2 ⊕ Fin 2)

omit [CharP F 2] in
private theorem upper_matrix (s t : F) :
    (upper s t).val = fromBlocks 1 !![s,t;t,0] 0 1 := by
  change rootMatrix 0 s * rootMatrix 4 t = _
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.single, Matrix.fromBlocks]

/-- A matrix commuting with a central element having both root parameters
nonzero lies in the original standard unipotent subgroup. -/
theorem mem_unipotent_of_commute_upper (s t : F) (hs : s ≠ 0) (ht : t ≠ 0)
    (g : Sp F) (h : g * upper s t = upper s t * g) : g ∈ unipotent := by
  let m := g.val
  have hm := congrArg (fun x : Sp F => x.val) h
  change m * (upper s t).val = (upper s t).val * m at hm
  rw [upper_matrix] at hm
  have hc (i j : Fin 2 ⊕ Fin 2) := congrArg (fun M => M i j) hm
  have hca := hc b a
  have hcb := hc b b
  have hda := hc a a
  have hdb := hc a b
  simp [Matrix.mul_apply, Matrix.fromBlocks, Fintype.sum_sum_type,
    Fin.sum_univ_two, Matrix.one_apply] at hca hcb
  have hca0 : m c a = 0 := by simpa [m, ht] using hca.symm
  have hcb0 : m c b = 0 := by simpa [m, ht] using hcb.symm
  simp [Matrix.mul_apply, Matrix.fromBlocks, Fintype.sum_sum_type,
    Fin.sum_univ_two, Matrix.one_apply, hca0, hcb0] at hda hdb
  have hda0 : m d a = 0 := by simpa [m, hca0, ht] using hda.symm
  have hdb0 : m d b = 0 := by simpa [m, hcb0, ht] using hdb.symm
  have hform : mᵀ * Matrix.J (Fin 2) F * m = Matrix.J (Fin 2) F :=
    SymplecticGroup.mem_iff'.mp g.property
  have h13 := hc a d
  have h23 := hc b d
  have h12 := hc b c
  have h02 := hc a c
  simp [Matrix.mul_apply, Matrix.fromBlocks, Fintype.sum_sum_type,
    Fin.sum_univ_two, Matrix.one_apply] at h13 h23 h12 h02
  have h13 : m a a * t = s * m c d + t * m d d := by linear_combination h13
  have h23 : m b a * t = t * m c d := by linear_combination h23
  have h12 : m b a * s + m b b * t = t * m c c := by linear_combination h12
  have h02 : m a a * s + m a b * t = s * m c c + t * m d c := by
    linear_combination h02
  have he : m c d = m b a := by
    exact (mul_left_cancel₀ ht (by simpa [mul_comm] using h23)).symm
  have hf (i j : Fin 2 ⊕ Fin 2) := congrArg (fun M => M i j) hform
  have hfad := hf a d
  have hfac := hf a c
  have hfbc := hf b c
  simp [Matrix.mul_apply, Matrix.J, Matrix.fromBlocks, Fintype.sum_sum_type,
    Fin.sum_univ_two, Matrix.transpose_apply, hca0, hcb0, hda0, hdb0,
    CharTwo.neg_eq, Matrix.one_apply] at hfad hfac hfbc
  rw [he] at h13 hfad
  have hba : m b a = 0 := by
    by_contra hn
    have hz : m b a * (m a a + m d d) = 0 := by linear_combination hfad
    have had := CharTwo.add_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hn)
    rw [had] at h13
    have hz : s * m b a = 0 := by linear_combination -h13
    exact hn ((mul_eq_zero.mp hz).resolve_left hs)
  have hacc : m c c = m b b := by
    exact (mul_left_cancel₀ ht (by simpa [hba, mul_comm] using h12)).symm
  have had : m a a * m b b = 1 := by simpa [hba, hacc] using hfac
  have hd : m b b ≠ 0 := right_ne_zero_of_mul_eq_one had
  have had_eq : m a a = m b b := by
    rw [hacc] at hfbc h02
    have hz : m b b * (m a b + m d c) = 0 := by linear_combination hfbc
    have heq := CharTwo.add_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hd)
    rw [heq] at h02
    apply mul_left_cancel₀ hs
    linear_combination h02
  have haa : m a a = 1 := by
    apply CharTwo.sq_injective
    simpa [pow_two, ← had_eq] using had
  have hbb : m b b = 1 := had_eq.symm.trans haa
  rw [mem_unipotent_iff, mem_borel_iff]
  refine ⟨⟨hba, ?_⟩, haa, hbb⟩
  intro i j
  fin_cases i <;> fin_cases j <;> assumption

/-- The literal nonroot central involution has exactly the marked unipotent
subgroup as its full ambient centralizer. -/
theorem centralizer_upper_eq_unipotent [Finite F] (s t : F)
    (hs : s ≠ 0) (ht : t ≠ 0) :
    centralizer ({upper s t} : Set (Sp F)) = unipotent := by
  ext g
  constructor
  · intro hg
    exact mem_unipotent_of_commute_upper s t hs ht g
      (mem_centralizer_singleton_iff.mp hg)
  · intro hg
    apply mem_centralizer_singleton_iff.mpr
    have h := mem_center_iff.mp (CentralRootGeometry.theta_mem_center s t) ⟨g,hg⟩
    simpa only [← Subtype.coe_inj, Subgroup.coe_mul,
      CentralRootGeometry.theta_val, upper] using h

/-- A nonzero long parameter makes the central-root product an involution. -/
theorem upper_orderOf (s t : F) (hs : s ≠ 0) : orderOf (upper s t) = 2 := by
  apply orderOf_eq_prime_iff.mpr
  constructor
  · have he : (CentralRootGeometry.theta s t).val = upper s t :=
      CentralRootGeometry.theta_val _ _
    have hp : (CentralRootGeometry.theta s t)^2 = 1 := by
      simp [CentralRootGeometry.theta, CentralRootGeometry.element_square,
        CentralRootGeometry.element_zero]
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, he] using
      congrArg (fun x : unipotent (F := F) => x.val) hp
  · intro he
    have hc := congrArg (fun g : Sp F => g.val a c) he
    rw [upper_matrix] at hc
    exact hs (by simpa [Matrix.fromBlocks] using hc)

/-- Avoiding both root axes supplies an element with both parameters nonzero;
no field-linearity assumption on V is required. -/
theorem exists_upper_nonzero_parameters (V : Subgroup (Sp F))
    (hc : V ≤ (CentralRootGeometry.parameter (F := F)).range)
    (hl : ¬V ≤ RootSubgroup.group 0) (hs : ¬V ≤ RootSubgroup.group 4) :
    ∃ s t : F, s ≠ 0 ∧ t ≠ 0 ∧ upper s t ∈ V := by
  obtain ⟨x,hx,hxs⟩ := SetLike.not_le_iff_exists.mp hs
  obtain ⟨⟨s,t⟩,rfl⟩ := hc hx
  have hs0 : s.toAdd ≠ 0 := by
    intro he
    apply hxs
    apply (RootSubgroup.mem_group_iff 4 _).mpr
    exact ⟨t.toAdd, by simp [CentralRootGeometry.parameter_apply, he,
      RootSubgroup.element_zero]⟩
  by_cases ht0 : t.toAdd = 0
  · obtain ⟨y,hy,hyl⟩ := SetLike.not_le_iff_exists.mp hl
    obtain ⟨⟨u,v⟩,rfl⟩ := hc hy
    have hv0 : v.toAdd ≠ 0 := by
      intro he
      apply hyl
      apply (RootSubgroup.mem_group_iff 0 _).mpr
      exact ⟨u.toAdd, by simp [CentralRootGeometry.parameter_apply, he,
        RootSubgroup.element_zero]⟩
    by_cases hu0 : u.toAdd = 0
    · refine ⟨s.toAdd,v.toAdd,hs0,hv0,?_⟩
      have hh := V.mul_mem hx hy
      rw [← map_mul] at hh
      simpa [CentralRootGeometry.parameter_apply, ht0, hu0, upper] using hh
    · exact ⟨u.toAdd,v.toAdd,hu0,hv0,by
        simpa only [CentralRootGeometry.parameter_apply, upper] using hy⟩
  · exact ⟨s.toAdd,t.toAdd,hs0,ht0,by
      simpa only [CentralRootGeometry.parameter_apply, upper] using hx⟩

/-- Inside the original subgroup, the same centralizer is its literal
intersection with the marked unipotent subgroup. -/
theorem subgroup_centralizer_upper [Finite F] (I : Subgroup (Sp F))
    (s t : F) (hs : s ≠ 0) (ht : t ≠ 0) (hi : upper s t ∈ I) :
    centralizer ({⟨upper s t,hi⟩} : Set I) = (unipotent (F := F)).subgroupOf I := by
  ext x
  rw [mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf,
    ← centralizer_upper_eq_unipotent s t hs ht, mem_centralizer_singleton_iff,
    ← Subtype.coe_inj]
  rfl

end Theory.SpecificGroups.SymplecticFour.TwoConjugate

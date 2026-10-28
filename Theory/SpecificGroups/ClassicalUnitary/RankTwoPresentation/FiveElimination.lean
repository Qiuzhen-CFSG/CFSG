module
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FiveCoordinates
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.ModelEightCells
import Mathlib.Tactic.Group

/-!
# Whole-SU₅ generation by the rank-two presentation generators

Choose a hyperbolic pivot in the first isotropic column. The C, A and full
Hermitian D roots clear it, and coordinate reversal moves it to the marked
line. In its stabilizer, the Hermitian B root and point reflection clear the
second column modulo the first. The resulting matrix lies in the literal
plane parabolic, whose complete radical and GL₂ Levi are already generated.
No line-Levi product splitting, simplicity or q=4 restriction is used; the
canonical scalar kernel remains in the generated group.
Source: Steinberg, Lectures on Chevalley Groups, Theorem 33 and Lemmas 63–64.
-/
@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FiveElimination
open FivePositive FiveWeyl FiveCoordinates
open Theory.SpecificGroups.UnitaryFive PlaneCore SmallCompletion FivePaths
variable {E : Type*} [Field E] [CharP E 2]
variable (J : HermitianForm 5 E) (κ : E) (hκ : κ+J.conj κ=1) (hJ : J.form=1)

/-- The rank-one clearing parameter retains the complete Hermitian equation. -/
def clearParameter (a b c : E) (hc : c≠0)
    (hi : J.conj a*c+J.conj b*b+J.conj c*a=0) : Parameter J :=
  ⟨(J.conj (b/c),J.conj (a/c)),by
    change J.conj (a/c)+J.conj (J.conj (a/c))+
      J.conj (b/c)*J.conj (J.conj (b/c))=0
    rw [J.conj_involutive,J.conj_involutive]
    simp only [map_div₀]
    have hc' : J.conj c≠0 := (map_ne_zero J.conj).mpr hc
    field_simp
    linear_combination hi⟩

omit [CharP E 2] in
theorem clear_first (a b c : E) (hc : c≠0)
    (hi : J.conj a*c+J.conj b*b+J.conj c*a=0) :
    a+(clearParameter J a b c hc hi).val.1*b+(clearParameter J a b c hc hi).val.2*c=0 := by
  dsimp [clearParameter]
  rw [map_div₀,map_div₀]
  have hc' : J.conj c≠0 := (map_ne_zero J.conj).mpr hc
  field_simp
  linear_combination hi

theorem clear_middle (a b c : E) (hc : c≠0)
    (hi : J.conj a*c+J.conj b*b+J.conj c*a=0) :
    b+J.conj (clearParameter J a b c hc hi).val.1*c=0 := by
  simp [clearParameter,div_mul_cancel₀ _ hc,CharTwo.add_self_eq_zero]

local notation "H" => ReflectionLaws.fullGenerated (roots J κ hκ hJ)
  (h J κ hκ hJ) (s J κ hκ hJ) (t J κ hκ hJ)

private theorem borel_le : (roots J κ hκ hJ).borel (h J κ hκ hJ)≤H :=
  fun _ hx => Subgroup.subset_closure (Or.inl hx)

theorem A_mem (a : E) : A J κ hκ hJ a∈H :=
  borel_le J κ hκ hJ ((roots J κ hκ hJ).A_mem_borel (h J κ hκ hJ) (Multiplicative.ofAdd a))
theorem B_mem (p : Parameter J) : B J hJ p∈H :=
  borel_le J κ hκ hJ ((roots J κ hκ hJ).B_mem_borel (h J κ hκ hJ) p)
theorem C_mem (a : E) : C J hJ a∈H :=
  borel_le J κ hκ hJ ((roots J κ hκ hJ).C_mem_borel (h J κ hκ hJ) (Multiplicative.ofAdd a))
theorem D_mem (p : Parameter J) : D J hJ p∈H :=
  borel_le J κ hκ hJ ((roots J κ hκ hJ).D_mem_borel (h J κ hκ hJ) p)
theorem s_mem : s J κ hκ hJ∈H := Subgroup.subset_closure (Or.inr (Or.inl rfl))
theorem t_mem : t J κ hκ hJ∈H := Subgroup.subset_closure (Or.inr (Or.inr rfl))

/-- The previously proved full plane radical and GL₂ Levi are already generated. -/
theorem plane_le : specialStabilizer J (plane E)≤H := by
  apply FiveRootGeneration.plane_le J κ hκ hJ H
  · exact A_mem J κ hκ hJ
  · intro x z hz
    let p : Parameter J := ⟨(x,z),by
      change z+J.conj z+x*J.conj x=0
      rw [hz,CharTwo.add_self_eq_zero]⟩
    exact B_mem J κ hκ hJ p
  · exact t_mem J κ hκ hJ
  · exact s_mem J κ hκ hJ
  · intro g hg
    exact borel_le J κ hκ hJ (Subgroup.mem_sup_right (diagonal_in_torus J κ hκ hJ g hg))

/-- A signed coordinate permutation chooses a nonzero last-coordinate pivot. -/
theorem exists_pivot (g : J.specialSubgroup) :
    ∃ w∈H, evaluate J κ (w*g) 4 0≠0 := by
  let M := evaluate J κ g
  by_cases h4 : M 4 0≠0
  · exact ⟨1,(H).one_mem,by simpa using h4⟩
  by_cases h3 : M 3 0≠0
  · refine ⟨s J κ hκ hJ,s_mem J κ hκ hJ,?_⟩
    simpa [map_mul,evaluate_s,Matrix5.S,Matrix.mul_apply,Fin.sum_univ_succ] using h3
  by_cases h1 : M 1 0≠0
  · refine ⟨s J κ hκ hJ*t J κ hκ hJ,(H).mul_mem (s_mem J κ hκ hJ) (t_mem J κ hκ hJ),?_⟩
    simpa [map_mul,evaluate_s,evaluate_t,Matrix.mul_assoc,Matrix5.S,Matrix5.T,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ] using h1
  by_cases h0 : M 0 0≠0
  · refine ⟨s J κ hκ hJ*t J κ hκ hJ*s J κ hκ hJ,
      (H).mul_mem ((H).mul_mem (s_mem J κ hκ hJ) (t_mem J κ hκ hJ)) (s_mem J κ hκ hJ),?_⟩
    simpa [map_mul,evaluate_s,evaluate_t,Matrix.mul_assoc,Matrix5.S,Matrix5.T,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ] using h0
  push Not at h4 h3 h1 h0
  have hi := pair_columns J κ hκ hJ g 0 0
  change pair J (fun i => M i 0) (fun i => M i 0)=0 at hi
  have h2 : M 2 0=0 := by
    have hh : J.conj (M 2 0)*M 2 0=0 := by simpa [pair,h0,h1,h3,h4] using hi
    exact (mul_eq_zero.mp hh).elim (fun hz => (map_eq_zero J.conj).mp hz) id
  exact (column_ne_zero J κ g 0 (by ext i; fin_cases i <;> assumption)).elim

/-- Once the final pivot is nonzero, three positive root operations clear the
first column to that pivot. -/
theorem clear_pivot (g : J.specialSubgroup) (hp : evaluate J κ g 4 0≠0) :
    ∃ u∈H, ∀ i, i≠4 → evaluate J κ (u*g) i 0=0 := by
  let c := C J hJ (J.conj (evaluate J κ g 1 0/evaluate J κ g 4 0))
  let g1 := c*g
  have hc : c∈H := C_mem J κ hκ hJ _
  have h14 : evaluate J κ g1 4 0=evaluate J κ g 4 0 := by
    simp [g1,c,map_mul,evaluate_C,Matrix5.C,Matrix.mul_apply,Fin.sum_univ_succ]
  have h11 : evaluate J κ g1 1 0=0 := by
    simp [g1,c,map_mul,evaluate_C,Matrix5.C,Matrix.mul_apply,Fin.sum_univ_succ,
      div_mul_cancel₀ _ hp,CharTwo.add_self_eq_zero]
  let a := A J κ hκ hJ (J.conj (evaluate J κ g1 3 0/evaluate J κ g1 4 0))
  let g2 := a*g1
  have ha : a∈H := A_mem J κ hκ hJ _
  have h24 : evaluate J κ g2 4 0=evaluate J κ g1 4 0 := by
    simp [g2,a,map_mul,evaluate_A,Matrix5.A,Matrix.mul_apply,Fin.sum_univ_succ]
  have hp2 : evaluate J κ g2 4 0≠0 := by rwa [h24,h14]
  have h21 : evaluate J κ g2 1 0=0 := by
    simpa [g2,a,map_mul,evaluate_A,Matrix5.A,Matrix.mul_apply,Fin.sum_univ_succ] using h11
  have h23 : evaluate J κ g2 3 0=0 := by
    have hp1 : evaluate J κ g1 4 0≠0 := by rwa [h14]
    simp [g2,a,map_mul,evaluate_A,Matrix5.A,Matrix.mul_apply,Fin.sum_univ_succ,
      div_mul_cancel₀ _ hp1,CharTwo.add_self_eq_zero]
  have hi : J.conj (evaluate J κ g2 0 0)*evaluate J κ g2 4 0+
      J.conj (evaluate J κ g2 2 0)*evaluate J κ g2 2 0+
      J.conj (evaluate J κ g2 4 0)*evaluate J κ g2 0 0=0 := by
    simpa [pair,h21,h23] using pair_columns J κ hκ hJ g2 0 0
  let p := clearParameter J _ _ _ hp2 hi
  refine ⟨D J hJ p*a*c,(H).mul_mem ((H).mul_mem (D_mem J κ hκ hJ p) ha) hc,?_⟩
  intro i hi4
  have he : (D J hJ p*a*c)*g=D J hJ p*g2 := by dsimp [g2,g1]; group
  rw [he,map_mul,evaluate_D]
  fin_cases i
  · simpa [Matrix5.D,Matrix.mul_apply,Fin.sum_univ_succ,add_assoc] using clear_first J _ _ _ hp2 hi
  · simpa [Matrix5.D,Matrix.mul_apply,Fin.sum_univ_succ] using h21
  · simpa [Matrix5.D,Matrix.mul_apply,Fin.sum_univ_succ] using clear_middle J _ _ _ hp2 hi
  · simpa [Matrix5.D,Matrix.mul_apply,Fin.sum_univ_succ] using h23
  · exact (hi4 rfl).elim

/-- The generated group moves every first isotropic column to the marked line. -/
theorem exists_line [Finite E] (g : J.specialSubgroup) :
    ∃ u∈H, u*g∈specialStabilizer J (line E) := by
  obtain ⟨w,hw,hp⟩ := exists_pivot J κ hκ hJ g
  obtain ⟨v,hv,hvcol⟩ := clear_pivot J κ hκ hJ (w*g) hp
  let r := (s J κ hκ hJ*t J κ hκ hJ)^2
  have hr : r∈H := (H).pow_mem ((H).mul_mem (s_mem J κ hκ hJ) (t_mem J κ hκ hJ)) 2
  refine ⟨r*v*w,(H).mul_mem ((H).mul_mem hr hv) hw,?_⟩
  apply (mem_line_iff J κ _).mpr
  intro i hi
  have he : (r*v*w)*g=r*(v*(w*g)) := by group
  rw [he,map_mul]
  have hR : evaluate J κ r=!![0,0,0,0,1;0,0,0,1,0;0,0,1,0,0;0,1,0,0,0;1,0,0,0,0] := by
    dsimp [r]; rw [map_pow,map_mul,evaluate_s,evaluate_t,Matrix5.ST_sq]
  rw [hR]
  have hh := hvcol i.rev (by fin_cases i <;> simp_all [Fin.rev])
  fin_cases i <;> simpa [Matrix.mul_apply,Fin.sum_univ_succ,Fin.rev] using hh
/-- Inside the line stabilizer, one Hermitian root and the point reflection
move the second column into the marked plane. -/
theorem exists_plane [Finite E] (g : J.specialSubgroup)
    (hg : g∈specialStabilizer J (line E)) :
    ∃ u∈H, u*g∈specialStabilizer J (plane E) := by
  let M := evaluate J κ g
  have hcol : ∀ i, i≠0 → M i 0=0 := (mem_line_iff J κ g).mp hg
  have h00 : M 0 0≠0 := by
    intro hh
    apply column_ne_zero J κ g 0
    ext i
    fin_cases i
    · exact hh
    all_goals exact hcol _ (by decide)
  have h41 : M 4 1=0 := by
    have he := pair_columns J κ hκ hJ g 0 1
    change pair J (fun i => M i 0) (fun i => M i 1)=0 at he
    have hh : J.conj (M 0 0)*M 4 1=0 := by
      simpa [pair,hcol 1 (by decide),hcol 2 (by decide),hcol 3 (by decide),hcol 4 (by decide)] using he
    exact (mul_eq_zero.mp hh).resolve_left ((map_ne_zero J.conj).mpr h00)
  have hi : J.conj (M 1 1)*M 3 1+J.conj (M 2 1)*M 2 1+J.conj (M 3 1)*M 1 1=0 := by
    have he := pair_columns J κ hκ hJ g 1 1
    change pair J (fun i => M i 1) (fun i => M i 1)=0 at he
    simpa [pair,h41] using he
  by_cases hp : M 3 1=0
  · have h21 : M 2 1=0 := by
      have he : J.conj (M 2 1)*M 2 1=0 := by simpa [hp] using hi
      exact (mul_eq_zero.mp he).elim (fun hz => (map_eq_zero J.conj).mp hz) id
    refine ⟨1,(H).one_mem,?_⟩
    rw [one_mul]
    apply (mem_plane_iff J κ g).mpr
    intro i j hi hj
    rcases hj with rfl|rfl
    · exact hcol i (by rcases hi with rfl|rfl|rfl <;> decide)
    · rcases hi with rfl|rfl|rfl
      · exact h21
      · exact hp
      · exact h41
  · let p := clearParameter J _ _ _ hp hi
    let u := t J κ hκ hJ*B J hJ p
    have hu : u∈H := (H).mul_mem (t_mem J κ hκ hJ) (B_mem J κ hκ hJ p)
    have hbline : B J hJ p∈specialStabilizer J (line E) := by
      apply (mem_line_iff J κ _).mpr
      intro i hi
      rw [evaluate_B]
      fin_cases i <;> simp_all [Matrix5.B]
    have huline : u*g∈specialStabilizer J (line E) :=
      (specialStabilizer J (line E)).mul_mem
        ((specialStabilizer J (line E)).mul_mem (middleSwap_mem_line J κ hκ hJ) hbline) hg
    refine ⟨u,hu,(mem_plane_iff J κ _).mpr ?_⟩
    intro i j hij hj
    rcases hj with rfl|rfl
    · exact (mem_line_iff J κ _).mp huline i (by rcases hij with rfl|rfl|rfl <;> decide)
    · change evaluate J κ ((t J κ hκ hJ*B J hJ p)*g) i 1=0
      simp only [map_mul,evaluate_t,evaluate_B,Matrix.mul_assoc]
      rcases hij with rfl|rfl|rfl
      · simpa [Matrix5.T,Matrix5.B,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ] using clear_middle J _ _ _ hp hi
      · simpa [Matrix5.T,Matrix5.B,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ,add_assoc] using clear_first J _ _ _ hp hi
      · simpa [Matrix5.T,Matrix5.B,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ] using h41

/-- General-parameter SU₅ generation, including q=2 and the complete scalar
center. Two isotropic columns reduce to the full existing plane parabolic. -/
theorem fullGenerated_eq_top [Finite E] : H=⊤ := by
  apply top_unique
  intro g _
  obtain ⟨u,hu,hug⟩ := exists_line J κ hκ hJ g
  obtain ⟨v,hv,hvug⟩ := exists_plane J κ hκ hJ (u*g) hug
  have hm : v*(u*g)∈H := plane_le J κ hκ hJ hvug
  have he : g=u⁻¹*(v⁻¹*(v*(u*g))) := by group
  rw [he]
  exact (H).mul_mem ((H).inv_mem hu) ((H).mul_mem ((H).inv_mem hv) hm)

end Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FiveElimination

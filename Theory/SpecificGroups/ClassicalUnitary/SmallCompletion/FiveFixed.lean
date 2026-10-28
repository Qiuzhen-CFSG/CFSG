module
public import Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FiveCartan
public import Theory.SpecificGroups.ClassicalUnitary.FiveIsotropicGeometry
public import Mathlib.FieldTheory.Fixed

/-!
# Split-torus fixed flags in Hermitian five-space

In the existing hyperbolic coordinates, the fixed-field split torus has
entries a, b, 1, a⁻¹, b⁻¹. Its fixed flags at either endpoint are precisely
the two coordinate reflection cosets. At the point endpoint the Hermitian
equation eliminates the anisotropic middle coordinate after eigenvalue
separation on the other two quotient coordinates. All calculations take
place in SU₅; the projective consumer retains its actual scalar kernel.

This is the local fixed-neighbor input for the Cartan apartment route of
Aschbacher–Smith F.4.10,16–17, printed pp.279,282–283 of
`refs/quasithin.pdf`, specialized by the consumer to PSU₅(4).
-/

@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.UnitaryFive.SmallCompletion.FiveFixed
open PlaneCore FivePaths
variable {F : Type*} [Field F] [CharP F 2]
variable (J : HermitianForm 5 F) (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)
local notation "K" => FixedBy.subfield F J.conj

def torusDiagonal (a b : Kˣ) : GL (Fin 5) F :=
  { val := diagonal ![((a : K) : F),((b : K) : F),1,((a⁻¹ : Kˣ) : K),((b⁻¹ : Kˣ) : K)]
    inv := diagonal ![(((a⁻¹ : Kˣ) : K) : F),((b⁻¹ : Kˣ) : K),1,((a : K) : F),((b : K) : F)]
    val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp
    inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp }

omit [CharP F 2] in
private theorem torusDiagonal_preserves (a b : Kˣ) :
    J.conjTranspose (torusDiagonal J a b).val * planeGram * (torusDiagonal J a b).val=planeGram := by
  have ha : J.conj ((a : K) : F)=((a : K) : F) := (a : K).property
  have hb : J.conj ((b : K) : F)=((b : K) : F) := (b : K).property
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torusDiagonal,HermitianForm.conjTranspose,planeGram,Matrix.mul_apply,Fin.sum_univ_succ,ha,hb]

include hc hJ in
private theorem conjugate_mem (d : GL (Fin 5) F)
    (hd : J.conjTranspose d.val * planeGram * d.val = planeGram) (hdet : d.val.det=1) :
    planeBasisGL c * d * (planeBasisGL c)⁻¹ ∈ J.specialSubgroup := by
  rw [J.mem_specialSubgroup_iff]
  constructor
  · change J.conjTranspose (planeBasis c*d.val*planeBasisInv c) * J.form *
        (planeBasis c*d.val*planeBasisInv c)=J.form
    rw [ct_mul,ct_mul]
    have hgram : J.conjTranspose (planeBasis c)*J.form*planeBasis c=planeGram := planeBasis_gram J c hc hJ
    have hi : J.conjTranspose (planeBasisInv c)*J.conjTranspose (planeBasis c)=1 := by
      rw [←ct_mul,planeBasis_mul_inv]
      change ((J.conj : F →+* F).mapMatrix 1).transpose=1
      rw [map_one,Matrix.transpose_one]
    calc
      _ = J.conjTranspose (planeBasisInv c) *
          (J.conjTranspose d.val * (J.conjTranspose (planeBasis c)*J.form*planeBasis c)*d.val)*planeBasisInv c := by simp only [mul_assoc]
      _ = J.conjTranspose (planeBasisInv c)*planeGram*planeBasisInv c := by rw [hgram,hd]
      _ = J.form := by rw [←hgram]; calc
        _ = (J.conjTranspose (planeBasisInv c)*J.conjTranspose (planeBasis c))*J.form*(planeBasis c*planeBasisInv c) := by simp only [mul_assoc]
        _ = _ := by rw [hi,planeBasis_mul_inv]; simp
  · apply Units.ext
    rw [GeneralLinearGroup.val_det_apply]
    change (planeBasis c*d.val*planeBasisInv c).det=1
    rw [Matrix.det_mul,Matrix.det_mul,hdet,mul_one,←Matrix.det_mul,planeBasis_mul_inv,Matrix.det_one]

def torus (hc : c + J.conj c = 1) (hJ : J.form = 1) (a b : Kˣ) : J.specialSubgroup :=
  ⟨planeBasisGL c*torusDiagonal J a b*(planeBasisGL c)⁻¹,
    by exact conjugate_mem J c hc hJ _ (torusDiagonal_preserves J a b) (by
      simp [torusDiagonal,Matrix.det_diagonal,Fin.prod_univ_succ]
      field_simp)⟩

theorem torus_coordinates (a b : Kˣ) : coordinates J c (torus J c hc hJ a b)=torusDiagonal J a b := by
  change (planeBasisGL c)⁻¹ * (planeBasisGL c*torusDiagonal J a b*(planeBasisGL c)⁻¹)*planeBasisGL c=_
  group

theorem point_torus (a b : Kˣ) :
    middleSwap J c hc hJ * torus J c hc hJ a b * middleSwap J c hc hJ=torus J c hc hJ a b⁻¹ := by
  apply coordinates_injective J c
  rw [map_mul,map_mul,coordinates_middleSwap,torus_coordinates,torus_coordinates]
  apply Units.ext
  change (blockPerm middlePerm).val*(torusDiagonal J a b).val*(blockPerm middlePerm).val=_
  rw [middle_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torusDiagonal,Matrix.mul_apply,Matrix.vecMul,Fin.sum_univ_succ]

theorem plane_torus (a b : Kˣ) :
    pairSwap J c hc hJ * torus J c hc hJ a b * pairSwap J c hc hJ=torus J c hc hJ b a := by
  apply coordinates_injective J c
  rw [map_mul,map_mul,coordinates_pairSwap,torus_coordinates,torus_coordinates]
  apply Units.ext
  change (blockPerm pairPerm).val*(torusDiagonal J a b).val*(blockPerm pairPerm).val=_
  rw [pair_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torusDiagonal,Matrix.mul_apply,Matrix.vecMul,Fin.sum_univ_succ]

private theorem action_coordinates (g : J.specialSubgroup) (v : Fin 5 → F) :
    linearAction J g v = planeBasis c *ᵥ ((coordinates J c g).val *ᵥ (planeBasisInv c *ᵥ v)) := by
  change g.val.val*ᵥ v=_
  rw [coordinates_val,mulVec_mulVec,mulVec_mulVec]
  have he : planeBasis c * (planeBasisInv c * g.val.val * planeBasis c) * planeBasisInv c=g.val.val := by
    simp only [←mul_assoc,planeBasis_mul_inv,one_mul]
    rw [mul_assoc,planeBasis_mul_inv,mul_one]
  rw [he]

theorem mem_line_iff [Finite F] (g : J.specialSubgroup) :
    g∈specialStabilizer J (line F) ↔ ∀ i, i≠0 → (coordinates J c g).val i 0=0 := by
  constructor
  · exact coordinates_line J c g
  · intro h
    apply IsotropicGeometry.mem_specialStabilizer_of_preserves J
    intro v hv
    rw [action_coordinates J c g]
    obtain ⟨hv1,hv2,hv3,hv4⟩ := hv
    have hw : planeBasisInv c *ᵥ v=![v 0,0,0,0,0] := by
      ext i
      fin_cases i <;> simp [planeBasisInv,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,hv1,hv2,hv3,hv4,
        add_mul,CharTwo.add_self_eq_zero,add_assoc,add_left_comm]
    rw [hw]
    have h1 := h 1 (by decide)
    have h2 := h 2 (by decide)
    have h3 := h 3 (by decide)
    have h4 := h 4 (by decide)
    have hi : (coordinates J c g).val *ᵥ ![v 0,0,0,0,0] =
        ![(coordinates J c g).val 0 0*v 0,0,0,0,0] := by
      ext i
      fin_cases i <;> simp [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,h1,h2,h3,h4]
    rw [hi]
    simp [line,planeBasis]

theorem mem_plane_iff [Finite F] (g : J.specialSubgroup) :
    g∈specialStabilizer J (plane F) ↔ ∀ i j, (i=2 ∨ i=3 ∨ i=4) → (j=0 ∨ j=1) →
      (coordinates J c g).val i j=0 := by
  constructor
  · exact coordinates_plane J c g
  · intro h
    apply IsotropicGeometry.mem_specialStabilizer_of_preserves J
    intro v hv
    rw [action_coordinates J c g]
    obtain ⟨hv1,hv3,hv4⟩ := hv
    have hw : planeBasisInv c *ᵥ v=![v 0,v 2,0,0,0] := by
      ext i
      fin_cases i <;> simp [planeBasisInv,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,hv1,hv3,hv4,
        add_mul,CharTwo.add_self_eq_zero,add_assoc,add_left_comm]
    rw [hw]
    have h20 := h 2 0 (by simp) (by simp)
    have h21 := h 2 1 (by simp) (by simp)
    have h30 := h 3 0 (by simp) (by simp)
    have h31 := h 3 1 (by simp) (by simp)
    have h40 := h 4 0 (by simp) (by simp)
    have h41 := h 4 1 (by simp) (by simp)
    have hi : (coordinates J c g).val *ᵥ ![v 0,v 2,0,0,0] =
        ![(coordinates J c g).val 0 0*v 0+(coordinates J c g).val 0 1*v 2,
          (coordinates J c g).val 1 0*v 0+(coordinates J c g).val 1 1*v 2,0,0,0] := by
      ext i
      fin_cases i <;> simp [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,h20,h21,h30,h31,h40,h41]
    rw [hi]
    simp [plane,planeBasis]

theorem torus_mem [Finite F] (a b : Kˣ) :
    torus J c hc hJ a b∈specialStabilizer J (line F) ⊓ specialStabilizer J (plane F) := by
  constructor
  · apply (mem_line_iff J c _).mpr
    intro i hi
    rw [torus_coordinates]
    exact Matrix.diagonal_apply_ne _ hi
  · apply (mem_plane_iff J c _).mpr
    intro i j hi hj
    rw [torus_coordinates]
    rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl <;> rfl

private theorem separating_unit [Finite F] (hq : 2 < Nat.card K) :
    ∃ a : Kˣ, ((a : K) : F) ≠ 1 ∧ ((a : K) : F) ≠ ((a⁻¹ : Kˣ) : K) := by
  have hcard : 1 < Nat.card Kˣ := by rw [Nat.card_units]; omega
  let : Nontrivial Kˣ := Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨a,ha⟩ := exists_ne (1 : Kˣ)
  have ha1 : ((a : K) : F) ≠ 1 := fun h => ha (Units.ext (Subtype.ext h))
  refine ⟨a,ha1,?_⟩
  intro h
  apply ha1
  apply CharTwo.sq_injective
  calc
    ((a : K) : F)^2 = ((a : K) : F)*((a⁻¹ : Kˣ) : K) := by rw [pow_two,h]
    _ = (1 : F)^2 := by simp

private theorem conjugate_equation (g t : J.specialSubgroup) :
    (coordinates J c t).val*(coordinates J c g).val=
      (coordinates J c g).val*(coordinates J c (g⁻¹*t*g)).val := by
  have h : t*g=g*(g⁻¹*t*g) := by group
  have hh := congrArg (coordinates J c) h
  rw [map_mul (coordinates J c) t g,map_mul (coordinates J c) g (g⁻¹*t*g)] at hh
  exact congrArg Units.val hh

theorem plane_fixed_coset [Finite F] (hq : 2 < Nat.card K) (g : J.specialSubgroup)
    (hg : g∈specialStabilizer J (plane F))
    (hfix : ∀ a b : Kˣ,g⁻¹*torus J c hc hJ a b*g∈specialStabilizer J (line F) ⊓ specialStabilizer J (plane F)) :
    g∈specialStabilizer J (line F) ⊓ specialStabilizer J (plane F) ∨
      pairSwap J c hc hJ*g∈specialStabilizer J (line F) ⊓ specialStabilizer J (plane F) := by
  obtain ⟨a,ha,_⟩ := separating_unit J hq
  let t := torus J c hc hJ a 1
  let z := g⁻¹*t*g
  let A := (coordinates J c g).val
  let Z := (coordinates J c z).val
  have hz := (hfix a 1).1
  have hz1 : Z 1 0=0 := coordinates_line J c z hz 1 (by decide)
  have hz2 : Z 2 0=0 := coordinates_line J c z hz 2 (by decide)
  have hz3 : Z 3 0=0 := coordinates_line J c z hz 3 (by decide)
  have hz4 : Z 4 0=0 := coordinates_line J c z hz 4 (by decide)
  have h20 : A 2 0=0 := coordinates_plane J c g hg 2 0 (by simp) (by simp)
  have h30 : A 3 0=0 := coordinates_plane J c g hg 3 0 (by simp) (by simp)
  have h40 : A 4 0=0 := coordinates_plane J c g hg 4 0 (by simp) (by simp)
  have hm := conjugate_equation J c g t
  change (coordinates J c t).val*A=A*Z at hm
  have h0 : ((a : K) : F)*A 0 0=A 0 0*Z 0 0 := by
    have h := congrArg (fun D : Matrix (Fin 5) (Fin 5) F => D 0 0) hm
    simpa [t,torus_coordinates,torusDiagonal,Matrix.mul_apply,Fin.sum_univ_succ,hz1,hz2,hz3,hz4] using h
  have h1 : A 1 0=A 1 0*Z 0 0 := by
    have h := congrArg (fun D : Matrix (Fin 5) (Fin 5) F => D 1 0) hm
    simpa [t,torus_coordinates,torusDiagonal,Matrix.mul_apply,Fin.sum_univ_succ,hz1,hz2,hz3,hz4] using h
  by_cases h10 : A 1 0=0
  · left
    refine ⟨(mem_line_iff J c g).mpr ?_,hg⟩
    intro i hi
    change A i 0=0
    fin_cases i
    · exact (hi rfl).elim
    · exact h10
    · exact h20
    · exact h30
    · exact h40
  · have hz0 : Z 0 0=1 := by apply mul_left_cancel₀ h10; simpa using h1.symm
    have h00 : A 0 0=0 := by
      rw [hz0,mul_one] at h0
      exact (mul_eq_mul_right_iff.mp (h0.trans (one_mul _).symm)).resolve_left ha
    right
    refine ⟨(mem_line_iff J c _).mpr ?_,(specialStabilizer J (plane F)).mul_mem (pairSwap_mem_plane J c hc hJ) hg⟩
    intro i hi
    rw [map_mul,coordinates_pairSwap]
    change ((blockPerm (F := F) pairPerm).val*A) i 0=0
    rw [pair_matrix]
    fin_cases i <;> simp_all [Matrix.mul_apply,Fin.sum_univ_succ]

include hc hJ in
private theorem point_row (g : J.specialSubgroup) (hg : g∈specialStabilizer J (line F)) :
    (coordinates J c g).val 3 1=0 := by
  let A := (coordinates J c g).val
  have h10 : A 1 0=0 := coordinates_line J c g hg 1 (by decide)
  have h20 : A 2 0=0 := coordinates_line J c g hg 2 (by decide)
  have h30 : A 3 0=0 := coordinates_line J c g hg 3 (by decide)
  have h40 : A 4 0=0 := coordinates_line J c g hg 4 (by decide)
  have hu := FiveCartan.coordinates_preserves J c hc hJ g
  change J.conjTranspose A*planeGram*A=planeGram at hu
  have he := congrArg (fun D : Matrix (Fin 5) (Fin 5) F => D 0 3) hu
  have hz := congrArg (fun D : Matrix (Fin 5) (Fin 5) F => D 0 1) hu
  simp [HermitianForm.conjTranspose,planeGram,Matrix.mul_apply,Fin.sum_univ_succ,h10,h20,h30,h40] at he hz
  have hn : A 0 0≠0 := by intro hh; simp [hh] at he
  exact hz.resolve_left hn

include hc hJ in
private theorem isotropic_column (g : J.specialSubgroup)
    (h31 : (coordinates J c g).val 3 1=0)
    (hz : (coordinates J c g).val 1 1=0 ∨ (coordinates J c g).val 4 1=0) :
    (coordinates J c g).val 2 1=0 := by
  let A := (coordinates J c g).val
  change A 3 1=0 at h31
  change A 1 1=0 ∨ A 4 1=0 at hz
  have hu := FiveCartan.coordinates_preserves J c hc hJ g
  have he := congrArg (fun D : Matrix (Fin 5) (Fin 5) F => D 1 1) hu
  change (J.conjTranspose A*(planeGram : Matrix (Fin 5) (Fin 5) F)*A) 1 1=planeGram 1 1 at he
  have hh : J.conj (A 2 1)*A 2 1=0 := by
    rcases hz with hz | hz <;>
      simpa [HermitianForm.conjTranspose,planeGram,Matrix.mul_apply,Fin.sum_univ_succ,h31,hz] using he
  rcases mul_eq_zero.mp hh with hh | hh
  · exact J.conj.injective (hh.trans (map_zero _).symm)
  · exact hh

theorem point_fixed_coset [Finite F] (hq : 2 < Nat.card K) (g : J.specialSubgroup)
    (hg : g∈specialStabilizer J (line F))
    (hfix : ∀ a b : Kˣ,g⁻¹*torus J c hc hJ a b*g∈specialStabilizer J (line F) ⊓ specialStabilizer J (plane F)) :
    g∈specialStabilizer J (line F) ⊓ specialStabilizer J (plane F) ∨
      middleSwap J c hc hJ*g∈specialStabilizer J (line F) ⊓ specialStabilizer J (plane F) := by
  obtain ⟨a,_,ha⟩ := separating_unit J hq
  let t := torus J c hc hJ 1 a
  let z := g⁻¹*t*g
  let A := (coordinates J c g).val
  let Z := (coordinates J c z).val
  have hz := (hfix 1 a).2
  have hz2 : Z 2 1=0 := coordinates_plane J c z hz 2 1 (by simp) (by simp)
  have hz3 : Z 3 1=0 := coordinates_plane J c z hz 3 1 (by simp) (by simp)
  have hz4 : Z 4 1=0 := coordinates_plane J c z hz 4 1 (by simp) (by simp)
  have h10 : A 1 0=0 := coordinates_line J c g hg 1 (by decide)
  have h20 : A 2 0=0 := coordinates_line J c g hg 2 (by decide)
  have h30 : A 3 0=0 := coordinates_line J c g hg 3 (by decide)
  have h40 : A 4 0=0 := coordinates_line J c g hg 4 (by decide)
  have h31 : A 3 1=0 := point_row J c hc hJ g hg
  have hm := conjugate_equation J c g t
  change (coordinates J c t).val*A=A*Z at hm
  have h1 : ((a : K) : F)*A 1 1=A 1 1*Z 1 1 := by
    have h := congrArg (fun D : Matrix (Fin 5) (Fin 5) F => D 1 1) hm
    simpa [t,torus_coordinates,torusDiagonal,Matrix.mul_apply,Fin.sum_univ_succ,hz2,hz3,hz4,h10] using h
  have h4 : (((a⁻¹ : Kˣ) : K) : F)*A 4 1=A 4 1*Z 1 1 := by
    have h := congrArg (fun D : Matrix (Fin 5) (Fin 5) F => D 4 1) hm
    simpa [t,torus_coordinates,torusDiagonal,Matrix.mul_apply,Fin.sum_univ_succ,hz2,hz3,hz4,h40] using h
  by_cases h41 : A 4 1=0
  · left
    have h21 : A 2 1=0 := isotropic_column J c hc hJ g h31 (Or.inr h41)
    refine ⟨hg,(mem_plane_iff J c g).mpr ?_⟩
    intro i j hi hj
    rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl <;> assumption
  · have hza : Z 1 1=(((a⁻¹ : Kˣ) : K) : F) := by
      apply mul_right_cancel₀ h41
      simpa only [mul_comm _ (A 4 1)] using h4.symm
    have h11 : A 1 1=0 := by
      rw [hza,mul_comm (A 1 1)] at h1
      exact (mul_eq_mul_right_iff.mp h1).resolve_left ha
    have h21 : A 2 1=0 := isotropic_column J c hc hJ g h31 (Or.inl h11)
    right
    refine ⟨(specialStabilizer J (line F)).mul_mem (middleSwap_mem_line J c hc hJ) hg,
      (mem_plane_iff J c _).mpr ?_⟩
    intro i j hi hj
    rw [map_mul,coordinates_middleSwap]
    change ((blockPerm (F := F) middlePerm).val*A) i j=0
    rw [middle_matrix]
    rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl <;>
      simp [Matrix.mul_apply,Fin.sum_univ_succ,h10,h20,h30,h11,h21,h31]

end Theory.SpecificGroups.UnitaryFive.SmallCompletion.FiveFixed

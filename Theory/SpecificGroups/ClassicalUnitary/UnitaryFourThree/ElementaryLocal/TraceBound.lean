module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.Model
public import Theory.ElementaryAbelian.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Elementary two-subgroups in the field-nine PSU₄ model

Choose representatives in the actual special-unitary image above the projective
carrier. Under the displayed trace hypothesis, distinct representatives are
orthogonal for the trace pairing, so an elementary abelian subgroup injects into
the sixteen-dimensional matrix algebra. At equality the representatives span
that algebra. A projective centralizer lift conjugates each representative by a
scalar whose square is one, because each representative squares to a scalar.
The square of the centralizer lift therefore commutes with the whole matrix
algebra and is itself scalar. Thus every projective centralizer element squares
to one, excluding divisibility of its order by three.

This is a conditional model calculation for Aschbacher–Smith, Theorem
0.1.2(4), printed p.4 of `refs/quasithin.pdf`, repeated as Theorem 0.1.1(4)
on printed p.482. The trace hypothesis remains an explicit premise for the
parent defining-prime assembly to discharge. The unitary and projective
conventions are those of GLS III, §2.7, `refs/KGroup/GLS3/chapter2.tex`:
PSU₄(3) is the projective image of SU₄ over the field of nine elements.
-/

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal

private noncomputable def liftRep (A : Subgroup (Carrier 4)) (a : A) : (form 4).specialSubgroup :=
  Classical.choose (project_surjective 4 (a : Carrier 4))

private theorem project_liftRep (A : Subgroup (Carrier 4)) (a : A) :
    project 4 (liftRep A a) = a := by
  exact Classical.choose_spec (project_surjective 4 (a : Carrier 4))

private theorem trace_pair_zero
    (htrace : ∀ g : (form 4).specialSubgroup, project 4 g ≠ 1 →
      (project 4 g)^2 = 1 → Matrix.trace g.val.val = 0)
    {A : Subgroup (Carrier 4)} [IsElementaryAbelian 2 A]
    (a b : A) (hab : a ≠ b) :
    Matrix.trace (((liftRep A b)⁻¹).val.val * (liftRep A a).val.val) = 0 := by
  have hproj_ne : project 4 ((liftRep A b)⁻¹ * liftRep A a) ≠ 1 := by
    intro he
    apply hab
    apply Subtype.ext
    rw [← project_liftRep A a, ← project_liftRep A b]
    have hh : (project 4 (liftRep A b))⁻¹ * project 4 (liftRep A a) = 1 := by
      simpa [map_mul, map_inv] using he
    exact (inv_mul_eq_one.mp hh).symm
  have hproj_sq : (project 4 ((liftRep A b)⁻¹ * liftRep A a))^2 = 1 := by
    rw [map_mul, map_inv, project_liftRep, project_liftRep]
    have hAprod : ((b : A)⁻¹ * a)^2 = (1 : A) :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 A) (b⁻¹ * a)
    simpa using congrArg (fun x : A => (x : Carrier 4)) hAprod
  have ht := htrace ((liftRep A b)⁻¹ * liftRep A a) hproj_ne hproj_sq
  rw [Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul] at ht
  exact ht

private theorem trace_pair_one {A : Subgroup (Carrier 4)} [IsElementaryAbelian 2 A]
    (a : A) :
    Matrix.trace (((liftRep A a)⁻¹).val.val * (liftRep A a).val.val) = 1 := by
  have hinv : ((liftRep A a)⁻¹).val * (liftRep A a).val =
      (1 : GL (Fin 4) FiniteField.Nine) := inv_mul_cancel _
  have hinv' : ((liftRep A a)⁻¹).val.val * (liftRep A a).val.val =
      (1 : Matrix (Fin 4) (Fin 4) FiniteField.Nine) := congrArg Units.val hinv
  rw [hinv']
  let : CharP FiniteField.Nine 3 :=
    charP_of_card_eq_prime_pow (p := 3) (f := 2) (by simp)
  calc
    Matrix.trace (1 : Matrix (Fin 4) (Fin 4) FiniteField.Nine) =
        (4 : FiniteField.Nine) := Matrix.trace_one
    _ = (3 : FiniteField.Nine) + 1 := by norm_num
    _ = 1 := by rw [show (3 : FiniteField.Nine) = 0 from CharP.cast_eq_zero _ _]; simp

private theorem liftRep_linearIndependent
    (htrace : ∀ g : (form 4).specialSubgroup, project 4 g ≠ 1 →
      (project 4 g)^2 = 1 → Matrix.trace g.val.val = 0)
    (A : Subgroup (Carrier 4)) [IsElementaryAbelian 2 A] :
    LinearIndependent FiniteField.Nine (fun a : A => (liftRep A a).val.val) := by
  let := Fintype.ofFinite A
  let v : A → Matrix (Fin 4) (Fin 4) FiniteField.Nine := fun a => (liftRep A a).val.val
  change LinearIndependent FiniteField.Nine v
  rw [Fintype.linearIndependent_iff]
  intro c hc a
  let L : Matrix (Fin 4) (Fin 4) FiniteField.Nine →ₗ[FiniteField.Nine]
      FiniteField.Nine :=
    (Matrix.traceLinearMap (Fin 4) FiniteField.Nine FiniteField.Nine).comp
      (LinearMap.mulLeft FiniteField.Nine ((liftRep A a)⁻¹).val.val)
  have hz : ∑ i, c i *
        (Matrix.trace (((liftRep A a)⁻¹).val.val * v i)) = 0 := by
    have hzero : L (∑ i, c i • v i) = 0 := by
      rw [hc]
      simp [L]
    simpa [L, Finset.smul_sum, Matrix.mul_sum, Matrix.trace_sum,
      Matrix.trace_smul, smul_eq_mul] using hzero
  have hsingle : (∑ i, c i *
        Matrix.trace (((liftRep A a)⁻¹).val.val * v i)) =
      c a * Matrix.trace (((liftRep A a)⁻¹).val.val * v a) := by
    rw [Finset.sum_eq_single a]
    · intro b hb hba
      rw [trace_pair_zero (htrace := htrace) b a hba]
      simp
    · intro haa
      exact False.elim (haa (Finset.mem_univ a))
  rw [hsingle] at hz
  rw [trace_pair_one a] at hz
  simpa using hz

/-- Trace-duality gives the sixteen-element bound. -/
public theorem elementary_card_le_sixteen
    (htrace : ∀ g : (form 4).specialSubgroup, project 4 g ≠ 1 →
      (project 4 g)^2 = 1 → Matrix.trace g.val.val = 0)
    (A : Subgroup (Carrier 4)) (hA : IsElementaryAbelian 2 A) : Nat.card A ≤ 16 := by
  let := hA
  let := Fintype.ofFinite A
  have hli := liftRep_linearIndependent htrace A
  have hcard : Fintype.card A ≤ Module.finrank FiniteField.Nine
      (Matrix (Fin 4) (Fin 4) FiniteField.Nine) := hli.fintype_card_le_finrank
  change Fintype.card A ≤ Module.finrank FiniteField.Nine
      (Fin 4 → Fin 4 → FiniteField.Nine) at hcard
  rw [Module.finrank_pi_fintype, Module.finrank_pi_fintype] at hcard
  rw [Nat.card_eq_fintype_card]
  norm_num at hcard ⊢
  exact hcard

private def scalarGL (u : FiniteField.Nineˣ) : GL (Fin 4) FiniteField.Nine :=
  GeneralLinearGroup.scalar (Fin 4) u

private theorem scalarGL_central (u : FiniteField.Nineˣ)
    (z : GL (Fin 4) FiniteField.Nine) : z * scalarGL u = scalarGL u * z := by
  have hu : scalarGL u ∈ Subgroup.center (GL (Fin 4) FiniteField.Nine) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨u, rfl⟩
  exact Subgroup.mem_center_iff.mp hu z

private theorem conjugate_sq_commute
    (x y : GL (Fin 4) FiniteField.Nine) (u v : FiniteField.Nineˣ)
    (hrel : x * y * x⁻¹ * scalarGL u = y)
    (hsq : y * y = scalarGL v) :
    (x * x) * y = y * (x * x) := by
  let L := x * y * x⁻¹
  let S := scalarGL u
  have hscL : L * S = S * L := scalarGL_central u L
  have hsqL : L * L = y * y := by
    dsimp [L]
    calc
      (x * y * x⁻¹) * (x * y * x⁻¹) = x * (y * y) * x⁻¹ := by
        simp [mul_assoc]
      _ = x * scalarGL v * x⁻¹ := by rw [hsq]
      _ = scalarGL v := by rw [scalarGL_central v x]; simp [mul_assoc]
      _ = y * y := hsq.symm
  have hsquare : (L * L) * (S * S) = y * y := by
    calc
      (L * L) * (S * S) = L * (L * S) * S := by simp [mul_assoc]
      _ = L * (S * L) * S := by rw [hscL]
      _ = (L * S) * (L * S) := by simp [mul_assoc]
      _ = y * y := by rw [show L * S = y from hrel]
  have hSS : S * S = 1 := by
    rw [hsqL] at hsquare
    apply mul_left_cancel (a := y * y)
    simpa using hsquare
  have hconj : (x * L * x⁻¹) * S = L := by
    calc
      (x * L * x⁻¹) * S = x * L * (x⁻¹ * S) := by simp [mul_assoc]
      _ = x * L * (S * x⁻¹) := by rw [scalarGL_central u x⁻¹]
      _ = x * (L * S) * x⁻¹ := by simp [mul_assoc]
      _ = x * y * x⁻¹ := by rw [show L * S = y from hrel]
      _ = L := rfl
  have hLS : L = y * S := by
    apply mul_right_cancel (b := S)
    calc
      L * S = y := hrel
      _ = (y * S) * S := by rw [mul_assoc, hSS]; simp
  have hxx : x * L * x⁻¹ = y := by
    apply mul_right_cancel (b := S)
    calc
      (x * L * x⁻¹) * S = L := hconj
      _ = y * S := hLS
  have hmul := congrArg (fun z => z * (x * x)) hxx
  simpa [L, mul_assoc] using hmul

private theorem square_eq_scalar
    (g : (form 4).specialSubgroup)
    (hg : (project 4 g)^2 = 1) :
    ∃ u : FiniteField.Nineˣ, g.val * g.val = scalarGL u := by
  have hp : ProjGenLinGroup.mk (g.val * g.val) = 1 := by
    have hgg := congrArg Subtype.val hg
    change (ProjGenLinGroup.mk g.val)^2 = 1 at hgg
    simpa [pow_two, ← map_mul] using hgg
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hp
  obtain ⟨u, hu⟩ := hp
  exact ⟨u, hu.symm⟩

private noncomputable def carrierLift (c : Carrier 4) : (form 4).specialSubgroup :=
  Classical.choose (project_surjective 4 c)

private theorem project_carrierLift (c : Carrier 4) :
    project 4 (carrierLift c) = c :=
  Classical.choose_spec (project_surjective 4 c)

private theorem centralizer_project_square_eq_one
    (htrace : ∀ g : (form 4).specialSubgroup, project 4 g ≠ 1 →
      (project 4 g)^2 = 1 → Matrix.trace g.val.val = 0)
    (A : Subgroup (Carrier 4)) (hA : IsElementaryAbelian 2 A)
    (hcard : Nat.card A = 16)
    (c : Carrier 4) (hc : c ∈ Subgroup.centralizer (A : Set (Carrier 4))) :
    c^2 = 1 := by
  let := hA
  let := Fintype.ofFinite A
  let y : A → Matrix (Fin 4) (Fin 4) FiniteField.Nine := fun a =>
    (liftRep A a).val.val
  have hli : LinearIndependent FiniteField.Nine y := liftRep_linearIndependent htrace A
  have hspan : Submodule.span FiniteField.Nine (Set.range y) = ⊤ := by
    apply hli.span_eq_top_of_card_eq_finrank
    rw [Nat.card_eq_fintype_card] at hcard
    change Fintype.card A = Module.finrank FiniteField.Nine
      (Fin 4 → Fin 4 → FiniteField.Nine)
    rw [Module.finrank_pi_fintype, Module.finrank_pi_fintype]
    norm_num at hcard ⊢
    exact hcard
  let x := carrierLift c
  have hcx : project 4 x = c := project_carrierLift c
  let W : Submodule FiniteField.Nine
      (Matrix (Fin 4) (Fin 4) FiniteField.Nine) := {
    carrier := {z | (x.val * x.val).val * z = z * (x.val * x.val).val}
    zero_mem' := by simp
    add_mem' := by
      intro z w hz hw
      change (x.val * x.val).val * (z + w) = (z + w) * (x.val * x.val).val
      rw [Matrix.mul_add, Matrix.add_mul, hz, hw]
    smul_mem' := by
      intro r z hz
      change (x.val * x.val).val * (r • z) = (r • z) * (x.val * x.val).val
      rw [Matrix.mul_smul, Matrix.smul_mul, hz] }
  have hWgen : Set.range y ⊆ W := by
    rintro z ⟨a, rfl⟩
    change (x.val * x.val).val * (liftRep A a).val.val =
      (liftRep A a).val.val * (x.val * x.val).val
    have hcomm := (Subgroup.mem_centralizer_iff.mp hc) (a : Carrier 4) a.property
    have hconj : project 4 (x * liftRep A a * x⁻¹) = project 4 (liftRep A a) := by
      calc
        project 4 (x * liftRep A a * x⁻¹) =
            project 4 x * project 4 (liftRep A a) * (project 4 x)⁻¹ := by simp
        _ = c * (a : Carrier 4) * c⁻¹ := by rw [hcx, project_liftRep]
        _ = (a : Carrier 4) := by rw [← hcomm]; simp
        _ = project 4 (liftRep A a) := (project_liftRep A a).symm
    have hp : ProjGenLinGroup.mk ((x * liftRep A a * x⁻¹).val) =
        ProjGenLinGroup.mk (liftRep A a).val := congrArg Subtype.val hconj
    obtain ⟨u, hu⟩ := (ProjGenLinGroup.mk_eq_mk_iff.mp hp)
    have hrel : x.val * (liftRep A a).val * x.val⁻¹ * scalarGL u =
        (liftRep A a).val := by
      simpa [scalarGL, Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul] using hu
    have hyproj : (project 4 (liftRep A a))^2 = 1 := by
      rw [project_liftRep]
      have ha : (a : A)^2 = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 A) a
      exact congrArg (fun z : A => (z : Carrier 4)) ha
    obtain ⟨v, hv⟩ := square_eq_scalar (liftRep A a) hyproj
    have hsqcomm := conjugate_sq_commute x.val (liftRep A a).val u v hrel hv
    simpa [Matrix.GeneralLinearGroup.coe_mul] using congrArg Units.val hsqcomm
  have hWtop : W = ⊤ := by
    apply top_unique
    rw [← hspan]
    exact Submodule.span_le.mpr hWgen
  have hcomm_all (z : Matrix (Fin 4) (Fin 4) FiniteField.Nine) :
      (x.val * x.val).val * z = z * (x.val * x.val).val := by
    have : z ∈ W := by rw [hWtop]; trivial
    exact this
  have hxcenter : x.val * x.val ∈ Subgroup.center (GL (Fin 4) FiniteField.Nine) := by
    rw [Subgroup.mem_center_iff]
    intro z
    apply Units.ext
    simpa [Matrix.GeneralLinearGroup.coe_mul] using (hcomm_all z.val).symm
  rw [GeneralLinearGroup.center_eq_range_scalar] at hxcenter
  obtain ⟨u, hu⟩ := hxcenter
  have hp : ProjGenLinGroup.mk ((x * x).val) = 1 := by
    rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨u, hu⟩
  have hproj_sq : project 4 (x * x) = 1 := by
    apply Subtype.ext
    exact hp
  calc
    c^2 = (project 4 x)^2 := by rw [hcx]
    _ = project 4 (x * x) := by
      simp [pow_two, map_mul]
    _ = 1 := hproj_sq

/-- An elementary abelian subgroup of order sixteen has a centralizer of order prime to three. -/
public theorem centralizer_not_three_dvd_of_card_eq_sixteen
    (htrace : ∀ g : (form 4).specialSubgroup, project 4 g ≠ 1 →
      (project 4 g)^2 = 1 → Matrix.trace g.val.val = 0)
    (A : Subgroup (Carrier 4)) (hA : IsElementaryAbelian 2 A)
    (hcard : Nat.card A = 16) :
    ¬ 3 ∣ Nat.card (Subgroup.centralizer (A : Set (Carrier 4))) := by
  intro hdiv
  let C := Subgroup.centralizer (A : Set (Carrier 4))
  let := Fintype.ofFinite C
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨c, hcorder⟩ := exists_prime_orderOf_dvd_card' 3 hdiv
  have hc_sq : (c : Carrier 4)^2 = 1 :=
    centralizer_project_square_eq_one htrace A hA hcard c.1 c.2
  have horder_map : orderOf (c : Carrier 4) = orderOf c :=
    orderOf_injective C.subtype C.subtype_injective c
  have hdvd : orderOf (c : Carrier 4) ∣ 2 := orderOf_dvd_of_pow_eq_one hc_sq
  rw [horder_map, hcorder] at hdvd
  norm_num at hdvd

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal

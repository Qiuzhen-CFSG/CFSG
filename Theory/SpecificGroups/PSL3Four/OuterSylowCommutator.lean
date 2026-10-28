module
public import Theory.SpecificGroups.PSL3Even.MinimalParabolicWitness.CentralActor
public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic
public import Theory.GroupTheory.PerfectCentralCoverOuter
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.Frattini.PGroup
import Mathlib.Tactic.LinearCombination

/-!
# Outer involutions have a non-elementary Sylow commutator

An involution normalizing a binary PSL₃ Sylow cannot have all its displacements
in an elementary subgroup unless it is inner. For a diagram-swapping actor,
the invariant elementary subgroup lies in the highest root. If the actor fixes
the diagram, triangular coordinates on the two simple roots kill its field
component; its remaining linear involution is inner.

Sylow conjugacy transports the calculation to the prescribed Sylow subgroup.
Perfect central descent then applies it to the literal cyclic commutator
`[⟨x⟩, S ∩ H]` in an ambient group. This commutator is a finite two-group,
so its Frattini subgroup is nontrivial whenever x acts outerly on H.

Source: Aschbacher--Smith, G.11.6, printed p.366, using G.10.9(2), p.360.
The reusable calculation holds over every finite field of characteristic two;
the actual source consumer specializes to SL₃(GF(4)). Matrix coordinates use
the attributed upper-unitriangular model imported by `CentralActor`.
-/

public noncomputable section
open scoped MatrixGroups
open Matrix Subgroup Matrix.PSL3 Matrix.PSL3.LinearThree
open Matrix.PSL3.RootPlaneGeometry Matrix.PSL3.LinearThree.OuterExtensions
open Matrix.PSL3Even.UnipotentGeometry Matrix.PSL3Even.MinimalParabolicWitness
open Matrix.PSL3.OuterSolvable Matrix.PSL3.CartanActions Matrix.PSL3.ExtensionBorel
namespace Matrix.PSL3Four.OuterSylowCommutator
variable (K : Type*) [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
private theorem field_projective (σ : K ≃+* K) (u : U K) :
    OuterSolvable.fieldAction K σ (projective K u) = projective K ⟨σ u.x, σ u.y, σ u.c⟩ := by
  change OuterSolvable.fieldAction K σ (QuotientGroup.mk (specialLinear K u)) =
    QuotientGroup.mk (specialLinear K ⟨σ u.x, σ u.y, σ u.c⟩)
  rw [fieldAction_mk]
  congr 1
  apply Subtype.ext
  ext i j
  change σ (matrix K u i j) = matrix K ⟨σ u.x, σ u.y, σ u.c⟩ i j
  fin_cases i <;> fin_cases j <;> simp [matrix]

omit [Finite K] [CharP K 2] in
private theorem scalar_of_projection_eq (x y : SL(3,K))
    (h : projection K x = projection K y) : ∃ r : K, x.val = r • y.val := by
  have hc := (projection K).eq_iff.mp h
  rw [projection_ker] at hc
  obtain ⟨r,_,hr⟩ := SpecialLinearGroup.mem_center_iff.mp hc
  refine ⟨r, ?_⟩
  calc
    x.val = (y * (y⁻¹ * x)).val := by simp only [mul_inv_cancel_left]
    _ = y.val * Matrix.scalar (Fin 3) r := by rw [SpecialLinearGroup.coe_mul, ← hr]
    _ = r • y.val := by
      ext i j
      simp [Matrix.scalar, Matrix.mul_diagonal, mul_comm]

omit [Finite K] [CharP K 2] in
private theorem triangular_diagonal (m : GL (Fin 3) K) (hm : m ∈ glBorel K) :
    ∀ i : Fin 3, m.val i i ≠ 0 := by
  have hn : Matrix.det m.val ≠ 0 := (GeneralLinearGroup.det m).ne_zero
  rw [Matrix.det_fin_three] at hn
  simp only [hm.1,hm.2.1,hm.2.2,mul_zero,zero_mul,sub_zero,add_zero] at hn
  intro i
  fin_cases i
  · exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).1
  · exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).2
  · exact (mul_ne_zero_iff.mp hn).2

omit [Finite K] [CharP K 2] in
private theorem simple_coordinates (m : GL (Fin 3) K) (hm : m ∈ glBorel K)
    (σ : K ≃+* K) (u v : U K)
    (h : (linearConj K m * OuterSolvable.fieldAction K σ) (projective K u) = projective K v) :
    m.val 0 0 * σ u.x = v.x * m.val 1 1 ∧
      m.val 1 1 * σ u.y = v.y * m.val 2 2 := by
  rw [MulAut.mul_apply, field_projective] at h
  have hp : projection K (linearConjSL K m (specialLinear K ⟨σ u.x,σ u.y,σ u.c⟩)) =
      projection K (specialLinear K v) :=
    (linearConj_mk K m _).symm.trans h
  obtain ⟨r,hr⟩ := scalar_of_projection_eq K _ _ hp
  have hv : (linearConjSL K m (specialLinear K ⟨σ u.x,σ u.y,σ u.c⟩)).val =
      m.val * matrix K ⟨σ u.x,σ u.y,σ u.c⟩ * m.inv :=
    congrArg Units.val (linearConjSL_toGL K m _)
  have he : m.val * matrix K ⟨σ u.x,σ u.y,σ u.c⟩ = (r • matrix K v) * m.val := by
    rw [← show (specialLinear K v).val = matrix K v from rfl,
      ← hr, hv, Matrix.mul_assoc, m.inv_val, mul_one]
  have h00 := congrArg (fun a : Matrix (Fin 3) (Fin 3) K => a 0 0) he
  have h00 : m.val 0 0 = r * m.val 0 0 := by
    simpa [matrix, Matrix.mul_apply, Fin.sum_univ_three, hm.1, hm.2.1] using h00
  have hr1 : r = 1 := (mul_eq_right₀ (triangular_diagonal K m hm 0)).mp h00.symm
  rw [hr1, one_smul] at he
  constructor
  · have h01 := congrArg (fun a : Matrix (Fin 3) (Fin 3) K => a 0 1) he
    simp [matrix, Matrix.mul_apply, Fin.sum_univ_three, hm.2.2] at h01
    linear_combination h01
  · have h12 := congrArg (fun a : Matrix (Fin 3) (Fin 3) K => a 1 2) he
    simp [matrix, Matrix.mul_apply, Fin.sum_univ_three, hm.1] at h12
    linear_combination h12

/-- An involutory Sylow actor whose displacements lie in an invariant elementary
subgroup of that Sylow is inner. Both diagram and coefficient actions are detected. -/
theorem inner_of_elementary_displacement {n : ℕ} (hn : 0 < n) (hK : Nat.card K = 2 ^ n)
    (a : MulAut PSL(3,K)) (ha : (unipotent K).map a.toMonoidHom = unipotent K)
    (hp : a ^ 2 = 1) (A : Subgroup PSL(3,K)) [IsElementaryAbelian 2 A]
    (hA : A ≤ unipotent K)
    (hd : ∀ u ∈ unipotent K, a u * u⁻¹ ∈ A) :
    a ∈ MulAut.innerSubgroup PSL(3,K) := by
  have hi : A.map a.toMonoidHom = A := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨u,hu,rfl⟩
      change a u ∈ A
      simpa only [inv_mul_cancel_right] using A.mul_mem (hd u (hA hu)) hu
    · rw [Subgroup.card_map_of_injective a.injective]
  by_cases hs : diagramAction K hn hK a = 1
  · have hl : a ∈ linearField K := by
      rw [← diagramAction_ker_eq_linearField K hn hK]
      exact hs
    obtain ⟨m,σ,he⟩ := linearField_factorization K a hl
    have hm : m ∈ glBorel K := ResidualLinear.linear_field_upperTriangular m σ (by rwa [← he])
    let W := A.comap (projective K)
    have hexp (u : U K) (hu : u ∈ W) : u ^ 2 = 1 := by
      apply projective_injective K
      rw [map_pow, map_one]
      exact elemPow_eq_one_of_isElementaryAbelian (projective K u) hu
    have hcoords (t : K) : ∃ d ∈ W,
        m.val 0 0 * σ t = (d.x + t) * m.val 1 1 ∧
        m.val 1 1 * σ t = (d.y + t) * m.val 2 2 := by
      let u : U K := ⟨t,t,0⟩
      have hu : projective K u ∈ unipotent K := by
        rw [← projective_range]; exact ⟨_,rfl⟩
      have hd' := hd _ hu
      obtain ⟨d,hdval⟩ := (show a (projective K u) * (projective K u)⁻¹ ∈
          (projective K).range by rw [projective_range]; exact hA hd')
      have hdW : d ∈ W := by change projective K d ∈ A; rwa [hdval]
      refine ⟨d,hdW,?_⟩
      have hdact : (linearConj K m * OuterSolvable.fieldAction K σ) (projective K u) =
          projective K (d * u) := by
        rw [← he, map_mul, hdval, inv_mul_cancel_right]
      exact simple_coordinates K m hm σ u (d * u) hdact
    have hσ : σ = 1 := by
      rcases le_plane_of_exponent_two K W hexp with h | h
      · have hf (t : K) : m.val 1 1 * σ t = t * m.val 2 2 := by
          obtain ⟨d,hd,_,hc⟩ := hcoords t
          have hz := (mem_V₁ K d).mp (h hd)
          simpa only [hz, zero_add] using hc
        have heq : m.val 1 1 = m.val 2 2 := by simpa using hf 1
        ext t
        change σ t = t
        apply mul_left_cancel₀ (triangular_diagonal K m hm 1)
        simpa only [← heq, mul_comm] using hf t
      · have hf (t : K) : m.val 0 0 * σ t = t * m.val 1 1 := by
          obtain ⟨d,hd,hc,_⟩ := hcoords t
          have hz := (mem_V₂ K d).mp (h hd)
          simpa only [hz, zero_add] using hc
        have heq : m.val 0 0 = m.val 1 1 := by simpa using hf 1
        ext t
        change σ t = t
        apply mul_left_cancel₀ (triangular_diagonal K m hm 0)
        simpa only [← heq, mul_comm] using hf t
    have he' : a = linearConj K m := by simpa only [hσ,map_one,mul_one] using he
    rw [he'] at hp ⊢
    exact ResidualInner.linearConj_twoPower_inner m (k := 1) (by simpa using hp)
  · exact inner_of_central_displacement K hn hK a ha hp fun u hu =>
      elementary_invariant_le_center K hn hK a ha hs A hA hi (hd u hu)

/-- The same calculation on any actual Sylow subgroup, with all subgroups
transported by the same conjugating equivalence. -/
theorem inner_of_elementary_displacement_sylow {n : ℕ} (hn : 0 < n)
    (hK : Nat.card K = 2 ^ n) (P : Sylow 2 PSL(3,K))
    (a : MulAut PSL(3,K)) (ha : (P : Subgroup PSL(3,K)).map a.toMonoidHom = P)
    (hp : a ^ 2 = 1) (A : Subgroup PSL(3,K)) [IsElementaryAbelian 2 A]
    (hA : A ≤ P) (hd : ∀ u ∈ P, a u * u⁻¹ ∈ A) :
    a ∈ MulAut.innerSubgroup PSL(3,K) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(3,K) P (unipotentSylow K hn hK)
  let e : MulAut PSL(3,K) := MulAut.conj g
  have hU : (P : Subgroup PSL(3,K)).map e.toMonoidHom = unipotent K :=
    congrArg Sylow.toSubgroup hg
  let b := MulAut.congr e a
  have hb (u : PSL(3,K)) : b (e u) = e (a u) := by simp [b]
  have hpres : (unipotent K).map b.toMonoidHom = unipotent K := by
    rw [← hU]
    have hmaps : ((P : Subgroup PSL(3,K)).map e.toMonoidHom).map b.toMonoidHom =
        ((P : Subgroup PSL(3,K)).map a.toMonoidHom).map e.toMonoidHom := by
      rw [Subgroup.map_map,Subgroup.map_map]
      congr 1
      ext u
      exact hb u
    rw [hmaps,ha]
  let : IsElementaryAbelian 2 (A.map e.toMonoidHom) := IsElementaryAbelian.map e.toMonoidHom
  have hbin : b ∈ MulAut.innerSubgroup PSL(3,K) :=
    inner_of_elementary_displacement K hn hK b hpres
      (by change (MulAut.congr e a) ^ 2 = 1; rw [← map_pow,hp,map_one])
      (A.map e.toMonoidHom) (by rw [← hU]; exact map_mono hA) (by
        intro u hu
        rw [← hU] at hu
        obtain ⟨v,hv,rfl⟩ := hu
        change b (e v) * (e v)⁻¹ ∈ A.map e.toMonoidHom
        rw [hb,← map_inv,← map_mul]
        exact mem_map_of_mem _ (hd v hv))
  rw [← MulAut.map_innerSubgroup_congr e] at hbin
  obtain ⟨c,hc,he⟩ := hbin
  exact (MulAut.congr e).injective he ▸ hc

/-- Passage through the literal central quotient of a perfect cover preserves
the obstruction; central descent detects innerness. -/
theorem cover_inner_of_elementary_displacement {n : ℕ} (hn : 0 < n)
    (hK : Nat.card K = 2 ^ n) {H : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    (e : H ⧸ center H ≃* PSL(3,K)) (P : Sylow 2 H) (a : MulAut H)
    (ha : (P : Subgroup H).map a.toMonoidHom = P) (hp : a ^ 2 = 1)
    (A : Subgroup H) [IsElementaryAbelian 2 A] (hA : A ≤ P)
    (hd : ∀ u ∈ P, a u * u⁻¹ ∈ A) : a ∈ MulAut.innerSubgroup H := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center H))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let Q := P.mapSurjective hf
  let b := MulAut.centralQuotientAction e a
  have hb (u : H) : b (f u) = f (a u) := MulAut.centralQuotientAction_apply e a u
  have hmaps : ((P : Subgroup H).map f).map b.toMonoidHom =
      ((P : Subgroup H).map a.toMonoidHom).map f := by
    rw [Subgroup.map_map,Subgroup.map_map]
    congr 1
    ext u
    exact hb u
  have hQ : (Q : Subgroup PSL(3,K)).map b.toMonoidHom = Q := by
    change ((P : Subgroup H).map f).map b.toMonoidHom = (P : Subgroup H).map f
    rw [hmaps,ha]
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  have hin := inner_of_elementary_displacement_sylow K hn hK Q b hQ
    (by change (MulAut.centralQuotientAction e a) ^ 2 = 1; rw [← map_pow,hp,map_one])
    (A.map f) (map_mono hA) (by
      rintro _ ⟨u,hu,rfl⟩
      rw [hb,← map_inv,← map_mul]
      exact mem_map_of_mem f (hd u hu))
  change a ∈ (MulAut.innerSubgroup PSL(3,K)).comap (MulAut.centralQuotientAction e) at hin
  rwa [MulAut.comap_inner_centralQuotientAction e] at hin

/-- An outer involution in an ambient Sylow has a non-elementary cyclic
commutator with the actual Sylow intersection of a perfect PSL₃ cover.
Consequently that finite two-group has nontrivial Frattini subgroup. -/
theorem cyclic_commutator_frattini_ne_bot {n : ℕ} (hn : 0 < n)
    (hK : Nat.card K = 2 ^ n) {D : Type*} [Group D] [Finite D]
    (H : Subgroup D) [H.Normal] [Group.IsPerfect H]
    (e : H ⧸ center H ≃* PSL(3,K)) (S : Sylow 2 D) (x : D)
    (hx : x ∈ S) (hp : x ^ 2 = 1)
    (ho : MulAut.conjNormal (H := H) x ∉ MulAut.innerSubgroup H) :
    frattini (⁅zpowers x,(S : Subgroup D) ⊓ H⁆ : Subgroup D) ≠ ⊥ := by
  intro hphi
  let C := (⁅zpowers x,(S : Subgroup D) ⊓ H⁆ : Subgroup D)
  have hCS : C ≤ S :=
    (commutator_mono (zpowers_le.mpr hx) inf_le_left).trans (commutator_le_self _)
  have hCH : C ≤ H :=
    (commutator_mono le_rfl inf_le_right).trans (commutator_le_right _ _)
  let : Fact (IsPGroup 2 C) :=
    ⟨S.isPGroup'.of_injective (inclusion hCS) (inclusion_injective hCS)⟩
  let : IsElementaryAbelian 2 C := (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hphi
  let : IsElementaryAbelian 2 (C.subgroupOf H) := IsElementaryAbelian.subgroupOf hCH
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal H
  let a := MulAut.conjNormal (H := H) x
  have hpres : (P : Subgroup H).map a.toMonoidHom = P := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨u,hu,rfl⟩
      rw [hP] at hu ⊢
      change x * (u : D) * x⁻¹ ∈ (S : Subgroup D)
      exact S.mul_mem (S.mul_mem hx hu) (S.inv_mem hx)
    · exact (Subgroup.card_map_of_injective (f := a.toMonoidHom) (K := (P : Subgroup H))
        (show Function.Injective a.toMonoidHom from a.injective)).ge
  apply ho
  exact cover_inner_of_elementary_displacement K hn hK e P a hpres
    (by change (MulAut.conjNormal (H := H) x) ^ 2 = 1; rw [← map_pow,hp,map_one])
    (C.subgroupOf H) (by rw [hP]; exact subgroupOf_mono H hCS) (by
      intro u hu
      change u ∈ (P : Subgroup H) at hu
      rw [hP] at hu
      change x * (u : D) * x⁻¹ * (u : D)⁻¹ ∈ C
      exact commutator_mem_commutator (mem_zpowers x) ⟨hu,u.property⟩)

end Matrix.PSL3Four.OuterSylowCommutator

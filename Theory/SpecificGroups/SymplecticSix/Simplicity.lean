module

public import Theory.SpecificGroups.PSp4Three.Simplicity
public import Theory.SpecificGroups.SymplecticSix.Basic

/-!
# Simplicity of the binary symplectic six-space group

The actual central quotient acts faithfully and primitively on its 63 projective
points. Its point-stabilizer orbits have sizes 1, 30 and 32; neither 31 nor 33
divides 63. The seven nonzero vectors of an isotropic three-space give a
transvection identity which proves perfectness over the two-element field.
Iwasawa's criterion then proves simplicity, and nontrivial perfectness also
proves noncommutativity.

The characteristic-independent geometry and Iwasawa structure are reused from
`PSp4Three`; their statements apply to this literal six-dimensional carrier.
Only the binary perfectness argument is newly ported from Gerald Höhn's ATLAS,
`Atlas/LinearGroups/Symplectic/{BinaryIdentity,PerfectTwo}.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`. Copyright (c) 2026 Gerald Höhn and the
ATLAS contributors. Covered adaptations retain the ATLAS Research and Attribution
License 1.0 (`LICENSES/ATLAS.txt`; citation `LICENSES/ATLAS-CITATION.cff`).
Changes: CFSG module boundaries, reuse of existing geometry, explicit binary
scalar hypotheses in the private helper, and current Mathlib proof syntax.

This supplies the intrinsic simplicity assertion for the Sp₆(2) sections in
Aschbacher–Smith A.2.19 (`refs/quasithin.pdf`, printed pp. 40–41), identified in
GLS3 Tables 5.3j and 5.3k. The sporadic quotient constructions are separate.
-/

public section

noncomputable section
namespace Matrix.PSp4Three.BinarySix
open Matrix.PSp4Three
variable {n : ℕ} {F : Type*} [Field F] [CharP F 2]

/-- The seven nonzero directions of an isotropic three-space give a symbolic relation. -/
private theorem binary_seven_transvections (u v w : Vector n F)
    (huv : form u v = 0) (huw : form u w = 0) (hvw : form v w = 0) :
    transvection u 1 * transvection v 1 * transvection w 1 * transvection (u+v) 1 *
      transvection (u+w) 1 * transvection (v+w) 1 * transvection (u+v+w) 1 = 1 := by
  have hvu : form v u = 0 := by rw [form_swap,huv,neg_zero]
  have hwu : form w u = 0 := by rw [form_swap,huw,neg_zero]
  have hwv : form w v = 0 := by rw [form_swap,hvw,neg_zero]
  apply ext_action
  intro x
  simp only [mul_smul,one_smul,transvection_apply]
  simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,
    form_self,huv,huw,hvw,hvu,hwu,hwv,add_zero,mul_zero]
  funext i
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring_nf
  have hc2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hc4 : (4 : F) = 0 := by linear_combination 2*hc2
  simp only [hc2,hc4,mul_zero,add_zero]

end Matrix.PSp4Three.BinarySix

end

noncomputable section
namespace Matrix.PSp4Three.BinarySix
open Matrix.PSp4Three
variable {n : ℕ} {F : Type*} [Field F] [CharP F 2]

/-- Perfectness from the binary scalar condition, starting at symplectic rank three. -/
private theorem perfect_of_binary_scalars (hn : 3 ≤ n) (hscalars : ∀ a : F, a = 0 ∨ a = 1) : Group.IsPerfect (Sp n F) := by
  classical
  let i : Fin n := ⟨0,by omega⟩
  let j : Fin n := ⟨1,by omega⟩
  let k : Fin n := ⟨2,by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; simp [i,j] at this
  have hik : i ≠ k := by intro h; have := congrArg Fin.val h; simp [i,k] at this
  have hjk : j ≠ k := by intro h; have := congrArg Fin.val h; simp [j,k] at this
  let u : Vector n F := e i
  let v : Vector n F := e j
  let w : Vector n F := e k
  have hu : u ≠ 0 := by intro h; have := congrFun h (.inl i); simp [u,e] at this
  have hv : v ≠ 0 := by intro h; have := congrFun h (.inl j); simp [v,e] at this
  have hw : w ≠ 0 := by intro h; have := congrFun h (.inl k); simp [w,e] at this
  have huv' : u+v ≠ 0 := by
    intro h; have := congrFun h (.inl i); simp [u,v,e,hij] at this
  have huw' : u+w ≠ 0 := by
    intro h; have := congrFun h (.inl i); simp [u,w,e,hik] at this
  have hvw' : v+w ≠ 0 := by
    intro h; have := congrFun h (.inl j); simp [v,w,e,hjk] at this
  have huvw : u+v+w ≠ 0 := by
    intro h; have := congrFun h (.inl i); simp [u,v,w,e,hij,hik] at this
  have horth (a b : Fin n) : form (e (F := F) a) (e b) = 0 := by
    rw [form_e_right]; simp [e]
  let f : Sp n F →* Abelianization (Sp n F) := Abelianization.of
  let z := f (transvection u 1)
  have hz2 : z^2=1 := by
    change f (transvection u 1)^2=1
    rw [← map_pow,transvection_pow]
    have h2 : (2 : ℕ) • (1 : F) = 0 := by
      simpa only [nsmul_eq_mul,mul_one] using (CharP.cast_eq_zero F 2)
    rw [h2,transvection_zero,map_one]
  have hz7 : z^7=1 := by
    have h := congrArg f (binary_seven_transvections u v w (horth i j) (horth i k) (horth j k))
    simp only [map_mul,map_one] at h
    rw [← abelian_transvection_images f hu hv,← abelian_transvection_images f hu hw,
      ← abelian_transvection_images f hu huv',← abelian_transvection_images f hu huw',
      ← abelian_transvection_images f hu hvw',← abelian_transvection_images f hu huvw] at h
    simpa only [z,pow_succ,pow_zero,one_mul] using h
  have hz : z=1 := by
    have hp : z^7=(z^2)^3*z := by rw [← pow_mul,← pow_succ]
    rw [hp,hz2,one_pow,one_mul] at hz7
    exact hz7
  have hunit (v : Vector n F) (hv : v ≠ 0) : f (transvection v 1)=1 := by
    rw [← abelian_transvection_images f hu hv]
    exact hz
  apply perfect_of_abelian_images
  intro v a
  change f (transvection v a)=1
  by_cases hv : v=0
  · subst v; simp [f]
  rcases hscalars a with rfl|rfl
  · simp
  · exact hunit v hv

end Matrix.PSp4Three.BinarySix

end

namespace Theory.SpecificGroups.SymplecticSix
open Matrix.PSp4Three

private theorem binary_projective_preprimitive :
    MulAction.IsPreprimitive (PSp (ZMod 2)) (Points 3 (ZMod 2)) := by
  classical
  let p : Points 3 (ZMod 2) := ePoint 0
  have hcard : Nat.card (Points 3 (ZMod 2)) = 63 := by
    rw [card_points]
    norm_num
  have hperp : Nat.card {q : Points 3 (ZMod 2) // Orthogonal p q} = 31 := by
    rw [card_perpendicular_points]
    norm_num
  apply Blocks.primitive_of_rankThree_nondivisibility p (suborbitIndex p)
    (suborbitIndex_self p) (fun x y h => suborbitIndex_transitive (by decide) p x y h)
    ![1,30,32] rfl
  · intro i
    fin_cases i
    · exact card_suborbit_zero p
    · simp [card_suborbit_one, hperp]
    · simp [card_suborbit_two, hperp, hcard]
  · exact hcard
  · rw [hcard]
    decide
  · rw [hcard]
    decide

/-- Perfectness of the actual binary six-dimensional matrix group. -/
theorem perfect_binary : Group.IsPerfect (Sp (ZMod 2)) :=
  Matrix.PSp4Three.BinarySix.perfect_of_binary_scalars (F := ZMod 2) (by decide)
    (by intro a; fin_cases a; exact Or.inl rfl; exact Or.inr rfl)

/-- Simplicity of the actual central quotient PSp₆(2). -/
theorem isSimpleGroup_binary : IsSimpleGroup (PSp (ZMod 2)) := by
  let := binary_projective_preprimitive
  let := projective_nontrivial (F := ZMod 2) (n := 3) (by decide)
  let := perfect_binary
  let : Group.IsPerfect (PSp (ZMod 2)) := inferInstance
  exact iwasawa.isSimpleGroup (Group.IsPerfect.commutator_eq_top (G := PSp (ZMod 2)))
    inferInstance

/-- The actual central quotient PSp₆(2) is nonabelian. -/
theorem not_isMulCommutative_binary : ¬ IsMulCommutative (PSp (ZMod 2)) := by
  let := projective_nontrivial (F := ZMod 2) (n := 3) (by decide)
  let := perfect_binary
  let : Group.IsPerfect (PSp (ZMod 2)) := inferInstance
  exact Group.IsPerfect.not_isMulCommutative (PSp (ZMod 2))

end Theory.SpecificGroups.SymplecticSix

module
/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Adapted from Atlas/LinearGroups/Symplectic/{BinaryIdentity,PerfectTwo}.lean.
Covered by the ATLAS Research and Attribution License 1.0; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
Changes: reuse the general Matrix.PSp4Three module carrier and its proved
transvection generation, conjugacy, and scalar-center statements.
-/
public import Theory.SpecificGroups.PSp4Three.Perfectness
public import Theory.SpecificGroups.PSp4Three.ProjectiveGeometry
public import Mathlib.RingTheory.Fintype
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Binary symplectic perfectness and center

Conjugacy makes every nonzero symplectic transvection have the same image in
an abelian quotient. In characteristic two that image has order dividing two;
the seven-direction identity in an isotropic three-space also makes its order
divide seven. Transvection generation therefore proves perfectness in rank
at least three. The existing scalar-center theorem gives trivial center over
F2. These facts feed the literal symplectic-residual rank obstruction in the
central-kernel branch of Aschbacher--Smith G.10.15, printed p.363.
-/


public noncomputable section
namespace Matrix.PSp4Three
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

end Matrix.PSp4Three
end


public noncomputable section
namespace Matrix.PSp4Three
variable {n : ℕ} {F : Type*} [Field F] [Finite F]

/-- Uniform perfectness over the two-element field, starting at symplectic rank three. -/
theorem perfect_of_card_two (hn : 3 ≤ n) (hq : Nat.card F = 2) : Group.IsPerfect (Sp n F) := by
  classical
  let := Fintype.ofFinite F
  have hq' : Fintype.card F = 2 := by simpa only [Nat.card_eq_fintype_card] using hq
  let : CharP F 2 := charP_of_card_eq_prime hq'
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
  have ha : a ∈ ({0,1} : Finset F) := by
    rw [← Finset.univ_of_card_le_two hq'.le]
    exact Finset.mem_univ a
  simp only [Finset.mem_insert,Finset.mem_singleton] at ha
  rcases ha with rfl|rfl
  · simp
  · exact hunit v hv

end Matrix.PSp4Three
end

public noncomputable section
namespace Matrix.PSp4Three
variable {n : ℕ}
/-- The center of the full binary symplectic group is trivial. -/
theorem binary_center_eq_bot (hn : 0 < n) : Subgroup.center (Sp n (ZMod 2)) = ⊥ := by
  apply bot_unique
  intro g hg
  obtain ⟨a, hact⟩ := central_is_scalar g hg
  let i : Fin n := ⟨0,hn⟩
  have hi : (e i : Vector n (ZMod 2)) ≠ 0 := by
    intro hz
    have he := congrFun hz (.inl i)
    simp [e] at he
  have hne : a ≠ 0 := by
    intro hz
    have he := hact (e i)
    rw [hz, zero_smul] at he
    exact hi ((toLinear g).injective (he.trans (map_zero (toLinear g)).symm))
  have he : a = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a hne
  apply Subgroup.mem_bot.mpr
  apply ext_action
  intro v
  rw [hact, he, one_smul, one_smul]
end Matrix.PSp4Three

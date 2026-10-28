module

public import Theory.GroupTheory.CentralS3InvolutionComplement
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# A central retraction in an elementary abelian extension of S₃

Let a finite group map onto S₃ with elementary abelian two-kernel A. Suppose
an order-three lift fixes precisely a central subgroup Z of A of order two,
and a transposition has an involutory lift. Then Z is a retract of the group.

On A, the actual conjugation norm 1 + a + a² is a retraction onto Z.
Conjugation factors through S₃ because A is abelian. Conjugating the cubic
action either preserves or inverts it, so the norm is invariant under the
whole group. Its kernel is therefore normal. Modulo that kernel, the given
involution splits the central extension of S₃ by Z. The resulting projection
onto Z pulls back to the required retraction.

This supplies the elementary-kernel splitting argument used in
Aschbacher–Smith, I.2.2(5), printed p.412 / PDF p.423. The literal M₁₂
centralizer application is in `BinaryExtension.Splitting`.
-/

open Subgroup
open scoped IsMulCommutative

namespace Theory.GroupTheory
variable {G : Type*} [Group G]

private theorem s3_conjugate_cubic : ∀ c g : Equiv.Perm (Fin 3),
    c ^ 3 = 1 → g⁻¹ * c * g = c ∨ g⁻¹ * c * g = c ^ 2 := by decide

private theorem action_ker (f : G →* Equiv.Perm (Fin 3))
    [IsElementaryAbelian 2 f.ker] : f.ker ≤ (MulAut.conjNormal (H := f.ker)).ker := by
  intro x hx
  apply MonoidHom.mem_ker.mpr
  ext y
  change x * (y : G) * x⁻¹ = y
  have hc : x * (y : G) = y * x := congrArg Subtype.val (mul_comm' (⟨x,hx⟩ : f.ker) y)
  rw [hc, mul_inv_cancel_right]

private theorem exists_kernel_norm
    (f : G →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    [IsElementaryAbelian 2 f.ker]
    (Z : Subgroup G) (hZA : Z ≤ f.ker) (hZ : Z ≤ center G)
    (a : G) (ha : a ^ 3 = 1) (ha_image : orderOf (f a) = 3)
    (hfixed : ∀ x : G, x ∈ f.ker → (Commute a x ↔ x ∈ Z)) :
    ∃ n : f.ker →* Z,
      (∀ z : Z, n ⟨z, hZA z.property⟩ = z) ∧
      (∀ (g : G) (x : f.ker), n (MulAut.conjNormal g x) = n x) := by
  let ρ : G →* MulAut f.ker := MulAut.conjNormal
  let σ : Equiv.Perm (Fin 3) →* MulAut f.ker := f.liftOfSurjective hf ⟨ρ, action_ker f⟩
  have hσ (g : G) : σ (f g) = ρ g :=
    f.liftOfRightInverse_comp_apply _ _ _ g
  let α := ρ a
  have hα3 : α ^ 3 = 1 := by dsimp [α]; rw [← map_pow, ha, map_one]
  have hα3x (x : f.ker) : α (α (α x)) = x :=
    congrArg (fun e : MulAut f.ker => e x) hα3
  let n : f.ker →* f.ker := (MonoidHom.id _ * α.toMonoidHom) *
    (α.toMonoidHom.comp α.toMonoidHom)
  have hn (x : f.ker) : n x = x * α x * α (α x) := rfl
  have hnZ (x : f.ker) : (n x : G) ∈ Z := by
    apply (hfixed _ (n x).property).mp
    have he : α (n x) = n x := by
      rw [hn, map_mul, map_mul, hα3x]
      ac_rfl
    have he' : a * (n x : G) * a⁻¹ = n x := congrArg Subtype.val he
    exact (mul_inv_eq_iff_eq_mul.mp he')
  let nZ : f.ker →* Z := (f.ker.subtype.comp n).codRestrict Z hnZ
  refine ⟨nZ, ?_, ?_⟩
  · intro z
    apply Subtype.ext
    have haz : α (⟨z, hZA z.property⟩ : f.ker) = ⟨z, hZA z.property⟩ := by
      apply Subtype.ext
      change a * (z : G) * a⁻¹ = z
      rw [mem_center_iff.mp (hZ z.property) a, mul_inv_cancel_right]
    have hz2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (z : G) (hZA z.property)
    change (n ⟨z, hZA z.property⟩ : G) = z
    simp only [hn, haz, Subgroup.coe_mul]
    rw [← pow_two, hz2, one_mul]
  · intro g x
    have hconj : (ρ g)⁻¹ * α * ρ g = α ∨ (ρ g)⁻¹ * α * ρ g = α ^ 2 := by
      have hc : (f a) ^ 3 = 1 := by
        simpa only [ha_image] using pow_orderOf_eq_one (f a)
      rcases s3_conjugate_cubic (f a) (f g) hc with h | h
      · left
        simpa only [map_mul, map_inv, hσ] using congrArg σ h
      · right
        simpa only [map_mul, map_inv, map_pow, hσ] using congrArg σ h
    have hequiv : n (ρ g x) = ρ g (n x) := by
      rcases hconj with h | h
      · have hab : α * ρ g = ρ g * α := by
          have := congrArg (fun t : MulAut f.ker => ρ g * t) h
          simpa only [← mul_assoc, mul_inv_cancel, one_mul] using this
        have habx (y : f.ker) : α (ρ g y) = ρ g (α y) :=
          congrArg (fun t : MulAut f.ker => t y) hab
        simp only [hn, habx, map_mul]
      · have hab : α * ρ g = ρ g * α ^ 2 := by
          have := congrArg (fun t : MulAut f.ker => ρ g * t) h
          simpa only [← mul_assoc, mul_inv_cancel, one_mul] using this
        have habx (y : f.ker) : α (ρ g y) = ρ g (α (α y)) :=
          congrArg (fun t : MulAut f.ker => t y) hab
        simp only [hn, habx, hα3x, map_mul]
        rw [mul_assoc, mul_comm (ρ g (α (α x))), ← mul_assoc]
    apply Subtype.ext
    change (n (ρ g x) : G) = n x
    rw [hequiv]
    change g * (n x : G) * g⁻¹ = n x
    rw [mem_center_iff.mp (hZ (hnZ x)) g, mul_inv_cancel_right]

private theorem retraction_of_central_complement
    (Z B : Subgroup G) (hZ : Z ≤ center G) (hB : Z.IsComplement' B) :
    ∃ r : G →* Z, ∀ z : Z, r z = z := by
  let m : Z × B →* G :=
    { toFun := fun x => x.1 * x.2
      map_one' := mul_one 1
      map_mul' := by
        rintro ⟨z,b⟩ ⟨z',b'⟩
        change ((z : G) * z') * ((b : G) * b') = ((z : G) * b) * ((z' : G) * b')
        rw [mul_assoc, ← mul_assoc (z' : G), ← mem_center_iff.mp (hZ z'.property) b]
        simp only [mul_assoc] }
  let e : Z × B ≃* G := MulEquiv.ofBijective m hB
  refine ⟨(MonoidHom.fst Z B).comp e.symm.toMonoidHom, ?_⟩
  intro z
  have he : e (z, 1) = (z : G) := mul_one _
  change (e.symm (z : G)).1 = z
  rw [← he, e.symm_apply_apply]

private theorem extend_invariant_retraction [Finite G]
    (f : G →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (Z : Subgroup G) (hZA : Z ≤ f.ker) (hZ : Z ≤ center G)
    (hZcard : Nat.card Z = 2)
    (n : f.ker →* Z) (hn : ∀ z : Z, n ⟨z, hZA z.property⟩ = z)
    (hinv : ∀ (g : G) (x : f.ker), n (MulAut.conjNormal g x) = n x)
    (w : G) (hw : w ^ 2 = 1) (hfw : orderOf (f w) = 2) :
    ∃ r : G →* Z, ∀ z : Z, r z = z := by
  let N : Subgroup G := n.ker.map f.ker.subtype
  have hNA : N ≤ f.ker := map_subtype_le _
  have hNmem (x : f.ker) : (x : G) ∈ N ↔ n x = 1 := by
    constructor
    · rintro ⟨y,hy,he⟩
      have : y = x := Subtype.ext he
      simpa only [this] using (MonoidHom.mem_ker.mp hy)
    · intro hx
      exact ⟨x,hx,rfl⟩
  have hNnormal : N.Normal := by
    constructor
    intro x hx g
    let y : f.ker := ⟨x, hNA hx⟩
    have hy : n y = 1 := (hNmem y).mp hx
    exact (hNmem (MulAut.conjNormal g y)).mpr ((hinv g y).trans hy)
  let : N.Normal := hNnormal
  let q := QuotientGroup.mk' N
  let fQ : G ⧸ N →* Equiv.Perm (Fin 3) := QuotientGroup.lift N f hNA
  have hfQ : Function.Surjective fQ := QuotientGroup.lift_surjective_of_surjective N f hf hNA
  let i : Z →* G ⧸ N := q.comp Z.subtype
  have hi : Function.Injective i := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro z hz
    have hzN : (z : G) ∈ N := (QuotientGroup.eq_one_iff _).mp hz
    have hz' := (hNmem (⟨z,hZA z.property⟩ : f.ker)).mp hzN
    rwa [hn] at hz'
  have hqnorm (x : f.ker) : q x = i (n x) := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    let y : f.ker := x / ⟨n x, hZA (n x).property⟩
    exact (hNmem y).mpr (by dsimp [y]; rw [map_div, hn]; exact div_self' (n x))
  have hker : fQ.ker = i.range := by
    ext x
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective N x
    constructor
    · intro hx
      have hxA : x ∈ f.ker := hx
      exact ⟨n ⟨x,hxA⟩, (hqnorm ⟨x,hxA⟩).symm⟩
    · rintro ⟨z,hz⟩
      have hzQ : fQ (i z) = 1 := hZA z.property
      rw [hz] at hzQ
      exact hzQ
  have hcenter : i.range ≤ center (G ⧸ N) := by
    rintro _ ⟨z,rfl⟩
    apply mem_center_iff.mpr
    intro x
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective N x
    exact congrArg q (mem_center_iff.mp (hZ z.property) x)
  have hcard : Nat.card i.range = 2 :=
    (Nat.card_congr (MonoidHom.ofInjective hi).toEquiv).symm.trans hZcard
  let : i.range.Normal := hker ▸ fQ.normal_ker
  obtain ⟨B,hB⟩ := exists_complement_of_central_s3_quotient_involution
    i.range hcenter hcard.le fQ hfQ hker (q w) (by
      intro hwZ
      have he : fQ (q w) = 1 := MonoidHom.mem_ker.mp (hker.symm ▸ hwZ)
      change f w = 1 at he
      rw [he, orderOf_one] at hfw
      omega) (by rw [← map_pow, hw, map_one])
  obtain ⟨r,hr⟩ := retraction_of_central_complement i.range B hcenter hB
  let eZ := MonoidHom.ofInjective hi
  refine ⟨eZ.symm.toMonoidHom.comp (r.comp q), ?_⟩
  intro z
  apply eZ.injective
  change eZ (eZ.symm (r (i z))) = eZ z
  rw [eZ.apply_symm_apply]
  exact hr (eZ z)


/-- An elementary abelian two-kernel over S₃ splits off its central subgroup
of order two when a cubic lift fixes exactly that subgroup and a transposition
has an involutory lift. The retraction fixes the literal inclusion of `Z`. -/
public theorem exists_central_retraction_of_elementary_s3_quotient [Finite G]
    (f : G →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (hA : IsElementaryAbelian 2 f.ker)
    (Z : Subgroup G) (hZA : Z ≤ f.ker) (hZ : Z ≤ center G)
    (hZcard : Nat.card Z = 2)
    (a : G) (ha : a ^ 3 = 1) (ha_image : orderOf (f a) = 3)
    (hfixed : ∀ x : G, x ∈ f.ker → (Commute a x ↔ x ∈ Z))
    (w : G) (hw : w ^ 2 = 1) (hw_image : orderOf (f w) = 2) :
    ∃ r : G →* Z, ∀ z : Z, r z = z := by
  let := hA
  obtain ⟨n, hn, hinv⟩ := exists_kernel_norm f hf Z hZA hZ a ha ha_image hfixed
  exact extend_invariant_retraction f hf Z hZA hZ hZcard n hn hinv w hw hw_image

end Theory.GroupTheory

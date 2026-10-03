module

public import Theory.GroupTheory.QuaternionCentralProductCenter
public import Theory.GroupTheory.PGroup.ExtraspecialCentralProduct
public import Mathlib.Data.Fintype.Prod

/-!
# Fixed points of a mixed involution on a quaternion central product

An involutory automorphism preserving two commuting quaternion factors, outer
on the first and inner on the second, has an extraspecial fixed subgroup.

Multiplication from the two quaternion models has kernel consisting of the
identity and the pair of central involutions. A kernel-checked finite table
counts sixteen lifts of fixed points and finds two lifts whose images do not
commute. Dividing by the kernel gives eight fixed elements, so the standard
nonabelian order-eight criterion applies. The same table includes both trivial
and nontrivial inner actions on the second factor.

Source: Janko–Thompson (1970), §4, printed pp.390–391, case (b)(i),
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
The private generator-image encoding follows the normal forms in
`Theory.GroupTheory.SpecificGroups.QuaternionEightAut`.
-/

namespace Subgroup

open QuaternionGroup
open scoped Pointwise
private abbrev Q := QuaternionGroup 2
private def pairMap (p : Q × Q) : Q → Q
  | a i => p.1 ^ i.val
  | xa i => p.2 * p.1 ^ i.val
private def diagonalKernel (u : Q × Q) : Prop := u = 1 ∨ u = (a 2, a 2)
private instance : DecidablePred diagonalKernel := fun _ => inferInstanceAs (Decidable (_ ∨ _))
private def fixedLift (p : Q × Q) (c : Q) (u : Q × Q) : Prop :=
  diagonalKernel (u⁻¹ * (pairMap p u.1, c * u.2 * c⁻¹))
private instance (p : Q × Q) (c : Q) : DecidablePred (fixedLift p c) := fun _ => inferInstanceAs (Decidable (diagonalKernel _))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem quaternion_mixed_table : ∀ p : Q × Q,
    (∀ x y, pairMap p (x*y) = pairMap p x * pairMap p y) →
    (∀ x, pairMap p (pairMap p x) = x) →
    (¬ ∃ b, ∀ x, pairMap p x = b*x*b⁻¹) →
    ∀ c : Q, Fintype.card {u : Q × Q // fixedLift p c u} = 16 ∧
      ∃ u v : Q × Q, fixedLift p c u ∧ fixedLift p c v ∧ ¬ diagonalKernel ((u*v)⁻¹*(v*u)) := by
  decide

private theorem quaternion_central_iff (x : Q) : (∀ y : Q, y*x=x*y) ↔ x=1 ∨ x=a 2 := by
  revert x
  decide

private theorem quaternion_product_kernel {G : Type*} [Group G] [Finite G]
    (B C : Subgroup G) (b : B ≃* Q) (c : C ≃* Q)
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ x ∈ B, ∀ y ∈ C, x*y=y*x)
    (i j : Q →* G) (hi : ∀ x, i x = (b.symm x : G))
    (hj : ∀ x, j x = (c.symm x : G)) :
    ∀ u : Q × Q, i u.1 * j u.2 = 1 ↔ diagonalKernel u := by
  have hii : Function.Injective i := by
    intro x y h
    apply b.symm.injective
    apply Subtype.ext
    simpa only [hi] using h
  have hji : Function.Injective j := by
    intro x y h
    apply c.symm.injective
    apply Subtype.ext
    simpa only [hj] using h
  have hzB : i (a 2) ∈ B ⊓ C := by
    rw [Subgroup.intersection_eq_factor_center B C ⟨b⟩ hinter hcomm, hi]
    refine ⟨b.symm (a 2), Subgroup.mem_center_iff.mpr ?_, rfl⟩
    intro x
    apply b.injective
    simpa using (quaternion_central_iff (a 2)).mpr (Or.inr rfl) (b x)
  have hzC : j (a 2) ∈ B ⊓ C := by
    rw [inf_comm, Subgroup.intersection_eq_factor_center C B ⟨c⟩
      (by simpa [inf_comm] using hinter) (fun x hx y hy => (hcomm y hy x hx).symm), hj]
    refine ⟨c.symm (a 2), Subgroup.mem_center_iff.mpr ?_, rfl⟩
    intro x
    apply c.injective
    simpa using (quaternion_central_iff (a 2)).mpr (Or.inr rfl) (c x)
  have hz : i (a 2) = j (a 2) := by
    obtain ⟨w, _, hw⟩ := (Nat.card_eq_two_iff' (1 : (B ⊓ C : Subgroup G))).mp hinter
    have hni : (⟨i (a 2), hzB⟩ : (B ⊓ C : Subgroup G)) ≠ 1 := by
      intro h
      have hh : i (a 2) = i 1 := (congrArg Subtype.val h).trans i.map_one.symm
      exact (by decide : (a 2 : Q) ≠ 1) (hii hh)
    have hnj : (⟨j (a 2), hzC⟩ : (B ⊓ C : Subgroup G)) ≠ 1 := by
      intro h
      have hh : j (a 2) = j 1 := (congrArg Subtype.val h).trans j.map_one.symm
      exact (by decide : (a 2 : Q) ≠ 1) (hji hh)
    exact congrArg Subtype.val ((hw _ hni).trans (hw _ hnj).symm)
  intro u
  constructor
  · intro hu
    have he : i u.1 = (j u.2)⁻¹ := eq_inv_of_mul_eq_one_left hu
    have hc : ∀ y : Q, y*u.1=u.1*y := by
      intro y
      apply hii
      rw [map_mul, map_mul, he]
      apply Commute.inv_right
      rw [hi, hj]
      exact hcomm _ (b.symm y).property _ (c.symm u.2).property
    rcases (quaternion_central_iff u.1).mp hc with hu1 | huz
    · have hu2 : u.2 = 1 := by
        apply hji
        simpa [hu1] using hu
      exact Or.inl (Prod.ext hu1 hu2)
    · have hu2 : u.2 = a 2 := by
        apply hji
        apply mul_left_cancel (a := j (a 2))
        have hzz : j (a 2) * j (a 2) = 1 := by
          rw [← map_mul]
          exact (congrArg j (by decide : (a 2 : Q)*(a 2)=1)).trans j.map_one
        rw [hzz, ← hz, ← huz]
        exact hu
      exact Or.inr (Prod.ext huz hu2)
  · rintro (hu | hu)
    · simp [hu]
    · change u = (a 2, a 2) at hu
      rw [hu]
      change i (a 2) * j (a 2) = 1
      rw [hz, ← map_mul]
      exact (congrArg j (by decide : (a 2 : Q)*(a 2)=1)).trans j.map_one

/-- An involutory automorphism acting outerly on one quaternion factor and
innerly on the other has an extraspecial fixed subgroup of order eight. -/
public theorem extraspecial_fixed_of_quaternion_mixed_involution {G : Type*} [Group G] [Finite G]
    (B C : Subgroup G) (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hsup : B ⊔ C = ⊤) (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b)
    (e : MulAut G) (he : e^2=1)
    (hBB : B.map e.toMonoidHom=B) (_hCC : C.map e.toMonoidHom=C)
    (hBO : ¬ ∃ b : B, ∀ x : B, e (x : G) = (b : G)*x*(b : G)⁻¹)
    (hCI : ∃ c : C, ∀ x : C, e (x : G) = (c : G)*x*(c : G)⁻¹) :
    IsExtraspecial 2 (e.toMonoidHom.eqLocus (MonoidHom.id G)) := by
  obtain ⟨b⟩ := hB
  obtain ⟨c⟩ := hC
  obtain ⟨d, hd⟩ := hCI
  let i : Q →* G := B.subtype.comp b.symm.toMonoidHom
  let j : Q →* G := C.subtype.comp c.symm.toMonoidHom
  let aB : MulAut B := (e.subgroupMap B).trans (MulEquiv.subgroupCongr hBB)
  let a : MulAut Q := (b.symm.trans aB).trans b
  have hi (x : Q) : i (a x) = e (i x) := by
    simp [i, a, aB]
    rfl
  have hj (x : Q) : j (c d * x * (c d)⁻¹) = e (j x) := by
    simpa [j] using (hd (c.symm x)).symm
  let p : Q × Q := (a (QuaternionGroup.a 1), a (xa 0))
  have hp (x : Q) : pairMap p x = a x := by
    cases x with
    | a k =>
      change (a (QuaternionGroup.a 1)) ^ k.val = a (QuaternionGroup.a k)
      rw [← map_pow, a_one_pow, ZMod.natCast_zmod_val]
    | xa k =>
      change a (xa 0) * (a (QuaternionGroup.a 1)) ^ k.val = a (xa k)
      rw [← map_pow, ← map_mul, a_one_pow, ZMod.natCast_zmod_val, xa_mul_a, zero_add]
  have hii : Function.Injective i := by
    intro x y h
    exact b.symm.injective (Subtype.ext h)
  have hm : ∀ x y, pairMap p (x*y) = pairMap p x * pairMap p y := by simp [hp]
  have ha2 : ∀ x, pairMap p (pairMap p x) = x := by
    intro x
    rw [hp, hp]
    apply hii
    rw [hi, hi]
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using DFunLike.congr_fun he (i x)
  have ho : ¬ ∃ z : Q, ∀ x, pairMap p x = z*x*z⁻¹ := by
    rintro ⟨z, hz⟩
    apply hBO
    refine ⟨b.symm z, ?_⟩
    intro x
    have hh := congrArg i (hz (b x))
    rw [hp, hi, map_mul, map_mul, map_inv] at hh
    simpa [i] using hh
  obtain ⟨hcard, u, v, hu, hv, huv⟩ := quaternion_mixed_table p hm ha2 ho (c d)
  let f : Q × Q →* G := {
    toFun := fun q => i q.1 * j q.2
    map_one' := by simp
    map_mul' := by
      intro x y
      change i (x.1*y.1) * j (x.2*y.2) = (i x.1*j x.2)*(i y.1*j y.2)
      rw [map_mul, map_mul]
      have hh : j x.2 * i y.1 = i y.1 * j x.2 :=
        (hcomm _ (b.symm y.1).property _ (c.symm x.2).property).symm
      calc
        i x.1 * i y.1 * (j x.2 * j y.2) = i x.1 * (i y.1 * j x.2) * j y.2 := by simp only [mul_assoc]
        _ = (i x.1 * j x.2) * (i y.1 * j y.2) := by rw [← hh]; simp only [mul_assoc] }
  have hk (q : Q × Q) : q ∈ f.ker ↔ diagonalKernel q :=
    quaternion_product_kernel B C b c hinter hcomm i j (fun _ => rfl) (fun _ => rfl) q
  have hf : Function.Surjective f := by
    intro x
    have hn : B ≤ Subgroup.normalizer (C : Set G) := by
      apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro y hy z hz
      exact (hcomm y hy z hz).symm
    have hx : x ∈ (B : Set G) * (C : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right B C hn, hsup]
      trivial
    obtain ⟨y, hy, z, hz, hyz⟩ := hx
    refine ⟨(b ⟨y, hy⟩, c ⟨z, hz⟩), ?_⟩
    simpa [f, i, j] using hyz
  let F := e.toMonoidHom.eqLocus (MonoidHom.id G)
  let L := F.comap f
  have hR (q : Q × Q) : q ∈ L ↔ fixedLift p (c d) q := by
    change e (f q) = f q ↔ diagonalKernel (q⁻¹ * (pairMap p q.1, c d * q.2 * (c d)⁻¹))
    rw [← hk, ← f.eq_iff]
    have heq : f (pairMap p q.1, c d * q.2 * (c d)⁻¹) = e (f q) := by
      change i (pairMap p q.1) * j (c d * q.2 * (c d)⁻¹) = e (i q.1 * j q.2)
      rw [hp, hi, hj, map_mul]
    rw [heq]
  have hL : Nat.card L = 16 := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight hR), Nat.card_eq_fintype_card]
    exact hcard
  have hker : Nat.card f.ker = 2 := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight hk), Nat.card_eq_fintype_card]
    decide
  have hle : f.ker ≤ L := by
    intro x hx
    change f x ∈ F
    rw [show f x = 1 from hx]
    exact F.one_mem
  have hmap : L.map f = F := Subgroup.map_comap_eq_self_of_surjective hf F
  have hcount := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup (Q × Q)) f.ker L bot_le hle
  rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left,
    Subgroup.relIndex_ker, hmap, hL, hker] at hcount
  apply IsExtraspecial.of_noncommutative_card_eight (show Nat.card F = 8 by omega)
  intro hcom
  let : IsMulCommutative F := hcom
  have huf : f u ∈ F := (hR u).mpr hu
  have hvf : f v ∈ F := (hR v).mpr hv
  apply huv
  apply (hk _).mp
  apply f.eq_iff.mp
  simpa only [map_mul, Subgroup.coe_mul] using congrArg Subtype.val (mul_comm' (⟨f v, hvf⟩ : F) ⟨f u, huf⟩)

end Subgroup

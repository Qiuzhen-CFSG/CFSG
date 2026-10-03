module
public import Theory.GroupTheory.QuaternionDiagonalMembership
public import Mathlib.GroupTheory.Commutator.Basic
/-!
# Commutators for an involution swapping quaternion factors

Two commuting quaternion subgroups with intersection of order two have an
explicit elementary diagonal for every factor isomorphism. If conjugation by
an involution supplies that isomorphism, the commutator of their join with
its cyclic subgroup equals the fixed subgroup, namely this diagonal.

The shared central involution belongs to the commutator: choose two elements
of one quaternion factor with that commutator, and commute the first with the
second element's commutator with the swapping involution. The other-factor
coordinate disappears by commutation. Squares in either factor lie in the
shared intersection, so every diagonal generator then belongs to the
commutator. Conversely, factor commutators lie in the diagonal, which is
normalized by the product and fixed by the involution; closure induction gives
the reverse containment. The finite quaternion calculations use kernel-checked
`decide`. No finiteness of the ambient group is required.

This supplies the fixed-eight commutator calculation for the quaternion
central product in Stellmacher (9.1), Journal of Algebra 190 (1997), p.48;
source `refs/files/stellmacher-n-group.pdf`.
-/

namespace Subgroup
open scoped Pointwise commutatorElement
universe u
variable {G : Type u} [Group G]

private theorem commutator_zpowers_le_of_factors
    (B C K : Subgroup G) (s : G)
    (hVK : B ⊔ C ≤ normalizer K) (hsK : s ∈ normalizer K)
    (hB : ∀ b ∈ B, ⁅b,s⁆ ∈ K) (hC : ∀ c ∈ C, ⁅c,s⁆ ∈ K) :
    ⁅B ⊔ C,zpowers s⁆ ≤ K := by
  have hxs : ∀ x ∈ B ⊔ C, ⁅x,s⁆ ∈ K := by
    intro x hx
    rw [sup_eq_closure] at hx
    induction hx using closure_induction with
    | mem x hx => exact hx.elim (hB x) (hC x)
    | one => simp
    | mul x y hx hy hxc hyc =>
      rw [commutatorElement_mul_left_eq_conj_mul]
      apply K.mul_mem _ hxc
      exact (mem_normalizer_iff.mp (hVK (by rwa [sup_eq_closure])) _).mp hyc
    | inv x hx hxc =>
      rw [commutatorElement_inv_left, ← commutatorElement_inv]
      simpa only [inv_inv] using (mem_normalizer_iff.mp (hVK (inv_mem (by rwa [sup_eq_closure]))) _).mp (K.inv_mem hxc)
  have hSK : closure ({s} : Set G) ≤ normalizer K :=
    (closure_le _).mpr (Set.singleton_subset_iff.mpr hsK)
  apply commutator_le.mpr
  intro x hx a ha
  rw [zpowers_eq_closure] at ha
  induction ha using closure_induction with
  | mem a ha => exact Set.mem_singleton_iff.mp ha ▸ hxs x hx
  | one => simp
  | mul a b ha hb hac hbc =>
    rw [commutatorElement_mul_right_eq_mul_conj]
    simpa only [mul_assoc] using K.mul_mem hac
      ((mem_normalizer_iff.mp (hSK ha) _).mp hbc)
  | inv a ha hac =>
    rw [commutatorElement_inv_right, ← commutatorElement_inv]
    simpa only [inv_inv] using (mem_normalizer_iff.mp (hSK (inv_mem ha)) _).mp (K.inv_mem hac)

public theorem commutator_zpowers_eq_fixed_of_quaternion_swap
    (B C : Subgroup G) (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b)
    (s : G) (hs : s^2=1) (hswap : B.map (MulAut.conj s).toMonoidHom = C) :
    ⁅B ⊔ C,zpowers s⁆ = (B ⊔ C) ⊓ centralizer ({s} : Set G) := by
  obtain ⟨model⟩ := hB
  let θ : B ≃* C := (B.equivMapOfInjective (MulAut.conj s).toMonoidHom
    (MulAut.conj s).injective).trans (MulEquiv.subgroupCongr hswap)
  have hθ (b : B) : (θ b : G) = s*(b:G)*s⁻¹ := rfl
  let V := B ⊔ C
  let D := quaternionDiagonal B C θ hcomm
  let W := ⁅V,zpowers s⁆
  have hfixed : V ⊓ centralizer ({s} : Set G) = D :=
    quaternion_diagonal_eq_inf_centralizer_of_swap B C θ hinter hcomm s hs (fun b => (hθ b).symm)
  obtain ⟨hDelem,_,hID,hDV⟩ := quaternion_diagonal_elementary_eight B C model θ hinter hcomm
  let _ := hDelem
  obtain ⟨z,hzne,huniq⟩ := (Nat.card_eq_two_iff' (1 : (B ⊓ C : Subgroup G))).mp hinter
  let zB : B := ⟨z,z.property.1⟩
  have hzBne : zB ≠ 1 := fun h => hzne (Subtype.ext (congrArg (fun x : B => (x:G)) h))
  have hzBsq : zB^2=1 := by
    apply Subtype.ext
    exact congrArg (fun x : (B ⊓ C : Subgroup G) => (x:G))
      (show z^2=1 by simpa only [hinter] using pow_card_eq_one' (x := z))
  have hfinite : ∀ z : QuaternionGroup 2, z ≠ 1 → z^2=1 →
      (∀ b : QuaternionGroup 2, b^2=1 ∨ b^2=z) ∧
        ∃ a b : QuaternionGroup 2, ⁅a,b⁆=z := by decide
  obtain ⟨hsquares,a,b,hab⟩ := hfinite (model zB)
    (fun h => hzBne (model.injective (h.trans model.map_one.symm)))
    (by rw [← map_pow,hzBsq,map_one])
  have hsquare (b : B) : (b:G)^2 ∈ B ⊓ C := by
    rcases hsquares (model b) with h | h
    · have hh : b^2=1 := model.injective (by simpa only [map_pow,map_one] using h)
      rw [← Subgroup.coe_pow,hh,Subgroup.coe_one]
      exact one_mem _
    · have hh : b^2=zB := model.injective (by simpa only [map_pow] using h)
      rw [← Subgroup.coe_pow,hh]
      exact z.property
  have hsBcomm (b : B) : ⁅(b:G),s⁆ = (b:G)*(θ b:G)⁻¹ := by
    rw [hθ]
    group
  have hsC (c : C) : s*(c:G)*s⁻¹ = (θ.symm c:G) := by
    have hh := hθ (θ.symm c)
    have hs' : s*s=1 := by simpa only [pow_two] using hs
    calc
      s*(c:G)*s⁻¹ = s*(s*(θ.symm c:G)*s⁻¹)*s⁻¹ := by rw [← hh]; simp only [MulEquiv.apply_symm_apply]
      _ = (s*s)*(θ.symm c:G)*(s*s)⁻¹ := by group
      _ = (θ.symm c:G) := by rw [hs']; simp
  have hWnorm : V ≤ normalizer W := normalizer_commutator_ge_left V (zpowers s)
  have hWb (b : B) : (b:G)*(θ b:G)⁻¹ ∈ W := by
    rw [← hsBcomm]
    exact commutator_mem_commutator (mem_sup_left b.property) (mem_zpowers s)
  have hzW : (z:G) ∈ W := by
    let aa := model.symm a
    let bb := model.symm b
    have hab' : ⁅aa,bb⁆ = zB := model.injective (by simpa only [map_commutatorElement,aa,bb,
      MulEquiv.apply_symm_apply] using hab)
    have hw := le_normalizer_iff_commutator_le_right.mp hWnorm
      (commutator_mem_commutator (mem_sup_left aa.property) (hWb bb))
    have heq : ⁅(aa:G),(bb:G)*(θ bb:G)⁻¹⁆ = ⁅(aa:G),(bb:G)⁆ := by
      have hac : (aa:G)*(θ bb:G) = (θ bb:G)*(aa:G) :=
        hcomm aa aa.property (θ bb) (θ bb).property
      rw [commutatorElement_mul_right_eq_mul_conj,
        commutatorElement_eq_one_iff_mul_comm.mpr ((Commute.inv_right hac).eq)]
      simp
    rw [heq] at hw
    exact (congrArg Subtype.val hab') ▸ hw
  have hIW : B ⊓ C ≤ W := by
    intro x hx
    by_cases hx1 : x=1
    · rw [hx1]; exact one_mem _
    have h := huniq (⟨x,hx⟩ : (B ⊓ C : Subgroup G)) (fun h => hx1 (congrArg Subtype.val h))
    have hxz : x=(z:G) := congrArg Subtype.val h
    rw [hxz]
    exact hzW
  have hDW : D ≤ W := by
    apply sup_le _ hIW
    rintro x ⟨b,rfl⟩
    change (b:G)*(θ b:G) ∈ W
    have hw := W.mul_mem (hIW (hsquare b)) (hWb b⁻¹)
    simpa only [map_inv,Subgroup.coe_inv,inv_inv,pow_two,mul_assoc,mul_inv_cancel_left] using hw
  have hWD : W ≤ D := by
    apply commutator_zpowers_le_of_factors B C D s
      (sup_le_normalizer_quaternionDiagonal B C model θ hinter hcomm)
      ((centralizer_le_normalizer (D:Set G)) ?_) ?_ ?_
    · intro d hd
      have hd' : d ∈ V ⊓ centralizer ({s}:Set G) := hfixed.symm ▸ hd
      exact mem_centralizer_singleton_iff.mp hd'.2
    · intro b hb
      let bb : B := ⟨b,hb⟩
      have hd : (b:G)*(θ bb:G) ∈ D :=
        (show (quaternionDiagonalHom B C θ hcomm).range ≤ D from le_sup_left) ⟨bb,rfl⟩
      have hsquareC : (θ bb:G)^2 ∈ B ⊓ C := by
        have hfix : (b:G)^2 ∈ V ⊓ centralizer ({s}:Set G) :=
          hfixed.symm ▸ hID (hsquare bb)
        have he := mem_centralizer_singleton_iff.mp hfix.2
        have hbfix : s*((b:G)^2)*s⁻¹=(b:G)^2 := by rw [← he,mul_inv_cancel_right]
        have heq : (θ bb:G)^2=(b:G)^2 := by
          rw [hθ]
          calc
            (s*(b:G)*s⁻¹)^2 = s*((b:G)^2)*s⁻¹ := by simp only [pow_two]; group
            _ = (b:G)^2 := hbfix
        rw [heq]
        exact hsquare bb
      rw [hsBcomm bb]
      have hh := D.mul_mem hd (D.inv_mem (hID hsquareC))
      simpa only [pow_two,mul_inv_rev,mul_assoc,mul_inv_cancel_left] using hh
    · intro c hc
      let cc : C := ⟨c,hc⟩
      have hd : (θ.symm cc:G)*(c:G) ∈ D :=
        (show (quaternionDiagonalHom B C θ hcomm).range ≤ D from le_sup_left) ⟨θ.symm cc,by change (θ.symm cc:G)*(θ (θ.symm cc):G) = _; rw [MulEquiv.apply_symm_apply]⟩
      have hh := D.mul_mem hd (D.inv_mem (hID (hsquare (θ.symm cc))))
      have hbc := hcomm (θ.symm cc) (θ.symm cc).property c hc
      have heq : ⁅c,s⁆ = ((θ.symm cc:G)*c)*((θ.symm cc:G)^2)⁻¹ := by
        have hcS : ⁅c,s⁆=c*(θ.symm cc:G)⁻¹ := by
          change ⁅(cc:G),s⁆=(cc:G)*(θ.symm cc:G)⁻¹
          rw [← hsC cc]
          group
        rw [hcS, hbc]
        group
      rwa [heq]
  exact (le_antisymm hWD hDW).trans hfixed.symm
end Subgroup

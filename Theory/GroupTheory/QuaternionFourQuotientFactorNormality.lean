module
public import Theory.GroupTheory.QuaternionDiagonalMembership
public import Theory.GroupTheory.QuaternionFixedEightNormal
/-!
# Normal quaternion factors in elementary extensions

Let a normal extraspecial subgroup be the central product of two quaternion
eights. If the ambient quotient is elementary abelian of exponent two and
there is no normal elementary subgroup of order at least eight, both quaternion
factors are normal. This applies in particular when the quotient has order four.

The factors are intrinsic, so conjugation either preserves them or swaps them.
For a swapping element `s`, the quotient hypothesis gives `s² ∈ P`; it does not
assert that `s` is an involution. The factor isomorphism induced by `s` defines
a diagonal elementary eight. The square condition makes the reverse factor
action inverse to this isomorphism modulo the shared center. Consequently the
diagonal is exactly `[P, ⟨s⟩]`. It contains the derived subgroup of `P`, so the
abelian ambient quotient makes it normal. This contradicts the normal-only
bound and excludes swapping.

The commutator calculation extends the involutory calculation in
`QuaternionSwapCommutator`; no condition on the order of the swapping lift is
imposed. The proof does not require a bound on arbitrary elementary subgroups.

Source: Janko–Thompson, Math. Z. 113 (1970), case (b)(ii), printed p.391,
with the structural results on printed p.386;
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
-/

namespace Subgroup
open scoped Pointwise commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
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

/-- A swapping lift whose square lies in the central product has its relative
commutator equal to a quaternion diagonal. The lift need not be an involution. -/
public theorem commutator_zpowers_eq_diagonal_of_quaternion_swap_square
    (B C : Subgroup G) (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b)
    (s : G) (hs : s^2 ∈ B ⊔ C) (hswap : B.map (MulAut.conj s).toMonoidHom = C) :
    ∃ θ : B ≃* C, ⁅B ⊔ C,zpowers s⁆ = quaternionDiagonal B C θ hcomm := by
  obtain ⟨model⟩ := hB
  let θ : B ≃* C := (B.equivMapOfInjective (MulAut.conj s).toMonoidHom
    (MulAut.conj s).injective).trans (MulEquiv.subgroupCongr hswap)
  have hθ (b : B) : (θ b : G) = s*(b:G)*s⁻¹ := rfl
  let V := B ⊔ C
  let D := quaternionDiagonal B C θ hcomm
  let W := ⁅V,zpowers s⁆
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
  have hsC (c : C) :
      (θ.symm c:G)⁻¹ * (s*(c:G)*s⁻¹) ∈ B ⊓ C := by
    have hh := hθ (θ.symm c)
    have heq : s*(c:G)*s⁻¹ = (s^2)*(θ.symm c:G)*(s^2)⁻¹ := by
      calc
        s*(c:G)*s⁻¹ = s*(s*(θ.symm c:G)*s⁻¹)*s⁻¹ := by
          rw [← hh]; simp only [MulEquiv.apply_symm_apply]
        _ = (s^2)*(θ.symm c:G)*(s^2)⁻¹ := by simp only [pow_two]; group
    rw [heq]
    exact factor_central_difference_of_mem_sup B C model hinter hcomm
      (s^2) hs (θ.symm c) (θ.symm c).property
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
  have hCswap (c : C) : s*(c:G)*s⁻¹ ∈ B := by
    have hh := B.mul_mem (θ.symm c).property (hsC c).1
    simpa only [mul_inv_cancel_left] using hh
  have hInorm : s ∈ normalizer (B ⊓ C : Subgroup G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (MulAut.conj s).injective])
    rintro x ⟨y,hy,rfl⟩
    refine ⟨hCswap ⟨y,hy.2⟩, ?_⟩
    change s*y*s⁻¹ ∈ C
    rw [← hθ ⟨y,hy.1⟩]
    exact (θ ⟨y,hy.1⟩).property
  have hsD : s ∈ normalizer D := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (MulAut.conj s).injective])
    rw [map_le_iff_le_comap]
    apply sup_le
    · rintro x ⟨b,rfl⟩
      let d : G := (b:G)⁻¹ * (s*(θ b:G)*s⁻¹)
      have hd : d ∈ B ⊓ C := by simpa only [MulEquiv.symm_apply_apply] using hsC (θ b)
      have hdiag : (b:G)*(θ b:G) ∈ D :=
        (show (quaternionDiagonalHom B C θ hcomm).range ≤ D from le_sup_left) ⟨b,rfl⟩
      have heq : s*((b:G)*(θ b:G))*s⁻¹ = ((b:G)*(θ b:G))*d := by
        calc
          s*((b:G)*(θ b:G))*s⁻¹ = (s*(b:G)*s⁻¹)*(s*(θ b:G)*s⁻¹) := by group
          _ = (θ b:G)*((b:G)*d) := by rw [← hθ]; dsimp [d]; group
          _ = ((b:G)*(θ b:G))*d := by rw [← mul_assoc, hcomm b b.property (θ b) (θ b).property]
      change s*((b:G)*(θ b:G))*s⁻¹ ∈ D
      rw [heq]
      exact D.mul_mem hdiag (hID hd)
    · intro x hx
      exact hID ((mem_normalizer_iff.mp hInorm x).mp hx)
  have hWD : W ≤ D := by
    apply commutator_zpowers_le_of_factors B C D s
      (sup_le_normalizer_quaternionDiagonal B C model θ hinter hcomm) hsD
    · intro b hb
      let bb : B := ⟨b,hb⟩
      have hd : (b:G)*(θ bb:G) ∈ D :=
        (show (quaternionDiagonalHom B C θ hcomm).range ≤ D from le_sup_left) ⟨bb,rfl⟩
      have hsquareC : (θ bb:G)^2 ∈ B ⊓ C := by
        have hh := (mem_normalizer_iff.mp hInorm _).mp (hsquare bb)
        have heq : s*((bb:G)^2)*s⁻¹ = (θ bb:G)^2 := by rw [hθ]; simp only [pow_two]; group
        rwa [heq] at hh
      rw [hsBcomm bb]
      have hh := D.mul_mem hd (D.inv_mem (hID hsquareC))
      simpa only [pow_two,mul_inv_rev,mul_assoc,mul_inv_cancel_left] using hh
    · intro c hc
      let cc : C := ⟨c,hc⟩
      let b := θ.symm cc
      let d : G := (b:G)⁻¹*(s*c*s⁻¹)
      have hd : d ∈ B ⊓ C := hsC cc
      have hdiag : (b:G)*c ∈ D :=
        (show (quaternionDiagonalHom B C θ hcomm).range ≤ D from le_sup_left)
          ⟨b,by change (θ.symm cc:G)*(θ (θ.symm cc):G) = _; rw [MulEquiv.apply_symm_apply]⟩
      have hcb : c*(b:G)⁻¹ ∈ D := by
        have hh := D.mul_mem hdiag (D.inv_mem (hID (hsquare b)))
        have heq : ((b:G)*c)*((b:G)^2)⁻¹ = c*(b:G)⁻¹ := by
          rw [hcomm b b.property c hc]; group
        rwa [heq] at hh
      have hdc : c*d = d*c := hcomm d hd.1 c hc |>.symm
      have heq : ⁅c,s⁆ = d⁻¹*(c*(b:G)⁻¹) := by
        have hsd : s*c*s⁻¹ = (b:G)*d := by dsimp [d]; group
        calc
          ⁅c,s⁆ = c*(s*c*s⁻¹)⁻¹ := by group
          _ = c*(d⁻¹*(b:G)⁻¹) := by rw [hsd, mul_inv_rev]
          _ = d⁻¹*(c*(b:G)⁻¹) := by rw [← mul_assoc, (Commute.inv_right hdc).eq, mul_assoc]
      rw [heq]
      exact D.mul_mem (D.inv_mem (hID hd)) hcb
  exact ⟨θ, le_antisymm hWD hDW⟩
/-- A quaternion swap whose square belongs to the normal extraspecial core
produces a normal elementary eight in an abelian extension. -/
public theorem quaternion_swap_square_normal_elementary_eight
    (P B C : Subgroup G) [P.Normal] [IsExtraspecial 2 P]
    [IsMulCommutative (G ⧸ P)]
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = P)
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b)
    (s : G) (hs : s^2 ∈ P)
    (hswap : B.map (MulAut.conj s).toMonoidHom = C) :
    ∃ E : Subgroup G, E ≤ P ∧ E.Normal ∧
      IsElementaryAbelian 2 E ∧ Nat.card E = 8 := by
  obtain ⟨θ, hθ⟩ := commutator_zpowers_eq_diagonal_of_quaternion_swap_square
    B C hB hinter hcomm s (hjoin ▸ hs) hswap
  obtain ⟨model⟩ := hB
  obtain ⟨helem, hcard, hID, hDP⟩ :=
    quaternion_diagonal_elementary_eight B C model θ hinter hcomm
  let D := quaternionDiagonal B C θ hcomm
  have hIcenter : B ⊓ C ≤ (center P).map P.subtype := by
    intro x hx
    have hxP : x ∈ P := hjoin ▸ mem_sup_left hx.1
    refine ⟨⟨x,hxP⟩, mem_center_iff.mpr ?_, rfl⟩
    intro p
    have hcentral : B ⊔ C ≤ centralizer ({x} : Set G) := by
      apply sup_le
      · intro b hb
        exact mem_centralizer_singleton_iff.mpr (hcomm b hb x hx.2)
      · intro c hc
        exact mem_centralizer_singleton_iff.mpr (hcomm x hx.1 c hc).symm
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hcentral (hjoin.symm ▸ p.property)))
  have hIeq : B ⊓ C = (center P).map P.subtype :=
    eq_of_le_of_card_ge hIcenter (by
      rw [card_map_of_injective P.subtype_injective, IsExtraspecial.center_order_p 2 P, hinter])
  have hder : ⁅P,P⁆ ≤ D := by
    apply le_trans ?_ hID
    rw [hIeq, ← map_subtype_commutator]
    exact map_mono (IsExtraspecial.quotient_elementary_abelian 2 P).commutator_le_center_of_central_quotient
  have hDnormal : D.Normal := by
    have heq : ⁅P,zpowers s⁆ = D := by simpa only [hjoin] using hθ
    rw [← heq]
    exact commutator_normal_of_abelian_quotient P (zpowers s) (heq ▸ hder)
  exact ⟨D, hDP.trans_eq hjoin, hDnormal, helem, hcard⟩

/-- In an elementary extension with no normal elementary eight, the two
intrinsic quaternion factors of a normal extraspecial core are normal. -/
public theorem quaternion_factors_normal_of_elementary_quotient
    (P B C : Subgroup G) [P.Normal] [IsExtraspecial 2 P]
    [IsElementaryAbelian 2 (G ⧸ P)]
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = P)
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b)
    (hno : ¬ ∃ E : Subgroup G, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E) :
    B.Normal ∧ C.Normal := by
  have hne : B ≠ C := by
    intro h
    obtain ⟨model⟩ := hB
    have hcard : Nat.card B = 8 := by
      rw [Nat.card_congr model.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    rw [← h, inf_idem, hcard] at hinter
    omega
  have hmaps (s : G) : B.map (MulAut.conj s).toMonoidHom = B ∧
      C.map (MulAut.conj s).toMonoidHom = C := by
    let e := MulAut.conj s
    have himage (D : Subgroup G) (hD : Nonempty (D ≃* QuaternionGroup 2))
        (hle : D ≤ P) : D.map e.toMonoidHom = B ∨ D.map e.toMonoidHom = C := by
      obtain ⟨model⟩ := hD
      apply quaternion_subgroup_eq_factor B C _ hB hC hinter hcomm
      · exact ⟨(D.equivMapOfInjective e.toMonoidHom e.injective).symm.trans model⟩
      · rw [hjoin]
        have hp : P.map e.toMonoidHom = P := mem_normalizer_iff_map_conj_eq.mp
          (by rw [P.normalizer_eq_top]; trivial)
        exact (map_mono hle).trans_eq hp
    have hBB : B.map e.toMonoidHom = B := by
      rcases himage B hB (le_sup_left.trans_eq hjoin) with hb | hb
      · exact hb
      have hs : s^2 ∈ P := by
        apply (QuotientGroup.eq_one_iff (s^2)).mp
        change (QuotientGroup.mk' P) (s^2) = 1
        rw [map_pow]
        exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 (G ⧸ P)) _
      obtain ⟨E, _, hn, he, hc⟩ := quaternion_swap_square_normal_elementary_eight
        P B C hB hjoin hinter hcomm s hs hb
      exact (hno ⟨E,hn,he,hc.ge⟩).elim
    refine ⟨hBB, ?_⟩
    rcases himage C hC (le_sup_right.trans_eq hjoin) with hc | hc
    · exact (hne (map_injective e.injective (hBB.trans hc.symm))).elim
    · exact hc
  constructor
  · apply normalizer_eq_top_iff.mp
    exact top_unique (fun s _ => mem_normalizer_iff_map_conj_eq.mpr (hmaps s).1)
  · apply normalizer_eq_top_iff.mp
    exact top_unique (fun s _ => mem_normalizer_iff_map_conj_eq.mpr (hmaps s).2)

end Subgroup

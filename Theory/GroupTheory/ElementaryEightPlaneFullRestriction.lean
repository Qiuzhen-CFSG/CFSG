module
public import Theory.ElementaryAbelian.AutomorphismCardEight
public import Theory.GroupTheory.CardFourAutomorphismStabilizer
public import Theory.GroupTheory.NormalCenterQuotient
public import Theory.GroupTheory.ElementaryEightPlaneOrder24

/-!
A subgroup of the automorphism group of an elementary group of order eight
is a full plane stabilizer if its restriction to a four-element subgroup
has image of order six and has nontrivial kernel. The conclusion is that
the automorphism subgroup has order twenty-four.

The restriction kernel consists of involutions. Its order divides the
available factor in the automorphism-group order 168, leaving orders two
and four. An order-two normal kernel is central; its nonzero displacement
would then be fixed by the whole restricted image. A point stabilizer on a
four-element group has order at most two, contradicting image order six.
The kernel consequently has order four. The literal restriction map and
its element formula are explicit, so no invariant-action instance is
silently replaced. This source-neutral recognition step supports the
neighbor-plane normalizer in Stellmacher (8.6)(c4).
-/

open scoped IsMulCommutative

public theorem elementaryEight_plane_card_twentyfour_of_full_restriction
    {U : Type*} [Group U] [Finite U] [IsElementaryAbelian 2 U]
    (hU : Nat.card U=8) (W : Subgroup U) (hW : Nat.card W=4)
    (J : Subgroup (MulAut U)) (restriction : J →* MulAut W)
    (hformula : ∀ j : J, ∀ w : W, (restriction j w : U)=(j:MulAut U) w)
    (hrange : Nat.card restriction.range=6) (hker : restriction.ker≠⊥) :
    Nat.card J=24 := by
  classical
  have hstable (j : J) (v : U) : v∈W ↔ (j:MulAut U) v∈W := by
    constructor
    · intro hv
      rw [← hformula j ⟨v,hv⟩]
      exact (restriction j ⟨v,hv⟩).property
    · intro hv
      have hh := (restriction j⁻¹ ⟨(j:MulAut U) v,hv⟩).property
      rw [hformula] at hh
      simpa using hh
  have hfix (r : J) (hr : r∈restriction.ker) (w : U) (hw : w∈W) :
      (r:MulAut U) w=w := by
    have hh := congrArg Subtype.val (MulEquiv.congr_fun (MonoidHom.mem_ker.mp hr) (⟨w,hw⟩:W))
    rw [hformula] at hh
    exact hh
  have hindex : W.index=2 := by
    have hh := W.index_mul_card
    rw [hW,hU] at hh
    omega
  have hdelta (r : J) (hr : r∈restriction.ker) (v : U) : v⁻¹*(r:MulAut U) v∈W := by
    rw [W.mul_mem_iff_of_index_two hindex,Subgroup.inv_mem_iff]
    exact hstable r v
  have hinv (v : U) : v⁻¹=v := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 U) v
  have hsquare (r : restriction.ker) : r^2=1 := by
    apply Subtype.ext
    apply Subtype.ext
    ext v
    have hh := hfix r r.property _ (hdelta r r.property v)
    change (r.val:MulAut U) (v⁻¹*(r.val:MulAut U) v)=v⁻¹*(r.val:MulAut U) v at hh
    simp only [map_mul,hinv] at hh
    change (r.val:MulAut U) ((r.val:MulAut U) v)=v
    apply mul_left_cancel (a := (r.val:MulAut U) v)
    exact hh.trans (mul_comm _ _)
  have htwo : IsPGroup 2 restriction.ker := fun r => ⟨1,by simpa using hsquare r⟩
  obtain ⟨n,hn⟩ := htwo.exists_card_eq
  have hproduct : Nat.card J=6*Nat.card restriction.ker := by
    rw [← restriction.ker.index_mul_card,Subgroup.index_ker,hrange]
  have hdiv : 6*2^n ∣ 168 := by
    have hh := J.card_subgroup_dvd_card
    rw [hproduct,hn,card_mulAut_of_elementary_eight U hU] at hh
    exact hh
  have hbound : n≤4 := by
    have hh := Nat.le_of_dvd (by decide : 0<168) hdiv
    by_contra! hbig
    have hp : 32≤2^n := by
      calc 32=2^5 := by decide
           _≤2^n := Nat.pow_le_pow_right (by decide) hbig
    nlinarith
  have hnotTwo : Nat.card restriction.ker≠2 := by
    intro hcardKernel
    have hcenter : restriction.ker≤Subgroup.center J :=
      Subgroup.central_of_normal_card_two restriction.ker hcardKernel
    obtain ⟨r,hrne⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hker
    have hrAut : (r.val:MulAut U)≠1 := by
      intro heq
      exact hrne (Subtype.ext (Subtype.ext heq))
    obtain ⟨v,hv⟩ : ∃ v:U,(r.val:MulAut U) v≠v := by
      by_contra! hh
      exact hrAut (MulEquiv.ext hh)
    let d : W := ⟨v⁻¹*(r.val:MulAut U) v,hdelta r r.property v⟩
    have hdne : d≠1 := by
      intro heq
      have hh := congrArg Subtype.val heq
      exact hv (inv_mul_eq_one.mp hh).symm
    have hvW : v∉W := fun hh => hv (hfix r r.property v hh)
    have hdfixed (j : J) : restriction j d=d := by
      have hjv : (j:MulAut U) v∉W := fun hh => hvW ((hstable j v).mpr hh)
      have hxW : v⁻¹*(j:MulAut U) v∈W := by
        rw [W.mul_mem_iff_of_index_two hindex,Subgroup.inv_mem_iff]
        exact iff_of_false hvW hjv
      have hrj : (r.val:MulAut U) ((j:MulAut U) v)=
          (r.val:MulAut U) v*(v⁻¹*(j:MulAut U) v) := by
        have hh := congrArg (fun x => (r.val:MulAut U) x)
          (mul_inv_cancel_left v ((j:MulAut U) v)).symm
        simpa only [map_mul,hfix r r.property _ hxW] using hh
      have hjr : (j:MulAut U) ((r.val:MulAut U) v)=
          (r.val:MulAut U) ((j:MulAut U) v) := by
        have hh := Subgroup.mem_center_iff.mp (hcenter r.property) j
        exact congrArg (fun x : J => (x:MulAut U) v) hh
      apply Subtype.ext
      rw [hformula]
      change (j:MulAut U) (v⁻¹*(r.val:MulAut U) v)=v⁻¹*(r.val:MulAut U) v
      rw [map_mul,map_inv,hjr,hrj]
      calc
        ((j:MulAut U) v)⁻¹*((r.val:MulAut U) v*(v⁻¹*(j:MulAut U) v))
            = (v⁻¹*(r.val:MulAut U) v)*(((j:MulAut U) v)⁻¹*(j:MulAut U) v) := by ac_rfl
        _ = v⁻¹*(r.val:MulAut U) v := by simp
    have hsmall := card_mulAut_subgroup_le_two_of_fixed_point hW d hdne restriction.range (by
      rintro f ⟨j,rfl⟩
      exact hdfixed j)
    omega
  interval_cases n
  · simp only [pow_zero] at hn
    exact (hker (Subgroup.card_eq_one.mp hn)).elim
  · simp only [pow_one] at hn
    exact (hnotTwo hn).elim
  · rw [hproduct, hn]
    norm_num
  · norm_num at hdiv
  · norm_num at hdiv

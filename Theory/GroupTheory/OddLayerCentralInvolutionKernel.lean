module

public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.Quotient
public import Mathlib.GroupTheory.FixedPointFree

/-!
# Central involutions acting on an odd layer

If every nontrivial normal subgroup of an actor has full commutator with a
nontrivial normal odd `p`-subgroup, the actor has at most one central involution.
The image of the odd layer modulo its Frattini subgroup is nontrivial and
elementary abelian. Coprime fixed-point decomposition and fixed-point-free
inversion force each central involution to invert this image. Two distinct
ones would have a nontrivial central involution product acting both trivially
and by inversion, contradicting the odd order of the image.
-/

open scoped IsMulCommutative Pointwise commutatorElement

namespace Theory.GroupTheory

@[expose] public section

private theorem inverts_of_full_commutator
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (V : Subgroup G) [V.Normal] (hV : IsElementaryAbelian p V)
    (a : G) (ha : a ^ 2 = 1) (hcomm : ⁅V, Subgroup.zpowers a⁆ = V) :
    ∀ v : V, MulAut.conjNormal a v = v⁻¹ := by
  let T := Subgroup.zpowers a
  have hT : IsPGroup 2 T := by
    let _ := IsElementaryAbelian.zpowers_of_pow_eq_one ha
    exact IsElementaryAbelian.isPGroup 2 T
  have hfixed := fixedPointSubgroup_eq_bot_of_commutator_eq_self V T hpodd hV hT
    (Subgroup.le_normalizer_of_normal) hcomm
  have hfree : MonoidHom.FixedPointFree (MulAut.conjNormal a : MulAut V) := by
    intro v hv
    have hac : a ∈ Subgroup.centralizer ({(v : G)} : Set G) := by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hv)
    have hTc : T ≤ Subgroup.centralizer ({(v : G)} : Set G) :=
      Subgroup.zpowers_le.mpr hac
    have hvfixed : v ∈ fixedPointSubgroup T V := by
      intro t
      apply Subtype.ext
      change (t : G) * (v : G) * (t : G)⁻¹ = v
      rw [Subgroup.mem_centralizer_singleton_iff.mp (hTc t.property)]
      simp
    simpa [hfixed] using hvfixed
  have hinvol : Function.Involutive (MulAut.conjNormal a : MulAut V) := by
    intro v
    let φ : G →* MulAut V := MulAut.conjNormal
    change (φ a * φ a) v = v
    rw [← map_mul, ← pow_two, ha, map_one]
    rfl
  exact congrFun (hfree.coe_eq_inv_of_involutive hinvol)

/-- The full-commutator criterion on an odd normal layer excludes distinct central
involutions of a `2`-subgroup. -/
theorem central_involutions_eq_of_odd_pgroup_commutator
    {X : Type*} [Group X] [Finite X]
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (R A : Subgroup X) (hRn : R.Normal) (hRp : IsPGroup p R)
    (hRne : R ≠ ⊥) (_hA2 : IsPGroup 2 A)
    (hcomm : ∀ J : Subgroup X, J ≤ A → (J.subgroupOf A).Normal →
      J ≠ ⊥ → ⁅R, J⁆ = R)
    (a b : A) (haZ : a ∈ Subgroup.center A) (hbZ : b ∈ Subgroup.center A)
    (ha : IsInvolution a) (hb : IsInvolution b) : a = b := by
  let _ : R.Normal := hRn
  let N := (frattini R).map R.subtype
  let _ : N.Normal := ConjAct.normal_of_characteristic_of_normal
  let q : X →* X ⧸ N := QuotientGroup.mk' N
  let V := R.map q
  let _ : V.Normal := hRn.map q (QuotientGroup.mk'_surjective N)
  have hVelem : IsElementaryAbelian p V := by
    rw [show V = (q.comp R.subtype).range from
      image_of_subgroup_eq_range_comp_subtype R q]
    apply elementaryAbelian_range_of_frattini_le_ker _ hRp
    intro r hr
    exact (QuotientGroup.eq_one_iff (N := N) (r : X)).mpr ⟨r, hr, rfl⟩
  have hVne : V ≠ ⊥ := by
    intro hbot
    have hRle : R ≤ N := by
      intro r hr
      have : q r ∈ V := ⟨r, hr, rfl⟩
      exact (QuotientGroup.eq_one_iff (N := N) r).mp
        (show q r = 1 from by simpa [hbot] using this)
    have hPhi : frattini R = ⊤ := by
      apply top_le_iff.mp
      intro r _
      obtain ⟨s, hs, heq⟩ := hRle r.property
      exact (Subtype.ext heq : s = r) ▸ hs
    have htriv : (⊥ : Subgroup R) = ⊤ :=
      frattini_nongenerating (by simpa using hPhi)
    apply hRne
    apply eq_bot_iff.mpr
    intro r hr
    have : (⟨r, hr⟩ : R) ∈ (⊥ : Subgroup R) := by rw [htriv]; trivial
    exact congrArg Subtype.val (Subgroup.mem_bot.mp this)
  have hfull (s : A) (hsZ : s ∈ Subgroup.center A) (hs : s ≠ 1) :
      ⁅V, Subgroup.zpowers (q (s : X))⁆ = V := by
    have hle : Subgroup.zpowers (s : X) ≤ A := Subgroup.zpowers_le.mpr s.property
    have hn : ((Subgroup.zpowers (s : X)).subgroupOf A).Normal := by
      apply Subgroup.normal_subgroupOf_iff hle |>.mpr
      intro x t hx ht
      have hst : (s : X) * t = t * (s : X) :=
        congrArg Subtype.val ((Subgroup.mem_center_iff.mp hsZ) ⟨t, ht⟩).symm
      have hxcentral : x ∈ Subgroup.centralizer ({t} : Set X) :=
        (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hst)) hx
      rw [← Subgroup.mem_centralizer_singleton_iff.mp hxcentral, mul_inv_cancel_right]
      exact hx
    have hne : Subgroup.zpowers (s : X) ≠ ⊥ := by
      intro heq
      apply hs
      apply Subtype.ext
      have := Subgroup.mem_zpowers (s : X)
      simpa [heq] using this
    have := congrArg (Subgroup.map q) (hcomm _ hle hn hne)
    simpa [V, Subgroup.map_commutator, MonoidHom.map_zpowers] using this
  let φ : A →* MulAut V := (MulAut.conjNormal : X ⧸ N →* MulAut V).comp
    (q.comp A.subtype)
  have hinvert (s : A) (hsZ : s ∈ Subgroup.center A) (hs : IsInvolution s) :
      ∀ v : V, φ s v = v⁻¹ := by
    apply inverts_of_full_commutator hpodd V hVelem (q (s : X))
    · have hs2 := congrArg (q.comp A.subtype) hs.2
      simpa using hs2
    · exact hfull s hsZ hs.1
  by_contra hab
  have habcomm : Commute a b := (Subgroup.mem_center_iff.mp haZ b).symm
  have hab2 : (a * b) ^ 2 = 1 := by
    rw [habcomm.mul_pow, ha.2, hb.2, one_mul]
  have habne : a * b ≠ 1 := by
    intro heq
    apply hab
    exact (eq_inv_of_mul_eq_one_left heq).trans
      ((eq_inv_of_mul_eq_one_left (by simpa [pow_two] using hb.2)).symm)
  have habZ := (Subgroup.center A).mul_mem haZ hbZ
  have hidentity (v : V) : φ (a * b) v = v := by
    rw [map_mul]
    change φ a (φ b v) = v
    rw [hinvert b hbZ hb, map_inv, hinvert a haZ ha, inv_inv]
  have hfixed := inverts_of_full_commutator hpodd V hVelem (q ((a * b : A) : X))
    (by simpa using congrArg (q.comp A.subtype) hab2) (hfull (a * b) habZ habne)
  apply hVne
  apply eq_bot_iff.mpr
  intro v hv
  have heq : (⟨v, hv⟩ : V) = (⟨v, hv⟩ : V)⁻¹ :=
    (hidentity ⟨v, hv⟩).symm.trans (hfixed ⟨v, hv⟩)
  have hv2 : v ^ 2 = 1 := by
    have heq' : v = v⁻¹ := congrArg Subtype.val heq
    calc
      v ^ 2 = v⁻¹ * v := by rw [pow_two]; exact congrArg (· * v) heq'
      _ = 1 := inv_mul_cancel v
  exact odd_pGroup_element_eq_one_of_sq_eq_one hpodd V
    (by let _ := hVelem; exact IsElementaryAbelian.isPGroup p V) v hv hv2


end

end Theory.GroupTheory

module

public import Theory.GroupTheory.SpecificGroups.CyclicInvertedDihedral
public import Mathlib.GroupTheory.FixedPointFree
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Two commuting dihedral groups of order six

Two commuting involutions acting on a nonabelian group of order 27 yield a
subgroup isomorphic to `DihedralGroup 3 × DihedralGroup 3` under the centralizer
and inversion hypotheses below. The fixed subgroup of the first involution
contains an element of order three, and the second involution inverts it.
The resulting dihedral groups commute and have trivial intersection because
their centers are trivial.

This is the dihedral-square construction in Wong (1964), printed pp. 109–110;
the fixed-point-free involution theorem replaces the invariant-plane argument.
-/

private def conjugationEnd {G : Type*} [Group G] (P : Subgroup G) (s : G)
    (hs : ∀ x ∈ P, s * x * s⁻¹ ∈ P) : P →* P where
  toFun x := ⟨s * x * s⁻¹, hs x x.property⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

private theorem conjugationEnd_involutive {G : Type*} [Group G] (P : Subgroup G)
    (s : G) (hs : ∀ x ∈ P, s * x * s⁻¹ ∈ P) (hs2 : s ^ 2 = 1) :
    Function.Involutive (conjugationEnd P s hs) := by
  intro x
  apply Subtype.ext
  change s * (s * (x : G) * s⁻¹) * s⁻¹ = x
  have hss : s * s = 1 := by simpa [pow_two] using hs2
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  rw [hsi]
  calc
    s * (s * (x : G) * s) * s = (s * s) * (x : G) * (s * s) := by group
    _ = x := by simp [hss]

private theorem exists_second_rotation {G : Type*} [Group G] [Finite G]
    (P : Subgroup G) (t m : G)
    (hP : Nat.card P = 27) (hnonabelian : ¬ IsMulCommutative P)
    (ht : t ^ 2 = 1) (hm : m ^ 2 = 1)
    (htP : t ∈ Subgroup.normalizer (P : Set G))
    (hmP : m ∈ Subgroup.normalizer (P : Set G))
    (htm : Commute t m)
    (hC : Nat.card (Subgroup.centralizer ({m} : Set G)) = 48)
    (hfixed : ∀ x ∈ P, Commute t x → Commute m x → x = 1) :
    ∃ l ∈ P, orderOf l = 3 ∧ Commute m l ∧ t * l * t⁻¹ = l⁻¹ := by
  have hmstable : ∀ x ∈ P, m * x * m⁻¹ ∈ P :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp hmP x).mp hx
  let f := conjugationEnd P m hmstable
  have hf2 : Function.Involutive f := conjugationEnd_involutive P m hmstable hm
  have hnfixed : ¬ MonoidHom.FixedPointFree f := by
    intro h
    apply hnonabelian
    exact ⟨⟨fun x y => (h.commute_all_of_involutive hf2 x y).eq⟩⟩
  obtain ⟨x, hx⟩ := Classical.not_forall.mp hnfixed
  have hxeq : f x = x := Classical.byContradiction (fun h => hx (fun he => (h he).elim))
  have hxne : x ≠ 1 := fun h => hx (fun _ => h)
  have hmx : Commute m (x : G) := by
    have h := congrArg Subtype.val hxeq
    change m * (x : G) * m⁻¹ = x at h
    exact mul_inv_eq_iff_eq_mul.mp h
  let Q : Subgroup G := P ⊓ Subgroup.centralizer ({m} : Set G)
  have hxQ : (x : G) ∈ Q := ⟨x.property,
    Subgroup.mem_centralizer_singleton_iff.mpr hmx.symm.eq⟩
  have htstable : ∀ y ∈ Q, t * y * t⁻¹ ∈ Q := by
    intro y hy
    refine ⟨(Subgroup.mem_normalizer_iff.mp htP y).mp hy.1, ?_⟩
    have hmy : Commute m y :=
      (Subgroup.mem_centralizer_singleton_iff.mp hy.2).symm
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((htm.symm.mul_right hmy).mul_right htm.symm.inv_right).symm.eq
  let g := conjugationEnd Q t htstable
  have hgfixed : MonoidHom.FixedPointFree g := by
    intro y hy
    apply Subtype.ext
    apply hfixed y y.property.1
    · have h := congrArg Subtype.val hy
      change t * (y : G) * t⁻¹ = y at h
      exact mul_inv_eq_iff_eq_mul.mp h
    · exact (Subgroup.mem_centralizer_singleton_iff.mp y.property.2).symm
  have hinv := hgfixed.coe_eq_inv_of_involutive
    (conjugationEnd_involutive Q t htstable ht)
  have horderP : orderOf (x : G) ∣ 27 := by
    rw [Subgroup.orderOf_coe, ← hP]
    exact orderOf_dvd_natCard x
  have horderC : orderOf (x : G) ∣ 48 := by
    rw [← hC, ← Subgroup.orderOf_mk (x : G) hxQ.2]
    exact orderOf_dvd_natCard (⟨x, hxQ.2⟩ : Subgroup.centralizer ({m} : Set G))
  have horder : orderOf (x : G) = 3 := by
    have hd : orderOf (x : G) ∣ 3 := Nat.dvd_gcd horderP horderC
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with h | h
    · exact False.elim (hxne (Subtype.ext (orderOf_eq_one_iff.mp h)))
    · exact h
  refine ⟨x, x.property, horder, hmx, ?_⟩
  exact congrArg Subtype.val (congrFun hinv (⟨x, hxQ⟩ : Q))

private theorem dihedral_of_orders {G : Type*} [Group G] [Finite G]
    (c s : G) (hc : orderOf c = 3) (hs : orderOf s = 2)
    (hinv : s * c * s⁻¹ = c⁻¹) :
    Nonempty ((↥(Subgroup.zpowers c ⊔ Subgroup.zpowers s : Subgroup G)) ≃* DihedralGroup 3) := by
  have hout : s ∉ Subgroup.zpowers c := by
    intro h
    have hd := orderOf_dvd_of_mem_zpowers h
    rw [hc, hs] at hd
    norm_num at hd
  have hi : ∀ x ∈ Subgroup.zpowers c, s * x * s⁻¹ = x⁻¹ := by
    intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← conj_zpow, hinv, inv_zpow]
  have h := Subgroup.nonempty_mulEquiv_dihedralGroup_of_cyclic_inverted
    (Subgroup.zpowers c) s inferInstance (hs ▸ pow_orderOf_eq_one s) hout hi
  have hcard : Nat.card (Subgroup.zpowers c) = 3 := (Nat.card_zpowers c).trans hc
  rw [hcard] at h
  exact h

private theorem commute_generated_pairs {G : Type*} [Group G]
    (a b c d : G) (hac : Commute a c) (had : Commute a d)
    (hbc : Commute b c) (hbd : Commute b d) :
    ∀ (x : ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G))
      (y : ↥(Subgroup.zpowers c ⊔ Subgroup.zpowers d : Subgroup G)), Commute (x : G) (y : G) := by
  have hAc : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤
      Subgroup.centralizer ({c} : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hac.eq))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hbc.eq))
  have hAd : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤
      Subgroup.centralizer ({d} : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr had.eq))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hbd.eq))
  have hBA : Subgroup.zpowers c ⊔ Subgroup.zpowers d ≤
      Subgroup.centralizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) : Set G) := by
    apply sup_le <;> apply Subgroup.zpowers_le.mpr
    · intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mp (hAc hx)
    · intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mp (hAd hx)
  intro x y
  exact hBA y.property x x.property

/-- A nonabelian subgroup of order 27 with the specified two involution actions
contains the rotations of a dihedral square containing `t`, `m`, and `r`. -/
public theorem Subgroup.exists_dihedral_three_square_of_nonabelian_three_group
    {G : Type*} [Group G] [Finite G] (P : Subgroup G) (t m r : G)
    (hP : Nat.card P = 27) (hnonabelian : ¬ IsMulCommutative P)
    (ht : orderOf t = 2) (hm : orderOf m = 2) (hr : orderOf r = 3)
    (_hrP : r ∈ P) (hcentral : P ≤ Subgroup.centralizer ({r} : Set G))
    (htP : t ∈ Subgroup.normalizer (P : Set G))
    (hmP : m ∈ Subgroup.normalizer (P : Set G))
    (htm : Commute t m) (htr : Commute t r)
    (hmr : m * r * m⁻¹ = r⁻¹)
    (hC : Nat.card (Subgroup.centralizer ({m} : Set G)) = 48)
    (hfixed : ∀ x ∈ P, Commute t x → Commute m x → x = 1) :
    ∃ M : Subgroup G, Subgroup.closure ({t, m, r} : Set G) ≤ M ∧
      Nonempty (M ≃* (DihedralGroup 3 × DihedralGroup 3)) := by
  obtain ⟨l, hlP, hl, hml, htl⟩ := exists_second_rotation P t m hP hnonabelian
    (ht ▸ pow_orderOf_eq_one t) (hm ▸ pow_orderOf_eq_one m) htP hmP htm hC hfixed
  let A : Subgroup G := Subgroup.zpowers r ⊔ Subgroup.zpowers m
  let B : Subgroup G := Subgroup.zpowers l ⊔ Subgroup.zpowers t
  obtain ⟨eA⟩ := dihedral_of_orders r m hr hm hmr
  obtain ⟨eB⟩ := dihedral_of_orders l t hl ht htl
  have hrl : Commute r l := (Subgroup.mem_centralizer_singleton_iff.mp (hcentral hlP)).symm
  have hcomm : ∀ (a : A) (b : B), Commute (A.subtype a) (B.subtype b) :=
    commute_generated_pairs r m l t hrl htr.symm hml htm.symm
  have hdisj : Disjoint A B := by
    apply Subgroup.disjoint_def.mpr
    intro x hxA hxB
    let a : A := ⟨x, hxA⟩
    have ha : a ∈ Subgroup.center A := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hcomm y ⟨x, hxB⟩).eq
    have hea : eA a ∈ Subgroup.center (DihedralGroup 3) := by
      rw [Subgroup.mem_center_iff]
      intro d
      obtain ⟨y, rfl⟩ := eA.surjective d
      simpa only [map_mul] using congrArg eA (Subgroup.mem_center_iff.mp ha y)
    rw [DihedralGroup.center_eq_bot_of_odd_ne_one (by decide) (by decide)] at hea
    have he : eA a = 1 := hea
    have ha1 : a = 1 := eA.injective (he.trans eA.map_one.symm)
    exact congrArg Subtype.val ha1
  let f : A × B →* G := A.subtype.noncommCoprod B.subtype hcomm
  have hfinj : Function.Injective f := by
    apply (MonoidHom.noncommCoprod_injective A.subtype B.subtype hcomm).mpr
    exact ⟨Subtype.coe_injective, Subtype.coe_injective,
      by simpa only [Subgroup.subtype_range] using hdisj⟩
  have hequiv : Nonempty (f.range ≃* (DihedralGroup 3 × DihedralGroup 3)) := by
    refine ⟨(MulEquiv.ofBijective f.rangeRestrict
      ⟨?_, f.rangeRestrict_surjective⟩).symm.trans (eA.prodCongr eB)⟩
    intro x y h
    exact hfinj (congrArg Subtype.val h)
  refine ⟨f.range, ?_, hequiv⟩
  change Subgroup.closure ({t, m, r} : Set G) ≤
    (A.subtype.noncommCoprod B.subtype hcomm).range
  rw [MonoidHom.noncommCoprod_range, Subgroup.subtype_range, Subgroup.subtype_range]
  apply (Subgroup.closure_le _).mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact Subgroup.mem_sup_right (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))

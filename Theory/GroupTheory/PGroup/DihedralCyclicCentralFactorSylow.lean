module

public import Theory.GroupTheory.PGroup.DihedralCentralFactor
public import Theory.GroupTheory.InvolutionTransfer
public import Theory.GroupTheory.CyclicSylowCenterNormalizer
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.SylowCentralizerNonfusion
public import Theory.GroupTheory.PGroup.NormalizedSylowConjugation
public import Theory.GroupTheory.PGroup.TrivialImage
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Theory.GroupTheory.QuaternionGenerated
public import Theory.GroupTheory.SpecificGroups.QuaternionEightInvolution

/-!
# Cyclic centralizers of dihedral central factors in simple Sylow groups

The intrinsic central-factor reduction identifies the cyclic centralizer with
the Sylow center. Fourth powers define a homomorphism into that center.
Fusion between central elements is controlled by the Sylow normalizer, which
fixes the cyclic center; transfer therefore kills the fourth-power map.

The remaining central product with a cyclic four-group has a quaternion
subgroup of index two. Its central involution is the common nontrivial square.
Sylow conjugacy in an involution centralizer prevents that involution from
fusing with any other Sylow involution, contradicting involution transfer.

Source: the cyclic branch of MacWilliams's theorem cited by Janko–Thompson,
Math. Z. 113 (1970), 1.2, printed pp.385–386, reference [12] on p.397.
The fusion arguments below use only elementary Sylow conjugacy and transfer.
-/

open Subgroup

namespace Sylow

private theorem cyclic_center_fusion_fixed
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    [IsCyclic (center S)] (x y : S) (hx : x ∈ center S) (hy : y ∈ center S)
    (hxy : IsConj (x : G) (y : G)) : y = x := by
  let Z := (center S).map (S : Subgroup G).subtype
  let e := (center S).equivMapOfInjective (S : Subgroup G).subtype
    (S : Subgroup G).subtype_injective
  let : IsCyclic Z := e.isCyclic.mp inferInstance
  have hSZ : (S : Subgroup G) ≤ centralizer (Z : Set G) := by
    intro s hs z hz
    obtain ⟨z, hz, rfl⟩ := hz
    exact (congrArg Subtype.val (mem_center_iff.mp hz ⟨s, hs⟩)).symm
  have hN := (normalizer_le_normalizer_characteristic_image
    (S : Subgroup G) (center S)).trans
    (normalizer_le_centralizer_of_cyclic_sylow_center S Z (map_subtype_le _) hSZ)
  apply Subtype.ext
  apply S.eq_of_isConj_of_normalizer_le_centralizer (x : G) (y : G) ?_ ?_ ?_ hxy
  · intro s hs
    exact congrArg Subtype.val (mem_center_iff.mp hx ⟨s, hs⟩)
  · intro s hs
    exact congrArg Subtype.val (mem_center_iff.mp hy ⟨s, hs⟩)
  · intro g hg
    exact mem_centralizer_singleton_iff.mpr
      ((hN hg) (x : G) (mem_map_of_mem (S : Subgroup G).subtype hx)).symm

private theorem dihedral_fourth_power
    {P : Type*} [Group P] (D : Subgroup P) (e : D ≃* DihedralGroup 4)
    (d : D) : (d : P) ^ 4 = 1 := by
  have hd : d ^ 4 = 1 := by
    apply e.injective
    simp only [map_pow, map_one]
    exact (by decide : ∀ a : DihedralGroup 4, a ^ 4 = 1) (e d)
  exact congrArg Subtype.val hd

private theorem central_factor_decomposition
    {P : Type*} [Group P] (D : Subgroup P)
    (hgen : D ⊔ center P = ⊤) (x : P) :
    ∃ d : D, ∃ c : center P, (d : P) * c = x := by
  obtain ⟨d, hd, c, hc, hdc⟩ := mem_sup_of_normal_right.mp
    (show x ∈ D ⊔ center P by rw [hgen]; trivial)
  exact ⟨⟨d, hd⟩, ⟨c, hc⟩, hdc⟩

private theorem fourth_power_central_factor
    {P : Type*} [Group P] (D : Subgroup P) (e : D ≃* DihedralGroup 4)
    (d : D) (c : center P) : ((d : P) * c) ^ 4 = (c : P) ^ 4 := by
  rw [(show Commute (d : P) (c : P) from mem_center_iff.mp c.property d).mul_pow,
    dihedral_fourth_power D e, one_mul]

private theorem fourth_power_central_factor_mul
    {P : Type*} [Group P] (D : Subgroup P) (e : D ≃* DihedralGroup 4)
    (hgen : D ⊔ center P = ⊤) (x y : P) : (x * y) ^ 4 = x ^ 4 * y ^ 4 := by
  obtain ⟨d, c, rfl⟩ := central_factor_decomposition D hgen x
  obtain ⟨d', c', rfl⟩ := central_factor_decomposition D hgen y
  have he : ((d : P) * c) * ((d' : P) * c') =
      ((d * d' : D) : P) * ((c * c' : center P) : P) := by
    change ((d : P) * c) * ((d' : P) * c') = (d : P) * d' * ((c : P) * c')
    rw [mul_assoc, ← mul_assoc (c : P), ← mem_center_iff.mp c.property (d' : P)]
    simp only [mul_assoc]
  rw [he, fourth_power_central_factor D e, fourth_power_central_factor D e,
    fourth_power_central_factor D e]
  exact (show Commute (c : P) (c' : P) from mem_center_iff.mp c'.property c).mul_pow 4

/-- In the cyclic-centralizer branch, transfer forces every Sylow fourth power
to be trivial. This intermediate result needs only absence of normal index two. -/
public theorem pow_four_eq_one_of_dihedral_cyclic_central_factor
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (D : Subgroup S) (e : D ≃* DihedralGroup 4)
    (hgen : D ⊔ centralizer (D : Set S) = ⊤)
    [IsCyclic (centralizer (D : Set S))] (x : S) : x ^ 4 = 1 := by
  have hcenter := centralizer_eq_center_of_dihedral_factor_of_isCyclic D hgen
  have hgen' : D ⊔ center S = ⊤ := by rwa [hcenter] at hgen
  let : IsCyclic (center S) := hcenter ▸ inferInstanceAs
    (IsCyclic (centralizer (D : Set S)))
  have hc (y : S) : y ^ 4 ∈ center S := by
    obtain ⟨d, c, rfl⟩ := central_factor_decomposition D hgen' y
    rw [fourth_power_central_factor D e]
    exact (center S).pow_mem c.property 4
  let : CommGroup (center S) := IsCyclic.commGroup
  let f : S →* center S := {
    toFun := fun y => ⟨y ^ 4, hc y⟩
    map_one' := Subtype.ext (one_pow 4)
    map_mul' := fun a b => Subtype.ext (fourth_power_central_factor_mul D e hgen' a b) }
  have hf (a b : S) (hab : IsConj (a : G) (b : G)) : f a = f b := by
    apply Subtype.ext
    exact (cyclic_center_fusion_fixed S (a ^ 4) (b ^ 4) (hc a) (hc b)
      (by change IsConj ((a : G) ^ 4) ((b : G) ^ 4); exact hab.pow 4)).symm
  have ht := MonoidHom.eq_one_of_no_normal_index_prime hno
    (S.isPGroup'.to_subgroup (center S)) (MonoidHom.transfer f) (x : G)
  rw [f.transfer_apply_eq_pow_of_fusion_invariant hf] at ht
  have hone : f x = 1 := (S.isPGroup'.to_subgroup (center S)).powEquiv'
    S.not_dvd_index |>.injective (ht.trans (one_pow _).symm)
  exact congrArg Subtype.val hone

/-- Conjugate a central square root into the Sylow subgroup inside `C_G(z)`.
Its nontrivial square must be `z`, so the original conjugator also fixes `z`. -/
private theorem eq_of_isConj_of_central_square_root
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (z c : S) (hz : z ≠ 1) (hc : c ∈ center S) (hc2 : c ^ 2 = z)
    (hsquare : ∀ x : S, x ^ 2 = 1 ∨ x ^ 2 = z)
    (t : S) (hconj : IsConj (t : G) (z : G)) : t = z := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  let f := MulAut.conj g
  change f (t : G) = (z : G) at hg
  let C : Subgroup G := centralizer ({(z : G)} : Set G)
  have hzC : z ∈ center S := hc2 ▸ (center S).pow_mem hc 2
  have hSC : (S : Subgroup G) ≤ C := by
    intro s hs
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp hzC ⟨s, hs⟩))
  have hfC : f (c : G) ∈ C := by
    apply mem_centralizer_singleton_iff.mpr
    rw [← hg, ← map_mul, ← map_mul]
    exact congrArg f (congrArg Subtype.val (mem_center_iff.mp hc t)).symm
  let W := zpowers (f (c : G))
  have hWp : IsPGroup 2 W := by
    have hWmap : W = (zpowers c).map (f.toMonoidHom.comp (S : Subgroup G).subtype) := by
      rw [MonoidHom.map_zpowers]
      rfl
    rw [hWmap]
    exact (S.isPGroup'.to_subgroup (zpowers c)).map _
  obtain ⟨a, ha, hW⟩ := IsPGroup.exists_conj_le_sylow_of_normalized S C W
    (hSC.trans C.le_normalizer) hWp (zpowers_le.mpr hfC)
  let v : G := (MulAut.conj a) (f (c : G))
  have hvS : v ∈ (S : Subgroup G) := hW
    (mem_map_of_mem (MulAut.conj a).toMonoidHom (mem_zpowers _))
  have haZ : (MulAut.conj a) (z : G) = (z : G) := by
    change a * (z : G) * a⁻¹ = (z : G)
    rw [mem_centralizer_singleton_iff.mp ha]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  have hpow : v ^ 2 = (MulAut.conj a) (f (z : G)) := by
    change ((MulAut.conj a) (f (c : G))) ^ 2 = _
    rw [← map_pow, ← map_pow]
    congr 2
    exact congrArg Subtype.val hc2
  have hne : v ^ 2 ≠ 1 := by
    rw [hpow]
    intro h
    apply hz
    apply Subtype.ext
    exact f.injective ((MulAut.conj a).injective (h.trans (map_one _).symm) |>.trans
      (map_one _).symm)
  have he : v ^ 2 = (z : G) := by
    rcases hsquare ⟨v, hvS⟩ with h | h
    · exact (hne (congrArg Subtype.val h)).elim
    · exact congrArg Subtype.val h
  apply Subtype.ext
  apply f.injective
  apply (MulAut.conj a).injective
  calc
    (MulAut.conj a) (f (t : G)) = (z : G) := by rw [hg, haZ]
    _ = (MulAut.conj a) (f (z : G)) := he.symm.trans hpow

private theorem central_square_eq_one_or
    {P : Type*} [Group P] [Finite P] [IsCyclic (center P)]
    (z : P) (hzC : z ∈ center P) (hz2 : orderOf z = 2)
    (c : center P) (hc4 : (c : P) ^ 4 = 1) :
    (c : P) ^ 2 = 1 ∨ (c : P) ^ 2 = z := by
  by_cases h : (c : P) ^ 2 = 1
  · exact Or.inl h
  right
  have hsq : orderOf (c ^ 2) = 2 := orderOf_eq_prime
    (Subtype.ext (by simpa only [Subgroup.coe_pow, Subgroup.coe_one, ← pow_mul] using hc4))
    (fun he => h (congrArg Subtype.val he))
  exact congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two hsq
    (show orderOf (⟨z, hzC⟩ : center P) = 2 by simpa using hz2))

/-- If the center has order four, a rotation and a reflection times a central
generator generate a quaternion subgroup of index two. -/
private theorem quaternion_index_two
    {P : Type*} [Group P] [Finite P]
    (D : Subgroup P) (e : D ≃* DihedralGroup 4)
    (hgen : D ⊔ centralizer (D : Set P) = ⊤)
    [IsCyclic (centralizer (D : Set P))]
    (hfour : Nat.card (center P) = 4) (hexp : ∀ x : P, x ^ 4 = 1) :
    ∃ z c t : P, ∃ Q : Subgroup P,
      z ≠ 1 ∧ c ∈ center P ∧ c ^ 2 = z ∧
      (∀ x : P, x ^ 2 = 1 ∨ x ^ 2 = z) ∧
      orderOf t = 2 ∧ t ≠ z ∧ Q.index = 2 ∧
      (∀ u : P, u ∈ Q → orderOf u = 2 → u = z) := by
  have hcenter := centralizer_eq_center_of_dihedral_factor_of_isCyclic D hgen
  let : IsCyclic (center P) := hcenter ▸ inferInstanceAs
    (IsCyclic (centralizer (D : Set P)))
  let a : D := e.symm (DihedralGroup.r 1)
  let s : D := e.symm (DihedralGroup.sr 0)
  let z : P := (a : P) ^ 2
  have ha4 : orderOf (a : P) = 4 := by
    rw [Subgroup.orderOf_coe, ← e.orderOf_eq a]
    change orderOf (e (e.symm (DihedralGroup.r 1))) = 4
    rw [e.apply_symm_apply]
    exact DihedralGroup.orderOf_r_one
  have hz2 : orderOf z = 2 := by
    dsimp [z]
    rw [orderOf_pow, ha4]
    decide
  have hz1 : z ≠ 1 := by
    intro h
    simp [h] at hz2
  have hzC : z ∈ center P := by
    rw [← hcenter]
    intro d hd
    have hh : (⟨d, hd⟩ : D) * a ^ 2 = a ^ 2 * ⟨d, hd⟩ := by
      apply e.injective
      simp only [map_mul, map_pow, a, e.apply_symm_apply]
      exact (by decide : ∀ x : DihedralGroup 4,
        x * (DihedralGroup.r 1) ^ 2 = (DihedralGroup.r 1) ^ 2 * x) _
    exact congrArg Subtype.val hh
  obtain ⟨c, hc⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := center P)
  rw [hfour] at hc
  have hc2 : (c : P) ^ 2 = z := by
    rcases central_square_eq_one_or z hzC hz2 c (hexp c) with h | h
    · have hdiv := orderOf_dvd_of_pow_eq_one (show c ^ 2 = 1 from Subtype.ext h)
      rw [hc] at hdiv
      norm_num at hdiv
    · exact h
  have hs2 : orderOf (s : P) = 2 := by
    rw [Subgroup.orderOf_coe, ← e.orderOf_eq s]
    change orderOf (e (e.symm (DihedralGroup.sr 0))) = 2
    rw [e.apply_symm_apply]
    exact DihedralGroup.orderOf_sr _
  have hsz : (s : P) ≠ z := by
    intro h
    have hh := congrArg e (show s = a ^ 2 from Subtype.ext h)
    simp only [map_pow, a, s, e.apply_symm_apply] at hh
    exact (by decide : (DihedralGroup.sr 0 : DihedralGroup 4) ≠
      (DihedralGroup.r 1) ^ 2) hh
  have hsquare (x : P) : x ^ 2 = 1 ∨ x ^ 2 = z := by
    obtain ⟨d, hd, v, hv, rfl⟩ := mem_sup_of_normal_right.mp
      (show x ∈ D ⊔ center P by rw [← hcenter, hgen]; trivial)
    have hd2 : d ^ 2 = 1 ∨ d ^ 2 = z := by
      have hh := (by decide : ∀ x : DihedralGroup 4,
        x ^ 2 = 1 ∨ x ^ 2 = (DihedralGroup.r 1) ^ 2) (e ⟨d, hd⟩)
      rcases hh with h | h
      · left
        exact congrArg Subtype.val (show (⟨d, hd⟩ : D) ^ 2 = 1 from
          e.injective (by simpa only [map_pow, map_one] using h))
      · right
        exact congrArg Subtype.val (show (⟨d, hd⟩ : D) ^ 2 = a ^ 2 from
          e.injective (by simpa only [map_pow, a, e.apply_symm_apply] using h))
    rw [(show Commute d v from mem_center_iff.mp hv d).mul_pow]
    rcases hd2 with hd2 | hd2 <;>
      rcases central_square_eq_one_or z hzC hz2 ⟨v, hv⟩ (hexp v) with hv2 | hv2
    · exact Or.inl (by rw [hd2, hv2, one_mul])
    · exact Or.inr (by rw [hd2, hv2, one_mul])
    · exact Or.inr (by rw [hd2, hv2, mul_one])
    · exact Or.inl (by rw [hd2, hv2, ← pow_two, ← hz2, pow_orderOf_eq_one])
  let b : P := (s : P) * c
  have hb2 : b ^ 2 = (a : P) ^ 2 := by
    dsimp [b]
    rw [(show Commute (s : P) (c : P) from mem_center_iff.mp c.property s).mul_pow,
      (show (s : P) ^ 2 = 1 by rw [← hs2, pow_orderOf_eq_one]), one_mul, hc2]
  have hsinv : (s : P) * a * (s : P)⁻¹ = (a : P)⁻¹ := by
    have hh : s * a * s⁻¹ = a⁻¹ := by
      apply e.injective
      simp only [map_mul, map_inv, s, a, e.apply_symm_apply]
      decide
    exact congrArg Subtype.val hh
  have hbinv : b * a * b⁻¹ = (a : P)⁻¹ := by
    dsimp [b]
    rw [mul_inv_rev]
    calc
      (s : P) * c * a * ((c : P)⁻¹ * (s : P)⁻¹) =
          s * ((c : P) * a * (c : P)⁻¹) * (s : P)⁻¹ := by group
      _ = s * a * (s : P)⁻¹ := by
        rw [← mem_center_iff.mp c.property (a : P)]
        simp only [mul_assoc, mul_inv_cancel, mul_one]
      _ = (a : P)⁻¹ := hsinv
  have hbout : b ∉ zpowers (a : P) := by
    rintro ⟨i, hi⟩
    have hcomm : Commute b (a : P) := hi ▸ (Commute.refl (a : P)).zpow_left i
    have hfix : b * a * b⁻¹ = (a : P) := by
      rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
    have ha2 : (a : P) ^ 2 = 1 := by
      calc
        (a : P) ^ 2 = (a : P) * a := pow_two _
        _ = (a : P)⁻¹ * a := congrArg (· * (a : P)) (hfix.symm.trans hbinv)
        _ = 1 := inv_mul_cancel _
    exact hz1 ha2
  obtain ⟨hQcard, ⟨eQ⟩⟩ := QuaternionGroup.closure_equiv_of_relations
    (m := 2) (by decide) (a : P) b ha4 hb2 hbinv hbout
  let Q : Subgroup P := closure ({(a : P), b} : Set P)
  have hzQ : z ∈ Q := Q.pow_mem (subset_closure (by simp)) 2
  have hidx : Q.index = 2 := by
    have hcard := card_eq_four_mul_card_centralizer_of_dihedral_factor D e hgen
    rw [hcenter, hfour] at hcard
    have hh := Q.card_mul_index
    change Nat.card Q = 8 at hQcard
    rw [hQcard, hcard] at hh
    omega
  refine ⟨z, c, s, Q, hz1, c.property, hc2, hsquare, hs2, hsz, hidx, ?_⟩
  intro u hu hu2
  have heq := QuaternionGroup.eq_of_orderOf_eq_two
    (eQ ⟨u, hu⟩) (eQ ⟨z, hzQ⟩)
    ((eQ.orderOf_eq ⟨u, hu⟩).trans ((Subgroup.orderOf_coe ⟨u, hu⟩).symm.trans hu2))
    ((eQ.orderOf_eq ⟨z, hzQ⟩).trans ((Subgroup.orderOf_coe ⟨z, hzQ⟩).symm.trans hz2))
  exact congrArg Subtype.val (eQ.injective heq)

/-- A dihedral central factor with cyclic centralizer is the whole Sylow
two-subgroup whenever the ambient group has no normal subgroup of index two. -/
public theorem dihedral_factor_eq_top_of_cyclic_centralizer_of_no_normal_index_two
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (D : Subgroup S) (e : D ≃* DihedralGroup 4)
    (hgen : D ⊔ centralizer (D : Set S) = ⊤)
    [IsCyclic (centralizer (D : Set S))] : D = ⊤ := by
  have hcenter := centralizer_eq_center_of_dihedral_factor_of_isCyclic D hgen
  let : IsCyclic (center S) := hcenter ▸ inferInstanceAs
    (IsCyclic (centralizer (D : Set S)))
  have hexp := S.pow_four_eq_one_of_dihedral_cyclic_central_factor hno D e hgen
  obtain ⟨c, hc⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := center S)
  have hdiv : Nat.card (center S) ∣ 4 := by
    rw [← hc]
    exact orderOf_dvd_of_pow_eq_one (show c ^ 4 = 1 from Subtype.ext (hexp c))
  have hbound : 2 ≤ Nat.card (center S) := by
    have hh := card_le_of_le (inf_le_right :
      D ⊓ centralizer (D : Set S) ≤ centralizer (D : Set S))
    rwa [card_inf_centralizer_of_dihedral D e, hcenter] at hh
  have hcases : Nat.card (center S) = 2 ∨ Nat.card (center S) = 4 := by
    have hh := Nat.le_of_dvd (by decide : 0 < 4) hdiv
    interval_cases h : Nat.card (center S) <;> simp_all
  apply (dihedral_factor_eq_top_iff_card_centralizer D e hgen).mpr
  rw [hcenter]
  rcases hcases with htwo | hfour
  · exact htwo
  obtain ⟨z, c, t, Q, hz, hc, hc2, hsquare, ht, htz, hQ, hunique⟩ :=
    quaternion_index_two D e hgen hfour hexp
  obtain ⟨u, hconj, hu⟩ := S.exists_isConj_mem_of_index_two hno Q hQ t ht
  have hu2 : orderOf u = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    rw [← Subgroup.orderOf_coe u, ← hg]
    exact ((MulAut.conj g).orderOf_eq (t : G)).trans
      ((Subgroup.orderOf_coe t).trans ht)
  have huz : u = z := hunique u hu hu2
  have htz' : t = z := eq_of_isConj_of_central_square_root S z c hz hc hc2
    hsquare t (huz ▸ hconj)
  exact (htz htz').elim

/-- In a finite simple group, a dihedral central factor with cyclic centralizer
is the whole Sylow two-subgroup. The rank and normality assumptions of the
usual rank-two application are unnecessary for this cyclic branch. -/
public theorem dihedral_factor_eq_top_of_cyclic_centralizer
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G)
    (_hrank : ∀ A : Subgroup S, IsElementaryAbelian 2 A → Nat.card A < 8)
    (D : Subgroup S) [D.Normal] (e : D ≃* DihedralGroup 4)
    (hgen : D ⊔ centralizer (D : Set S) = ⊤)
    [IsCyclic (centralizer (D : Set S))] : D = ⊤ := by
  apply S.dihedral_factor_eq_top_of_cyclic_centralizer_of_no_normal_index_two
    (D := D) (e := e) (hgen := hgen)
  have hD : Nat.card D = 8 := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hlarge : 8 ≤ Nat.card G := by
    exact hD ▸ (D.card_le_card_group.trans (S : Subgroup G).card_le_card_group)
  intro N hN hi
  rcases hN.eq_bot_or_eq_top with hb | ht
  · have hc : Nat.card G = 2 := by simpa only [hb, index_bot] using hi
    omega
  · simp only [ht, index_top] at hi
    omega

end Sylow

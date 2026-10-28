module

public import BenderSuzuki.ZD.Recognition.Interfaces
public import Theory.GroupTheory.PGroup.NormalizerBarrier
public import Theory.GroupTheory.InvolutionOddProduct

/-!
# Conjugacy, Sylow containment and fusion for product disconnection

An even-order product of two distinguished involutions produces a central
involution in their dihedral group. It is itself a product of distinguished
involutions, so product disconnection forces its centralizer into `M`. This
proves the odd-product assertion and then single-class conjugacy. The
normalizer condition for two-groups supplies ambient Sylow subgroups in `M`.

A distinguished involution centralizing a subgroup permits correction of
fusion conjugators inside a target centralizer. Finally an odd number of
distinguished involutions in `M` gives a fixed point for a Sylow action,
proving two-centrality and hence the fusion conclusion. The odd cardinality
is an explicit remaining premise, to be discharged by the counting argument.

Source: GLS, Volume 4, Chapter 2, Lemmas 3.1(c–e), 3.2(a), 3.3(a), 4.1 and
4.2(a), printed pp.27–30, 33–34. The source obtains the odd cardinality in
Proposition 3.6(e). This module does not assume generation or minimality.
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
variable {G : Type*} [Group G] {Z : Set G} {M : Subgroup G}

private theorem reflection_mem (h : IsProductDisconnected Z M)
    {s t : G} (hs : s ∈ Z) (ht : t ∈ Z) (n : ℕ) : (s * t) ^ n * s ∈ Z := by
  have hsInv := (h.involutions s hs).inv_eq_self
  have htInv := (h.involutions t ht).inv_eq_self
  have hmove : s * (s * t)⁻¹ = (s * t) * s := by
    rw [mul_inv_rev, hsInv, htInv, mul_assoc]
  induction n using Nat.twoStepInduction with
  | zero => simpa using hs
  | one => simpa [MulAut.conj_apply, hsInv, pow_one] using h.invariant s t ht
  | more n hn _ =>
    have he : (s * t) ^ (n + 2) * s = MulAut.conj (s * t) ((s * t) ^ n * s) := by
      symm
      change (s * t) * ((s * t) ^ n * s) * (s * t)⁻¹ = _
      calc
        (s * t) * ((s * t) ^ n * s) * (s * t)⁻¹ = (s * t) * ((s * t) ^ n * (s * (s * t)⁻¹)) := by group
        _ = (s * t) * ((s * t) ^ n * ((s * t) * s)) := by rw [hmove]
        _ = (s * t) ^ (n + 2) * s := by rw [pow_succ, pow_succ']; group
    rw [he]
    exact h.invariant _ _ hn

variable [Finite G]

/-- GLS Lemma 3.2(a): the factors may lie on opposite sides of `M`, or
in the same outside right coset. Since `t` is an involution, `s * t ∈ M`
is exactly the assertion `s ∈ M t`. -/
public theorem productDisconnected_odd_orderOf_mul (h : IsProductDisconnected Z M)
    {s t : G} (hs : s ∈ Z) (ht : t ∈ Z) (htM : t ∉ M)
    (hsM : s ∈ M ∨ s * t ∈ M) : Odd (orderOf (s * t)) := by
  by_contra hn
  obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.mp hn
  let r := s * t
  have hrpos := orderOf_pos r
  have hnum : k * 2 = orderOf r := by dsimp [r]; omega
  have hk0 : k ≠ 0 := by omega
  have hklt : k < orderOf r := by omega
  let v := r ^ k
  have hv : IsInvolution v := by
    refine ⟨pow_ne_one_of_lt_orderOf hk0 hklt, ?_⟩
    change (r ^ k) ^ 2 = 1
    rw [← pow_mul, hnum, pow_orderOf_eq_one]
  have hsInv := (h.involutions s hs).inv_eq_self
  have htInv := (h.involutions t ht).inv_eq_self
  have hss : s * s = 1 := by simpa [pow_two] using (h.involutions s hs).sq_eq_one
  have ha : MulAut.conj s r = r⁻¹ := by
    change s * (s * t) * s⁻¹ = (s * t)⁻¹
    rw [mul_inv_rev, hsInv, htInv, ← mul_assoc s s t, hss, one_mul]
  have hb : MulAut.conj t r = r⁻¹ := by
    change t * (s * t) * t⁻¹ = (s * t)⁻¹
    have htt : t * t = 1 := by simpa [pow_two] using (h.involutions t ht).sq_eq_one
    simp [mul_inv_rev, hsInv, htInv, mul_assoc, htt]
  have hcs : Commute s v := by
    have he : MulAut.conj s v = v := by
      change MulAut.conj s (r ^ k) = v
      rw [map_pow, ha, inv_pow]
      exact hv.inv_eq_self
    exact mul_inv_eq_iff_eq_mul.mp he
  have hct : Commute t v := by
    have he : MulAut.conj t v = v := by
      change MulAut.conj t (r ^ k) = v
      rw [map_pow, hb, inv_pow]
      exact hv.inv_eq_self
    exact mul_inv_eq_iff_eq_mul.mp he
  have hvM : v ∈ M := by
    rcases hsM with hsM | hrM
    · exact mem_of_commute h hs hsM hcs
    · exact M.pow_mem hrM k
  have hvs : v * s ∈ Z := reflection_mem h hs ht k
  have hprod : (v * s) * s = v := by rw [mul_assoc, hss, mul_one]
  have hC : Subgroup.centralizer ({v} : Set G) ≤ M := by
    simpa only [hprod] using h.product_centralizer (v * s) hvs s hs
      (hprod.symm ▸ hv) (hprod.symm ▸ hvM)
  exact htM (hC (Subgroup.mem_centralizer_singleton_iff.mpr hct.eq))

/-- The distinguished involutions form one ambient conjugacy class (GLS 3.3(a)). -/
public theorem productDisconnected_isConj (h : IsProductDisconnected Z M) :
    ∀ x ∈ Z, ∀ z ∈ Z, IsConj x z := by
  have hcross {x z : G} (hx : x ∈ Z) (hz : z ∈ Z) (hxM : x ∈ M) (hzM : z ∉ M) :
      IsConj x z := isConj_of_involutions_odd_product x z
        (h.involutions x hx).sq_eq_one (h.involutions z hz).sq_eq_one
        (productDisconnected_odd_orderOf_mul h hx hz hzM (Or.inl hxM))
  obtain ⟨a, ha, haM⟩ := h.nonempty
  obtain ⟨b, hb, hbM⟩ := exists_not_mem h
  intro x hx z hz
  have hbase {y : G} (hy : y ∈ Z) : IsConj a y := by
    by_cases hyM : y ∈ M
    · exact (hcross ha hb haM hbM).trans (hcross hy hb hyM hbM).symm
    · exact hcross ha hy haM hyM
  exact (hbase hx).symm.trans (hbase hz)

/-- The distinguished involutions in `M` form one `M`-class (GLS 3.3(a)). -/
public theorem productDisconnected_conjugator_mem (h : IsProductDisconnected Z M)
    {x z : G} (hx : x ∈ Z) (hxM : x ∈ M) (hz : z ∈ Z) (hzM : z ∈ M) :
    ∃ g : M, (g : G) * x * (g : G)⁻¹ = z := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (productDisconnected_isConj h x hx z hz)
  have hgM : g ∈ M := (h.conjugate_mem_iff x hx hxM g).mp (by
    simpa only [MulAut.conj_apply, hg] using hzM)
  exact ⟨⟨g, hgM⟩, hg⟩

/-- Every distinguished involution in `M` lies in an ambient Sylow subgroup contained in `M`. -/
public theorem productDisconnected_exists_sylow_le (h : IsProductDisconnected Z M) {z : G} (hz : z ∈ Z) (hzM : z ∈ M) :
    ∃ S : Sylow 2 G, z ∈ S ∧ (S : Subgroup G) ≤ M := by
  obtain ⟨S, hS⟩ := (isPGroup_zpowers_of_involution (h.involutions z hz)).exists_le_sylow
  refine ⟨S, hS (Subgroup.mem_zpowers z), ?_⟩
  apply Subgroup.p_overgroup_le_of_normalizers_le S.isPGroup' hS
    ((Subgroup.zpowers_le).mpr hzM)
  intro W _ hW hWM
  exact normalizer_le h hWM ⟨z, hz, hW (Subgroup.mem_zpowers z)⟩

/-- A distinguished involution in `M` controls element fusion on any subgroup it centralizes. -/
public theorem productDisconnected_controlsFusionIn_of_centralizes (h : IsProductDisconnected Z M)
    {z : G} (hz : z ∈ Z) (hzM : z ∈ M) (P : Subgroup G)
    (hc : ∀ s ∈ P, Commute z s) : ControlsFusionIn M P := by
  apply ControlsFusionIn.of_conjugators
  intro x y hx hy hxy
  obtain ⟨g, hg⟩ := isConj_iff.mp hxy
  let C := Subgroup.centralizer ({y} : Set G)
  have hzC : z ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr (hc y hy).eq
  let zC : C := ⟨z, hzC⟩
  obtain ⟨Q, hQ⟩ := (isPGroup_zpowers_of_involution
    (IsInvolution.subtype (h.involutions z hz) hzC)).exists_le_sylow
  have hzQ : zC ∈ (Q : Subgroup C) := hQ (Subgroup.mem_zpowers zC)
  have hQM : (Q : Subgroup C).map C.subtype ≤ M := by
    apply Subgroup.p_overgroup_le_of_normalizers_le (Q.isPGroup'.map C.subtype)
      ((Subgroup.zpowers_le).mpr (Subgroup.mem_map_of_mem C.subtype hzQ))
      ((Subgroup.zpowers_le).mpr hzM)
    intro W _ hW hWM
    exact normalizer_le h hWM ⟨z, hz, hW (Subgroup.mem_zpowers z)⟩
  have hgzC : MulAut.conj g z ∈ C := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have he := congrArg (MulAut.conj g) (hc x hx).eq
    change MulAut.conj g x = y at hg
    simpa only [map_mul, hg] using he
  let gzC : C := ⟨MulAut.conj g z, hgzC⟩
  obtain ⟨R, hR⟩ := (isPGroup_zpowers_of_involution
    (IsInvolution.subtype (h.involutions _ (h.invariant g z hz)) hgzC)).exists_le_sylow
  obtain ⟨c, hcQ⟩ := MulAction.exists_smul_eq C R Q
  have hcMem : MulAut.conj c gzC ∈ (Q : Subgroup C) := by
    rw [← hcQ]
    exact Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom
      (hR (Subgroup.mem_zpowers gzC))
  have hcgM : (c : G) * g ∈ M := by
    apply (h.conjugate_mem_iff z hz hzM ((c : G) * g)).mp
    have hm := hQM (Subgroup.mem_map_of_mem C.subtype hcMem)
    change (c : G) * (g * z * g⁻¹) * (c : G)⁻¹ ∈ M at hm
    simpa only [MulAut.conj_apply, mul_inv_rev, mul_assoc] using hm
  refine ⟨⟨(c : G) * g, hcgM⟩, ?_⟩
  change ((c : G) * g) * x * ((c : G) * g)⁻¹ = y
  calc
    ((c : G) * g) * x * ((c : G) * g)⁻¹ = (c : G) * (g * x * g⁻¹) * (c : G)⁻¹ := by group
    _ = (c : G) * y * (c : G)⁻¹ := by rw [hg]
    _ = y := mul_inv_eq_iff_eq_mul.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp c.property)

/-- Two-centrality supplies an ambient Sylow subgroup in `M` on which `M` controls fusion. -/
public theorem productDisconnected_fusion_of_two_central (h : IsProductDisconnected Z M)
    (hcentral : ∀ z ∈ Z, ∃ S : Sylow 2 G,
      z ∈ S ∧ ∀ s : S, Commute z (s : G)) :
    ∃ S : Sylow 2 G, (S : Subgroup G) ≤ M ∧ ControlsFusionIn M (S : Subgroup G) := by
  obtain ⟨z, hz, hzM⟩ := h.nonempty
  obtain ⟨S, _, hS⟩ := hcentral z hz
  have hcomm : ∀ s ∈ (S : Subgroup G), Commute z s := fun s hs => hS ⟨s, hs⟩
  exact ⟨S, fun _ hs => mem_of_commute h hz hzM (hcomm _ hs),
    productDisconnected_controlsFusionIn_of_centralizes h hz hzM _ hcomm⟩

public theorem two_central_of_odd_card (h : IsProductDisconnected Z M)
    (hodd : Odd (Nat.card {z : G // z ∈ Z ∧ z ∈ M})) :
    ∀ z ∈ Z, ∃ S : Sylow 2 G, z ∈ S ∧ ∀ s : S, Commute z (s : G) := by
  obtain ⟨a, ha, haM⟩ := h.nonempty
  obtain ⟨S, _, hSM⟩ := productDisconnected_exists_sylow_le h ha haM
  let T := {z : G // z ∈ Z ∧ z ∈ M}
  let : MulAction S T := {
    smul s z := ⟨(s : G) * (z : G) * (s : G)⁻¹,
      by simpa only [MulAut.conj_apply] using h.invariant s z z.property.1,
      M.mul_mem (M.mul_mem (hSM s.property) z.property.2) (M.inv_mem (hSM s.property))⟩
    one_smul z := by
      apply Subtype.ext
      change (1 : G) * (z : G) * (1 : G)⁻¹ = (z : G)
      simp
    mul_smul s t z := by
      apply Subtype.ext
      change ((s : G) * (t : G)) * (z : G) * ((s : G) * (t : G))⁻¹ =
        (s : G) * ((t : G) * (z : G) * (t : G)⁻¹) * (s : G)⁻¹
      group }
  obtain ⟨w, hw⟩ := S.isPGroup'.nonempty_fixed_point_of_prime_not_dvd_card T
    hodd.not_two_dvd_nat
  have hwc : ∀ s : S, Commute (w : G) (s : G) := by
    intro s
    have he := congrArg Subtype.val (hw s)
    change (s : G) * (w : G) * (s : G)⁻¹ = (w : G) at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hwS : (w : G) ∈ S := by
    have hn : (w : G) ∈ Subgroup.normalizer (S : Set G) := by
      apply Subgroup.centralizer_le_normalizer
      intro s hs
      exact (hwc ⟨s, hs⟩).eq.symm
    have hm : (w : G) ∈ Subgroup.zpowers (w : G) ⊓ Subgroup.normalizer (S : Set G) :=
      ⟨Subgroup.mem_zpowers _, hn⟩
    rw [(isPGroup_zpowers_of_involution (h.involutions w w.property.1)).inf_normalizer_sylow S] at hm
    exact hm.2
  intro z hz
  obtain ⟨g, hg⟩ := isConj_iff.mp (productDisconnected_isConj h w w.property.1 z hz)
  refine ⟨g • S, ?_, ?_⟩
  · change z ∈ (S : Subgroup G).map (MulAut.conj g).toMonoidHom
    exact Subgroup.mem_map.mpr ⟨w, hwS, hg⟩
  · intro s
    obtain ⟨t, ht, he⟩ := Subgroup.mem_map.mp s.property
    have hct := (hwc ⟨t, ht⟩).map (MulAut.conj g).toMonoidHom
    change Commute (MulAut.conj g w) (MulAut.conj g t) at hct
    change MulAut.conj g w = z at hg
    change MulAut.conj g t = (s : G) at he
    rw [hg, he] at hct
    exact hct

end BenderSuzuki.ZD

module

public import Glauberman.SuzukiCharacterization.Hypotheses
public import Theory.Character.ClassFunction
public import BenderGlauberman.ClassFunction
public import Theory.GroupTheory.PGroup.MaximalIndex
public import Theory.GroupTheory.InvolutionOddProduct

/-!
# The commutator support used in character selection

This interface records condition (c') and the subsequent maximal-subgroup
choice: a central involution v, a maximal subgroup P₀ of P, and a linear
character with kernel P₀. The two-part condition is expressed using commuting
two- and odd-order factors, avoiding a choice of a primary-part function.
For the prime two, products of two involutions admit a direct dihedral
argument: fusion carries central Sylow elements to central Sylow elements.
The two-part inverted by the first involution consequently has square one;
an odd-product conjugacy then puts it in the Sylow center. Noncommutativity
makes that center proper. Enlarge it to a maximal subgroup and take the
sign character of the resulting quotient of order two. This constructs the
data from `Hypotheses` without the general-prime form of Proposition 2.2.

Source: Glauberman, *A Characterization of the Suzuki Groups* (1968),
Proposition 2.3 and the beginning of Section 4, pp. 81–82 and 88–89, saved in
`refs/original/n-group-global/odd-core-rank-two-source/`.
-/

namespace Glauberman.SuzukiCharacterization

/-- The support and linear-character choices preceding Lemma 4.1. -/
public structure CommutatorSupportData {G : Type*} [Group G] (P : Sylow 2 G) where
  v : P
  involution : orderOf v = 2
  central : v ∈ Subgroup.center P
  P₀ : Subgroup P
  maximal : IsCoatom P₀
  theta : ClassFunction P
  linear : IsLinearCharacter theta
  kernel : ∀ x : P, theta x = 1 ↔ x ∈ P₀
  support : ∀ g h : G, ∀ x : P, ∀ y : G,
    Commute (x : G) y → Nat.Coprime 2 (orderOf y) →
    (g * (v : G) * g⁻¹) * (h * (v : G) * h⁻¹)⁻¹ = (x : G) * y → x ∈ P₀

/-- The chosen linear character is nonprincipal because its kernel is proper. -/
public theorem CommutatorSupportData.theta_ne_one
    {G : Type*} [Group G] {P : Sylow 2 G} (s : CommutatorSupportData P) :
    s.theta ≠ 1 := by
  intro he
  apply s.maximal.1
  apply top_unique
  intro x _
  exact (s.kernel x).mp (by simp [he])

/-- The character difference vanishes on every relevant two-part. -/
public theorem CommutatorSupportData.difference_eq_zero
    {G : Type*} [Group G] {P : Sylow 2 G} (s : CommutatorSupportData P)
    (g h : G) (x : P) (y : G) (hxy : Commute (x : G) y)
    (hy : Nat.Coprime 2 (orderOf y))
    (he : (g * (s.v : G) * g⁻¹) * (h * (s.v : G) * h⁻¹)⁻¹ = (x : G) * y) :
    (s.theta - 1) x = 0 := by
  change s.theta x - 1 = 0
  rw [(s.kernel x).mpr (s.support g h x y hxy hy he), sub_self]

private theorem Hypotheses.central_of_isConj {G : Type*} [Group G]
    {P : Sylow 2 G} (h : Hypotheses P) {v w : P}
    (hv : v ∈ Subgroup.center P) (he : IsConj (v : G) (w : G)) :
    w ∈ Subgroup.center P := by
  obtain ⟨n, hn, he⟩ := h.fusion v v.property w w.property he
  let f : MulAut P := (P : Subgroup G).normalizerMonoidHom ⟨n, hn⟩
  have hf : f v = w := Subtype.ext he
  exact hf ▸ (Subgroup.centerCongr f ⟨v, hv⟩).property

/-- The two-part of a product of two conjugates of a central involution is central.
This is the binary support assertion of Proposition 2.3. -/
public theorem Hypotheses.twoPart_mem_center {G : Type*} [Group G] [Finite G]
    {P : Sylow 2 G} (h : Hypotheses P) (v : P)
    (hv : orderOf v = 2) (hvZ : v ∈ Subgroup.center P)
    (g k : G) (x : P) (y : G) (hxy : Commute (x : G) y)
    (hy : Nat.Coprime 2 (orderOf y))
    (he : (g * (v : G) * g⁻¹) * (k * (v : G) * k⁻¹)⁻¹ = (x : G) * y) :
    x ∈ Subgroup.center P := by
  let a := (MulAut.conj g) (v : G)
  let b := (MulAut.conj k) (v : G)
  have hv2 : (v : G) ^ 2 = 1 := by
    have hh : v ^ 2 = 1 := by simpa only [hv] using pow_orderOf_eq_one v
    exact congrArg Subtype.val hh
  have ha2 : a ^ 2 = 1 := by
    change ((MulAut.conj g) (v : G)) ^ 2 = 1
    rw [← map_pow, hv2, map_one]
  have hb2 : b ^ 2 = 1 := by
    change ((MulAut.conj k) (v : G)) ^ 2 = 1
    rw [← map_pow, hv2, map_one]
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using ha2)
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hb2)
  have hab : a * b = (x : G) * y := by
    change a * b⁻¹ = (x : G) * y at he
    rwa [hbi] at he
  have haRot : (MulAut.conj a) (a * b) = (a * b)⁻¹ := by
    change a * (a * b) * a⁻¹ = (a * b)⁻¹
    rw [mul_inv_rev, hai, hbi]
    have haa : a * a = 1 := by simpa only [pow_two] using ha2
    simp only [← mul_assoc, haa, one_mul]
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_orderOf_eq_pow x
  have hxp : (x : G) ^ (2 ^ n) = 1 := by
    exact congrArg Subtype.val (hn ▸ pow_orderOf_eq_one x)
  have hcop : (orderOf y).Coprime (orderOf (x : G)) := by
    rw [Subgroup.orderOf_coe, hn]
    exact hy.symm.pow_right n
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (x := (x : G)) hcop
  have hxpow : (a * b) ^ (orderOf y * m) = (x : G) := by
    rw [pow_mul, hab, hxy.mul_pow, pow_orderOf_eq_one, mul_one, hm]
  have hainv : a * (x : G) * a⁻¹ = (x : G)⁻¹ := by
    change MulAut.conj a (x : G) = (x : G)⁻¹
    rw [← hxpow, map_pow, haRot, inv_pow]
  have hxpGroup : IsPGroup 2 (Subgroup.zpowers (x : G)) :=
    IsPGroup.of_card_dvd_pow (n := n) (by
      simpa only [Nat.card_zpowers] using orderOf_dvd_of_pow_eq_one hxp)
  have hapGroup : IsPGroup 2 (Subgroup.zpowers a) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      simpa only [Nat.card_zpowers, pow_one] using orderOf_dvd_of_pow_eq_one ha2)
  have hnorm : Subgroup.zpowers a ≤ Subgroup.normalizer (Subgroup.zpowers (x : G)) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change Subgroup.zpowers (a * (x : G) * a⁻¹) = Subgroup.zpowers (x : G)
    rw [hainv, Subgroup.zpowers_inv]
  obtain ⟨Q, hQ⟩ := (hxpGroup.to_sup_of_normal_left' hapGroup hnorm).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G Q P
  have hmem {z : G} (hz : z ∈ (Q : Subgroup G)) :
      (MulAut.conj c) z ∈ (P : Subgroup G) := by
    rw [← hc]
    exact Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom hz
  let xP : P := ⟨(MulAut.conj c) (x : G),
    hmem ((le_sup_left.trans hQ) (Subgroup.mem_zpowers (x : G)))⟩
  let aP : P := ⟨(MulAut.conj c) a,
    hmem ((le_sup_right.trans hQ) (Subgroup.mem_zpowers a))⟩
  have hva : IsConj (v : G) a := isConj_iff.mpr ⟨g, rfl⟩
  have haZ : aP ∈ Subgroup.center P := h.central_of_isConj hvZ
    (hva.trans (isConj_iff.mpr ⟨c, rfl⟩))
  have hacomm : Commute a (x : G) := by
    apply (MulAut.conj c).injective
    rw [map_mul, map_mul]
    exact (congrArg (fun z : P => (z : G)) (Subgroup.mem_center_iff.mp haZ xP)).symm
  have hxsq : (x : G) ^ 2 = 1 := by
    have hself : (x : G) = (x : G)⁻¹ := by
      simpa only [hacomm.eq, mul_assoc, mul_inv_cancel, mul_one] using hainv
    rw [pow_two]
    calc
      (x : G) * (x : G) = (x : G)⁻¹ * (x : G) := congrArg (· * (x : G)) hself
      _ = 1 := inv_mul_cancel _
  have haxsq : (a * (x : G)) ^ 2 = 1 := by rw [hacomm.mul_pow, ha2, hxsq, one_mul]
  have haxprod : (a * (x : G)) * b = y := by
    have h1 : a * ((x : G) * y) = b := by
      rw [← hab, ← mul_assoc]
      simpa [pow_two] using congrArg (· * b) ha2
    rw [← h1]
    calc
      (a * (x : G)) * (a * ((x : G) * y)) = ((a * (x : G)) ^ 2) * y := by
        simp only [pow_two, mul_assoc]
      _ = y := by rw [haxsq, one_mul]
  have haxconj : IsConj (a * (x : G)) b :=
    isConj_of_involutions_odd_product _ _ haxsq hb2 (by
      rw [haxprod]
      exact Nat.coprime_two_left.mp hy)
  have haxZ : aP * xP ∈ Subgroup.center P := h.central_of_isConj hvZ
    ((isConj_iff.mpr ⟨k, rfl⟩).trans
      (haxconj.symm.trans (isConj_iff.mpr ⟨c, (MulAut.conj c).map_mul a (x : G)⟩)))
  have hxZ : xP ∈ Subgroup.center P := by
    have hh := (Subgroup.center P).mul_mem ((Subgroup.center P).inv_mem haZ) haxZ
    simpa only [inv_mul_cancel_left] using hh
  exact h.central_of_isConj hxZ (isConj_iff.mpr ⟨c, rfl⟩).symm

/-- The sign character attached to a subgroup of index two. -/
private theorem exists_linearCharacter_of_index_two
    {G : Type*} [Group G] [Finite G] (M : Subgroup G) (hM : M.index = 2) :
    ∃ theta : ClassFunction G, IsLinearCharacter theta ∧
      ∀ x, theta x = 1 ↔ x ∈ M := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let f : G →* ℂˣ := {
    toFun := fun x => if x ∈ M then 1 else -1
    map_one' := by simp
    map_mul' := by
      intro x y
      have hm := M.mul_mem_iff_of_index_two hM (a := x) (b := y)
      by_cases hx : x ∈ M <;> by_cases hy : y ∈ M <;> simp_all
  }
  refine ⟨fun x => (f x : ℂ), BenderGlauberman.isLinearCharacter_of_hom f, ?_⟩
  intro x
  by_cases hx : x ∈ M <;> norm_num [f, hx]

/-- A nonabelian finite Sylow two-subgroup has a central involution. -/
public theorem Hypotheses.exists_central_involution
    {G : Type*} [Group G] [Finite G] (P : Sylow 2 G) (h : Hypotheses P) :
    ∃ v : P, orderOf v = 2 ∧ v ∈ Subgroup.center P := by
  have hnontriv : Nontrivial P := by
    by_contra hn
    have : Subsingleton P := not_nontrivial_iff_subsingleton.mp hn
    exact h.not_commutative ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  let := hnontriv
  let := P.isPGroup'.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center P)
  let v := z ^ (orderOf z / 2)
  have hv : orderOf v = 2 :=
    orderOf_pow_orderOf_div (orderOf_pos z).ne'
      ((P.isPGroup'.to_subgroup (Subgroup.center P)).dvd_orderOf hz)
  exact ⟨v, (Subgroup.orderOf_coe v).trans hv, v.property⟩

/-- Proposition 2.3 and the maximal-subgroup and linear-character choices
at the beginning of Section 4, for the nonabelian Sylow two-subgroup case. -/
public theorem Hypotheses.nonempty_commutatorSupportData
    {G : Type*} [Group G] [Finite G] (P : Sylow 2 G) (h : Hypotheses P) :
    Nonempty (CommutatorSupportData P) := by
  obtain ⟨v, hv, hvZ⟩ := h.exists_central_involution P
  have hZ : Subgroup.center P ≠ ⊤ :=
    fun he => h.not_commutative (Subgroup.center_eq_top_iff.mp he)
  obtain ⟨M, hM, hZM⟩ := (eq_top_or_exists_le_coatom (Subgroup.center P)).resolve_left hZ
  obtain ⟨theta, htheta, hker⟩ := exists_linearCharacter_of_index_two M
    (P.isPGroup'.index_of_isCoatom M hM)
  exact ⟨{
    v := v
    involution := hv
    central := hvZ
    P₀ := M
    maximal := hM
    theta := theta
    linear := htheta
    kernel := hker
    support := fun g k x y hxy hy he =>
      hZM (h.twoPart_mem_center v hv hvZ g k x y hxy hy he)
  }⟩

/-- Chosen support data for the character-selection argument. -/
public noncomputable def Hypotheses.commutatorSupportData
    {G : Type*} [Group G] [Finite G] (P : Sylow 2 G) (h : Hypotheses P) :
    CommutatorSupportData P :=
  Classical.choice (h.nonempty_commutatorSupportData P)

end Glauberman.SuzukiCharacterization

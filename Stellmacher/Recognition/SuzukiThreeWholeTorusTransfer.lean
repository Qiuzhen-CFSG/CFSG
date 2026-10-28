module

public import Stellmacher.Recognition.SuzukiThreeCentralizingFusion
public import Theory.GroupTheory.CentralEightIndexFour
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Theory.GroupTheory.CyclicEightWeakClosure
public import BenderSuzuki.External.Hall.IndexFour
import Mathlib.Tactic.Group

/-!
# Transfer in the whole-torus branch

In Suzuki's degree 28 action, suppose the point swap centralizes the torus
and a nonidentity root element centralizes the whole torus. The two Bruhat
cells give at least 96 elements of its centralizer. The involution census
bounds that centralizer by 96, identifying it with the centralizer of the
unique torus involution. The cyclic torus is weakly closed in an ambient
Sylow two-subgroup: two order 8 subgroups in order 32 intersect nontrivially,
and their common involution forces the conjugating element into the torus
centralizer. Local and Hall–Wielandt transfer then give index 4 globally.

Source: Suzuki (1965), Section II, Lemma 3, the case W=K.
-/

namespace Stellmacher.Recognition.SuzukiThreeHypotheses

open MulAction Subgroup

variable {G Ω : Type*} [Group G] [MulAction G Ω]
    {a : Ω} {Q : Subgroup (stabilizer G a)} [Q.Normal]
    (h : SuzukiThreeHypotheses G Ω a Q)

include h

private theorem wholeTorus_bruhat_lower_bound [FaithfulSMul G Ω]
    (b : Ω) (hb : b ≠ a) (t : G)
    (hta : t • a = b) (htb : t • b = a)
    (htK : ∀ k : stabilizer (stabilizer G a) b,
      t⁻¹ * ((k : stabilizer G a) : G) * t = ((k : stabilizer G a) : G))
    (hu : ∃ u : Q, u ≠ 1 ∧ ∀ k : stabilizer (stabilizer G a) b,
      Commute ((u : stabilizer G a) : G) ((k : stabilizer G a) : G)) :
    96 ≤ Nat.card (centralizer (stabilizer G a ⊓ stabilizer G b : Set G)) := by
  classical
  let : Finite G := h.finite_group
  let K := stabilizer (stabilizer G a) b
  let C := centralizer (stabilizer G a ⊓ stabilizer G b : Set G)
  let f : Q →* G := (stabilizer G a).subtype.comp Q.subtype
  let U := C.comap f
  let : IsCyclic K := h.twoPoint_cyclic b hb
  have hkC (k : K) : ((k : stabilizer G a) : G) ∈ C := by
    apply mem_centralizer_iff.mpr
    intro l hl
    let lK : K := ⟨⟨l, hl.1⟩, hl.2⟩
    exact congrArg (fun z : K => ((z : stabilizer G a) : G)) (mul_comm' lK k)
  have htC : t ∈ C := by
    apply mem_centralizer_iff.mpr
    intro k hk
    have he := congrArg (fun z : G => t * z) (htK ⟨⟨k, hk.1⟩, hk.2⟩)
    simpa only [← mul_assoc, mul_inv_cancel, one_mul] using he
  have hUcard : 3 ≤ Nat.card U := by
    have hne : U ≠ ⊥ := by
      obtain ⟨u, hune, huc⟩ := hu
      intro he
      have huU : u ∈ U := by
        apply mem_centralizer_iff.mpr
        intro k hk
        exact (huc ⟨⟨k, hk.1⟩, hk.2⟩).symm.eq
      rw [he, mem_bot] at huU
      exact hune huU
    have hd : Nat.card U ∣ 27 := h.root_card ▸ U.card_subgroup_dvd_card
    have hp : 0 < Nat.card U := Nat.card_pos
    have hnotone : Nat.card U ≠ 1 := fun he => hne (card_eq_one.mp he)
    have hnot2 : Nat.card U ≠ 2 := by intro he; rw [he] at hd; norm_num at hd
    omega
  let small : U × K → C := fun p =>
    ⟨f p.1.val * ((p.2 : stabilizer G a) : G), C.mul_mem p.1.property (hkC p.2)⟩
  let large : U × K × U → C := fun p =>
    ⟨f p.1.val * ((p.2.1 : stabilizer G a) : G) * t * f p.2.2.val,
      C.mul_mem (C.mul_mem (C.mul_mem p.1.property (hkC p.2.1)) htC) p.2.2.property⟩
  have hsmall : Function.Injective small := by
    rintro ⟨u, k⟩ ⟨v, l⟩ he
    have heG := congrArg Subtype.val he
    have heb := congrArg (fun g : G => g • b) heG
    have hkb : ((k : stabilizer G a) : G) • b = b := k.property
    have hlb : ((l : stabilizer G a) : G) • b = b := l.property
    change (f u.val * ((k : stabilizer G a) : G)) • b =
      (f v.val * ((l : stabilizer G a) : G)) • b at heb
    rw [mul_smul, mul_smul, hkb, hlb] at heb
    have huv : u = v := Subtype.ext (h.root_smul_injective b hb heb)
    subst v
    have hkl : k = l := Subtype.ext (Subtype.ext (mul_left_cancel heG))
    subst l
    rfl
  have hlarge : Function.Injective large := by
    rintro ⟨u, k, v⟩ ⟨u', k', v'⟩ he
    have heq := h.bruhat_injective b hb t hta htb
      (a₁ := (u.val, k, v.val)) (a₂ := (u'.val, k', v'.val))
      (congrArg Subtype.val he)
    change (u.val, k, v.val) = (u'.val, k', v'.val) at heq
    have hu' : u = u' := Subtype.ext (congrArg Prod.fst heq)
    have hk' : k = k' := congrArg (fun p => p.2.1) heq
    have hv' : v = v' := Subtype.ext (congrArg (fun p => p.2.2) heq)
    subst u'; subst k'; subst v'; rfl
  have hsep (x : U × K) (y : U × K × U) : small x ≠ large y := by
    intro he
    have hea := congrArg (fun z : C => (z : G) • a) he
    have hxa : f x.1.val • a = a := x.1.val.val.property
    have hxka : ((x.2 : stabilizer G a) : G) • a = a := x.2.val.property
    have hyva : f y.2.2.val • a = a := y.2.2.val.val.property
    have hykb : ((y.2.1 : stabilizer G a) : G) • b = b := y.2.1.property
    have hyua : f y.1.val • a = a := y.1.val.val.property
    change (f x.1.val * ((x.2 : stabilizer G a) : G)) • a =
      (f y.1.val * ((y.2.1 : stabilizer G a) : G) * t * f y.2.2.val) • a at hea
    simp only [mul_smul, hxa, hxka, hyva, hta, hykb] at hea
    exact hb (MulAction.injective (f y.1.val) (hea.symm.trans hyua.symm))
  let cells : (U × K) ⊕ (U × K × U) → C := Sum.elim small large
  have hinj : Function.Injective cells := by
    intro x y he
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (hsmall he)
      | inr y => exact (hsep x y he).elim
    | inr x =>
      cases y with
      | inl y => exact (hsep y x he.symm).elim
      | inr y => exact congrArg Sum.inr (hlarge he)
  have hc := Nat.card_le_card_of_injective cells hinj
  rw [Nat.card_sum, Nat.card_prod, Nat.card_prod, Nat.card_prod, h.twoPoint_card b hb] at hc
  change 96 ≤ Nat.card C
  nlinarith

/-- In the whole-torus branch, its centralizer is the centralizer of each
of its involutions, and has order 96. -/
public theorem wholeTorus_centralizer_eq [FaithfulSMul G Ω]
    (b : Ω) (hb : b ≠ a) (t : G)
    (hta : t • a = b) (htb : t • b = a)
    (htK : ∀ k : stabilizer (stabilizer G a) b,
      t⁻¹ * ((k : stabilizer G a) : G) * t = ((k : stabilizer G a) : G))
    (hc : ∀ j : G, orderOf j = 2 → Nat.card (centralizer ({j} : Set G)) = 96)
    (hu : ∃ u : Q, u ≠ 1 ∧ ∀ k : stabilizer (stabilizer G a) b,
      Commute ((u : stabilizer G a) : G) ((k : stabilizer G a) : G))
    (j : G) (hjK : j ∈ stabilizer G a ⊓ stabilizer G b) (hj : orderOf j = 2) :
    centralizer (stabilizer G a ⊓ stabilizer G b : Set G) = centralizer ({j} : Set G) ∧
      Nat.card (centralizer (stabilizer G a ⊓ stabilizer G b : Set G)) = 96 := by
  let : Finite G := h.finite_group
  have hle : centralizer (stabilizer G a ⊓ stabilizer G b : Set G) ≤
      centralizer ({j} : Set G) :=
    centralizer_le (Set.singleton_subset_iff.mpr hjK)
  have he := eq_of_le_of_card_ge hle (by
    rw [hc j hj]
    exact h.wholeTorus_bruhat_lower_bound b hb t hta htb htK hu)
  exact ⟨he, he ▸ hc j hj⟩

/-- The whole-torus centralizing branch yields the normal index-four subgroup
required by Suzuki's transfer argument. The centralizer-size census suffices;
no assumption about conjugacy of all involutions is needed. -/
public theorem exists_normal_index_four_of_wholeTorus [FaithfulSMul G Ω]
    (b : Ω) (hb : b ≠ a) (t : G)
    (hta : t • a = b) (htb : t • b = a)
    (htK : ∀ k : stabilizer (stabilizer G a) b,
      t⁻¹ * ((k : stabilizer G a) : G) * t = ((k : stabilizer G a) : G))
    (hc : ∀ j : G, orderOf j = 2 → Nat.card (centralizer ({j} : Set G)) = 96)
    (hu : ∃ u : Q, u ≠ 1 ∧ ∀ k : stabilizer (stabilizer G a) b,
      Commute ((u : stabilizer G a) : G) ((k : stabilizer G a) : G)) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 4 := by
  classical
  let : Finite G := h.finite_group
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K : Subgroup G := stabilizer G a ⊓ stabilizer G b
  let e : stabilizer (stabilizer G a) b ≃* K := {
    toFun k := ⟨((k : stabilizer G a) : G), k.val.property, k.property⟩
    invFun k := ⟨⟨(k : G), k.property.1⟩, k.property.2⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  have hK : Nat.card K = 8 :=
    (Nat.card_congr e.toEquiv).symm.trans (h.twoPoint_card b hb)
  let : IsCyclic K := e.isCyclic.mp (h.twoPoint_cyclic b hb)
  obtain ⟨j, hj⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 (by rw [hK]; decide)
  let C := centralizer (K : Set G)
  have hjG : orderOf (j : G) = 2 := (orderOf_coe j).trans hj
  obtain ⟨hCeq, hCcard⟩ := h.wholeTorus_centralizer_eq b hb t hta htb htK hc hu
    (j : G) j.property hjG
  change C = centralizer ({(j : G)} : Set G) at hCeq
  change Nat.card C = 96 at hCcard
  have hNC : normalizer (K : Set G) = C :=
    h.normalizer_eq_centralizer_of_le_twoPoint_of_swap_centralizes b hb t hta htb htK K le_rfl
  have hKC : K ≤ C := K.le_centralizer
  let Z := K.subgroupOf C
  have hZcard : Nat.card Z = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hKC).toEquiv).trans hK
  have hZcenter : Z ≤ center C := by
    intro z hz
    apply mem_center_iff.mpr
    intro c
    exact Subtype.ext (mem_centralizer_iff.mp c.property z hz).symm
  let : Z.Normal := ⟨fun z hz c => by
    rw [mem_center_iff.mp (hZcenter hz) c, mul_inv_cancel_right]
    exact hz⟩
  let S : Sylow 2 C := Sylow.nonempty.some
  have hScard : Nat.card S = 32 := by
    rw [S.card_eq_multiplicity, hCcard]
    decide +kernel
  let P₀ : Subgroup G := (S : Subgroup C).map C.subtype
  have hPcard : Nat.card P₀ = 32 :=
    (card_map_of_injective C.subtype_injective).trans hScard
  have hPtwo : IsPGroup 2 P₀ := S.isPGroup'.map C.subtype
  have hPi : P₀.index = 189 := by
    have hm := P₀.card_mul_index
    rw [hPcard, h.group_card] at hm
    omega
  let P : Sylow 2 G := hPtwo.toSylow (by rw [hPi]; decide)
  have hPC : (P : Subgroup G) ≤ C := map_subtype_le _
  have hZtwo : IsPGroup 2 Z := IsPGroup.of_card (n := 3) hZcard
  have hKP : K ≤ (P : Subgroup G) := by
    intro k hk
    exact ⟨⟨k, hKC hk⟩, hZtwo.le_sylow_of_normal S hk, rfl⟩
  have hweak : BenderSuzuki.External.WeaklyClosedIn (P : Subgroup G) K :=
    weaklyClosed_cyclic_eight_of_involution_centralizer (P : Subgroup G) K hPcard hK hKP hPC
      j hj (by rw [← hCeq, hNC])
  have hHcard : Nat.card (normalizer (K : Set G)) = 96 := by rw [hNC]; exact hCcard
  let ZN := K.subgroupOf (normalizer (K : Set G))
  have hZNcard : Nat.card ZN = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe K.le_normalizer).toEquiv).trans hK
  have hZNcenter : ZN ≤ center (normalizer (K : Set G)) := by
    intro z hz
    apply mem_center_iff.mpr
    intro c
    have hcC : (c : G) ∈ C := hNC ▸ c.property
    exact Subtype.ext (mem_centralizer_iff.mp hcC z hz).symm
  obtain ⟨L, hLnormal, hLindex⟩ :=
    exists_normal_index_four_of_card_ninetySix_of_central_eight hHcard ZN hZNcard hZNcenter
  let : L.Normal := hLnormal
  exact BenderSuzuki.External.exists_normal_index_four_of_weaklyClosed_central P K hweak
    (fun u z hu hz => (mem_centralizer_iff.mp (hPC hu) z hz).symm) L hLindex

/-- The source-facing whole-torus transfer statement, with both census
conclusions and the involutory swap supplied by Suzuki's setup. -/
public theorem wholeTorus_transfer_index_four [FaithfulSMul G Ω]
    (b : Ω) (hb : b ≠ a) (t : G) (_ht2 : t ^ 2 = 1)
    (hta : t • a = b) (htb : t • b = a)
    (htK : ∀ k : stabilizer (stabilizer G a) b,
      t⁻¹ * ((k : stabilizer G a) : G) * t = ((k : stabilizer G a) : G))
    (hc : ∀ j : G, orderOf j = 2 → Nat.card (centralizer ({j} : Set G)) = 96)
    (_hconj : ∀ i j : G, orderOf i = 2 → orderOf j = 2 → IsConj i j)
    (hu : ∃ u : Q, u ≠ 1 ∧ ∀ k : stabilizer (stabilizer G a) b,
      Commute ((u : stabilizer G a) : G) ((k : stabilizer G a) : G)) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 4 :=
  h.exists_normal_index_four_of_wholeTorus b hb t hta htb htK hc hu

end Stellmacher.Recognition.SuzukiThreeHypotheses

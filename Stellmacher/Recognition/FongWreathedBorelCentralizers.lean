module

public import Stellmacher.Recognition.FongWreathedBorelData
public import Stellmacher.Recognition.FongWreathedLocal
public import ABG.ChapterII.Section3.SourceThreeWreathedOrder
public import ABG.ChapterII.Section1.WreathedOrderEightCentralizer
public import ABG.ChapterII.Section1.WreathedDerived
public import Theory.GroupTheory.CyclicNormalCentralizer
public import Theory.GroupAction.NinePointSevenCentralizer
public import Theory.GroupAction.SimpleCosets

/-!
# Fong's local centralizer calculation

The source characteristic-three Q-group structure gives order 96 for the
involution centralizer modulo its odd core. At ambient order 6048 the core
has order dividing 63. Simplicity and the coset action exclude core orders
at least nine. A cyclic core of order seven is centralized by the Sylow
derived group, contradicting the centralizer order of a seven-cycle in
the resulting degree-nine action. A core of order three contradicts the
character obstruction at `X*F²`.

With trivial odd core, the Q-group centralizes its Sylow center, giving
`C_G(F²) = C_G(J)`. The character congruences make the remaining centralizers
two-groups. Wreathed centralizer geometry then gives the cyclic centralizer
of `F` and identifies the centralizer of `X*F²` with the actual abelian base
of the chosen Sylow presentation.
Source: Fong, *Some Sylow subgroups of order 32 and a characterization of
U(3,3)*, J. Algebra 6 (1967), pp.70–71 and p.75.
-/

namespace Stellmacher.Recognition.FongWreathed

variable {G : Type*} [Group G] {S : Sylow 2 G}
variable (P : ABG.Wreathed.Presentation S 2)

public theorem sylow_le_centralizer_J :
    (S : Subgroup G) ≤ Subgroup.centralizer ({J P} : Set G) := by
  intro s hs
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  rw [J_eq_x]
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp P.x_mem_center (⟨s, hs⟩ : S))

public theorem X_mul_F_sq_mem_centralizer_J :
    X P * F P ^ 2 ∈ Subgroup.centralizer ({J P} : Set G) := by
  rw [X_mul_F_sq]
  exact sylow_le_centralizer_J P (P.r⁻¹).property

/-- Every cyclic normal subgroup of the involution centralizer commutes
with the specified Sylow derived generator. -/
public theorem cyclic_normal_le_centralizer_X_mul_F_sq
    (N : Subgroup (Subgroup.centralizer ({J P} : Set G))) [N.Normal] [IsCyclic N] :
    N.map (Subgroup.centralizer ({J P} : Set G)).subtype ≤
      Subgroup.centralizer ({X P * F P ^ 2} : Set G) := by
  let C := Subgroup.centralizer ({J P} : Set G)
  let f : S →* C := Subgroup.inclusion (sylow_le_centralizer_J P)
  have hr : P.r⁻¹ ∈ _root_.commutator S := by
    rw [P.derived_structure.1]
    exact (Subgroup.zpowers P.r).inv_mem (Subgroup.mem_zpowers _)
  have hrC : f (P.r⁻¹) ∈ _root_.commutator C := by
    have hm : (_root_.commutator S).map f ≤ _root_.commutator C := by
      rw [map_commutator_eq, commutator_def]
      exact Subgroup.commutator_mono le_top le_top
    exact hm (Subgroup.mem_map_of_mem f hr)
  have hcentral := Subgroup.commutator_le_centralizer_of_isCyclic_normal N hrC
  rintro y ⟨o, ho, rfl⟩
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  rw [X_mul_F_sq]
  exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hcentral o ho)

public theorem orderOf_X_mul_F_sq : orderOf (X P * F P ^ 2) = 4 := by
  rw [X_mul_F_sq, Subgroup.orderOf_coe, orderOf_inv, P.r_order]
  norm_num

public theorem X_mul_F_sq_sq : (X P * F P ^ 2) ^ 2 = J P := by
  have hi : (J P)⁻¹ = J P := inv_eq_of_mul_eq_one_right (by
    rw [← pow_two, ← orderOf_J P]
    exact pow_orderOf_eq_one _)
  rw [X_mul_F_sq]
  change (((P.r⁻¹) ^ 2 : S) : G) = _
  rw [inv_pow]
  change (((P.r ^ 2 : S) : G))⁻¹ = _
  rw [← J_eq_r_sq, hi]

public theorem centralizer_F_le_centralizer_J :
    Subgroup.centralizer ({F P} : Set G) ≤ Subgroup.centralizer ({J P} : Set G) := by
  intro g hg
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    ((show Commute g (F P) from Subgroup.mem_centralizer_singleton_iff.mp hg).pow_right 4).eq

public theorem centralizer_X_mul_F_sq_le_centralizer_J :
    Subgroup.centralizer ({X P * F P ^ 2} : Set G) ≤
      Subgroup.centralizer ({J P} : Set G) := by
  intro g hg
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  rw [← X_mul_F_sq_sq]
  exact ((show Commute g (X P * F P ^ 2) from
    Subgroup.mem_centralizer_singleton_iff.mp hg).pow_right 2).eq

public theorem base_le_centralizer_X_mul_F_sq :
    P.U.map (S : Subgroup G).subtype ≤ Subgroup.centralizer ({X P * F P ^ 2} : Set G) := by
  rintro g ⟨a, ha, rfl⟩
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  rw [X_mul_F_sq]
  have hr : P.r ∈ P.U := (P.mem_U_iff _).mpr ⟨1, -1, by simp [ABG.Wreathed.Presentation.r]⟩
  exact congrArg Subtype.val (P.commute_of_mem_U ha (P.U.inv_mem hr)).eq

public theorem X_mul_F_sq_not_commute_z : ¬ Commute (X P * F P ^ 2) (P.z : G) := by
  intro hh
  rw [X_mul_F_sq] at hh
  have hcomm : Commute P.r⁻¹ P.z := Subtype.ext hh.eq
  have hcomm' : Commute P.z P.r := by simpa using hcomm.inv_left.symm
  have heq := P.z_conj_r
  rw [hcomm'.eq, mul_inv_cancel_right] at heq
  have hpow : P.r ^ 2 = 1 := by
    rw [pow_two, ← inv_eq_iff_mul_eq_one]
    exact heq.symm
  have hd := orderOf_dvd_of_pow_eq_one hpow
  rw [P.r_order] at hd
  norm_num at hd

/-- The normal odd core of order three would supply precisely the commuting
order-three element excluded by the character calculation. -/
public theorem oddCore_centralizer_J_card_ne_three [Finite G]
    (c : CharacterData P) :
    Nat.card (pPrimeCore 2 (Subgroup.centralizer ({J P} : Set G))) ≠ 3 := by
  intro hO
  let C := Subgroup.centralizer ({J P} : Set G)
  let O := pPrimeCore 2 C
  let : IsCyclic O := isCyclic_of_prime_card hO
  apply c.three_not_dvd_centralizer_X_mul_F_sq
  have hc : Nat.card (O.map C.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact hO
  exact hc ▸ Subgroup.card_dvd_of_le (cyclic_normal_le_centralizer_X_mul_F_sq P O)

public theorem centralizer_J_ne_top [Finite G] [IsSimpleGroup G]
    (hG : Nat.card G = 6048) : Subgroup.centralizer ({J P} : Set G) ≠ ⊤ := by
  intro htop
  have hj : J P ∈ Subgroup.center G := by
    apply Subgroup.mem_center_iff.mpr
    intro g
    exact Subgroup.mem_centralizer_singleton_iff.mp (htop ▸ Subgroup.mem_top g)
  let Z := Subgroup.zpowers (J P)
  have hZ : Z ≤ Subgroup.center G := Subgroup.zpowers_le.mpr hj
  let : Z.Normal := ⟨fun z hz g => by
    have hh := Subgroup.mem_center_iff.mp (hZ hz) g
    simpa only [hh, mul_inv_cancel_right] using hz⟩
  have hZcard : Nat.card Z = 2 := by rw [Nat.card_zpowers, orderOf_J]
  rcases (inferInstance : Z.Normal).eq_bot_or_eq_top with hz | hz
  · rw [hz, Subgroup.card_bot] at hZcard
    omega
  · rw [hz, Subgroup.card_top, hG] at hZcard
    omega

section Simple

variable [Finite G] [IsSimpleGroup G]
variable (hS : ABG.IsWreathedOfHeight S 2) (x : G) (hx : orderOf x = 2)
variable [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))]

include hS x hx

public theorem centralizer_J_oddCore_quotient_card :
    Nat.card ((Subgroup.centralizer ({J P} : Set G)) ⧸
      pPrimeCore 2 (Subgroup.centralizer ({J P} : Set G))) = 96 := by
  obtain ⟨hQ, hq, T, hT⟩ :=
    involutionCentralizer_data_of_simple_wreathed32 S hS x hx (J P) (orderOf_J P)
  exact ABG.card_oddCore_quotient_eq_96_of_sourceThree_wreathed32 hQ T hT hq

public theorem centralizer_J_card_eq_oddCore_mul :
    Nat.card (Subgroup.centralizer ({J P} : Set G)) =
      96 * Nat.card (pPrimeCore 2 (Subgroup.centralizer ({J P} : Set G))) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    (pPrimeCore 2 (Subgroup.centralizer ({J P} : Set G))),
    centralizer_J_oddCore_quotient_card P hS x hx]

public theorem oddCore_centralizer_J_card_dvd_63 (hG : Nat.card G = 6048) :
    Nat.card (pPrimeCore 2 (Subgroup.centralizer ({J P} : Set G))) ∣ 63 := by
  have hd := (Subgroup.centralizer ({J P} : Set G)).card_subgroup_dvd_card
  rw [centralizer_J_card_eq_oddCore_mul P hS x hx, hG] at hd
  exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 96)).mp hd

public theorem oddCore_centralizer_J_card_ne_nine (hG : Nat.card G = 6048) :
    Nat.card (pPrimeCore 2 (Subgroup.centralizer ({J P} : Set G))) ≠ 9 := by
  intro hO
  let C := Subgroup.centralizer ({J P} : Set G)
  have hC : Nat.card C = 864 := by
    rw [centralizer_J_card_eq_oddCore_mul P hS x hx, hO]
  have hi : C.index = 7 := by
    have hh := C.card_mul_index
    rw [hC, hG] at hh
    omega
  have hproper : C ≠ ⊤ := by
    intro he
    rw [he, Subgroup.index_top] at hi
    omega
  have hd := C.card_dvd_factorial_index_of_simple hproper
  rw [hG, hi] at hd
  norm_num at hd

public theorem oddCore_centralizer_J_card_ne_seven (hG : Nat.card G = 6048) :
    Nat.card (pPrimeCore 2 (Subgroup.centralizer ({J P} : Set G))) ≠ 7 := by
  classical
  intro hO
  let C := Subgroup.centralizer ({J P} : Set G)
  let O := pPrimeCore 2 C
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : IsCyclic O := isCyclic_of_prime_card hO
  have hC : Nat.card C = 672 := by
    rw [centralizer_J_card_eq_oddCore_mul P hS x hx, hO]
  have hi : C.index = 9 := by
    have hh := C.card_mul_index
    rw [hC, hG] at hh
    omega
  let Ω := G ⧸ C
  let := Fintype.ofFinite Ω
  have hΩ : Fintype.card Ω = 9 := by
    rw [← Nat.card_eq_fintype_card]
    exact hi
  let ρ := MulAction.toPermHom G Ω
  have hρ : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, ← C.normalCore_eq_ker]
    exact C.normalCore_eq_bot_of_simple (centralizer_J_ne_top P hG)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := O) 7 (by rw [hO])
  have hyG : orderOf ((y : C) : G) = 7 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy]
  have hcomm : Commute ((y : C) : G) (X P * F P ^ 2) :=
    Subgroup.mem_centralizer_singleton_iff.mp
      (cyclic_normal_le_centralizer_X_mul_F_sq P O
        (Subgroup.mem_map_of_mem C.subtype y.property))
  exact Equiv.Perm.not_commute_order_four_seven_on_nine hΩ
    (ρ (X P * F P ^ 2)) (ρ ((y : C) : G))
    ((orderOf_injective ρ hρ _).trans (orderOf_X_mul_F_sq P))
    ((orderOf_injective ρ hρ _).trans hyG) (hcomm.symm.map ρ)

public theorem oddCore_centralizer_J_eq_bot (hG : Nat.card G = 6048)
    (c : CharacterData P) :
    pPrimeCore 2 (Subgroup.centralizer ({J P} : Set G)) = ⊥ := by
  let C := Subgroup.centralizer ({J P} : Set G)
  let O := pPrimeCore 2 C
  have hindex : 7 < C.index := by
    by_contra h
    have hd := C.card_dvd_factorial_index_of_simple (centralizer_J_ne_top P hG)
    have hh := hd.trans (Nat.factorial_dvd_factorial (by omega : C.index ≤ 7))
    rw [hG] at hh
    norm_num at hh
  have hsmall : Nat.card O < 9 := by
    have hh := C.card_mul_index
    rw [centralizer_J_card_eq_oddCore_mul P hS x hx, hG] at hh
    change 96 * Nat.card O * C.index = 6048 at hh
    nlinarith
  have hd := oddCore_centralizer_J_card_dvd_63 P hS x hx hG
  have h3 := oddCore_centralizer_J_card_ne_three P c
  have h7 := oddCore_centralizer_J_card_ne_seven P hS x hx hG
  have hposs : Nat.card O = 1 ∨ Nat.card O = 3 ∨ Nat.card O = 7 := by
    have hm := Nat.mem_divisors.mpr ⟨hd, by decide⟩
    rw [show Nat.divisors 63 = {1, 3, 7, 9, 21, 63} by decide] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    change Nat.card O = 1 ∨ Nat.card O = 3 ∨ Nat.card O = 7 ∨
      Nat.card O = 9 ∨ Nat.card O = 21 ∨ Nat.card O = 63 at hm
    omega
  apply Subgroup.eq_bot_of_card_eq
  rcases hposs with h | h | h
  · exact h
  · exact (h3 h).elim
  · exact (h7 h).elim

public theorem card_centralizer_J (hG : Nat.card G = 6048) (c : CharacterData P) :
    Nat.card (Subgroup.centralizer ({J P} : Set G)) = 96 := by
  rw [centralizer_J_card_eq_oddCore_mul P hS x hx,
    oddCore_centralizer_J_eq_bot P hS x hx hG c, Subgroup.card_bot, mul_one]

public theorem centralizer_F_sq_eq_centralizer_J (hG : Nat.card G = 6048)
    (c : CharacterData P) :
    Subgroup.centralizer ({F P ^ 2} : Set G) = Subgroup.centralizer ({J P} : Set G) := by
  apply le_antisymm
  · intro g hg
    have hh := (show Commute g (F P ^ 2) from
      Subgroup.mem_centralizer_singleton_iff.mp hg).pow_right 2
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    simpa [J, ← pow_mul] using hh.eq
  · let C := Subgroup.centralizer ({J P} : Set G)
    let T : Sylow 2 C := S.subtype (sylow_le_centralizer_J P)
    let e : T ≃* S := Subgroup.subgroupOfEquivOfLe (sylow_le_centralizer_J P)
    have hQ := (involutionCentralizer_data_of_simple_wreathed32 S hS x hx
      (J P) (orderOf_J P)).1
    have hZ : ABG.subgroupCenter (T : Subgroup C) ≤ Subgroup.center C := by
      have hh := ABG.qGroup_eq_oddCore_mul_sylowCenterCentralizer hQ T
      rw [oddCore_centralizer_J_eq_bot P hS x hx hG c, bot_sup_eq] at hh
      exact Subgroup.centralizer_eq_top_iff_subset.mp hh
    have hu : e.symm P.u ∈ Subgroup.center T := by
      apply Subgroup.mem_center_iff.mpr
      intro t
      apply e.injective
      simpa only [map_mul, e.apply_symm_apply] using
        Subgroup.mem_center_iff.mp P.u_mem_center (e t)
    have huC : ((e.symm P.u : T) : C) ∈ Subgroup.center C :=
      hZ ⟨e.symm P.u, hu, rfl⟩
    intro g hg
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    rw [F_sq]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp huC (⟨g, hg⟩ : C))

public theorem card_centralizer_F_sq (hG : Nat.card G = 6048) (c : CharacterData P) :
    Nat.card (Subgroup.centralizer ({F P ^ 2} : Set G)) = 96 := by
  rw [centralizer_F_sq_eq_centralizer_J P hS x hx hG c,
    card_centralizer_J P hS x hx hG c]

private theorem centralizer_card_dvd_32 (hG : Nat.card G = 6048) (c : CharacterData P)
    (D : Subgroup G) (hD : D ≤ Subgroup.centralizer ({J P} : Set G))
    (h3 : ¬ 3 ∣ Nat.card D) : Nat.card D ∣ 32 := by
  have hd := Subgroup.card_dvd_of_le hD
  rw [card_centralizer_J P hS x hx hG c] at hd
  have hcop : Nat.Coprime (Nat.card D) 3 := (Nat.prime_three.coprime_iff_not_dvd.mpr h3).symm
  exact hcop.dvd_of_dvd_mul_left (show Nat.card D ∣ 3 * 32 from hd)

public theorem centralizer_F_eq_zpowers (hG : Nat.card G = 6048) (c : CharacterData P) :
    Subgroup.centralizer ({F P} : Set G) = Subgroup.zpowers (F P) := by
  let C := Subgroup.centralizer ({F P} : Set G)
  have htwo : IsPGroup 2 C := IsPGroup.of_card_dvd_pow (n := 5)
    (centralizer_card_dvd_32 P hS x hx hG c C (centralizer_F_le_centralizer_J P)
      c.three_not_dvd_centralizer_F)
  obtain ⟨T, hCT⟩ := htwo.exists_le_sylow
  have hT : ABG.IsWreathedOfHeight T 2 := ABG.wreathed_equiv (S.equiv T) hS
  obtain ⟨Q⟩ := ABG.Wreathed.nonempty_presentation hT
  let f : T := ⟨F P, hCT (Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl _).eq)⟩
  have hf : orderOf f = 8 := (Subgroup.orderOf_coe f).symm.trans (orderOf_F P)
  apply le_antisymm
  · intro g hg
    let t : T := ⟨g, hCT hg⟩
    have ht : t ∈ Subgroup.centralizer ({f} : Set T) := by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hg)
    rw [Q.centralizer_eq_zpowers_of_order_eight f hf] at ht
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ht
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, congrArg Subtype.val hk⟩
  · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl _).eq)

public theorem card_centralizer_F (hG : Nat.card G = 6048) (c : CharacterData P) :
    Nat.card (Subgroup.centralizer ({F P} : Set G)) = 8 := by
  rw [centralizer_F_eq_zpowers P hS x hx hG c, Nat.card_zpowers, orderOf_F]

public theorem card_centralizer_X_mul_F_sq (hG : Nat.card G = 6048)
    (c : CharacterData P) :
    Nat.card (Subgroup.centralizer ({X P * F P ^ 2} : Set G)) = 16 := by
  let r := X P * F P ^ 2
  let C := Subgroup.centralizer ({r} : Set G)
  have hd : Nat.card C ∣ 32 := centralizer_card_dvd_32 P hS x hx hG c C
    (centralizer_X_mul_F_sq_le_centralizer_J P) c.three_not_dvd_centralizer_X_mul_F_sq
  have h16 : 16 ∣ Nat.card C := by
    have hh := Subgroup.card_dvd_of_le (base_le_centralizer_X_mul_F_sq P)
    rw [Subgroup.card_map_of_injective (S : Subgroup G).subtype_injective, P.card_U] at hh
    exact hh
  have hnot32 : Nat.card C ≠ 32 := by
    intro h32
    have htwo : IsPGroup 2 C := IsPGroup.of_card_dvd_pow (n := 5) hd
    obtain ⟨T, hCT⟩ := htwo.exists_le_sylow
    have hT : ABG.IsWreathedOfHeight T 2 := ABG.wreathed_equiv (S.equiv T) hS
    have heq : C = (T : Subgroup G) := Subgroup.eq_of_le_of_card_ge hCT (by
      rw [h32, hT.2.1]
      norm_num)
    obtain ⟨Q⟩ := ABG.Wreathed.nonempty_presentation
      (ABG.wreathed_equiv (MulEquiv.subgroupCongr heq).symm hT)
    have hu : F P ^ 2 ∈ C := by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      have hh := X_mul_F_sq_mem_centralizer_J P
      rw [← centralizer_F_sq_eq_centralizer_J P hS x hx hG c] at hh
      exact (Subgroup.mem_centralizer_singleton_iff.mp hh).symm
    let u : C := ⟨F P ^ 2, hu⟩
    have huc : u ∈ Subgroup.center C := by
      apply Subgroup.mem_center_iff.mpr
      intro g
      apply Subtype.ext
      have hh := centralizer_X_mul_F_sq_le_centralizer_J P g.property
      rw [← centralizer_F_sq_eq_centralizer_J P hS x hx hG c] at hh
      exact Subgroup.mem_centralizer_singleton_iff.mp hh
    have hZ : Subgroup.zpowers u = Subgroup.center C := by
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr huc)
      rw [Q.card_center, Nat.card_zpowers, ← Subgroup.orderOf_coe u, orderOf_F_sq]
      norm_num
    let v : C := ⟨r, Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl r).eq⟩
    have hvc : v ∈ Subgroup.center C := by
      apply Subgroup.mem_center_iff.mpr
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.property)
    rw [← hZ] at hvc
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hvc
    have hkG : (F P ^ 2) ^ k = r := congrArg Subtype.val hk
    have hz : Commute (F P ^ 2) (P.z : G) := by
      rw [F_sq]
      exact (P.u_commute P.z).map (S : Subgroup G).subtype
    apply X_mul_F_sq_not_commute_z P
    change Commute r (P.z : G)
    rw [← hkG]
    exact hz.zpow_left k
  have hlo : 0 < Nat.card C := Nat.card_pos
  have hhi : Nat.card C ≤ 32 := Nat.le_of_dvd (by decide) hd
  obtain ⟨k, hk⟩ := h16
  have hk12 : k = 1 ∨ k = 2 := by omega
  rcases hk12 with rfl | rfl
  · omega
  · exact (hnot32 (by omega)).elim

/-- The centralizer is the actual abelian base in the chosen Sylow subgroup. -/
public theorem centralizer_X_mul_F_sq_eq_base (hG : Nat.card G = 6048)
    (c : CharacterData P) :
    Subgroup.centralizer ({X P * F P ^ 2} : Set G) = P.U.map (S : Subgroup G).subtype := by
  symm
  apply Subgroup.eq_of_le_of_card_ge (base_le_centralizer_X_mul_F_sq P)
  rw [card_centralizer_X_mul_F_sq P hS x hx hG c,
    Subgroup.card_map_of_injective (S : Subgroup G).subtype_injective, P.card_U]
  norm_num

end Simple
end Stellmacher.Recognition.FongWreathed

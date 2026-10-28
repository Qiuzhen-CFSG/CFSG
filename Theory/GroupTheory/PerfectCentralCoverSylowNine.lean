module

public import Theory.GroupTheory.PerfectCentralCover
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# Three-primary kernel bound over an order-nine Sylow subgroup

For a finite perfect central cover, a cyclic Sylow subgroup downstairs gives
the usual transfer exclusion.  If a Sylow subgroup of order nine is
noncyclic, it is elementary abelian of rank two.  Two lifts generate the
Sylow subgroup upstairs modulo its Frattini subgroup; their commutator is
central, has cube one, and generates the derived subgroup.  Central Sylow
transfer puts the kernel inside this derived subgroup, whose order is at most
three.
-/

open scoped IsMulCommutative commutatorElement
open Subgroup

namespace PerfectCentralCovering

namespace SylowNine

private theorem pair_lifts_generate
    {E G : Type*} [Group E] [Group G] [Finite E] [Group.IsPerfect E]
    (f : E →* G) (hker : f.ker ≤ center E)
    (P : Sylow 3 E) (x y : P)
    (himage : closure ({f x, f y} : Set G) = (P : Subgroup E).map f) :
    closure ({x, y} : Set P) = ⊤ := by
  let g : P →* G := f.comp (P : Subgroup E).subtype
  have hmap : (closure ({x, y} : Set P)).map g = g.range := by
    rw [MonoidHom.map_closure]
    simpa only [Set.image_insert_eq, Set.image_singleton, g, MonoidHom.comp_apply,
      Subgroup.coe_subtype, MonoidHom.range_comp, range_subtype] using himage
  have hs : closure ({x, y} : Set P) ⊔ g.ker = ⊤ := by
    have h := congrArg (Subgroup.comap g) hmap
    simpa only [comap_map_eq, MonoidHom.comap_range_self] using h
  have hF : g.ker ≤ frattini P := ker_comap_le_frattini_sylow P f hker
  apply frattini_nongenerating
  exact top_unique (hs ▸ sup_le_sup_left hF _)

private theorem commutator_mem_center_of_pair {G : Type*} [Group G]
    (x y : G) (hgen : closure ({x, y} : Set G) = ⊤)
    (hx : Commute ⁅x, y⁆ x) (hy : Commute ⁅x, y⁆ y) :
    ⁅x, y⁆ ∈ center G := by
  have hle : closure ({x, y} : Set G) ≤ centralizer ({⁅x, y⁆} : Set G) := by
    rw [closure_le]
    intro z hz
    rcases hz with rfl | hz
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hx.eq.symm
    · obtain rfl := hz
      exact Subgroup.mem_centralizer_singleton_iff.mpr hy.eq.symm
  rw [hgen] at hle
  exact mem_center_iff.mpr fun z =>
    Subgroup.mem_centralizer_singleton_iff.mp (hle (mem_top z))

private theorem derived_le_of_pair {G : Type*} [Group G]
    (x y : G) (hgen : closure ({x, y} : Set G) = ⊤)
    (N : Subgroup G) [N.Normal] (hxy : ⁅x, y⁆ ∈ N) :
    _root_.commutator G ≤ N := by
  let q := QuotientGroup.mk' N
  have hgenq : closure ({q x, q y} : Set (G ⧸ N)) = ⊤ := by
    have h := congrArg (Subgroup.map q) hgen
    simpa only [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
      map_top_of_surjective q (QuotientGroup.mk'_surjective N)] using h
  have hxyq : q x * q y = q y * q x := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr hxy
  have hcomm : IsMulCommutative (closure ({q x, q y} : Set (G ⧸ N))) := by
    apply isMulCommutative_closure
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact hxyq
    · exact hxyq.symm
    · rfl
  rw [hgenq] at hcomm
  let := hcomm
  apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
  exact ⟨⟨fun a b => congrArg Subtype.val
    (mul_comm' (⟨a, mem_top a⟩ : (⊤ : Subgroup (G ⧸ N)))
      ⟨b, mem_top b⟩)⟩⟩

private theorem cube_commutator {G : Type*} [Group G] (x y : G)
    (hx : Commute ⁅x, y⁆ x) (hcube : Commute (x ^ 3) y) :
    ⁅x, y⁆ ^ 3 = 1 := by
  have hpow (n : ℕ) : ⁅x ^ n, y⁆ = ⁅x, y⁆ ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, commutatorElement_mul_left_eq_conj_mul,
        hx.symm.pow_left n |>.eq, mul_inv_cancel_right, ih, ← pow_succ']
  rw [← hpow 3]
  exact hcube.commutator_eq

private theorem commutator_le_zpowers_of_pair {G : Type*} [Group G]
    (x y : G) (hgen : closure ({x, y} : Set G) = ⊤)
    (hx : Commute ⁅x, y⁆ x) (hy : Commute ⁅x, y⁆ y) :
    _root_.commutator G ≤ zpowers ⁅x, y⁆ := by
  have hc := commutator_mem_center_of_pair x y hgen hx hy
  let : (zpowers ⁅x, y⁆).Normal := ⟨fun z hz w => by
    rw [mem_center_iff.mp (zpowers_le.mpr hc hz) w, mul_inv_cancel_right]
    exact hz⟩
  exact derived_le_of_pair x y hgen _ (mem_zpowers _)

end SylowNine

public theorem Cover.not_nine_dvd_card_kernel_of_sylow_nine
    {E G : Type*} [Group E] [Finite E] [Group G] [Finite G]
    (f : Cover E G) (Q : Sylow 3 G) (hQ : Nat.card Q = 9) :
    ¬ 9 ∣ Nat.card f.toMonoidHom.ker := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hQcyc : IsCyclic Q
  · have hcyclic : ∀ Q' : Sylow 3 G, IsCyclic Q' := by
      intro Q'
      exact (MulEquiv.isCyclic (Sylow.equiv Q' Q)).mpr hQcyc
    have hnot : ¬ 3 ∣ Nat.card f.toMonoidHom.ker := by
      exact f.not_dvd_card_multiplier_of_isCyclic_sylow hcyclic
    intro h9
    apply hnot
    exact dvd_trans (by norm_num) h9
  · let : Nontrivial Q := Nontrivial.of_not_isCyclic hQcyc
    obtain ⟨qx, hqx_ne⟩ := exists_ne (1 : Q)
    have hQcomm : IsMulCommutative Q := by
      apply IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3)
      rw [hQ]
      norm_num
    have hqxorder : orderOf qx = 3 := by
      obtain ⟨k, hk⟩ := Q.isPGroup'.exists_orderOf_eq_pow qx
      have hdiv : orderOf qx ∣ 3 ^ 2 := by
        have hdiv' := orderOf_dvd_natCard qx
        change orderOf qx ∣ Nat.card (Q : Subgroup G) at hdiv'
        rw [hQ] at hdiv'
        convert hdiv' using 1
        all_goals norm_num
      obtain ⟨i, hi, hieq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdiv
      have hi0 : i ≠ 0 := by
        intro hi0
        subst i
        exact hqx_ne (orderOf_eq_one_iff.mp (by simpa using hieq))
      have hi2 : i ≠ 2 := by
        intro hi2
        subst i
        apply hQcyc
        exact isCyclic_of_orderOf_eq_card qx (by simpa [hQ] using hieq)
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
      · exact False.elim (hi0 rfl)
      · simpa using hieq
      · exact False.elim (hi2 rfl)
    have hqy_exists : ∃ qy : Q, qy ∉ zpowers qx := by
      by_contra h
      have hall : ∀ qy : Q, qy ∈ zpowers qx := by
        intro qy
        by_contra hqy
        exact h ⟨qy, hqy⟩
      apply hQcyc
      exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨qx, top_unique (fun q _ => hall q)⟩
    obtain ⟨qy, hqy_not⟩ := hqy_exists
    have hqy_ne : qy ≠ 1 := by
      intro hqy1
      apply hqy_not
      simp [hqy1]
    have hqyorder : orderOf qy = 3 := by
      have hdiv : orderOf qy ∣ 3 ^ 2 := by
        have hdiv' := orderOf_dvd_natCard qy
        change orderOf qy ∣ Nat.card (Q : Subgroup G) at hdiv'
        rw [hQ] at hdiv'
        convert hdiv' using 1
        all_goals norm_num
      obtain ⟨i, hi, hieq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdiv
      have hi0 : i ≠ 0 := by
        intro hi0
        subst i
        exact hqy_ne (orderOf_eq_one_iff.mp (by simpa using hieq))
      have hi2 : i ≠ 2 := by
        intro hi2
        subst i
        apply hQcyc
        exact isCyclic_of_orderOf_eq_card qy (by simpa [hQ] using hieq)
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
      · exact False.elim (hi0 rfl)
      · simpa using hieq
      · exact False.elim (hi2 rfl)
    let E0 : Subgroup Q := zpowers qx
    let : IsElementaryAbelian 3 E0 :=
      IsElementaryAbelian.zpowers_of_pow_eq_one (by
        simpa [hqxorder] using (pow_orderOf_eq_one qx))
    have hdis : Disjoint E0 (zpowers qy) :=
      E0.disjoint_zpowers_of_prime_order_not_mem qy hqyorder hqy_not
    have hfix : E0 ≤ centralizer ({qy} : Set Q) := by
      intro z hz
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      exact hQcomm.is_comm.comm z qy
    let J : Subgroup Q := E0 ⊔ zpowers qy
    have hjoincard : Nat.card J = 3 ^ 2 := by
      have h := IsElementaryAbelian.fixed_join_card (p := 3) (n := 1)
        E0 qy hqyorder hdis hfix (by
        rw [Nat.card_zpowers, hqxorder]
        norm_num)
      exact h.2
    have hjoin : J = ⊤ := by
      apply Subgroup.eq_of_le_of_card_ge le_top
      rw [Subgroup.card_top, hQ, hjoincard]
      norm_num
    have hQgen : closure ({qx, qy} : Set Q) = ⊤ := by
      have hxle : E0 ≤ closure ({qx, qy} : Set Q) :=
        zpowers_le.mpr (subset_closure (by simp))
      have hyle : zpowers qy ≤ closure ({qx, qy} : Set Q) :=
        zpowers_le.mpr (subset_closure (by simp))
      apply top_unique
      rw [← hjoin]
      exact sup_le hxle hyle
    obtain ⟨P, hPQ⟩ := Sylow.mapSurjective_surjective f.surjective 3 Q
    have hPmap : (P : Subgroup E).map f.toMonoidHom = (Q : Subgroup G) := by
      rw [← Sylow.coe_mapSurjective f.surjective, hPQ]
    have hqxmap : (qx : G) ∈ (P : Subgroup E).map f.toMonoidHom := by
      rw [hPmap]
      exact qx.2
    have hqymap : (qy : G) ∈ (P : Subgroup E).map f.toMonoidHom := by
      rw [hPmap]
      exact qy.2
    obtain ⟨qxE, hqxP, hfx⟩ := Subgroup.mem_map.mp hqxmap
    obtain ⟨qyE, hqyP, hfy⟩ := Subgroup.mem_map.mp hqymap
    let x : P := ⟨qxE, hqxP⟩
    let y : P := ⟨qyE, hqyP⟩
    have hfx' : f.toMonoidHom x = qx := hfx
    have hfy' : f.toMonoidHom y = qy := hfy
    let : Group.IsPerfect E := f.isPerfect
    have hQgenG : closure ({(qx : G), (qy : G)} : Set G) = (Q : Subgroup G) := by
      have h := congrArg (Subgroup.map (Q : Subgroup G).subtype) hQgen
      have hmaptop : Subgroup.map (Q : Subgroup G).subtype (⊤ : Subgroup Q) =
          (Q : Subgroup G) := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      simpa only [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
        Subgroup.coe_subtype, hmaptop] using h
    have hgenP : closure ({x, y} : Set P) = ⊤ :=
      SylowNine.pair_lifts_generate f.toMonoidHom f.ker_le_center P x y (by
        rw [hfx', hfy', hQgenG, hPmap])
    let c : P := ⁅x, y⁆
    have hc_center : (c : E) ∈ center E := f.ker_le_center (by
      change f.toMonoidHom ⁅(x : E), (y : E)⁆ = 1
      rw [map_commutatorElement, hfx', hfy']
      apply commutatorElement_eq_one_iff_mul_comm.mpr
      exact congrArg Subtype.val (hQcomm.is_comm.comm qx qy))
    have hcx : Commute c x := by
      apply Subtype.ext
      exact (mem_center_iff.mp hc_center x).symm
    have hcy : Commute c y := by
      apply Subtype.ext
      exact (mem_center_iff.mp hc_center y).symm
    have hder : _root_.commutator P ≤ zpowers c :=
      SylowNine.commutator_le_zpowers_of_pair x y hgenP hcx hcy
    have hc3 : c ^ 3 = 1 := by
      apply SylowNine.cube_commutator x y hcx
      apply Subtype.ext
      exact (mem_center_iff.mp (f.ker_le_center (by
        change f.toMonoidHom (x ^ 3) = 1
        rw [map_pow, hfx']
        show (qx : G) ^ 3 = 1
        simpa [hqxorder] using congrArg Subtype.val (pow_orderOf_eq_one qx))) y).symm
    have hcardc : Nat.card (zpowers c) ≤ 3 := by
      rw [Nat.card_zpowers]
      exact (orderOf_le_of_pow_eq_one (by decide) hc3)
    intro h9
    obtain ⟨Z, hZcard⟩ := Sylow.exists_subgroup_card_pow_prime (G := f.toMonoidHom.ker)
      3 (n := 2) h9
    have hZp : IsPGroup 3 Z := IsPGroup.of_card (n := 2) (by simpa using hZcard)
    let R : Subgroup E := Z.map f.toMonoidHom.ker.subtype
    have hRcard : Nat.card R = 9 := by
      dsimp [R]
      rw [Subgroup.card_map_of_injective f.toMonoidHom.ker.subtype_injective]
      simpa using hZcard
    have hRcenter : R ≤ center E := by
      rintro r ⟨z, hz, rfl⟩
      exact f.ker_le_center z.property
    let : R.Normal := ⟨fun z hz g => by
      rw [mem_center_iff.mp (hRcenter hz) g, mul_inv_cancel_right]
      exact hz⟩
    have hRP : R ≤ (P : Subgroup E) :=
      (hZp.map f.toMonoidHom.ker.subtype).le_sylow_of_normal P
    have hRder : R.subgroupOf (P : Subgroup E) ≤ _root_.commutator P := by
      intro z hz
      have hzR : (z : E) ∈ R := Subgroup.mem_subgroupOf.mp hz
      have hzambient := center_inf_commutator_inf_sylow_le_commutator P
        ⟨⟨hRcenter hzR, Group.IsPerfect.mem_commutator⟩, z.property⟩
      rw [← map_subtype_commutator] at hzambient
      obtain ⟨w, hw, hwz⟩ := hzambient
      have : w = z := Subtype.ext hwz
      simpa [this] using hw
    have hRz : R.subgroupOf (P : Subgroup E) ≤ zpowers c := hRder.trans hder
    have hRsubcard : Nat.card (R.subgroupOf (P : Subgroup E)) = 9 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRP).toEquiv, hRcard]
    have hle := Subgroup.card_le_of_le hRz
    rw [hRsubcard] at hle
    have hbad : (9 : ℕ) ≤ 3 := hle.trans hcardc
    omega

end PerfectCentralCovering

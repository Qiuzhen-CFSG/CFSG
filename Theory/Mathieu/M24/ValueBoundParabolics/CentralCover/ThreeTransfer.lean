module

public import Theory.Mathieu.M24.ValueBoundParabolics.CentralCover.ThreeLocalData

/-!
# Excluding a central three-kernel by an inverted Sylow configuration

In a finite perfect central cover, the two generators of the displayed Sylow
three-subgroup lift to generators of a Sylow subgroup `P`: its central kernel
lies in the Frattini subgroup by transfer.

Let `c` be the commutator of these lifts. Its commutators with the two lifts
lie in the central kernel. A lift of the ambient inverter fixes `c` modulo
that kernel and inverts both generators modulo that kernel. It therefore
both fixes and inverts these weight-three commutators. They vanish because
`P` is a three-group, so `P` has cyclic central derived subgroup generated
by `c`. The cube of the first generator is central, giving `c ^ 3 = 1`.
The image of `c` is nonidentity, so the cover is injective on the derived
subgroup. Sylow transfer puts the central kernel in that subgroup, finishing
the proof.

This argument needs no involutory or Sylow-normalizing lift of the inverter:
commutators in a central extension depend only on the images of their inputs.
The conclusion is conditional on the actual local configuration; no concrete
Mathieu witness or multiplier value is assumed or constructed here.

Source application: Aschbacher--Smith, *The Classification of Quasithin
Groups*, E.4.3(2), printed pp.241--242, and the central-cover conventions and
multiplier results I.1.1--I.1.4, printed pp.407--408.
-/
open scoped commutatorElement IsMulCommutative
open Subgroup

namespace PerfectCentralCovering.ThreeTransfer

variable {E G : Type*} [Group E] [Group G]

/-- Central changes of lifts do not change their commutator. -/
private theorem commutator_eq_of_map_eq (f : E →* G)
    (hker : f.ker ≤ center E) {u v x y : E}
    (hu : f u = f v) (hx : f x = f y) : ⁅u, x⁆ = ⁅v, y⁆ := by
  have hleft {a b z : E} (h : f a = f b) : ⁅a, z⁆ = ⁅b, z⁆ := by
    have hk : b⁻¹ * a ∈ center E := hker (by simp [MonoidHom.mem_ker, h])
    have heq : a = b * (b⁻¹ * a) := by simp
    calc
      ⁅a, z⁆ = ⁅b * (b⁻¹ * a), z⁆ := congrArg (fun w => ⁅w, z⁆) heq
      _ = ⁅b, z⁆ := by
        rw [commutatorElement_mul_left_eq_conj_mul,
          commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hk z).symm]
        simp
  calc
    ⁅u, x⁆ = ⁅v, x⁆ := hleft hu
    _ = ⁅x, v⁆⁻¹ := (commutatorElement_inv _ _).symm
    _ = ⁅y, v⁆⁻¹ := congrArg Inv.inv (hleft hx)
    _ = ⁅v, y⁆ := commutatorElement_inv _ _

private theorem commutator_inv_inv_of_commute (a b : G)
    (ha : Commute ⁅a, b⁆ a) (hb : Commute ⁅a, b⁆ b) :
    ⁅a⁻¹, b⁻¹⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_inv_left, commutatorElement_inv_left]
  rw [← hb.inv_right.eq, inv_mul_cancel_right, ← ha.inv_right.eq, inv_mul_cancel_right]

/-- Fixing one input and inverting the other modulo a central kernel
forces their kernel-valued commutator to have square one. -/
private theorem commutator_sq_of_fixed_inverted (f : E →* G)
    (hker : f.ker ≤ center E) (c x t : E)
    (hcx : Commute (f c) (f x))
    (hct : f (t * c * t⁻¹) = f c)
    (hxt : f (t * x * t⁻¹) = f x⁻¹) :
    ⁅c, x⁆ ^ 2 = 1 := by
  have hz : ⁅c, x⁆ ∈ center E := hker (by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact hcx.commutator_eq)
  have ht : t * ⁅c, x⁆ * t⁻¹ = ⁅c, x⁆ := by
    rw [mem_center_iff.mp hz t, mul_inv_cancel_right]
  have hinv : ⁅c, x⁻¹⁆ = ⁅c, x⁆⁻¹ := by
    rw [commutatorElement_inv_right, ← commutatorElement_inv]
    rw [mem_center_iff.mp ((center E).inv_mem hz) x⁻¹, inv_mul_cancel_right]
  have heq : ⁅c, x⁆ = ⁅c, x⁆⁻¹ := by
    calc
      ⁅c, x⁆ = t * ⁅c, x⁆ * t⁻¹ := ht.symm
      _ = ⁅t * c * t⁻¹, t * x * t⁻¹⁆ := conjugate_commutatorElement _ _ _
      _ = ⁅c, x⁻¹⁆ := commutator_eq_of_map_eq f hker hct hxt
      _ = ⁅c, x⁆⁻¹ := hinv
  rw [pow_two]
  calc
    ⁅c, x⁆ * ⁅c, x⁆ = ⁅c, x⁆⁻¹ * ⁅c, x⁆ := congrArg (fun z => z * ⁅c, x⁆) heq
    _ = 1 := inv_mul_cancel _

private theorem commutator_mem_center_of_pair (x y : G)
    (hgen : closure ({x, y} : Set G) = ⊤)
    (hx : Commute ⁅x, y⁆ x) (hy : Commute ⁅x, y⁆ y) :
    ⁅x, y⁆ ∈ center G := by
  have hle : closure ({x, y} : Set G) ≤ centralizer ({⁅x, y⁆} : Set G) := by
    rw [closure_le]
    intro z hz
    rcases hz with rfl | hz
    · exact mem_centralizer_singleton_iff.mpr hx.eq.symm
    · obtain rfl := hz
      exact mem_centralizer_singleton_iff.mpr hy.eq.symm
  rw [hgen] at hle
  exact mem_center_iff.mpr fun z => mem_centralizer_singleton_iff.mp (hle (mem_top z))

private theorem derived_le_of_pair (x y : G)
    (hgen : closure ({x, y} : Set G) = ⊤)
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
    (mul_comm' (⟨a, mem_top a⟩ : (⊤ : Subgroup (G ⧸ N))) ⟨b, mem_top b⟩)⟩⟩

private theorem derived_eq_zpowers_of_pair (x y : G)
    (hgen : closure ({x, y} : Set G) = ⊤)
    (hx : Commute ⁅x, y⁆ x) (hy : Commute ⁅x, y⁆ y) :
    _root_.commutator G = zpowers ⁅x, y⁆ := by
  have hc := commutator_mem_center_of_pair x y hgen hx hy
  let : (zpowers ⁅x, y⁆).Normal := ⟨fun z hz w => by
    rw [mem_center_iff.mp (zpowers_le.mpr hc hz) w, mul_inv_cancel_right]
    exact hz⟩
  exact le_antisymm (derived_le_of_pair x y hgen _ (mem_zpowers _))
    (zpowers_le.mpr (commutator_mem_commutator (mem_top x) (mem_top y)))

private theorem cube_commutator (x y : G) (hx : Commute ⁅x, y⁆ x)
    (hcube : Commute (x ^ 3) y) : ⁅x, y⁆ ^ 3 = 1 := by
  have hpow (n : ℕ) : ⁅x ^ n, y⁆ = ⁅x, y⁆ ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, commutatorElement_mul_left_eq_conj_mul, hx.symm.pow_left n |>.eq,
        mul_inv_cancel_right, ih, ← pow_succ']
  rw [← hpow 3]
  exact hcube.commutator_eq

private theorem pair_lifts_generate [Finite E] [Group.IsPerfect E]
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

private theorem sylow_kernel_eq_bot [Finite E] [Finite G]
    (f : Cover E G) (d : InvertedHeisenbergSylowThree G)
    (P : Sylow 3 E) (hP : (P : Subgroup E).map f.toMonoidHom = d.sylow) :
    f.toMonoidHom.ker.comap (P : Subgroup E).subtype = ⊥ := by
  let := f.isPerfect
  have ha : d.a ∈ (d.sylow : Subgroup G) := d.generate ▸ subset_closure (by simp)
  have hb : d.b ∈ (d.sylow : Subgroup G) := d.generate ▸ subset_closure (by simp)
  obtain ⟨a, haP, hfa⟩ := mem_map.mp (hP ▸ ha)
  obtain ⟨b, hbP, hfb⟩ := mem_map.mp (hP ▸ hb)
  let x : P := ⟨a, haP⟩
  let y : P := ⟨b, hbP⟩
  have hfx : f.toMonoidHom x = d.a := hfa
  have hfy : f.toMonoidHom y = d.b := hfb
  have hgen : closure ({x, y} : Set P) = ⊤ :=
    pair_lifts_generate f.toMonoidHom f.ker_le_center P x y (by rw [hfx, hfy, d.generate, hP])
  -- The lift may be arbitrary: no normalizer or order condition is needed.
  obtain ⟨t, ht⟩ := f.surjective d.inverter
  have hfc : f.toMonoidHom (⁅x, y⁆ : P) = ⁅d.a, d.b⁆ := by
    change f.toMonoidHom ⁅a, b⁆ = _
    rw [map_commutatorElement, hfa, hfb]
  have hct : f.toMonoidHom (t * (⁅x, y⁆ : P) * t⁻¹) = f.toMonoidHom (⁅x, y⁆ : P) := by
    rw [map_mul, map_mul, map_inv, ht, hfc, conjugate_commutatorElement,
      d.conjugate_a, d.conjugate_b]
    exact commutator_inv_inv_of_commute d.a d.b d.commutator_a d.commutator_b
  have hcomm (z : P) (hz : Commute ⁅d.a, d.b⁆ (f.toMonoidHom z))
      (hinv : d.inverter * f.toMonoidHom z * d.inverter⁻¹ = (f.toMonoidHom z)⁻¹) :
      Commute ⁅x, y⁆ z := by
    apply commutatorElement_eq_one_iff_commute.mp
    apply (P.isPGroup'.powEquiv' (n := 2) (by decide)).injective
    change ⁅⁅x, y⁆, z⁆ ^ 2 = (1 : P) ^ 2
    apply Subtype.ext
    change ⁅((⁅x, y⁆ : P) : E), (z : E)⁆ ^ 2 = (1 : E) ^ 2
    rw [one_pow]
    apply commutator_sq_of_fixed_inverted f.toMonoidHom f.ker_le_center _ _ t
    · rwa [hfc]
    · exact hct
    · simpa only [map_mul, map_inv, ht] using hinv
  have hx : Commute ⁅x, y⁆ x := hcomm x
    (by simpa only [hfx] using d.commutator_a)
    (by simpa only [hfx] using d.conjugate_a)
  have hy : Commute ⁅x, y⁆ y := hcomm y
    (by simpa only [hfy] using d.commutator_b)
    (by simpa only [hfy] using d.conjugate_b)
  have hder : _root_.commutator P = zpowers ⁅x, y⁆ :=
    derived_eq_zpowers_of_pair x y hgen hx hy
  have hc3 : (⁅x, y⁆ : P) ^ 3 = 1 := by
    apply cube_commutator x y hx
    have hcube : (x : E) ^ 3 ∈ center E := f.ker_le_center (by
      rw [MonoidHom.mem_ker, map_pow, hfx, d.a_cube])
    exact show x ^ 3 * y = y * x ^ 3 from Subtype.ext (mem_center_iff.mp hcube y).symm
  have ho : orderOf (f.toMonoidHom (⁅x, y⁆ : P)) = 3 := by
    have hd : orderOf (f.toMonoidHom (⁅x, y⁆ : P)) ∣ 3 := orderOf_dvd_of_pow_eq_one (by
      rw [← map_pow]
      change f.toMonoidHom ((⁅x, y⁆ : P) ^ 3 : P) = 1
      rw [hc3]
      exact map_one _)
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with h | h
    · exact False.elim (d.commutator_ne_one (hfc ▸ orderOf_eq_one_iff.mp h))
    · exact h
  apply eq_bot_iff.mpr
  intro z hz
  have hzker : f.toMonoidHom (z : E) = 1 := hz
  -- Perfectness and central Sylow transfer put every kernel element in P′.
  have hzder : (z : E) ∈ ⁅(P : Subgroup E), (P : Subgroup E)⁆ :=
    center_inf_commutator_inf_sylow_le_commutator P
      ⟨⟨f.ker_le_center hz, Group.IsPerfect.mem_commutator⟩, z.property⟩
  rw [← map_subtype_commutator] at hzder
  obtain ⟨w, hw, hwz⟩ := hzder
  have hwz' : w = z := Subtype.ext hwz
  subst w
  rw [hder] at hw
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hw
  have hfn : (f.toMonoidHom (⁅x, y⁆ : P)) ^ n = 1 := by
    rw [← map_zpow]
    change f.toMonoidHom ((⁅x, y⁆ : P) ^ n : P) = 1
    rw [hn]
    exact hzker
  have hdiv := orderOf_dvd_iff_zpow_eq_one.mpr hfn
  rw [ho] at hdiv
  obtain ⟨k, hk⟩ := hdiv
  apply mem_bot.mpr
  rw [← hn, hk, zpow_mul, zpow_natCast, hc3, one_zpow]

end PerfectCentralCovering.ThreeTransfer

namespace PerfectCentralCovering

/-- A finite perfect central cover has no central three-kernel if its quotient
has the published inverted Heisenberg Sylow configuration. -/
public theorem not_three_dvd_kernel_of_invertedHeisenbergSylow
    {E G : Type*} [Group E] [Finite E] [Group G] [Finite G]
    (f : Cover E G) (d : InvertedHeisenbergSylowThree G) :
    ¬ 3 ∣ Nat.card f.toMonoidHom.ker := by
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective f.surjective 3 d.sylow
  have hmap : (P : Subgroup E).map f.toMonoidHom = d.sylow := by
    rw [← Sylow.coe_mapSurjective f.surjective, hP]
  have hbot := ThreeTransfer.sylow_kernel_eq_bot f d P hmap
  intro hthree
  obtain ⟨z, hzorder⟩ := exists_prime_orderOf_dvd_card' 3 hthree
  have hzorderE : orderOf (z : E) = 3 := (Subgroup.orderOf_coe z).trans hzorder
  let Z : Subgroup E := zpowers (z : E)
  have hZcenter : Z ≤ center E := zpowers_le.mpr (f.ker_le_center z.property)
  let : Z.Normal := ⟨fun w hw v => by
    rw [mem_center_iff.mp (hZcenter hw) v, mul_inv_cancel_right]
    exact hw⟩
  have hZthree : IsPGroup 3 Z := by
    apply IsPGroup.of_card (n := 1)
    simp only [Z, Nat.card_zpowers, hzorderE, pow_one]
  have hzP : (z : E) ∈ (P : Subgroup E) := hZthree.le_sylow_of_normal P (mem_zpowers _)
  have hzbot : (⟨z, hzP⟩ : P) ∈ (⊥ : Subgroup P) := by
    rw [← hbot]
    exact z.property
  have hzone : (z : E) = 1 := congrArg Subtype.val (mem_bot.mp hzbot)
  have : (3 : ℕ) = 1 := hzorderE.symm.trans (orderOf_eq_one_iff.mpr hzone)
  norm_num at this

end PerfectCentralCovering

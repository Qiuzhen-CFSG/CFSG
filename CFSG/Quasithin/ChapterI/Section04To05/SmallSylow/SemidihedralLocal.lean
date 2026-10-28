module

public import CFSG.Quasithin.ChapterA.Section01.Fitting.Characteristic
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.SemidihedralCentralizerQuotientGeometry
public import Theory.GroupTheory.SemidihedralOrderFourFusion
public import Theory.GroupTheory.NonsolvableTwoLocal
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Stellmacher.SectionThree.OmegaNormalClosureElementary

/-!
# The central quotient in the semidihedral branch of I.4.3

Even characteristic makes the centralizer of the central Sylow involution
of characteristic two. A.1.8 passes this property to its actual central
quotient. The quarter-order rotation gives a central involution of the
quotient Sylow subgroup, and its normal closure lies in the elementary
center of the quotient two-core. This retains the literal quotient map
needed to lift that closure in the subsequent quaternion argument.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.4.3,
printed pp.416–417. The identification of the lifted quaternion core and
the final GL₂(3) recognition are subsequent to the results here.
-/

namespace CFSG.Quasithin.ChapterI.SemidihedralLocal
open Subgroup Stellmacher Theory.GroupTheory

private theorem omegaCore_normal {X : Type*} [Group X] :
    (omegaOneCenterAmbient (pCore 2 X)).Normal := by
  let Q := pCore 2 X
  let ZQ : Subgroup Q := center Q
  let W : Subgroup ZQ := omega₁ (G := ZQ) (p := 2)
  let E : Subgroup Q := W.map ZQ.subtype
  let _ : ZQ.Characteristic := centerCharacteristic
  let _ : W.Characteristic := omega₁_characteristic ZQ
  let _ : E.Characteristic := characteristic_of_characteristic_of_characteristic
  exact ConjAct.normal_of_characteristic_of_normal

/-- The marked central involution has elementary normal closure inside the
omega-center of the actual two-core. -/
public theorem central_involution_normalClosure
    {X : Type*} [Group X] [Finite X]
    (S : Sylow 2 X) (hc : centralizer (pCore 2 X : Set X) ≤ pCore 2 X)
    (j : S) (hj : orderOf j = 2) (hjZ : j ∈ center S) :
    zpowers (j : X) ≤ omegaOneCenterAmbient (S : Subgroup X) ⊓ pCore 2 X ∧
      normalClosure ({(j : X)} : Set X) ≤ omegaOneCenterAmbient (pCore 2 X) ∧
      IsElementaryAbelian 2 (normalClosure ({(j : X)} : Set X)) := by
  have hQS : pCore 2 X ≤ (S : Subgroup X) := pCore_isPGroup.le_sylow_of_normal S
  have hp : (j : X) ^ 2 = 1 := by
    simpa only [← Subgroup.coe_pow, Subgroup.coe_one, hj] using
      congrArg (fun x : S => (x : X)) (pow_orderOf_eq_one j)
  have hcomm : ∀ q ∈ (S : Subgroup X), q * (j : X) = (j : X) * q := by
    intro q hq
    exact congrArg (fun x : S => (x : X)) (mem_center_iff.mp hjZ ⟨q, hq⟩)
  have hjQ : (j : X) ∈ pCore 2 X := hc (mem_centralizer_iff.mpr
    (fun q hq => hcomm q (hQS hq)))
  have hjOmega : (j : X) ∈ omegaOneCenterAmbient (pCore 2 X) :=
    (mem_omegaOneCenterAmbient_iff _ _).mpr ⟨hjQ, hp, fun q hq => hcomm q (hQS hq)⟩
  let _ : (omegaOneCenterAmbient (pCore 2 X)).Normal := omegaCore_normal
  have hN : normalClosure ({(j : X)} : Set X) ≤ omegaOneCenterAmbient (pCore 2 X) :=
    normalClosure_le_normal (Set.singleton_subset_iff.mpr hjOmega)
  let _ : IsElementaryAbelian 2 (omegaOneCenterAmbient (pCore 2 X)) :=
    omegaOneCenterAmbient_elementaryAbelian _
  exact ⟨zpowers_le.mpr ⟨(mem_omegaOneCenterAmbient_iff _ _).mpr
    ⟨j.property, hp, hcomm⟩, hjQ⟩, hN, IsElementaryAbelian.of_le hN⟩

/-- The actual centralizer quotient in I.4.3 is of characteristic two, and
its marked Sylow-central involution has elementary normal closure. The
semidihedral quotient geometry supplies exactly `S`, `j`, `hj`, and `hjZ`. -/
public theorem centralizer_quotient_normalClosure
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)
    (hE : IsEvenCharacteristicAt T) (z : G) (hz : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (zH : centralizer ({z} : Set G)) (hzH : (zH : G) = z)
    [(zpowers zH).Normal]
    (S : Sylow 2 ((centralizer ({z} : Set G)) ⧸ zpowers zH))
    (j : S) (hj : orderOf j = 2) (hjZ : j ∈ center S) :
    generalizedFitting ((centralizer ({z} : Set G)) ⧸ zpowers zH) =
      pCore 2 ((centralizer ({z} : Set G)) ⧸ zpowers zH) ∧
    zpowers (j : (centralizer ({z} : Set G)) ⧸ zpowers zH) ≤
      omegaOneCenterAmbient (S : Subgroup _) ⊓ pCore 2 _ ∧
    normalClosure ({(j : (centralizer ({z} : Set G)) ⧸ zpowers zH)} : Set _) ≤
      omegaOneCenterAmbient (pCore 2 _) ∧
    IsElementaryAbelian 2
      (normalClosure ({(j : (centralizer ({z} : Set G)) ⧸ zpowers zH)} : Set _)) := by
  have hzcenter : zH ∈ center (centralizer ({z} : Set G)) := by
    apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, hzH] using mem_centralizer_singleton_iff.mp x.property
  have hH : generalizedFitting (centralizer ({z} : Set G)) =
      pCore 2 (centralizer ({z} : Set G)) :=
    (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
      (Chapter1.mem_He_iff.mp (Chapter1.twoLocal_mem_He_of_sylow_le T hE
        (Theory.GroupTheory.isTwoLocal_involution_centralizer hz) hTH))
  have hX := ChapterA.lemma_A_1_8 2 hH (zpowers zH) (zpowers_le.mpr hzcenter)
  exact ⟨hX, central_involution_normalClosure S
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hX) j hj hjZ⟩

/-- The marked dihedral quotient Sylow, together with its elementary central
normal closure, on the original quotient and inclusion. -/
@[expose] public def QuotientSetup
    {T H : Type*} [Group T] [Group H] (n : ℕ) (a : T)
    (ι : T →* H) (zH : H) [(zpowers zH).Normal] : Prop :=
  generalizedFitting (H ⧸ zpowers zH) = pCore 2 (H ⧸ zpowers zH) ∧
  ∃ S : Sylow 2 (H ⧸ zpowers zH),
    (S : Subgroup _) = ((QuotientGroup.mk' (zpowers zH)).comp ι).range ∧
    Nat.card S = 2 ^ (n - 1) ∧
    Nonempty (S ≃* DihedralGroup (2 ^ (n - 2))) ∧
    ∃ j : S, (j : H ⧸ zpowers zH) = QuotientGroup.mk' (zpowers zH)
        (ι (a ^ (2 ^ (n - 3)))) ∧
      orderOf j = 2 ∧ j ∈ center S ∧
      zpowers (j : H ⧸ zpowers zH) ≤
        omegaOneCenterAmbient (S : Subgroup _) ⊓ pCore 2 _ ∧
      normalClosure ({(j : H ⧸ zpowers zH)} : Set _) ≤
        omegaOneCenterAmbient (pCore 2 _) ∧
      IsElementaryAbelian 2 (normalClosure ({(j : H ⧸ zpowers zH)} : Set _))

/-- The original even-characteristic and semidihedral hypotheses construct
all the marked central quotient data used in the source quaternion argument. -/
public theorem quotient_setup
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)
    (hE : IsEvenCharacteristicAt T)
    {n : ℕ} (hn : 4 ≤ n) (hcard : Nat.card T = 2 ^ n)
    (a b : T) (ha : orderOf a = 2 ^ (n - 1)) (hb : orderOf b = 2)
    (hconj : b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1))
    (hgen : closure ({a, b} : Set T) = ⊤) :
    let z : G := (a ^ (2 ^ (n - 2)) : T)
    orderOf z = 2 ∧
      ∃ hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G),
        let H := centralizer ({z} : Set G)
        let zH : H := ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩
        ∃ hZ : (zpowers zH).Normal,
          letI := hZ
          QuotientSetup n a (inclusion hTH) zH := by
  obtain ⟨hz, -, -, -, hTH, _, hZ, hgeo⟩ :=
    semidihedral_centralizer_quotient_geometry T hn hcard a b ha hb hconj hgen
  refine ⟨hz, hTH, hZ, ?_⟩
  obtain ⟨S, hrange, hS, he, j, hjmap, hj, hjZ⟩ := hgeo
  obtain ⟨hX, hmem, hN, hNe⟩ := centralizer_quotient_normalClosure T hE _ hz hTH
    _ rfl S j hj hjZ
  exact ⟨hX, S, hrange, hS, he, j, hjmap, hj, hjZ, hmem, hN, hNe⟩

/-- An elementary normal container for the outer order-four image forces
the semidihedral presentation to have order sixteen. -/
public theorem exponent_parameter_eq_four {T X : Type*} [Group T] [Group X]
    {n : ℕ} (hn : 4 ≤ n) (a b : T)
    (ha : orderOf a = 2 ^ (n - 1))
    (hconj : b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1))
    (f : T →* X) (hh : f (a ^ (2 ^ (n - 2))) = 1)
    (hk : ∀ t : T, f t = 1 → t ^ 2 = 1)
    (V : Subgroup X) [V.Normal] [IsElementaryAbelian 2 V]
    (hab : f (a * b) ∈ V) : n = 4 := by
  have hba : f b * f a * (f b)⁻¹ = (f a)⁻¹ := by
    have h := congrArg f hconj
    simp only [map_mul, map_inv, map_pow] at h
    rw [h]
    apply eq_inv_iff_mul_eq_one.mpr
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ (by decide))]
    simpa only [map_pow] using hh
  have hbai : f b * (f a)⁻¹ * (f b)⁻¹ = f a := by
    have h := congrArg Inv.inv hba
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using h
  have hc : f a * f (a * b) * (f a)⁻¹ * (f (a * b))⁻¹ ∈ V :=
    V.mul_mem (Subgroup.Normal.conj_mem inferInstance _ hab (f a)) (V.inv_mem hab)
  have he : f a * f (a * b) * (f a)⁻¹ * (f (a * b))⁻¹ = (f a) ^ 2 := by
    rw [map_mul]
    calc
      f a * (f a * f b) * (f a)⁻¹ * (f a * f b)⁻¹ =
        f a * f a * (f b * (f a)⁻¹ * (f b)⁻¹) * (f a)⁻¹ := by group
      _ = (f a) ^ 2 := by rw [hbai]; simp only [pow_two]; group
  have hf4 : f (a ^ 4) = 1 := by
    have h := elemPow_eq_one_of_isElementaryAbelian (p := 2) _ (he ▸ hc)
    simpa only [map_pow, ← pow_mul] using h
  have ha8 : a ^ 8 = 1 := by
    have h := hk (a ^ 4) hf4
    simpa only [← pow_mul] using h
  have hd : 2 ^ (n - 1) ∣ 2 ^ 3 := by
    simpa only [ha, show (2 : ℕ) ^ 3 = 8 by decide] using orderOf_dvd_of_pow_eq_one ha8
  have := (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 2)).mp hd
  omega

/-- The semidihedral Sylow subgroup in I.4.3 has order sixteen. Transfer
fuses the two marked order-four elements; their common square places the
conjugator in the literal involution centralizer. -/
public theorem sylow_card_sixteen_of_presentation {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)
    (hE : IsEvenCharacteristicAt T)
    (hno : ∀ K : Subgroup G, K.Normal → K.index ≠ 2)
    {n : ℕ} (hn : 4 ≤ n) (hcard : Nat.card T = 2 ^ n)
    (a b : T) (ha : orderOf a = 2 ^ (n - 1)) (hb : orderOf b = 2)
    (hconj : b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1))
    (hgen : closure ({a, b} : Set T) = ⊤) : Nat.card T = 16 := by
  obtain ⟨hz, hTH, hZ, hdata⟩ := quotient_setup T hE hn hcard a b ha hb hconj hgen
  obtain ⟨_, hsquare, habsquare, _, _⟩ :=
    semidihedral_centralizer_quotient_geometry T hn hcard a b ha hb hconj hgen
  let z : G := (a ^ (2 ^ (n - 2)) : T)
  let H := centralizer ({z} : Set G)
  let zH : H := ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩
  let _ : (zpowers zH).Normal := hZ
  let X := H ⧸ zpowers zH
  let q : H →* X := QuotientGroup.mk' (zpowers zH)
  let ι : T →* H := inclusion hTH
  let f : T →* X := q.comp ι
  obtain ⟨_, S, _, _, _, j, hjmap, _, _, _, _, hV⟩ := hdata
  let V := normalClosure ({(j : X)} : Set X)
  let _ : IsElementaryAbelian 2 V := hV
  have hh : f (a ^ (2 ^ (n - 2))) = 1 := by
    change q zH = 1
    exact (QuotientGroup.eq_one_iff _).mpr (mem_zpowers zH)
  have hk : ∀ t : T, f t = 1 → t ^ 2 = 1 := by
    intro t ht
    have htmem : ι t ∈ zpowers zH := (QuotientGroup.eq_one_iff _).mp ht
    have hzH : orderOf zH = 2 := (Subgroup.orderOf_coe zH).symm.trans hz
    have hp : (ι t) ^ 2 = 1 := by
      apply orderOf_dvd_iff_pow_eq_one.mp
      exact (orderOf_dvd_of_mem_zpowers htmem).trans (by rw [hzH])
    apply inclusion_injective hTH
    simpa only [map_pow, map_one] using hp
  have hjV : f (a ^ (2 ^ (n - 3))) ∈ V := by
    change q (ι _) ∈ V
    rw [← hjmap]
    exact subset_normalClosure (Set.mem_singleton _)
  have hfusion := semidihedral_order_four_generators_isConj hno T n hn hcard
    a b ha hb hconj hgen
  obtain ⟨g, hg⟩ := isConj_iff.mp hfusion
  have hs : g * z * g⁻¹ = z := by
    have h := congrArg (fun t : G => t ^ 2) hg
    rw [conj_pow] at h
    have hj2 : (((a ^ (2 ^ (n - 3))) : T) : G) ^ 2 = z :=
      congrArg (fun t : T => (t : G)) hsquare
    have hab2 : (((a * b) : T) : G) ^ 2 = z :=
      congrArg (fun t : T => (t : G)) habsquare
    simpa only [hj2, hab2] using h
  have hgH : g ∈ H := mem_centralizer_singleton_iff.mpr
    (mul_inv_eq_iff_eq_mul.mp hs)
  let gH : H := ⟨g, hgH⟩
  have hlocal : gH * ι (a ^ (2 ^ (n - 3))) * gH⁻¹ = ι (a * b) := Subtype.ext hg
  have hquot : q gH * f (a ^ (2 ^ (n - 3))) * (q gH)⁻¹ = f (a * b) := by
    simpa only [map_mul, map_inv, f, MonoidHom.comp_apply] using congrArg q hlocal
  have habV : f (a * b) ∈ V := hquot ▸
    Subgroup.Normal.conj_mem inferInstance _ hjV (q gH)
  have hn4 := exponent_parameter_eq_four hn a b ha hconj f hh hk V habV
  simpa only [hn4, show (2 : ℕ) ^ 4 = 16 by decide] using hcard

/-- I.4.3's order bound, stated directly for the semidihedral predicate. -/
public theorem sylow_card_sixteen
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)
    (hE : IsEvenCharacteristicAt T)
    (hno : ∀ K : Subgroup G, K.Normal → K.index ≠ 2)
    (hT : IsSemidihedralGroup T) : Nat.card T = 16 := by
  obtain ⟨n, hn, hc, a, b, ha, hb, hab, hg⟩ := hT
  exact sylow_card_sixteen_of_presentation T hE hno hn hc a b ha hb hab hg

end CFSG.Quasithin.ChapterI.SemidihedralLocal

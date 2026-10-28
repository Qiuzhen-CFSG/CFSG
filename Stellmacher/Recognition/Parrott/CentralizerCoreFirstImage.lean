module

public import Stellmacher.Recognition.Parrott.CentralizerCoreOrientationSeed
public import Stellmacher.Recognition.Parrott.CosetSelection
public import Theory.GroupAction.Order512FiveInvolutionCosets
public import Theory.GroupAction.FivePointOrderFour
/-!
# Orienting the first core image by a power of x

Let H=C_G(z), J=O₂(H), and E be the ambient image of J′. The nonidentity
core cosets with involutory representatives form a five-point orbit. The
stabilizer of aE is the supplied Sylow subgroup: it contains its generators
and has index five. Thus an element outside that Sylow moves aE.

The normalized relations show that x fixes aE and that x² moves dE. Indeed,
if x² fixed dE, then [y,d]=bw and w∈E would give b∈E; [b,x]=a would then
give a∈E, a contradiction. Hence x cycles the other four points, and a
power of x orients the first image to dE while retaining the supplied frame.
The involution and fifth-power seed conditions are included in the interface;
the selection itself only needs the seed's centralizer and Sylow memberships.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.680, the centralizer-generator paragraph.
-/

open Subgroup
open scoped IsMulCommutative
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}
namespace ParrottSylowGeneratorData
variable (f : ParrottSylowGeneratorData n)
set_option maxHeartbeats 1000000 in
/-- A power of the supplied x conjugates an actual outer seed so that its
first core-coset image is dE. No generator or elementary witness is replaced. -/
public theorem core_orientation_first_image_xpow (h : ParrottCentralizerHypotheses z) (r : G)
    (hrH : r ∈ centralizer ({z} : Set G)) (hrT : r ∉ e.sylow)
    (_hr : r ^ 2 = 1) (_hry : (r * f.y) ^ 5 = 1) :
    ∃ i : Fin 4, f.d⁻¹ *
      (((f.x ^ i.val)⁻¹ * r * f.x ^ i.val)⁻¹ * f.a *
        ((f.x ^ i.val)⁻¹ * r * f.x ^ i.val)) ∈
      (commutator (pCore 2 (centralizer ({z} : Set G)))).map
        ((centralizer ({z} : Set G)).subtype.comp
          (pCore 2 (centralizer ({z} : Set G))).subtype) := by
  classical
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let D := commutator J
  let DH := D.map J.subtype
  let E := D.map (H.subtype.comp J.subtype)
  let q := QuotientGroup.mk' DH
  let qJ := QuotientGroup.mk' J
  let qD := QuotientGroup.mk' D
  -- Embed the core abelianization in H/J′ to calculate with the given relations.
  have hker : D = (q.comp J.subtype).ker := by
    ext j
    change j ∈ D ↔ q (j : H) = 1
    rw [show q (j : H) = 1 ↔ (j : H) ∈ DH from QuotientGroup.eq_one_iff _]
    constructor
    · exact mem_map_of_mem J.subtype
    · rintro ⟨k,hk,he⟩
      exact (Subtype.ext he : k = j) ▸ hk
  let ι : (J ⧸ D) →* (H ⧸ DH) := QuotientGroup.lift D (q.comp J.subtype) hker.le
  have hι : Function.Injective ι := (QuotientGroup.injective_lift_iff _ _ _).mpr hker
  have hiq (j : J) : ι (qD j) = q (j : H) := rfl
  obtain ⟨ρ, _hρ, heval⟩ := parrott_core_quotient_action z h
  let : MulDistribMulAction (H ⧸ J) (J ⧸ D) :=
    MulDistribMulAction.compHom (J ⧸ D) ρ
  have hevalQ (g : H) (v : J ⧸ D) :
      ι (qJ g • v) = q g * ι v * (q g)⁻¹ := by
    obtain ⟨j,rfl⟩ := QuotientGroup.mk'_surjective D v
    let k : J := ⟨g * (j : H) * g⁻¹, (inferInstance : J.Normal).conj_mem j j.property g⟩
    change ι (ρ (qJ g) (qD j)) = _
    rw [heval g j k rfl, hiq]
    exact map_mul q (g * (j : H)) g⁻¹ |>.trans (by rw [map_mul, map_inv, hiq])
  have hE (g : H) : q g = 1 ↔ (g : G) ∈ E := by
    change (g : H ⧸ DH) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨j,hj,rfl⟩; exact mem_map_of_mem (H.subtype.comp J.subtype) hj
    · rintro ⟨j,hj,he⟩; exact ⟨j,hj,Subtype.ext he⟩
  obtain ⟨aH,haJ,haeq⟩ := f.core_orientation_mem_core.1
  obtain ⟨dH,hdJ,hdeq⟩ := f.core_orientation_mem_core.2.2.2
  change (aH : G) = f.a at haeq
  change (dH : G) = f.d at hdeq
  let a : J := ⟨aH,haJ⟩
  let d : J := ⟨dH,hdJ⟩
  have haG : (a : G) = f.a := haeq
  have hdG : (d : G) = f.d := hdeq
  have ha2 : a ^ 2 = 1 := by apply Subtype.ext; apply Subtype.ext; simpa [haG] using f.a_sq
  have hd2 : d ^ 2 = 1 := by apply Subtype.ext; apply Subtype.ext; simpa [hdG] using f.d_sq
  have haD : a ∉ D := fun ha => f.core_orientation_not_mem_derived h |>.1
    (haG ▸ mem_map_of_mem (H.subtype.comp J.subtype) ha)
  have hdD : d ∉ D := fun hd => f.core_orientation_not_mem_derived h |>.2
    (hdG ▸ mem_map_of_mem (H.subtype.comp J.subtype) hd)
  let qa := qD a
  let qd := qD d
  have hOcard : (MulAction.orbit (H ⧸ J) qa).ncard = 5 := by
    change (Set.range (fun g => ρ g (QuotientGroup.mk' D a))).ncard = 5
    rw [← centralizer_index_eq_subgroup_quotient_orbit_card J D ρ heval a]
    apply parrott_core_involution_coset_centralizer_index z h aH haJ
    · apply orderOf_eq_prime_iff.mpr
      refine ⟨congrArg (fun j : J => (j : H)) ha2, ?_⟩
      intro hh
      exact haD (show a ∈ D from (show a = 1 from Subtype.ext hh) ▸ one_mem D)
    · intro hh
      obtain ⟨j,hj,hja⟩ := hh
      exact haD ((show j = a from Subtype.ext hja) ▸ hj)
  -- The involution census puts dE in the same five-point orbit as aE.
  obtain ⟨P, hPfixed⟩ := h.five_centralizer
  have hPcard : Nat.card P = 5 := by
    rw [P.card_eq_multiplicity, (h.card_and_solvable z).1]
    decide +kernel
  let : MulDistribMulAction P J :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (P : Subgroup H) J
      (Subgroup.le_normalizer_of_normal (H := J))
  have hfixed : FixedPoints.subgroup P J ≤ center J := by
    intro j hj
    apply hPfixed
    change (j : H) ∈ centralizer (P : Set H)
    intro g hg
    have hh := congrArg (fun j : J => (j : H)) (hj ⟨g,hg⟩)
    exact mul_inv_eq_iff_eq_mul.mp hh
  obtain ⟨p,hp⟩ := (Theory.GroupAction.parrott_involutory_derived_coset_census
    pCore_isPGroup h.core_card h.core_class hPcard hfixed d hd2 hdD).2 a ha2 haD
  have hdO : qd ∈ MulAction.orbit (H ⧸ J) qa := by
    refine ⟨qJ (p : H), ?_⟩
    change ρ (qJ (p : H)) (qD a) = qD d
    rw [heval (p : H) a (p • a) rfl]
    exact hp
  let xH : H := ⟨f.x, e.sylow_le_centralizer f.local_mem_sylow.2.2.2.2.2.2.2.2.2.1⟩
  let yH : H := ⟨f.y, e.sylow_le_centralizer f.local_mem_sylow.2.2.2.2.2.2.2.2.2.2⟩
  let bH : H := ⟨f.b, e.sylow_le_centralizer f.local_mem_sylow.2.2.2.2.2.2.1⟩
  let wH : H := ⟨f.w, e.sylow_le_centralizer f.local_mem_sylow.2.2.2.2.1⟩
  let zH : H := ⟨z, e.sylow_le_centralizer f.local_mem_sylow.1⟩
  have hx4 : xH ^ 4 = 1 := Subtype.ext f.eq01_x
  have hxa : Commute xH aH := by
    apply Subtype.ext
    change f.x * (aH : G) = (aH : G) * f.x
    rw [haeq]
    exact ((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq16_ax).symm.eq
  have hxfix : qJ xH • qa = qa := by
    apply hι
    rw [hevalQ, hiq]
    rw [← map_mul, ← map_inv, ← map_mul, hxa.eq]
    simp [a]
  -- The full stabilizer pulls back to the literal supplied Sylow subgroup.
  let S : Subgroup H := (MulAction.stabilizer (H ⧸ J) qa).comap qJ
  have hSidx : S.index = 5 := by
    dsimp only [S]
    rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective J),
      MulAction.index_stabilizer]
    exact hOcard
  have hScard : Nat.card S = 2048 := by
    have hh := S.index_mul_card
    rw [hSidx, (h.card_and_solvable z).1] at hh
    omega
  have hJS : J ≤ S := by
    intro j hj
    change qJ j • qa = qa
    rw [show qJ j = 1 from (QuotientGroup.eq_one_iff j).mpr hj, one_smul]
  have hTS : (e.sylow : Subgroup G) = S.map H.subtype := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [← f.sylow_generators]
      rw [closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl
      · exact ⟨xH, hxfix, rfl⟩
      all_goals
        apply (Subgroup.map_mono hJS)
      · exact f.core_orientation_mem_core.1
      · exact f.core_orientation_mem_core.2.1
      · exact f.core_orientation_mem_core.2.2.1
      · exact f.core_orientation_mem_core.2.2.2
    · rw [Subgroup.card_map_of_injective H.subtype_injective, hScard, e.sylow_card h]
  let rH : H := ⟨r,hrH⟩
  have hrmove : qJ rH⁻¹ • qa ≠ qa := by
    intro hh
    have hm : rH⁻¹ ∈ S := hh
    apply hrT
    change r ∈ (e.sylow : Subgroup G)
    rw [hTS]
    simpa only [inv_inv, rH, Subgroup.subtype_apply] using
      mem_map_of_mem H.subtype (S.inv_mem hm)
  -- Relations (4), (17), and (18) force x² to move dE.
  have hzq : q zH = 1 := (hE zH).mpr f.core_orientation_mem_derived.1
  have hwq : q wH = 1 := (hE wH).mpr f.core_orientation_mem_derived.2.2.2.2
  have hx2 : (q xH)^2 = q yH := by
    have hh : xH^2 = yH * zH := Subtype.ext f.eq04
    rw [← map_pow, hh, map_mul, hzq, mul_one]
  have hbx : Tits.parrottCommutator (q bH) (q xH) = q aH := by
    have hh : Tits.parrottCommutator bH xH = aH := Subtype.ext (f.eq18_bx.trans haeq.symm)
    simpa only [Tits.parrottCommutator, map_mul, map_inv] using congrArg q hh
  have hyd : Tits.parrottCommutator (q yH) (q dH) = q bH := by
    have hh : Tits.parrottCommutator yH dH = bH*wH := by
      apply Subtype.ext
      change Tits.parrottCommutator f.y (dH : G) = f.b*f.w
      rw [hdeq]
      exact f.eq17_yd
    simpa only [Tits.parrottCommutator, map_mul, map_inv, hwq, mul_one] using congrArg q hh
  have hx2move : (qJ xH)^2 • qd ≠ qd := by
    intro hh
    have he := congrArg ι hh
    rw [← map_pow, hevalQ, hiq, map_pow, hx2] at he
    have hc : Commute (q yH) (q dH) := mul_inv_eq_iff_eq_mul.mp he
    have hbq : q bH = 1 := hyd.symm.trans ((Tits.parrottCommutator_eq_one_iff _ _).mpr hc)
    have haq : q aH = 1 := by
      rw [← hbx, hbq]
      simp [Tits.parrottCommutator]
    exact f.core_orientation_not_mem_derived h |>.1 (haeq ▸ (hE aH).mp haq)
  -- On five points this makes x a four-cycle off its fixed point aE.
  let O := MulAction.orbit (H ⧸ J) qa
  let root : O := ⟨qa, MulAction.mem_orbit_self _⟩
  let left : O := ⟨qJ rH⁻¹ • qa, MulAction.mem_orbit _ _⟩
  let right : O := ⟨qd,hdO⟩
  let π := MulAction.toPermHom (H ⧸ J) O
  let p := π (qJ xH⁻¹)
  have hp4 : p^4 = 1 := by
    rw [← map_pow, ← map_pow, inv_pow, hx4, inv_one, map_one, map_one]
  have hroot : p root = root := by
    apply Subtype.ext
    change qJ xH⁻¹ • qa = qa
    rw [map_inv, inv_smul_eq_iff, hxfix]
  have hp2 : p^2 ≠ 1 := by
    intro hh
    change (π (qJ xH⁻¹))^2 = 1 at hh
    rw [← map_pow] at hh
    have he := congrArg (fun k : Equiv.Perm O => (k right : J ⧸ D)) hh
    change (qJ xH⁻¹)^2 • qd = qd at he
    rw [map_inv, inv_pow, inv_smul_eq_iff] at he
    exact hx2move he.symm
  have hright : right ≠ root := by
    intro hh
    have he : qd = qa := congrArg Subtype.val hh
    apply hx2move
    rw [he, pow_two, mul_smul, hxfix, hxfix]
  obtain ⟨i,hi⟩ := Equiv.Perm.exists_pow_apply_eq_of_order_four_card_five
    (show Nat.card O = 5 from hOcard) p hp4 hp2 hroot
    (show left ≠ root from fun hh => hrmove (congrArg Subtype.val hh)) hright
  have hpow (m : ℕ) : (qJ xH)^m • qa = qa := by
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, mul_smul, hxfix, ih]
  let kH := xH^i.val
  let sH := kH⁻¹ * rH * kH
  have hsimage : qJ sH⁻¹ • qa = qd := by
    change (π (qJ xH⁻¹)^i.val) left = right at hi
    rw [← map_pow] at hi
    have hi' := congrArg (fun v : O => (v : J ⧸ D)) hi
    change (qJ xH⁻¹)^i.val • (qJ rH⁻¹ • qa) = qd at hi'
    change qJ (kH⁻¹ * rH * kH)⁻¹ • qa = qd
    simp only [mul_inv_rev, inv_inv, map_mul, map_inv, mul_smul]
    have hkfix : qJ kH • qa = qa := by rw [map_pow]; exact hpow i.val
    rw [hkfix]
    simpa only [kH, map_pow, map_inv, inv_pow] using hi'
  -- Return from the quotient action to ambient derived-core membership.
  have hsQ := congrArg ι hsimage
  rw [hevalQ, hiq, hiq, map_inv, inv_inv] at hsQ
  refine ⟨i, ?_⟩
  have hh : q (dH⁻¹ * (sH⁻¹ * aH * sH)) = 1 := by
    simp only [map_mul, map_inv]
    rw [hsQ, inv_mul_cancel]
  have hm := (hE _).mp hh
  change (dH : G)⁻¹ * ((sH : G)⁻¹ * (aH : G) * (sH : G)) ∈ E at hm
  simpa only [sH, kH, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow,
    xH, rH, haeq, hdeq] using hm
end ParrottSylowGeneratorData
end Stellmacher.Recognition

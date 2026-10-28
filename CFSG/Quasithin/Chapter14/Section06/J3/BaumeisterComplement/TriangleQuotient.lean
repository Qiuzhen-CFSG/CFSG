module
public import CFSG.Quasithin.Chapter14.Section06.J3.BaumeisterComplement.PointCore

/-!
# The literal third parabolic covers the involution-centralizer quotient

The point centralizer has image of order twelve in C_G(f)/O₂(C_G(f)).
The pair centralizer contains an element inverting the same cubic. Such
an element cannot lie in that image: in A₄ × C₂ a nontrivial cubic cannot
be inverted even modulo the central involution. The index-five point
image and the inverter therefore generate the whole A₅ quotient.

The application uses the actual L₃ = ⟨C_{L₁}(f), C_{L₂}(f)⟩, the original
field embedding and the literal quotient map. This proves quotient
surjectivity, not the missing assertion that L₃ meets Q_f only in ⟨f⟩.

Source: Baumeister, A geometry for groups of J₃-type (2007), Lemma 2.6,
pp.496–497; this separates its quotient generation from complement alignment.
-/

open Subgroup
namespace CFSG.Quasithin.Janko23.J3Recognition.Ambient.BaumeisterComplement
public noncomputable section
private theorem four_no_inversion_mod_two
    (s x : alternatingGroup (Fin 4) × Multiplicative (ZMod 2))
    (hs : s^3=1) (hxs : (x*s*x⁻¹*s)^2=1) : s=1 := by
  revert s x
  decide +kernel

/-- An A₄ × C₂ subgroup meeting the kernel in its central involution,
together with an element inverting its cubic, maps onto the A₅ quotient. -/
theorem alternating_quotient_generated {H : Type*} [Group H] [Finite H]
    (Q X L : Subgroup H) [Q.Normal]
    (eQ : (H ⧸ Q) ≃* alternatingGroup (Fin 5))
    (eX : X ≃* (alternatingGroup (Fin 4) × Multiplicative (ZMod 2)))
    (z s r : H) (hz : orderOf z = 2) (hs : orderOf s = 3)
    (hXQ : X ⊓ Q = zpowers z) (hsX : s ∈ X)
    (hXL : X ≤ L) (hrL : r ∈ L) (hrs : r*s*r⁻¹=s⁻¹) :
    L.map (QuotientGroup.mk' Q) = ⊤ := by
  let q := QuotientGroup.mk' Q
  have hX : Nat.card X = 24 := by
    rw [Nat.card_congr eX.toEquiv,Nat.card_prod,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hk : Nat.card (q.ker.subgroupOf X) = 2 := by
    rw [←card_map_of_injective X.subtype_injective,subgroupOf_map_subtype,
      QuotientGroup.ker_mk',inf_comm,hXQ,Nat.card_zpowers,hz]
  have hXi : Nat.card (X.map q) = 12 := by
    have hh := (q.ker.subgroupOf X).index_mul_card
    change q.ker.relIndex X * Nat.card (q.ker.subgroupOf X) = Nat.card X at hh
    rw [hk,hX,relIndex_ker] at hh
    omega
  have hrout : q r ∉ X.map q := by
    rintro ⟨x,hx,hqx⟩
    let t := x*s*x⁻¹*s
    have htX : t ∈ X := X.mul_mem (X.mul_mem (X.mul_mem hx hsX) (X.inv_mem hx)) hsX
    have htQ : t ∈ Q := (QuotientGroup.eq_one_iff t).mp (by
      change q t=1
      dsimp only [t]
      rw [map_mul,map_mul,map_mul,map_inv,hqx,←map_inv,←map_mul,←map_mul,hrs,
        map_inv,inv_mul_cancel])
    have htZ : t ∈ zpowers z := hXQ ▸ ⟨htX,htQ⟩
    have ht2 : t^2=1 := orderOf_dvd_iff_pow_eq_one.mp (by
      simpa only [hz] using orderOf_dvd_of_mem_zpowers htZ)
    have htX2 : ((⟨x,hx⟩ : X) * ⟨s,hsX⟩ * (⟨x,hx⟩ : X)⁻¹ * ⟨s,hsX⟩)^2=1 :=
      Subtype.ext ht2
    have he := four_no_inversion_mod_two (eX ⟨s,hsX⟩) (eX ⟨x,hx⟩)
      (by rw [←map_pow]; exact (congrArg eX (Subtype.ext (hs ▸ pow_orderOf_eq_one s))).trans (map_one _))
      (by simpa only [map_mul,map_inv,map_pow,map_one] using congrArg eX htX2)
    have hs1 : s=1 := congrArg Subtype.val (eX.injective (he.trans (map_one _).symm))
    simp [hs1] at hs
  have hquot : Nat.card (H ⧸ Q) = 60 := by
    rw [Nat.card_congr eQ.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hle : X.map q ≤ L.map q := map_mono hXL
  have hidx : (X.map q).index = 5 := by
    have hh := (X.map q).card_mul_index
    rw [hXi,hquot] at hh
    omega
  have hd : (L.map q).index ∣ 5 := hidx ▸ index_dvd_of_le hle
  rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd with h1 | h5
  · exact index_eq_one.mp h1
  · have h12 : Nat.card (L.map q)=12 := by
      have hh := (L.map q).card_mul_index
      rw [h5,hquot] at hh
      omega
    have he := eq_of_le_of_card_ge hle (by rw [hXi,h12])
    exact (hrout (he.symm ▸ mem_map_of_mem q hrL)).elim

/-- Fusion transports the literal two-core quotient to A₅. -/
theorem involution_twoCore_quotient {G : Type*} [Group G] [Finite G]
    {z : G} (h : HTypeAt z) (hc : OneInvolutionClass G) (f : G) (hf : orderOf f=2) :
    Nonempty ((involutionCentralizer f ⧸ pCore 2 (involutionCentralizer f)) ≃*
      alternatingGroup (Fin 5)) := by
  obtain ⟨g,hg⟩ := isConj_iff.mp (hc.isConj h.involution hf)
  let c := MulAut.conj g
  have hcz : c f = z := hg
  let e : involutionCentralizer f ≃* involutionCentralizer z :=
    (Theory.GroupTheory.CentralizerSmallKernelTransport.centralizerEquiv c f).trans
      (MulEquiv.subgroupCongr (by rw [hcz]))
  exact ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    ((QuotientGroup.quotientMulEquivOfEq h.core_eq_pCore.symm).trans h.quotient_equiv.some)⟩

open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.SingerField hiding normalizer
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics
variable {G : Type*} [Group G] [Finite G]

private theorem pair_cubic_inverter
    (s : Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)) (hs : s^3=1) :
    ∃ r : Equiv.Perm (Fin 3) × Multiplicative (ZMod 2), r*s*r⁻¹=s⁻¹ := by
  revert s
  decide +kernel

/-- The actual third parabolic covers the whole A₅ quotient of C_G(f).
The quotient is by the literal O₂(C_G(f)); no complement is assumed. -/
theorem field_third_quotient {D : LocalSixteen.Seed G}
    (P : LocalSixteen.ReturningPair D) (hc : OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) (hAR : A ≤ P.R)
    (j : Model →* G) (hj : Function.Injective j) :
    let f := j fieldElement
    let C := involutionCentralizer f
    ((Seventeen.third j.range (overlap j) f).subgroupOf C).map
      (QuotientGroup.mk' (pCore 2 C)) = ⊤ := by
  let f := j fieldElement
  let s := j cubic
  let C := involutionCentralizer f
  let X := j.range ⊓ C
  let L := Seventeen.third j.range (overlap j) f
  have hf : orderOf f=2 := image_involution_order j hj
  have hs : orderOf s=3 := (orderOf_injective j hj cubic).trans cubic_order
  have hsf : Commute s f := (cubic_commutes_complement
    ⟨fieldElement,(mem_pointComplement _).mpr rfl⟩).map j
  obtain ⟨e2⟩ := field_pair_equiv P hc A hA hAR j hj
  let Y := Seventeen.second (overlap j) ⊓ C
  let eY : Y ≃* (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)) :=
    BaumeisterParabolics.pair_centralizer_equiv j hj e2
  let sY : Y := ⟨s,⟨(overlap j).le_normalizer (mem_map_of_mem j cubic_mem),
    mem_centralizer_singleton_iff.mpr hsf.eq⟩⟩
  obtain ⟨r0,hr0⟩ := pair_cubic_inverter (eY sY) (by
    rw [←map_pow]
    exact (congrArg eY (Subtype.ext (hs ▸ pow_orderOf_eq_one s))).trans (map_one _))
  let rY := eY.symm r0
  let r : G := rY.val
  have hrC : r ∈ C := rY.property.2
  have hrs : r*s*r⁻¹=s⁻¹ := congrArg Subtype.val (eY.injective
    (show eY (rY*sY*rY⁻¹) = eY (sY⁻¹) from by
      simpa only [rY,map_mul,map_inv,eY.apply_symm_apply] using hr0))
  let fC : C := ⟨f,mem_centralizer_singleton_iff.mpr rfl⟩
  let sC : C := ⟨s,mem_centralizer_singleton_iff.mpr hsf.eq⟩
  let rC : C := ⟨r,hrC⟩
  obtain ⟨eQ⟩ := involution_twoCore_quotient D.localType hc f hf
  let eX := (subgroupOfEquivOfLe (show X ≤ C from inf_le_right)).trans
    (PointCentralizer.imagePointCentralizerEquiv j hj)
  have hXQ : X.subgroupOf C ⊓ pCore 2 C = zpowers fC := by
    apply map_injective C.subtype_injective
    rw [map_inf _ _ _ C.subtype_injective,map_subgroupOf_eq_of_le inf_le_right,
      MonoidHom.map_zpowers]
    exact field_point_centralizer_core D.localType hc j hj
  exact alternating_quotient_generated (pCore 2 C) (X.subgroupOf C) (L.subgroupOf C)
    eQ eX fC sC rC ((orderOf_coe fC).symm.trans hf) ((orderOf_coe sC).symm.trans hs)
    hXQ ⟨⟨cubic,rfl⟩,sC.property⟩ (fun _ hx => (le_sup_left : X ≤ L) hx)
    (show r ∈ L from (le_sup_right : Y ≤ L) rY.property) (Subtype.ext hrs)


end
end CFSG.Quasithin.Janko23.J3Recognition.Ambient.BaumeisterComplement

module
public import CFSG.Quasithin.Chapter14.Section06.J3.BaumeisterComplement.CubicSplitting
public import Theory.SpecificGroups.PGL2.InvolutionCentralizerBound

/-!
# The two cubic fusion classes in Baumeister 2.4

An involutory inverter of the chosen cubic maps outside the derived A₆ in
its literal PGL₂(9) normalizer quotient. The centralizer of such an outer
involution has no factor three. Consequently an independent commuting
cubic inverted by an involution centralizing the original cubic cannot
be conjugate to the original cubic. Cubics centralizing involutions are
conjugate by the original H-type and one-class hypotheses. These facts
prove the source nonfusion comparison from its precise involution actors.

The actors are constructed in `PlaneActors`; `Source` discharges their
premises on the same cubic in the actual plane complement.
Source: Baumeister, A geometry for groups of J₃-type (2007), Lemma 2.4,
printed pp.495–496.
-/


open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Janko23.J3Recognition.Ambient.BaumeisterComplement
public noncomputable section
open GorensteinWalter

private theorem pgl_nine_outer_centralizer_not_three
    (t : PGL2 Atlas.Comparisons.Exceptional.Nine.F) (ht : IsInvolution t)
    (hout : t ∉ _root_.commutator (PGL2 Atlas.Comparisons.Exceptional.Nine.F)) :
    ¬ 3 ∣ Nat.card (centralizer ({t} : Set _)) := by
  let F := Atlas.Comparisons.Exceptional.Nine.F
  let : Finite (PGL2 F) := Finite.of_surjective Matrix.ProjGenLinGroup.mk
    Matrix.ProjGenLinGroup.mk_surjective
  have hF : Nat.card F = 9 := Atlas.Comparisons.Exceptional.Nine.card
  have hodd : IsOddPrimePower (Nat.card F) := ⟨3,2,by decide,by decide,by decide,hF⟩
  let P : Sylow 2 (PGL2 F) := Classical.choice inferInstance
  obtain ⟨m,_,⟨eP⟩⟩ := pgl2_odd_hasDihedralSylowTwo_model F hodd P
  obtain ⟨D⟩ := pgl2_low_reflected_tori_card_four F hodd (by omega) P eP
  have hJ := pgl2_commutator_eq_psl2_range_of_card_gt_three F hodd (by omega)
  obtain ⟨g,hg⟩ := isConj_iff.mp (pgl2_outer_involutions_conjugate_of_odd_prime_power
    F hodd D.s_involution ht (hJ ▸ D.s_not_mem_commutator) (hJ ▸ hout))
  have heq : (centralizer ({D.s} : Set (PGL2 F))).map (MulAut.conj g).toMonoidHom =
      centralizer ({t} : Set (PGL2 F)) := by
    rw [map_centralizer_equiv,Set.image_singleton]
    change centralizer ({g * D.s * g⁻¹} : Set (PGL2 F)) = _
    rw [hg]
  rw [← heq,card_map_of_injective (MulAut.conj g).injective,D.centralizer_eq]
  have hn : zpowers D.w ≤ normalizer (D.U : Set (PGL2 F)) := by
    apply zpowers_le.mpr
    apply mem_normalizer_iff.mpr
    intro u
    constructor
    · intro hu
      rw [D.w_inverts_U u hu]
      exact D.U.inv_mem hu
    · intro hu
      have hh := D.U.inv_mem hu
      have hiw : D.w⁻¹ = D.w := inv_eq_of_mul_eq_one_right D.w_involution
      rw [← D.w_inverts_U _ hu,hiw] at hh
      have he : D.w * (D.w * u * D.w) * D.w = u := by
        calc
          _ = (D.w * D.w) * u * (D.w * D.w) := by group
          _ = u := by rw [D.w_involution]; simp
      rwa [he] at hh
  have hw : orderOf D.w = 2 := orderOf_eq_prime
    (by simpa only [pow_two] using D.w_involution)
    (fun he => D.w_not_mem_U (he ▸ D.U.one_mem))
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes D.U (zpowers D.w) hn
  rw [Nat.card_zpowers,hw] at hprod
  intro hthree
  have hd : 3 ∣ Nat.card D.U * 2 := by
    rw [hprod]
    exact dvd_mul_of_dvd_right hthree _
  rcases D.U_card with h | h <;> rw [h,hF] at hd <;> norm_num at hd

variable {G : Type*} [Group G] [Finite G]

theorem inverter_centralized_cubic_mem_kernel {D : LocalSixteen.Seed G}
    (P : LocalSixteen.ReturningPair D) (hc : OneInvolutionClass G)
    (s : G) (hs : orderOf s = 3)
    (e : (centralizer ({s} : Set G) ⧸ cubicKernel s) ≃* alternatingGroup (Fin 6))
    (r : normalizer (zpowers s : Set G)) (hr : orderOf r = 2)
    (hri : (r : G) * s * (r : G)⁻¹ = s⁻¹)
    (u : centralizer ({s} : Set G)) (hu : orderOf u = 3)
    (hru : Commute (r : G) (u : G)) : u ∈ cubicKernel s := by
  obtain ⟨eQ⟩ := cubic_normalizer_quotient_pgl_nine P hc s hs e
  let N := normalizer (zpowers s : Set G)
  let q := QuotientGroup.mk' (cubicNormalizerKernel s)
  let uN : N := ⟨u,cubic_centralizer_le_normalizer s u.property⟩
  have hp : IsPGroup 3 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact IsPGroup.of_card (n := 1) (by simpa using cubicNormalizerKernel_card s hs)
  have hrq : orderOf (eQ (q r)) = 2 := by
    rw [eQ.orderOf_eq,q.orderOf_map_eq_of_coprime_of_isPGroup_ker hp r (by rw [hr]; decide),hr]
  have hro : eQ (q r) ∉ _root_.commutator (PGL2 Atlas.Comparisons.Exceptional.Nine.F) := by
    intro hh
    have hh' : q r ∈ _root_.commutator (N ⧸ cubicNormalizerKernel s) := by
      have hm : (_root_.commutator (N ⧸ cubicNormalizerKernel s)).map eQ.toMonoidHom =
          _root_.commutator (PGL2 Atlas.Comparisons.Exceptional.Nine.F) := by
        rw [map_commutator_eq,MonoidHom.range_eq_top.mpr eQ.surjective]
        rfl
      rw [← hm] at hh
      simpa only [eQ.symm_apply_apply] using mem_map_equiv.mp hh
    rw [cubic_normalizer_quotient_commutator D.localType hc s hs e,
      cubicQuotientInclusion_preimage] at hh'
    have he : s = s⁻¹ := by
      rw [mem_centralizer_singleton_iff.mp hh',mul_inv_cancel_right] at hri
      exact hri
    have hh2 : s ^ 2 = 1 := by
      rw [pow_two]
      nth_rw 1 [he]
      exact inv_mul_cancel s
    have hd := orderOf_dvd_of_pow_eq_one hh2
    norm_num [hs] at hd
  by_contra hout
  have huq : orderOf (eQ (q uN)) = 3 := by
    apply orderOf_eq_prime
    · rw [← map_pow,← map_pow]
      have hpowU : u ^ 3 = 1 := hu ▸ pow_orderOf_eq_one u
      have hpow : uN ^ 3 = 1 := Subtype.ext (congrArg (fun x : centralizer ({s} : Set G) => (x : G)) hpowU)
      rw [hpow,map_one,map_one]
    · intro hh
      exact hout ((QuotientGroup.eq_one_iff uN).mp ((eQ.map_eq_one_iff).mp hh))
  have hcomm : Commute (eQ (q uN)) (eQ (q r)) := by
    apply Commute.map
    apply Commute.map
    exact Subtype.ext hru.symm.eq
  let uC : centralizer ({eQ (q r)} : Set _) :=
    ⟨eQ (q uN),mem_centralizer_singleton_iff.mpr hcomm.eq⟩
  have hd : 3 ∣ Nat.card (centralizer ({eQ (q r)} : Set _)) := by
    have huc : orderOf uC = 3 := (orderOf_coe uC).symm.trans huq
    have hd' := _root_.orderOf_dvd_natCard uC
    rwa [huc] at hd'
  exact pgl_nine_outer_centralizer_not_three (eQ (q r))
    ⟨by intro hh; simp [hh] at hrq,by simpa only [hrq] using pow_orderOf_eq_one (eQ (q r))⟩ hro hd

theorem cubic_not_conjugate_of_inverter {D : LocalSixteen.Seed G}
    (P : LocalSixteen.ReturningPair D) (hc : OneInvolutionClass G)
    (s : G) (hs : orderOf s = 3)
    (e : (centralizer ({s} : Set G) ⧸ cubicKernel s) ≃* alternatingGroup (Fin 6))
    (σ : centralizer ({s} : Set G)) (hσ : orderOf σ = 3) (hout : σ ∉ cubicKernel s)
    (r : G) (hr : orderOf r = 2) (hrs : Commute r s)
    (hri : r * (σ : G) * r⁻¹ = (σ : G)⁻¹) : ¬ IsConj (σ : G) s := by
  rintro ⟨g,hg⟩
  have hg' : (g : G) * (σ : G) * (g : G)⁻¹ = s := mul_inv_eq_iff_eq_mul.mpr hg
  let a := MulAut.conj (g : G)
  have haσ : a σ = s := hg'
  have has : a s ∈ centralizer ({s} : Set G) := by
    have hcomm : Commute s (σ : G) := (mem_centralizer_singleton_iff.mp σ.property).symm
    apply mem_centralizer_singleton_iff.mpr
    simpa only [MulEquiv.coe_toMonoidHom,haσ] using (hcomm.map a.toMonoidHom).eq
  have har : a r * s * (a r)⁻¹ = s⁻¹ := by
    rw [← haσ,← map_inv,← map_mul,← map_mul,hri,map_inv]
  have hrN : a r ∈ normalizer (zpowers s : Set G) := by
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · rintro ⟨n,rfl⟩
      change a r * s ^ n * (a r)⁻¹ ∈ zpowers s
      rw [← conj_zpow,har]
      exact zpow_mem (inv_mem (mem_zpowers s)) n
    · intro hx
      have harinv : (a r)⁻¹ = a r := inv_eq_of_mul_eq_one_left (by
        rw [← pow_two,← map_pow]
        have hr2 : r ^ 2 = 1 := hr ▸ pow_orderOf_eq_one r
        rw [hr2,map_one])
      have hh : a r * (a r * x * (a r)⁻¹) * (a r)⁻¹ ∈ zpowers s := by
        obtain ⟨n,hn⟩ := hx
        rw [← hn]
        change a r * s ^ n * (a r)⁻¹ ∈ zpowers s
        rw [← conj_zpow,har]
        exact zpow_mem (inv_mem (mem_zpowers s)) n
      have he : a r * (a r * x * (a r)⁻¹) * (a r)⁻¹ = x := by
        have hh2 : a r * a r = 1 := by
          calc
            _ = a r * (a r)⁻¹ := by rw [harinv]
            _ = 1 := mul_inv_cancel _
        rw [harinv]
        calc
          _ = (a r * a r) * x * (a r * a r) := by group
          _ = x := by rw [hh2]; simp
      rwa [he] at hh
  have hmem := inverter_centralized_cubic_mem_kernel P hc s hs e
    ⟨a r,hrN⟩ ((orderOf_coe _).symm.trans ((a.orderOf_eq r).trans hr)) har
    ⟨a s,has⟩ ((orderOf_coe _).symm.trans ((a.orderOf_eq s).trans hs))
    (hrs.map a.toMonoidHom)
  have hss : s ∈ zpowers (σ : G) := by
    change a s ∈ zpowers s at hmem
    have hz : zpowers s = (zpowers (σ : G)).map a.toMonoidHom := by
      rw [MonoidHom.map_zpowers]
      change zpowers s = zpowers (a σ)
      rw [haσ]
    rw [hz] at hmem
    simpa only [a.symm_apply_apply] using mem_map_equiv.mp hmem
  have heq : zpowers s = zpowers (σ : G) := eq_of_le_of_card_ge (zpowers_le.mpr hss) (by
    rw [Nat.card_zpowers,Nat.card_zpowers,orderOf_coe,hs,hσ])
  apply hout
  change (σ : G) ∈ zpowers s
  rw [heq]
  exact mem_zpowers _

private theorem local_cubics_conjugate {D : LocalSixteen.Seed G}
    (P : LocalSixteen.ReturningPair D)
    (s u : involutionCentralizer D.z) (hs : orderOf s = 3) (hu : orderOf u = 3) :
    IsConj s u := by
  classical
  have hcard (x : involutionCentralizer D.z) (hx : orderOf x = 3) :
      Nat.card (zpowers x) = 3 ^ (Nat.card (involutionCentralizer D.z)).factorization 3 := by
    rw [Nat.card_zpowers,hx,D.localType.centralizer_card]
    decide +kernel
  let S : Sylow 3 (involutionCentralizer D.z) := Sylow.ofCard (zpowers s) (hcard s hs)
  let U : Sylow 3 (involutionCentralizer D.z) := Sylow.ofCard (zpowers u) (hcard u hu)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (involutionCentralizer D.z) S U
  have hm : (zpowers s).map (MulAut.conj g).toMonoidHom = zpowers u :=
    congrArg (fun Q : Sylow 3 (involutionCentralizer D.z) =>
      (Q : Subgroup (involutionCentralizer D.z))) hg
  have hh : g * s * g⁻¹ ∈ zpowers u := hm ▸ mem_map_of_mem _ (mem_zpowers s)
  rw [mem_zpowers_iff_mem_range_orderOf,hu] at hh
  obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hh
  have hn3 : n < 3 := Finset.mem_range.mp hn
  interval_cases n
  · have hg1 : MulAut.conj g s = 1 := by simpa using he.symm
    have hs1 : s = 1 := (MulAut.conj g).injective (hg1.trans (map_one _).symm)
    simp [hs1] at hs
  · exact isConj_iff.mpr ⟨g,by simpa using he.symm⟩
  · have huinv : u ^ 2 = u⁻¹ := eq_inv_of_mul_eq_one_left (by
      rw [← pow_succ]; simpa only [hu] using pow_orderOf_eq_one u)
    have hsu : IsConj s u⁻¹ := isConj_iff.mpr ⟨g,he.symm.trans huinv⟩
    obtain ⟨r,_,hr⟩ := cubic_local_involutory_inverter P u hu
    exact hsu.trans (isConj_iff.mpr ⟨r,hr⟩).symm

theorem cubics_conjugate_of_commuting_involutions {D : LocalSixteen.Seed G}
    (P : LocalSixteen.ReturningPair D) (hc : OneInvolutionClass G)
    (s u t v : G) (hs : orderOf s = 3) (hu : orderOf u = 3)
    (ht : orderOf t = 2) (hv : orderOf v = 2) (hst : Commute s t) (huv : Commute u v) :
    IsConj s u := by
  obtain ⟨a,ha⟩ := isConj_iff.mp (hc.isConj D.localType.involution ht)
  obtain ⟨b,hb⟩ := isConj_iff.mp (hc.isConj D.localType.involution hv)
  let ea := MulAut.conj a
  let eb := MulAut.conj b
  have has : ea s ∈ involutionCentralizer D.z := by
    apply mem_centralizer_singleton_iff.mpr
    rw [← ha]
    exact (hst.map ea.toMonoidHom).eq
  have hbu : eb u ∈ involutionCentralizer D.z := by
    apply mem_centralizer_singleton_iff.mpr
    rw [← hb]
    exact (huv.map eb.toMonoidHom).eq
  have hh := local_cubics_conjugate P ⟨ea s,has⟩ ⟨eb u,hbu⟩
    ((orderOf_coe _).symm.trans ((ea.orderOf_eq s).trans hs))
    ((orderOf_coe _).symm.trans ((eb.orderOf_eq u).trans hu))
  exact (isConj_iff.mpr ⟨a,rfl⟩).trans
    (((involutionCentralizer D.z).subtype.map_isConj hh).trans (isConj_iff.mpr ⟨b,rfl⟩).symm)

theorem cubic_nonfusion_of_involution_actors {D : LocalSixteen.Seed G}
    (P : LocalSixteen.ReturningPair D) (hc : OneInvolutionClass G)
    (s : G) (hs : orderOf s = 3)
    (e : (centralizer ({s} : Set G) ⧸ cubicKernel s) ≃* alternatingGroup (Fin 6))
    (σ : centralizer ({s} : Set G)) (hσ : orderOf σ = 3) (hout : σ ∉ cubicKernel s)
    (r t : G) (hr : orderOf r = 2) (ht : orderOf t = 2)
    (hrs : Commute r s) (hri : r * (σ : G) * r⁻¹ = (σ : G)⁻¹)
    (htfix : Commute (s * (σ : G)) t) : ¬ IsConj (σ : G) (s * (σ : G)) := by
  have hprod : orderOf (s * (σ : G)) = 3 := by
    apply orderOf_eq_prime
    · have hcomm : Commute s (σ : G) := (mem_centralizer_singleton_iff.mp σ.property).symm
      rw [hcomm.mul_pow]
      have hs3 : s ^ 3 = 1 := hs ▸ pow_orderOf_eq_one s
      have hσ3 : (σ : G) ^ 3 = 1 := congrArg (fun x : centralizer ({s} : Set G) => (x : G))
        (show σ ^ 3 = 1 from hσ ▸ pow_orderOf_eq_one σ)
      rw [hs3,hσ3,one_mul]
    · intro hh
      have hσinv : (σ : G) = s⁻¹ := eq_inv_of_mul_eq_one_right hh
      apply hout
      change (σ : G) ∈ zpowers s
      rw [hσinv]
      exact inv_mem (mem_zpowers s)
  obtain ⟨v,hv⟩ := exists_prime_orderOf_dvd_card' (G := centralizer ({s} : Set G))
    2 (by rw [cubic_centralizer_card s hs e]; decide)
  have hconj := cubics_conjugate_of_commuting_involutions P hc (s * (σ : G)) s t v
    hprod hs ht ((orderOf_coe v).trans hv) htfix
    (mem_centralizer_singleton_iff.mp v.property).symm
  exact fun hh => cubic_not_conjugate_of_inverter P hc s hs e σ hσ hout r hr hrs hri
    (hh.trans hconj)

theorem normalizer_complement_projective_of_involution_actors {D : LocalSixteen.Seed G}
    (P : LocalSixteen.ReturningPair D) (hc : OneInvolutionClass G)
    (s : G) (hs : orderOf s = 3)
    (e : (centralizer ({s} : Set G) ⧸ cubicKernel s) ≃* alternatingGroup (Fin 6))
    (σ : centralizer ({s} : Set G)) (hσ : orderOf σ = 3) (hout : σ ∉ cubicKernel s)
    (r t : G) (hr : orderOf r = 2) (ht : orderOf t = 2)
    (hrs : Commute r s) (hri : r * (σ : G) * r⁻¹ = (σ : G)⁻¹)
    (htfix : Commute (s * (σ : G)) t) :
    ∃ (M : Subgroup (normalizer (zpowers s : Set G)))
      (eQ : (normalizer (zpowers s : Set G) ⧸ cubicNormalizerKernel s) ≃*
        GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F)
      (eM : M ≃* GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F),
      (cubicNormalizerKernel s).IsComplement' M ∧
      ∀ x : M, eM x = eQ (QuotientGroup.mk' (cubicNormalizerKernel s) x.val) :=
  normalizer_complement_projective_of_cubic_nonfusion P hc s hs e σ hσ hout
    (cubic_nonfusion_of_involution_actors P hc s hs e σ hσ hout r t hr ht hrs hri htfix)

end
end CFSG.Quasithin.Janko23.J3Recognition.Ambient.BaumeisterComplement

module
public import ABG.ChapterII.Section1.Fusion
public import ABG.ChapterII.Section1.FusionFrame
public import ABG.ChapterII.Section1.WreathedFusion
public import ABG.ChapterII.Section1.SylowShapeRankCenter
public import ABG.ChapterII.Section2.SylowShapeTransport
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup
public import Theory.GroupTheory.CyclicNormalCentralizer
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# Two-five overgroups of semidihedral and wreathed Sylow subgroups

The three-free order bound rules out automizer index six in ABG's fusion
alternatives, yielding a normal two-complement. Its order divides five.
The central Sylow involution lies in the Sylow derived subgroup, hence
centralizes this cyclic complement and the whole overgroup. The argument
works at every semidihedral exponent and every wreathed height.

Source: Alperin–Brauer–Gorenstein II.1 Propositions 1–2, pp.10–13;
Aschbacher–Smith 6.1.4, the odd ternary containing row.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TwoFiveSylow
variable {G : Type*} [Group G] [Finite G]

private theorem normal_complement (S : Sylow 2 G)
    (hS : Stellmacher.IsSemidihedralGroup S ∨ ABG.IsWreathedGroup S)
    (h3 : ¬3 ∣ Nat.card G) : HasNormalPComplement 2 G := by
  have hno (U V : Subgroup G) : V.relIndex U ≠ 6 := by
    intro he
    exact h3 ((show 3 ∣ 6 by decide).trans
      (he ▸ (relIndex_dvd_card V U).trans U.card_subgroup_dvd_card))
  rcases hS with hS | ⟨n,hS⟩
  · obtain ⟨T,Q,hf⟩ := ABG.exists_quasiDihedralFusionFrame S hS
    rcases ABG.quasiDihedral_fusion S T Q hf with h | h | h | h
    · exact (hno (normalizer (T : Set G)) (centralizer (T : Set G)) h.2.2.2.1).elim
    · exact (hno (normalizer (Q : Set G)) (Q ⊔ centralizer (Q : Set G)) h.2.2.2.2.2).elim
    · exact (hno (normalizer (T : Set G)) (centralizer (T : Set G)) h.2.2.2.1).elim
    · exact h.1
  · obtain ⟨P⟩ := ABG.Wreathed.nonempty_presentation hS
    let U := P.U.map (S : Subgroup G).subtype
    let V := P.V.map (S : Subgroup G).subtype
    have hf := P.fusionFrame S
    have hu : ABG.automizerIndex U = 2 :=
      (ABG.Wreathed.u_automizer_index S n U V hf).resolve_right
        (hno (normalizer (U : Set G)) (centralizer (U : Set G)))
    have hv : ABG.outerAutomizerIndex V = 2 :=
      (ABG.Wreathed.v_outer_automizer_index S n U V hf).resolve_right
        (hno (normalizer (V : Set G)) (V ⊔ centralizer (V : Set G)))
    exact ABG.hasNormalTwoComplement_of_cyclic_focalSubgroupOf S (by
      rw [(ABG.Wreathed.focal_subgroup_cases S P).1 hu hv]
      exact P.derived_structure.2.1)

private theorem central_involution_derived {Q : Type*} [Group Q] [Finite Q]
    (hQ : Stellmacher.IsSemidihedralGroup Q ∨ ABG.IsWreathedGroup Q)
    (z : Q) (hz : orderOf z = 2) (hc : z ∈ center Q) : z ∈ commutator Q := by
  rcases hQ with ⟨n,hn,hcard,a,b,ha,hb,hab,hgen⟩ | ⟨n,hQ⟩
  · have hd := ABG.QuasiDihedral.derived_eq_frattini hn hcard a b ha hb hab hgen
    rw [hd.1,hd.2.1]
    have hle : center Q ≤ zpowers (a^2) := by
      rw [ABG.QuasiDihedral.center_eq hn a b ha hb hab hgen]
      apply zpowers_le.mpr
      have he : 2^(n-2) = 2 * 2^(n-3) := by
        rw [show n-2=(n-3)+1 by omega,pow_succ]
        omega
      rw [he,pow_mul]
      exact (zpowers (a^2)).pow_mem (mem_zpowers _) _
    exact hle hc
  · obtain ⟨P⟩ := ABG.Wreathed.nonempty_presentation hQ
    let : IsCyclic (center Q) := P.center_cyclic
    have he : (⟨z,hc⟩ : center Q) = ⟨P.x,P.x_mem_center⟩ :=
      IsCyclic.eq_of_orderOf_eq_two ((orderOf_coe _).symm.trans hz)
        ((orderOf_coe _).symm.trans P.x_orderOf)
    have hzP : z = P.x := congrArg Subtype.val he
    rw [hzP,←P.r_half,P.derived_structure.1]
    exact (zpowers P.r).pow_mem (mem_zpowers _) _

private theorem central_involution (S : Sylow 2 G)
    (hS : Stellmacher.IsSemidihedralGroup S ∨ ABG.IsWreathedGroup S)
    {k : ℕ} (hd : Nat.card G ∣ 2^k*5)
    (z : S) (hz : orderOf z = 2) (hc : z ∈ center S) : (z : G) ∈ center G := by
  have h3 : ¬3 ∣ Nat.card G := Nat.prime_three.coprime_iff_not_dvd.mp
    ((((by decide : Nat.Coprime 3 2).pow_right k).mul_right (by decide)).of_dvd_right hd)
  obtain ⟨N,hN,hcop,hquot⟩ := normal_complement S hS h3
  let : N.Normal := hN
  have hN5 : Nat.card N ∣ 5 :=
    (hcop.symm.pow_right k).dvd_of_dvd_mul_left (N.card_subgroup_dvd_card.trans hd)
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let : IsCyclic N := isCyclic_of_card_dvd_prime hN5
  have hzcomm : (z : G) ∈ commutator G := by
    have hh := mem_map_of_mem (S : Subgroup G).subtype (central_involution_derived hS z hz hc)
    rw [map_commutator_eq] at hh
    exact commutator_mono le_top le_top hh
  have hzN : (z : G) ∈ centralizer (N : Set G) :=
    commutator_le_centralizer_of_isCyclic_normal N hzcomm
  apply mem_center_iff.mpr
  intro y
  have hall : N ⊔ (S : Subgroup G) ≤ centralizer ({(z : G)} : Set G) := by
    apply sup_le
    · intro n hn
      exact mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hzN) n hn)
    · intro s hs
      exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_center_iff.mp hc (⟨s,hs⟩ : S)))
  have hy := hall (show y ∈ N ⊔ (S : Subgroup G) from by
    rw [sup_comm,S.sup_eq_top_of_quotient_isPGroup N hquot]; trivial)
  exact mem_centralizer_singleton_iff.mp hy

private theorem fixed_central_involution (S : Sylow 2 G)
    (hS : Stellmacher.IsSemidihedralGroup S ∨ ABG.IsWreathedGroup S)
    {k : ℕ} (hd : Nat.card G ∣ 2^k*5)
    (z : S) (hz : orderOf z = 2) (hc : z ∈ center S) (φ : MulAut G) :
    φ (z : G) = z := by
  have hzcentral := central_involution S hS hd z hz hc
  have hpz : φ (z : G) ∈ center G := (centerCongr φ ⟨z,hzcentral⟩).property
  have hpord : orderOf (φ (z : G)) = 2 := (φ.orderOf_eq _).trans ((orderOf_coe z).trans hz)
  have hps : φ (z : G) ∈ S := by
    let Q := zpowers (φ (z : G))
    have hQc : Q ≤ center G := zpowers_le.mpr hpz
    let : Q.Normal := ⟨fun x hx g => by
      have hc := mem_center_iff.mp (hQc hx) g
      simpa only [hc,mul_inv_cancel_right] using hx⟩
    have hQp : IsPGroup 2 Q := IsPGroup.of_card (n := 1) (by
      simpa only [Q,Nat.card_zpowers,pow_one] using hpord)
    exact hQp.le_sylow_of_normal S (mem_zpowers _)
  let : IsCyclic (center S) := (ABG.rank_two_and_cyclic_center_of_sylow_shape hS).2.2
  let zz : center S := ⟨z,hc⟩
  let ww : center S := ⟨⟨φ z,hps⟩,mem_center_iff.mpr
    (fun s => Subtype.ext (mem_center_iff.mp hpz s))⟩
  have he : ww = zz := IsCyclic.eq_of_orderOf_eq_two
    ((orderOf_coe ww).symm.trans ((orderOf_coe ww.val).symm.trans hpord))
    ((orderOf_coe zz).symm.trans hz)
  exact congrArg (fun x : center S => x.val.val) he

/-- A two-five overgroup centralizes the supplied central involution of its
full semidihedral or wreathed Sylow, at arbitrary height. -/
theorem overgroup_le_involution_centralizer (S : Sylow 2 G)
    (hS : Stellmacher.IsSemidihedralGroup S ∨ ABG.IsWreathedGroup S)
    (H : Subgroup G) (hSH : (S : Subgroup G) ≤ H) {k : ℕ}
    (hd : Nat.card H ∣ 2^k*5) (z : S)
    (hz : orderOf z = 2) (hc : z ∈ center S) :
    H ≤ centralizer ({(z : G)} : Set G) := by
  let P := S.subtype hSH
  let e : S ≃* P := (subgroupOfEquivOfLe hSH).symm
  have hP : Stellmacher.IsSemidihedralGroup P ∨ ABG.IsWreathedGroup P := by
    rcases hS with hS | ⟨n,hS⟩
    · exact .inl (ABG.semidihedral_equiv e hS)
    · exact .inr ⟨n,ABG.wreathed_equiv e hS⟩
  have hcz : e z ∈ center P := (centerCongr e ⟨z,hc⟩).property
  have hh := central_involution P hP hd (e z) ((e.orderOf_eq z).trans hz) hcz
  intro x hx
  apply mem_centralizer_singleton_iff.mpr
  exact congrArg H.subtype (mem_center_iff.mp hh ⟨x,hx⟩)

/-- The full ambient normalizer of the two-five overgroup fixes the same
supplied central Sylow involution, without preserving that Sylow itself. -/
theorem normalizer_le_involution_centralizer (S : Sylow 2 G)
    (hS : Stellmacher.IsSemidihedralGroup S ∨ ABG.IsWreathedGroup S)
    (H : Subgroup G) (hSH : (S : Subgroup G) ≤ H) {k : ℕ}
    (hd : Nat.card H ∣ 2^k*5) (z : S)
    (hz : orderOf z = 2) (hc : z ∈ center S) :
    normalizer (H : Set G) ≤ centralizer ({(z : G)} : Set G) := by
  let P := S.subtype hSH
  let e : S ≃* P := (subgroupOfEquivOfLe hSH).symm
  have hP : Stellmacher.IsSemidihedralGroup P ∨ ABG.IsWreathedGroup P := by
    rcases hS with hS | ⟨n,hS⟩
    · exact .inl (ABG.semidihedral_equiv e hS)
    · exact .inr ⟨n,ABG.wreathed_equiv e hS⟩
  have hcz : e z ∈ center P := (centerCongr e ⟨z,hc⟩).property
  intro x hx
  have hh := fixed_central_involution P hP hd (e z) ((e.orderOf_eq z).trans hz) hcz
    (H.normalizerMonoidHom ⟨x,hx⟩)
  have he : x * (z : G) * x⁻¹ = z := congrArg H.subtype hh
  exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he)

/-- Any ambient automorphism preserving the actual overgroup fixes its
marked central Sylow involution; preservation of the Sylow is unnecessary. -/
theorem automorphism_fixes_involution (S : Sylow 2 G)
    (hS : Stellmacher.IsSemidihedralGroup S ∨ ABG.IsWreathedGroup S)
    (H : Subgroup G) (hSH : (S : Subgroup G) ≤ H) {k : ℕ}
    (hd : Nat.card H ∣ 2^k*5) (z : S)
    (hz : orderOf z = 2) (hc : z ∈ center S)
    (φ : MulAut G) (hφ : H.map φ.toMonoidHom = H) : φ (z : G) = z := by
  let P := S.subtype hSH
  let e : S ≃* P := (subgroupOfEquivOfLe hSH).symm
  have hP : Stellmacher.IsSemidihedralGroup P ∨ ABG.IsWreathedGroup P := by
    rcases hS with hS | ⟨n,hS⟩
    · exact .inl (ABG.semidihedral_equiv e hS)
    · exact .inr ⟨n,ABG.wreathed_equiv e hS⟩
  have hcz : e z ∈ center P := (centerCongr e ⟨z,hc⟩).property
  let a : MulAut H := (φ.subgroupMap H).trans (MulEquiv.subgroupCongr hφ)
  exact congrArg H.subtype
    (fixed_central_involution P hP hd (e z) ((e.orderOf_eq z).trans hz) hcz a)

end Theory.GroupTheory.TwoFiveSylow

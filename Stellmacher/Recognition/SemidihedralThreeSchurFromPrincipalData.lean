module

public import ABG.ChapterIII.Section2.ThreePrincipalData
public import Stellmacher.Recognition.SemidihedralCentralizerQuotient
public import Theory.Character.OddRationalSchur
public import Theory.Character.SchurSmallDegrees
public import Theory.Character.CentralInvolutionMinus
public import Theory.Character.CharacterKernel
public import Theory.Character.ModularBlock.PrincipalKernel
public import Theory.GroupTheory.NormalSubgroupCentralInvolution

/-!
# Schur bounds from supplied semidihedral principal characters

The actual irreducible rows of `ThreePrincipalData` are faithful in the
simple ambient group. Their rationality gives the degree-eleven and
degree-thirteen global order bounds. Locally, the negative eigenspace at
the central involution has degree four: use the first row in the first
alternative, and the fourth row (degree twelve, involution value four)
in the second alternative.

A normal local kernel avoiding the central involution lies in the odd core.
The local principal character annihilates that core, so the section identities
and ambient faithfulness force the negative-eigenspace kernel to be trivial.
The resulting genuine constituent character is rational on all local elements
and satisfies the source degree constraints. Schur's complex-character argument
then gives the centralizer bound; no rational realization is assumed.

The final theorem retains the original elementary-four configuration and its
nontrivial index hypothesis. The local construction itself proves a stronger
statement without that hypothesis. Principal-character existence is a separate
input, and no final Schur-bound assembly is imported.

Source: Alperin–Brauer–Gorenstein, III.8 Lemmas 1–2, pp.114–115. The use of
the fourth row specializes the local argument to the two retained degree lists.
-/

namespace Stellmacher.Recognition
open ABG
noncomputable section

/-- The degree-eleven principal row gives the first global Schur bound. -/
public theorem semidihedral_three_global_schur_eleven
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    {x : G} (c : ThreePrincipalData G x) (hdegree : c.degree 0 = 11) :
    Nat.card G ∣ 16 * 3^6 * 5^2 * 7 * 11 := by
  apply Theory.Character.card_dvd_degree_eleven_bound_of_sylow_bounds S
    (semidihedral_sylow_card_sixteen_of_simple_nTwo S hS hN)
  intro p hp hodd P
  apply (c.irreducible 1).sylow_card_dvd_of_odd_rational (by decide : 1 < 11)
    (by simpa [ThreePrincipalData.χ, hdegree] using c.degree_value 1)
    (fun g _ => c.rational 1 g) p hodd P

/-- The degree-thirteen principal row gives the second global Schur bound. -/
public theorem semidihedral_three_global_schur_thirteen
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    {x : G} (c : ThreePrincipalData G x) (hdegree : c.degree 1 = 13) :
    Nat.card G ∣ 16 * 3^8 * 5^3 * 7^2 * 11 * 13 := by
  apply Theory.Character.card_dvd_degree_thirteen_bound_of_sylow_bounds S
    (semidihedral_sylow_card_sixteen_of_simple_nTwo S hS hN)
  intro p hp hodd P
  apply (c.irreducible 2).sylow_card_dvd_of_odd_rational (by decide : 1 < 13)
    (by simpa [ThreePrincipalData.χ, hdegree] using c.degree_value 2)
    (fun g _ => c.rational 2 g) p hodd P

/-- A faithful degree-four local character rational on odd-order elements
gives the centralizer order bound, with no rational-realizability assumption. -/
public theorem involutionCentralizer_card_dvd_of_odd_rational_degree_four
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2)
    (ρ : Representation ℂ (Subgroup.centralizer ({x} : Set G)) (Fin 4 → ℂ))
    (hf : Function.Injective ρ)
    (hrat : ∀ g, Odd (orderOf g) → ∃ q : ℚ, ρ.character g = (q : ℂ)) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) ∣ 720 := by
  have hQD := isQDGroup_of_simple ⟨S, hS⟩
  obtain ⟨R, _, ⟨e⟩⟩ := hQD.exists_semidihedral_sylow_in_centralizer S hS x hx
  have hR : Nat.card R = 16 := (Nat.card_congr e.toEquiv).symm.trans
    (semidihedral_sylow_card_sixteen_of_simple_nTwo S hS hN)
  apply Theory.Character.card_dvd_degree_four_bound_of_sylow_bounds R hR
  intro p hp hodd P
  exact ρ.sylow_card_dvd_pow_mul_factorial_of_odd_rational_character hf hrat hodd P

/-- The weak degree inequality in the printed source forces degree four,
both for the degree-eleven row and for the degree-thirteen row. -/
public theorem semidihedral_local_constituent_degree_eq_four
    {d f : ℕ} (hd : 0 < d) (hfour : 4 ∣ d)
    (hbound : 2 * d ≤ f - 3) (hf : f = 11 ∨ f = 13) : d = 4 := by
  obtain ⟨k, rfl⟩ := hfour
  rcases hf with rfl | rfl <;> omega

/-- Apply the local bound once the constituent construction supplies its
faithful complex realization and the source degree estimates. -/
public theorem semidihedral_three_local_schur_of_constituent
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2) {d f : ℕ}
    (ρ : Representation ℂ (Subgroup.centralizer ({x} : Set G)) (Fin d → ℂ))
    (hinj : Function.Injective ρ)
    (hrat : ∀ g, Odd (orderOf g) → ∃ q : ℚ, ρ.character g = (q : ℂ))
    (hd : 0 < d) (hfour : 4 ∣ d) (hbound : 2 * d ≤ f - 3)
    (hf : f = 11 ∨ f = 13) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) ∣ 720 := by
  have hd4 := semidihedral_local_constituent_degree_eq_four hd hfour hbound hf
  subst d
  exact involutionCentralizer_card_dvd_of_odd_rational_degree_four S hS hN x hx ρ hinj hrat


open ModularBlock.CompatibleBrauerBlock ModularBlock.PrincipalBlockKernel

private theorem threePrincipal_section_eq_on_oddCore
    {G : Type*} [Group G] [Finite G] {x : G}
    (c : ThreePrincipalData G x) (i : Fin 8)
    (r : Subgroup.centralizer ({x} : Set G))
    (hr : r ∈ pPrimeCore 2 (Subgroup.centralizer ({x} : Set G))) :
    c.χ i (ConjClasses.mk (x * (r : G))) = c.χ i (ConjClasses.mk x) := by
  let N := Subgroup.centralizer ({x} : Set G)
  let rO : pPrimeCore 2 N := ⟨r, hr⟩
  have ho : Odd (orderOf r) := by
    rw [Subgroup.orderOf_coe rO]
    exact (Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := N))).of_dvd_nat
      (orderOf_dvd_natCard rO)
  have hv := character_mul_right_eq_of_mem_block (localData c.blockData N)
    c.local_mem 1 r hr
  simp only [one_mul] at hv
  have hv3 : (localData c.blockData N).chi c.localRow (ConjClasses.mk r) = 3 :=
    hv.trans c.local_degree
  have h := c.involution_section r ho i
  have h0 := c.involution_section 1 (by simp) i
  rw [hv3] at h
  simp only [OneMemClass.coe_one, mul_one, c.local_degree] at h0
  exact h.trans h0.symm

private theorem threePrincipal_minus_faithful_of_inputs
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (x : G) (hx : orderOf x = 2) (c : ThreePrincipalData G x) (i : Fin 5)
    (d : ℕ) (hd : 1 < d)
    (hdegree : c.χ ⟨i.val, by omega⟩ (ConjClasses.mk 1) = (d : ℂ))
    (hvalue : c.χ ⟨i.val, by omega⟩ (ConjClasses.mk x) = (d : ℂ) - 8)
    (hminus : IsCharacter (fun r : Subgroup.centralizer ({x} : Set G) =>
      (c.χ ⟨i.val, by omega⟩ (ConjClasses.mk (r : G)) -
        c.χ ⟨i.val, by omega⟩ (ConjClasses.mk (x * (r : G)))) / 2))
    (hkernel : ∀ (K : Subgroup (Subgroup.centralizer ({x} : Set G))), K.Normal →
      (⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ :
        Subgroup.centralizer ({x} : Set G)) ∉ K →
      K ≤ pPrimeCore 2 (Subgroup.centralizer ({x} : Set G))) :
    ∃ ρ : Representation ℂ (Subgroup.centralizer ({x} : Set G)) (Fin 4 → ℂ),
      Function.Injective ρ ∧
      (∀ r, ρ.character r =
        (c.χ ⟨i.val, by omega⟩ (ConjClasses.mk (r : G)) -
          c.χ ⟨i.val, by omega⟩ (ConjClasses.mk (x * (r : G)))) / 2) ∧
      (∀ r, ∃ q : ℚ, ρ.character r = (q : ℂ)) := by
  let N := Subgroup.centralizer ({x} : Set G)
  let z : N := ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  let j : Fin 8 := ⟨i.val, by omega⟩
  obtain ⟨n, ρ, hρ⟩ := hminus
  have hn : n = 4 := by
    have h := congrFun hρ (1 : N)
    change (c.χ j (ConjClasses.mk 1) - c.χ j (ConjClasses.mk (x * 1))) / 2 =
      ρ.character 1 at h
    rw [mul_one, hdegree, hvalue] at h
    have heval : ((d : ℂ) - ((d : ℂ) - 8)) / 2 = 4 := by ring
    rw [heval] at h
    have hncast : (n : ℂ) = 4 := by simpa using h.symm
    exact_mod_cast hncast
  subst n
  have hchar (r : N) : ρ.character r =
      (c.χ j (ConjClasses.mk (r : G)) - c.χ j (ConjClasses.mk (x * (r : G)))) / 2 :=
    (congrFun hρ r).symm
  have hzval : ρ.character z = -4 := by
    rw [hchar]
    change (c.χ j (ConjClasses.mk x) - c.χ j (ConjClasses.mk (x * x))) / 2 = -4
    have hx2 : x * x = 1 := by simpa only [hx, pow_two] using pow_orderOf_eq_one x
    rw [hx2, hdegree, hvalue]
    ring
  have hzker : z ∉ ρ.ker := by
    intro hzker
    have h := (ρ.mem_ker_iff_character_eq_degree z).mp hzker
    rw [hzval] at h
    norm_num at h
  have hinj : Function.Injective ρ := by
    apply ρ.ker_eq_bot_iff.mp
    apply bot_unique
    intro r hr
    have hrO := hkernel ρ.ker inferInstance hzker hr
    have hfull : c.χ j (ConjClasses.mk (r : G)) = c.χ j (ConjClasses.mk 1) := by
      have h := (ρ.mem_ker_iff_character_eq_degree r).mp hr
      rw [hchar, threePrincipal_section_eq_on_oddCore c j r hrO, hvalue] at h
      have h' : (c.χ j (ConjClasses.mk (r : G)) - ((d : ℂ) - 8)) / 2 = 4 := by
        simpa using h
      rw [hdegree]
      linear_combination 2 * h'
    obtain ⟨σ, hσ, hfaithful⟩ := (c.irreducible j).exists_faithful_representation hd hdegree
    have hrσ : (r : G) ∈ σ.ker := by
      apply (σ.mem_ker_iff_character_eq_degree (r : G)).mpr
      rw [hσ] at hfull
      change σ.character (r : G) = σ.character 1 at hfull
      exact hfull
    have hr1 : (r : G) = 1 := hfaithful (hrσ.trans (map_one σ).symm)
    exact Subtype.ext hr1
  refine ⟨ρ, hinj, hchar, ?_⟩
  intro r
  obtain ⟨q, hq⟩ := c.rational i (r : G)
  obtain ⟨qz, hqz⟩ := c.rational i (x * (r : G))
  refine ⟨(q - qz) / 2, ?_⟩
  rw [hchar]
  change (c.blockData.chi (c.row j).val (ConjClasses.mk (r : G)) -
    c.blockData.chi (c.row j).val (ConjClasses.mk (x * (r : G)))) / 2 = _
  rw [hq, hqz]
  push_cast
  rfl


private theorem threePrincipal_minus_isCharacter
    {G : Type*} [Group G] [Finite G] (x : G) (hx : orderOf x = 2)
    (c : ThreePrincipalData G x) (i : Fin 5) :
    IsCharacter (fun r : Subgroup.centralizer ({x} : Set G) =>
      (c.χ ⟨i.val, by omega⟩ (ConjClasses.mk (r : G)) -
        c.χ ⟨i.val, by omega⟩ (ConjClasses.mk (x * (r : G)))) / 2) := by
  let N := Subgroup.centralizer ({x} : Set G)
  let z : N := ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hzc : z ∈ Subgroup.center N := by
    apply Subgroup.mem_center_iff.mpr
    intro r
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp r.property)
  have hzsq : z ^ 2 = 1 := by
    apply Subtype.ext
    change x ^ 2 = 1
    rw [← hx]
    exact pow_orderOf_eq_one x
  obtain ⟨n, ρ, hρ⟩ := (c.irreducible ⟨i.val, by omega⟩).1
  have h := Representation.isCharacter_centralInvolutionMinus (ρ.comp N.subtype) z hzc hzsq
  rw [hρ]
  change IsCharacter (fun r : N => (Representation.character (ρ.comp N.subtype) r -
    Representation.character (ρ.comp N.subtype) (z * r)) / 2)
  exact h

private theorem threePrincipal_local_kernel_criterion
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S)
    (x : G) (hx : orderOf x = 2)
    (K : Subgroup (Subgroup.centralizer ({x} : Set G))) (hK : K.Normal)
    (hxK : (⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ :
        Subgroup.centralizer ({x} : Set G)) ∉ K) :
    K ≤ pPrimeCore 2 (Subgroup.centralizer ({x} : Set G)) := by
  let N := Subgroup.centralizer ({x} : Set G)
  let z : N := ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  let : K.Normal := hK
  have hzc : z ∈ Subgroup.center N := by
    apply Subgroup.mem_center_iff.mpr
    intro r
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp r.property)
  have hz : orderOf z = 2 := (Subgroup.orderOf_coe z).symm.trans hx
  have hQD := isQDGroup_of_simple ⟨S, hS⟩
  obtain ⟨R, hR, _⟩ := hQD.exists_semidihedral_sylow_in_centralizer S hS x hx
  exact Subgroup.le_oddCore_of_not_mem_central_involution
    (fun P => QuasiDihedral.card_center (semidihedral_equiv (R.equiv P) hR))
    z hz hzc K hxK

public theorem semidihedral_three_local_degree_four_of_eleven
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S)
    (x : G) (hx : orderOf x = 2) (c : ThreePrincipalData G x) (hd : c.degree 0 = 11) :
    ∃ ρ : Representation ℂ (Subgroup.centralizer ({x} : Set G)) (Fin 4 → ℂ),
      Function.Injective ρ ∧
      (∀ r, ρ.character r = (c.χ 1 (ConjClasses.mk (r : G)) -
        c.χ 1 (ConjClasses.mk (x * (r : G)))) / 2) ∧
      (∀ r, ∃ q : ℚ, ρ.character r = (q : ℂ)) := by
  apply threePrincipal_minus_faithful_of_inputs x hx c 1 11 (by decide)
    (by simpa [ThreePrincipalData.χ, hd] using c.degree_value 1)
    (by norm_num; exact c.involution_values 1)
    (threePrincipal_minus_isCharacter x hx c 1)
    (threePrincipal_local_kernel_criterion S hS x hx)

public theorem semidihedral_three_local_degree_four_of_thirteen
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S)
    (x : G) (hx : orderOf x = 2) (c : ThreePrincipalData G x) (hd : c.degree 1 = 13) :
    ∃ ρ : Representation ℂ (Subgroup.centralizer ({x} : Set G)) (Fin 4 → ℂ),
      Function.Injective ρ ∧
      (∀ r, ρ.character r = (c.χ 4 (ConjClasses.mk (r : G)) -
        c.χ 4 (ConjClasses.mk (x * (r : G)))) / 2) ∧
      (∀ r, ∃ q : ℚ, ρ.character r = (q : ℂ)) := by
  have hd4 : c.degree 3 = 12 := by have := c.degree_identities.2.1; omega
  apply threePrincipal_minus_faithful_of_inputs x hx c 4 12 (by decide)
    (by simpa [ThreePrincipalData.χ, hd4] using c.degree_value 4)
    (by norm_num; exact c.involution_values 4)
    (threePrincipal_minus_isCharacter x hx c 4)
    (threePrincipal_local_kernel_criterion S hS x hx)

/-- A genuine local constituent character with the degree constraints used
in ABG III.8. In the second alternative the fourth global row supplies a
smaller negative eigenspace directly. -/
public theorem semidihedral_three_exists_local_schur_character
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S)
    (x : G) (hx : orderOf x = 2) (c : ThreePrincipalData G x) :
    ∃ (d : ℕ) (ρ : Representation ℂ (Subgroup.centralizer ({x} : Set G)) (Fin d → ℂ)),
      Function.Injective ρ ∧
      (∀ r, Odd (orderOf r) → ∃ q : ℚ, ρ.character r = (q : ℂ)) ∧
      0 < d ∧ 4 ∣ d ∧
      ((c.degree 0 = 11 ∧ 2 * d ≤ c.degree 0 - 3 ∧
        ∀ r, ρ.character r = (c.χ 1 (ConjClasses.mk (r : G)) -
          c.χ 1 (ConjClasses.mk (x * (r : G)))) / 2) ∨
       (c.degree 1 = 13 ∧ 2 * d ≤ c.degree 1 - 3 ∧
        ∀ r, ρ.character r = (c.χ 4 (ConjClasses.mk (r : G)) -
          c.χ 4 (ConjClasses.mk (x * (r : G)))) / 2)) := by
  rcases c.degree_alternatives with h | h
  · obtain ⟨ρ, hf, hc, hr⟩ := semidihedral_three_local_degree_four_of_eleven S hS x hx c h.1
    refine ⟨4, ρ, hf, fun r _ => hr r, by decide, dvd_refl 4, Or.inl ?_⟩
    exact ⟨h.1, by omega, hc⟩
  · obtain ⟨ρ, hf, hc, hr⟩ := semidihedral_three_local_degree_four_of_thirteen S hS x hx c h.2.1
    refine ⟨4, ρ, hf, fun r _ => hr r, by decide, dvd_refl 4, Or.inr ?_⟩
    exact ⟨h.2.1, by omega, hc⟩

/-- The local constituent degree constraints give the centralizer order bound. -/
public theorem semidihedral_three_local_schur_from_principalData
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2) (c : ThreePrincipalData G x) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) ∣ 720 := by
  obtain ⟨d, ρ, hf, hr, hd, hfour, hcases⟩ :=
    semidihedral_three_exists_local_schur_character S hS x hx c
  rcases hcases with ⟨hdegree, hbound, _⟩ | ⟨hdegree, hbound, _⟩
  · exact semidihedral_three_local_schur_of_constituent S hS hN x hx ρ hf hr hd hfour hbound
      (Or.inl hdegree)
  · exact semidihedral_three_local_schur_of_constituent S hS hN x hx ρ hf hr hd hfour hbound
      (Or.inr hdegree)

/-- The original semidihedral local configuration with explicit principal
characters gives all three Schur bounds. -/
public theorem semidihedral_three_schur_bounds_from_principalData
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2) (T : Subgroup G) [IsElementaryAbelian 2 T]
    (_hT : Nat.card T = 4) (_hxT : x ∈ T) (c : ThreePrincipalData G x) :
    let N := Subgroup.centralizer ({x} : Set G)
    let K := (pPrimeCore 2 N).map N.subtype
    let A := (Subgroup.centralizer (T : Set G)).subgroupOf K
    A.index ≠ 1 → Nat.card N ∣ 720 ∧
      (c.degree 0 = 11 → Nat.card G ∣ 16 * 3^6 * 5^2 * 7 * 11) ∧
      (c.degree 1 = 13 → Nat.card G ∣ 16 * 3^8 * 5^3 * 7^2 * 11 * 13) := by
  dsimp only
  intro _hb
  exact ⟨semidihedral_three_local_schur_from_principalData S hS hN x hx c,
    semidihedral_three_global_schur_eleven S hS hN c,
    semidihedral_three_global_schur_thirteen S hS hN c⟩

end
end Stellmacher.Recognition

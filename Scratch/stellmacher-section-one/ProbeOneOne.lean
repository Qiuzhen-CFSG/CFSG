module

import Stellmacher.SectionOne.Defs
import Theory.PGroup

open scoped BigOperators Pointwise

namespace Stellmacher.SectionOne

universe u v

example {G : Type u} {V : Type v} [Group G] [Group V]
    [Finite G] [Finite V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G) :
    ¬ IsCyclic S → IsMulCommutative S →
      oddCore G =
        ⨆ (a : S) (_ : (a : G) ≠ 1),
          oddCore G ⊓
            Subgroup.centralizer (Subgroup.zpowers (a : G) : Set G) := by
  intro hncyc hcommS
  let W : Subgroup G := oddCore G
  let hWnormal : W.Normal := by
    dsimp [W]
    exact pPrimeCore_normal
  let hSnormW : (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G) :=
    Subgroup.le_normalizer_of_normal
  letI : MulDistribMulAction S W :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (S : Subgroup G) W hSnormW
  letI : CommGroup S := IsMulCommutative.instCommGroup
  letI : Fact (IsPGroup 2 S) := ⟨S.isPGroup'⟩
  have hcop : Nat.Coprime 2 (Nat.card W) := by
    dsimp [W]
    exact pPrimeCore_coprime_card (p := 2) (G := G)
  have htop :
      (⨆ (a : S) (_ : a ≠ 1),
        fixedPointSubgroup (↥(Subgroup.zpowers a)) (↥W)) = ⊤ :=
    iSup_fixedPointSubgroup_zpowers_eq_top_of_noncyclic_abelian_pGroup_action
      (G := ↥W) (A := ↥S) (p := 2) hcop (hncyc := hncyc)
  have htopmap : (⊤ : Subgroup W).map W.subtype = W := by
    ext x
    simp
  have hterm (a : S) :
      (fixedPointSubgroup (↥(Subgroup.zpowers a)) (↥W)).map W.subtype =
        W ⊓ Subgroup.centralizer (Subgroup.zpowers (a : G) : Set G) := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w.property, Subgroup.mem_centralizer_iff.mpr ?_⟩
      have hafix :
          (⟨a, Subgroup.mem_zpowers a⟩ : Subgroup.zpowers a) • w = w :=
        hw ⟨a, Subgroup.mem_zpowers a⟩
      have hacomm : (a : G) * (w : G) = (w : G) * (a : G) := by
        have hconj : (a : G) * (w : G) * (a : G)⁻¹ = (w : G) := by
          have hSfix : (a : S) • w = w := by
            simpa only [Subgroup.smul_def] using hafix
          have hcoe := congrArg Subtype.val hSfix
          exact
            (Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe_explicit
              (S : Subgroup G) W hSnormW a w).symm.trans hcoe
        have := congrArg (fun z : G => z * (a : G)) hconj
        simpa [mul_assoc] using this
      have hacomm' : Commute (a : G) (w : G) := hacomm
      intro z hz
      rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, rfl⟩
      exact (hacomm'.zpow_left n).eq
    · rintro ⟨hxW, hxcent⟩
      refine ⟨⟨x, hxW⟩, ?_, rfl⟩
      change ∀ z : Subgroup.zpowers a, z • (⟨x, hxW⟩ : W) = ⟨x, hxW⟩
      intro z
      apply Subtype.ext
      have hzmem : (z : G) ∈ Subgroup.zpowers (a : G) := by
        rcases Subgroup.mem_zpowers_iff.mp z.property with ⟨n, hn⟩
        refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
        simpa using congrArg (fun y : S => (y : G)) hn
      have hzcomm : (z : G) * x = x * (z : G) :=
        Subgroup.mem_centralizer_iff.mp hxcent (z : G) hzmem
      have hconj : (z : G) * x * (z : G)⁻¹ = x := by
        rw [hzcomm]
        simp [mul_assoc]
      calc
        ((z : S) • (⟨x, hxW⟩ : W) : W) =
            (z : G) * x * (z : G)⁻¹ :=
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe_explicit
            (S : Subgroup G) W hSnormW (z : S) ⟨x, hxW⟩
        _ = x := hconj
  have hmap := congrArg (fun K : Subgroup W => K.map W.subtype) htop
  simp only [Subgroup.map_iSup] at hmap
  simp_rw [hterm] at hmap
  rw [htopmap] at hmap
  simpa [W] using hmap.symm

example {G : Type u} {V : Type v} [Group G] [Group V]
    [Finite G] [Finite V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G) :
    IsQuadraticAction S V → IsElementaryAbelian 2 S := by
  intro hquadratic
  letI : CommGroup V := IsMulCommutative.instCommGroup
  let φ : G →* MulAut V := MulDistribMulAction.toMulAut G V
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [← fixingSubgroupOf_univ_eq_ker_toMulAut]
    exact h.action_faithful
  let ψ : S →* MulAut V := φ.comp (S : Subgroup G).subtype
  have hψinj : Function.Injective ψ := by
    intro a b hab
    apply Subtype.ext
    exact hφinj hab
  have hdelta_mem (a : S) (v : V) :
      v⁻¹ * (a • v) ∈ commutatorAction S V := by
    rw [commutatorAction_eq_closure]
    exact Subgroup.subset_closure ⟨a, v, rfl⟩
  have hfix_delta (a b : S) (v : V) :
      b • (v⁻¹ * (a • v)) = v⁻¹ * (a • v) := by
    let d : V := v⁻¹ * (a • v)
    have hd : d ∈ commutatorAction S V := hdelta_mem a v
    have hiter : d⁻¹ * (b • d) ∈ commutatorAction₂ S V := by
      exact Subgroup.subset_closure ⟨b, d, hd, rfl⟩
    have hiter_bot : d⁻¹ * (b • d) ∈ (⊥ : Subgroup V) := by
      rw [← hquadratic]
      exact hiter
    have hone : d⁻¹ * (b • d) = 1 := by simpa using hiter_bot
    have : d = b • d := eq_of_inv_mul_eq_one hone
    simpa [d] using this.symm
  have hformula (a b : S) (v : V) :
      (b * a) • v = (b • v) * v⁻¹ * (a • v) := by
    have hfix := hfix_delta a b v
    have hmul := congrArg (fun z : V => (b • v) * z) hfix
    simpa [smul_mul', smul_smul, mul_assoc] using hmul
  have hcomm : IsMulCommutative S := by
    refine ⟨⟨fun a b => ?_⟩⟩
    apply hψinj
    ext v
    change (a * b) • v = (b * a) • v
    rw [hformula b a v, hformula a b v]
    ac_rfl
  refine
    { toIsMulCommutative := hcomm
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro s
  apply hψinj
  ext v
  simp only [ψ, φ, MonoidHom.comp_apply, MulDistribMulAction.toMulAut_apply,
    map_one, MulAut.one_apply]
  change (s ^ 2) • v = v
  rw [pow_two, hformula s s v]
  have hsv2 : (s • v) ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) (s • v)
  have hv2 : v ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) v
  have hvinv : v⁻¹ = v :=
    inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hv2)
  calc
    (s • v) * v⁻¹ * (s • v) = (s • v) * (s • v) * v⁻¹ := by ac_rfl
    _ = v⁻¹ := by rw [← pow_two, hsv2, one_mul]
    _ = v := hvinv

example {G : Type u} {V : Type v} [Group G] [Group V]
    [Finite G] [Finite V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G) :
    IsElementaryAbelian 2 S →
      oddCore G =
        ⨆ (S0 : Subgroup S) (_ : Nat.card S = 2 * Nat.card S0),
          oddCore G ⊓
            Subgroup.centralizer
              ((S0.map (S : Subgroup G).subtype : Subgroup G) : Set G) := by
  intro hSelem
  letI : IsElementaryAbelian 2 S := hSelem
  letI : CommGroup S := IsMulCommutative.instCommGroup
  letI : Fact (IsPGroup 2 S) := ⟨S.isPGroup'⟩
  let W : Subgroup G := oddCore G
  let hWnormal : W.Normal := by
    dsimp [W]
    exact pPrimeCore_normal
  let hSnormW : (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G) :=
    Subgroup.le_normalizer_of_normal
  letI : MulDistribMulAction S W :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (S : Subgroup G) W hSnormW
  have hS_ne_bot : (S : Subgroup G) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card S h.G_even.two_dvd
  haveI : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot (S : Subgroup G)).2 hS_ne_bot
  have hindex_top :
      (⨆ (S0 : Subgroup S) (_ : Nat.card S = 2 * Nat.card S0),
        fixedPointSubgroup (↥S0) (↥W)) = ⊤ := by
    by_cases hScyc : IsCyclic S
    · letI : IsCyclic S := hScyc
      have hScard : Nat.card S = 2 := by
        rw [← hScyc.exponent_eq_card]
        exact IsElementaryAbelian.exponent_eq_prime
      have hbotcard : Nat.card S = 2 * Nat.card (⊥ : Subgroup S) := by
        simp [hScard]
      have hfixbot : fixedPointSubgroup (↥(⊥ : Subgroup S)) (↥W) = ⊤ := by
        ext w
        simp [FixedPoints.mem_subgroup]
      apply top_unique
      rw [← hfixbot]
      exact le_iSup_of_le (⊥ : Subgroup S)
        (le_iSup_of_le hbotcard le_rfl)
    · have hcop : Nat.Coprime 2 (Nat.card W) := by
        dsimp [W]
        exact pPrimeCore_coprime_card (p := 2) (G := G)
      have hcyclic_top :
          (⨆ (Y : Subgroup S) (_ : IsCyclic (S ⧸ Y)),
            fixedPointSubgroup (↥Y) (↥W)) = ⊤ :=
        iSup_fixedPointSubgroup_cyclicQuot_eq_top_of_noncyclic_abelian_pGroup_action
          (G := ↥W) (A := S) (p := 2) hcop (hncyc := hScyc)
      have hcyclic_le :
          (⨆ (Y : Subgroup S) (_ : IsCyclic (S ⧸ Y)),
            fixedPointSubgroup (↥Y) (↥W)) ≤
            ⨆ (S0 : Subgroup S) (_ : Nat.card S = 2 * Nat.card S0),
              fixedPointSubgroup (↥S0) (↥W) := by
        refine iSup₂_le ?_
        intro Y hYcyc
        by_cases hYtop : Y = ⊤
        · obtain ⟨M, hM⟩ := IsCoatomic.exists_coatom (Subgroup S)
          have hMquot : Nat.card (S ⧸ M) = 2 :=
            Theory.PGroup.card_quotient_coatom_eq_prime (p := 2) hM
          have hMcard : Nat.card S = 2 * Nat.card M := by
            simpa [hMquot] using
              (Subgroup.card_eq_card_quotient_mul_card_subgroup M)
          refine le_iSup_of_le M (le_iSup_of_le hMcard ?_)
          subst Y
          exact fixedPoints_subgroup_antitone S W le_top
        · letI : Y.Normal := inferInstance
          have hYelem : IsElementaryAbelian 2 (S ⧸ Y) := by
            refine
              { toIsMulCommutative := inferInstance
                exponent_dvd_p := ?_ }
            refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
            intro q
            obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective Y q
            have hs2 : s ^ 2 = 1 :=
              Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
                (IsElementaryAbelian.exponent_dvd_p 2 S) s
            simpa only [map_pow, map_one] using
              congrArg (QuotientGroup.mk' Y) hs2
          letI : IsElementaryAbelian 2 (S ⧸ Y) := hYelem
          letI : Nontrivial (S ⧸ Y) := QuotientGroup.nontrivial_iff.mpr hYtop
          have hYcardQ : Nat.card (S ⧸ Y) = 2 := by
            rw [← hYcyc.exponent_eq_card]
            exact IsElementaryAbelian.exponent_eq_prime
          have hYcard : Nat.card S = 2 * Nat.card Y := by
            simpa [hYcardQ] using
              (Subgroup.card_eq_card_quotient_mul_card_subgroup Y)
          exact le_iSup_of_le Y (le_iSup_of_le hYcard le_rfl)
      apply top_unique
      rw [← hcyclic_top]
      exact hcyclic_le
  have htopmap : (⊤ : Subgroup W).map W.subtype = W := by
    ext x
    simp
  have hterm (Y : Subgroup S) :
      (fixedPointSubgroup (↥Y) (↥W)).map W.subtype =
        W ⊓ Subgroup.centralizer
          ((Y.map (S : Subgroup G).subtype : Subgroup G) : Set G) := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w.property, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨s, hsY, rfl⟩
      have hsfix : (⟨s, hsY⟩ : Y) • w = w := hw ⟨s, hsY⟩
      have hSfix : (s : S) • w = w := by
        simpa only [Subgroup.smul_def] using hsfix
      have hconj : (s : G) * (w : G) * (s : G)⁻¹ = (w : G) :=
        (Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe_explicit
          (S : Subgroup G) W hSnormW s w).symm.trans
            (congrArg Subtype.val hSfix)
      have hmul := congrArg (fun z : G => z * (s : G)) hconj
      simpa [mul_assoc] using hmul
    · rintro ⟨hxW, hxcent⟩
      refine ⟨⟨x, hxW⟩, ?_, rfl⟩
      change ∀ y : Y, y • (⟨x, hxW⟩ : W) = ⟨x, hxW⟩
      intro y
      apply Subtype.ext
      have hymem : (y : G) ∈ Y.map (S : Subgroup G).subtype :=
        Subgroup.mem_map.mpr ⟨(y : S), y.property, rfl⟩
      have hycomm : (y : G) * x = x * (y : G) :=
        Subgroup.mem_centralizer_iff.mp hxcent (y : G) hymem
      calc
        ((y : S) • (⟨x, hxW⟩ : W) : W) =
            (y : G) * x * (y : G)⁻¹ :=
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe_explicit
            (S : Subgroup G) W hSnormW (y : S) ⟨x, hxW⟩
        _ = x := by rw [hycomm]; simp [mul_assoc]
  have hmap := congrArg (fun K : Subgroup W => K.map W.subtype) hindex_top
  simp only [Subgroup.map_iSup] at hmap
  simp_rw [hterm] at hmap
  rw [htopmap] at hmap
  simpa [W] using hmap.symm

end Stellmacher.SectionOne

module
public import Theory.SpecificGroups.OrthogonalFourBinary.SylowGeometry.SmallTwoSubgroups
public import Theory.SpecificGroups.OrthogonalFourBinary.CyclicFourOffenders
public import Theory.Representation.BinaryOffender.FourDimensionalCubic
public import Theory.Representation.BinaryOffender.FourDimensionalRatio
public import Theory.Representation.BinaryOffender.CubicRatio.Monotonicity
/-!
# Ratios of the natural binary omega four-space

Every elementary two-subgroup of the genuine Siegel-generated omega group
lies in the omega-part of a singular-point stabilizer, an elementary four-group.
An involution fixes four vectors and a whole four-group fixes two. Their action
ratios are therefore two and three halves. Four-groups act cubically, so the
latter attains the cubic infimum. The general four-dimensional non-FF argument
then gives quadratic ratio two.

Source: Aschbacher–Smith, original 15.1.8, printed p.1088. The coordinate counts
use the actual orthogonal group and its established 72 isometry coordinates.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped ENNReal
namespace OrthogonalFourBinary
open TerminalLines SylowGeometry
set_option synthInstance.maxSize 10000
private abbrev FixedVectors (B : Subgroup IsometryGroup) := {v : Space // ∀ g ∈ B, g.val v = v}
set_option maxRecDepth 10000 in
private theorem finite_involution_fixed : ∀ k : Code,
    (∃ v : Space, eval k v ≠ v) → k.1.2 = k.2.1.2 →
    (∀ v : Space, eval k (eval k v) = v) →
    Fintype.card {v : Space // eval k v = v} = 4 := by decide +kernel

set_option maxRecDepth 10000 in
private theorem finite_point_omega_fixed : ∀ x : Space, x ≠ 0 → q x = 0 →
    Fintype.card {v : Space // ∀ k : Code,
      eval k x = x → k.1.2 = k.2.1.2 → eval k v = v} = 2 := by decide +kernel

private theorem involution_fixed_card (g : Actor) (hg : g ∈ omega)
    (hne : g ≠ 1) (h2 : g ^ 2 = 1) : Nat.card {v : Space // g.val v = v} = 4 := by
  obtain ⟨k,rfl⟩ := codeMap_bijective.surjective g
  change Nat.card {v : Space // candidate k v = v} = 4
  simp_rw [candidate_eval]
  rw [Nat.card_eq_fintype_card]
  refine finite_involution_fixed k ?_ ((codeMap_mem_omega k).mp hg) ?_
  · by_contra! h
    apply hne
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    exact (candidate_eval k v).trans (h v)
  · intro v
    have hh := congrArg (fun a : Actor => a.val v) h2
    change candidate k (candidate k v) = v at hh
    simpa only [candidate_eval] using hh

private theorem point_omega_fixed_card (x : Space) (hx : x ≠ 0) (hqx : form x = 0) :
    Nat.card (FixedVectors (MulAction.stabilizer Actor x ⊓ omega)) = 2 := by
  let e : FixedVectors (MulAction.stabilizer Actor x ⊓ omega) ≃
      {v : Space // ∀ k : Code,
        eval k x = x → k.1.2 = k.2.1.2 → eval k v = v} :=
    (Equiv.refl Space).subtypeEquiv (fun v => by
      constructor
      · intro h k hk hp
        rw [← candidate_eval]
        exact h (codeMap k) ⟨(candidate_eval k x).trans hk,
          (codeMap_mem_omega k).mpr hp⟩
      · intro h g hg
        obtain ⟨k,rfl⟩ := codeMap_bijective.surjective g
        change candidate k v = v
        rw [candidate_eval]
        exact h k ((candidate_eval k x).symm.trans hg.1)
          ((codeMap_mem_omega k).mp hg.2))
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  exact finite_point_omega_fixed x hx hqx


/-- The natural action of the genuine Siegel-generated omega subgroup. -/
noncomputable abbrev omegaRepresentation : Representation (ZMod 2) omega Space :=
  naturalRepresentation.comp omega.subtype

private theorem fixedCodim_of_fixed_card (B : Subgroup IsometryGroup)
    (n : ℕ) (hc : Nat.card (FixedVectors B) = 2 ^ n) :
    fixedCodim naturalRepresentation B + n = 4 := by
  have he : Nat.card (fixedSpace naturalRepresentation B) = 2 ^ n := by
    let e : fixedSpace naturalRepresentation B ≃ FixedVectors B :=
      (Equiv.refl Space).subtypeEquiv (fun v => by
        constructor
        · intro h g hg; exact h ⟨g,hg⟩
        · intro h g; exact h g g.property)
    exact (Nat.card_congr e).trans hc
  have hp := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := fixedSpace naturalRepresentation B)
  rw [Nat.card_zmod,he] at hp
  have hn : Module.finrank (ZMod 2) (fixedSpace naturalRepresentation B) = n :=
    Nat.pow_right_injective (by decide : 2 ≤ 2) hp.symm
  simpa only [hn, Space, Plane, F, Module.finrank_prod, Module.finrank_self] using
    fixedCodim_add_finrank naturalRepresentation B

private theorem elementary_actor_cases (B : Subgroup IsometryGroup)
    (hB : IsElementaryTwo B) (hΩ : B ≤ omega) :
    (rank B = 1 ∧ fixedCodim naturalRepresentation B = 2) ∨
      (rank B = 2 ∧ fixedCodim naturalRepresentation B = 3) := by
  let := hB.2
  obtain ⟨S,hBS⟩ := (IsElementaryAbelian.isPGroup 2 B).exists_le_sylow
  obtain ⟨x,hx,hqx,hS⟩ := sylow_eq_point_stabilizer S
  let H : Subgroup IsometryGroup := MulAction.stabilizer IsometryGroup x ⊓ omega
  have hBH : B ≤ H := le_inf (hS ▸ hBS) hΩ
  have hH : Nat.card H = 4 := point_omega_card x hx hqx
  have hd : Nat.card B ∣ 4 := hH ▸ card_dvd_of_le hBH
  let : Nontrivial B := (Subgroup.nontrivial_iff_ne_bot B).mpr hB.1
  have hpos : 1 < Nat.card B := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  have hcard : Nat.card B = 2 ∨ Nat.card B = 4 := by
    have hle := Nat.le_of_dvd (by decide : 0 < 4) hd
    interval_cases h : Nat.card B <;> norm_num at *
  rcases hcard with hc | hc
  · left
    have hr : rank B = 1 := by norm_num [rank,hc]
    obtain ⟨g,hg⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB.1
    have hg1 : (g : IsometryGroup) ≠ 1 := fun he => hg (Subtype.ext he)
    have hg2 : (g : IsometryGroup)^2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ g.property
    have ho : orderOf (g : IsometryGroup) = 2 := orderOf_eq_prime hg2 hg1
    have hgen : zpowers (g : IsometryGroup) = B :=
      eq_of_le_of_card_ge (zpowers_le.mpr g.property) (by rw [Nat.card_zpowers,ho,hc])
    have hfix : Nat.card (FixedVectors B) = 4 := by
      rw [← hgen]
      let e : FixedVectors (zpowers (g : IsometryGroup)) ≃
          {v : Space // (g : IsometryGroup).val v = v} :=
        (Equiv.refl Space).subtypeEquiv (fun v => by
          change (∀ a ∈ zpowers (g : IsometryGroup), naturalRepresentation a v = v) ↔ _
          constructor
          · intro h; exact h g (mem_zpowers _)
          · intro h a ha
            exact ((mem_fixedSpace_zpowers_iff naturalRepresentation (g : IsometryGroup) v).mpr h) ⟨a,ha⟩)
      exact (Nat.card_congr e).trans (involution_fixed_card g (hΩ g.property) hg1 hg2)
    have hdim := fixedCodim_of_fixed_card B 2 hfix
    exact ⟨hr,by omega⟩
  · right
    have hEq : B = H := eq_of_le_of_card_ge hBH (by rw [hc,hH])
    have hfix : Nat.card (FixedVectors B) = 2 := hEq ▸ point_omega_fixed_card x hx hqx
    have hdim := fixedCodim_of_fixed_card B 1 hfix
    exact ⟨by norm_num [rank,hc],by omega⟩

/-- Every nontrivial elementary actor has ratio at least three halves. -/
theorem omega_actor_ratio_ge (A : Subgroup omega) (hA : IsElementaryTwo A) :
    3 / 2 ≤ actionRatio omegaRepresentation A := by
  let := hA.2
  let B := A.map omega.subtype
  have hB : IsElementaryTwo B := ⟨by
    intro he
    apply hA.1
    exact Subgroup.map_injective omega.subtype_injective (by simpa only [Subgroup.map_bot] using he),
    IsElementaryAbelian.map _⟩
  have hΩ : B ≤ omega := map_le_iff_le_comap.mpr (by simp)
  have hr : rank B = rank A := rank_map_injective omega.subtype omega.subtype_injective A
  have hf : fixedCodim omegaRepresentation A = fixedCodim naturalRepresentation B := by
    unfold fixedCodim
    rw [fixedSpace_comp_map]
  rcases elementary_actor_cases B hB hΩ with ⟨h1,h2⟩ | ⟨h1,h2⟩
  all_goals rw [actionRatio,hf,←hr,h1,h2]; norm_num [ENNReal.div_le_iff, ENNReal.lt_div_iff_mul_lt]

/-- A point stabilizer attains the cubic ratio three halves. -/
theorem omega_cubicRatio : cubicRatio omegaRepresentation = 3 / 2 := by
  apply le_antisymm
  · let x : Space := ((1,0),(1,0))
    have hx : x ≠ 0 := by decide
    have hqx : form x = 0 := by decide
    let H : Subgroup IsometryGroup := MulAction.stabilizer IsometryGroup x ⊓ omega
    have hH : Nat.card H = 4 := point_omega_card x hx hqx
    have hHΩ : H ≤ omega := inf_le_right
    let A := H.subgroupOf omega
    have hAcard : Nat.card A = 4 :=
      (Nat.card_congr (subgroupOfEquivOfLe hHΩ).toEquiv).trans hH
    have hmap : A.map omega.subtype = H := map_subgroupOf_eq_of_le hHΩ
    let : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by rw [hAcard]; decide)
    let : IsKleinFour A := ⟨hAcard,(Monoid.exponent_eq_prime_iff Nat.prime_two).mpr
      (fun a hne => orderOf_eq_prime (by
        apply Subtype.ext; apply Subtype.ext
        exact point_omega_square x hx hqx a.val.val a.property)
        hne)⟩
    let : IsElementaryAbelian 2 A :=
      { toIsMulCommutative := IsKleinFour.isMulCommutative
        exponent_dvd_p := by simp }
    have hA : IsElementaryTwo A := ⟨by intro he; rw [he,card_bot] at hAcard; omega,inferInstance⟩
    have hcod : fixedCodim omegaRepresentation A = 3 := by
      have hfix := fixedCodim_of_fixed_card H 1 (point_omega_fixed_card x hx hqx)
      have he : fixedCodim omegaRepresentation A = fixedCodim naturalRepresentation H := by
        unfold fixedCodim
        rw [fixedSpace_comp_map,hmap]
      omega
    have hr : rank A = 2 := by norm_num [rank,hAcard]
    have hbound : cubicRatio omegaRepresentation ≤ actionRatio omegaRepresentation A :=
      iInf_le_of_le A (iInf_le_of_le
        ⟨hA,isCubic_of_elementary_card_four omegaRepresentation A inferInstance hAcard⟩ le_rfl)
    simpa [actionRatio,hcod,hr] using hbound
  · exact le_iInf (fun A => le_iInf (fun hA => omega_actor_ratio_ge A hA.1))

/-- The natural omega four-space has quadratic ratio two. -/
theorem omega_quadraticRatio : quadraticRatio omegaRepresentation = 2 := by
  apply quadraticRatio_eq_two_of_four_cubic omegaRepresentation
  · simp [Space,Plane,F]
  · rw [omega_cubicRatio]; norm_num [ENNReal.div_le_iff, ENNReal.lt_div_iff_mul_lt]
  · rw [omega_cubicRatio]; norm_num [ENNReal.div_le_iff, ENNReal.lt_div_iff_mul_lt]
/-- Intertwining coordinates transfer both ratios to the original action. -/
theorem ratios_of_omega_coordinates {D V : Type*} [Group D] [Finite D]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (c : V ≃ₗ[ZMod 2] Space)
    (e : D ≃* omega) (he : ∀ g v, c (ρ g v) = (e g).val.val (c v)) :
    cubicRatio ρ = 3 / 2 ∧ quadraticRatio ρ = 2 := by
  have hi : ∀ g v, c.symm (omegaRepresentation g v) = ρ (e.symm g) (c.symm v) := by
    intro g v
    apply c.injective
    rw [c.apply_symm_apply,he,c.apply_symm_apply,e.apply_symm_apply]
    rfl
  have hq : cubicRatio ρ = 3 / 2 := le_antisymm
    ((cubicRatio_le_of_injective_equivariant omegaRepresentation ρ
      e.symm.toMonoidHom e.symm.injective c.symm hi).trans omega_cubicRatio.le)
    (omega_cubicRatio.symm.le.trans (cubicRatio_le_of_injective_equivariant ρ
      omegaRepresentation e.toMonoidHom e.injective c he))
  refine ⟨hq,quadraticRatio_eq_two_of_four_cubic ρ ?_ ?_ ?_⟩
  · rw [c.finrank_eq]; simp [Space,Plane,F]
  · rw [hq]; norm_num [ENNReal.lt_div_iff_mul_lt]
  · rw [hq]; norm_num [ENNReal.div_le_iff]

end OrthogonalFourBinary

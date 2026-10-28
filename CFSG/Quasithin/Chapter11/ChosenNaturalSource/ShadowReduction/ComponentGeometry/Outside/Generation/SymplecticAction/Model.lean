module
public import Theory.Representation.SymplecticNaturalNormalizer.Centralizers
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearLocalKernel
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.LocalCoreKernel

/-!
# Odd actions on the symplectic point section

An odd element of the actual binary natural normalizer which centralizes
L₁/O₂(L₁) is trivial when its order is coprime to the field-unit order.
The proved semilinear normal form and the point SL₂ quotient remove its
field twist. The determinant character then puts the inner representative
in L₁; the centerless quotient puts it in O₂(L₁). Odd order kills this
representative, and coprimality kills the remaining coefficient scalar.

This is the model calculation in source 11.4.4, consumed by the original
chosen-flag transport in Generation.SymplecticAction. It assumes neither
automorphism coverage nor a splitting of an ambient central cover.
Source: Aschbacher--Smith, printed p.778 of refs/quasithin.pdf. The native
symplectic APIs include the attributed ATLAS port; see LICENSES/ATLAS.txt.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Subgroup Representation Theory.GroupTheory
open scoped MatrixGroups commutatorElement
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open SymplecticConjugatePair.Ambient.Normalizer
open SymplecticNaturalNormalizer
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.SymplecticAction
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Finite F] [CharP F 2] [Algebra (ZMod 2) F] in
private theorem unit_eq_one_of_coprime (u : Fˣ) {r : ℕ}
    (hc : Nat.Coprime r (Nat.card F - 1)) (hu : u^r=1) : u=1 := by
  apply orderOf_eq_one_iff.mp
  apply Nat.eq_one_of_dvd_coprimes hc (orderOf_dvd_of_pow_eq_one hu)
  simpa only [Nat.card_units] using orderOf_dvd_natCard u

omit [Algebra (ZMod 2) F] in
private theorem quotient_trivial {n : ℕ}
  (hF : Nat.card F = 2^n) (hn : 1<n)
  (a : MulAut (Sp F)) (hK : pointLocal.map a.toMonoidHom = pointLocal)
  (hc : ∀ x ∈ pointLocal (F := F), a x / x ∈ (pointLocal (F := F)).pCoreIn 2) :
  pointSL2Action hF hn a hK = 1 := by
  apply MulEquiv.ext
  intro y
  obtain ⟨x,rfl⟩ := pointQuotient_surjective y
  rw [pointSL2Action_quotient]
  have hh : restrict a pointLocal hK x / x ∈ pCore 2 pointLocal := by
    exact (mem_map_iff_mem (pointLocal (F := F)).subtype_injective).mp (hc x x.property)
  rw [pointLocal_core_eq hF hn] at hh
  change pointQuotient (restrict a pointLocal hK x / x) = 1 at hh
  change pointQuotient (restrict a pointLocal hK x) = pointQuotient x
  exact div_eq_one.mp (by simpa only [map_div] using hh)

omit [Algebra (ZMod 2) F] in
private theorem inner_mem_core (g : Sp F) (hgl : g ∈ pointLocal)
  {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1<n)
  (hc : ∀ x ∈ pointLocal (F := F), (MulAut.conj g) x / x ∈ (pointLocal (F := F)).pCoreIn 2) :
  (⟨g,hgl⟩ : pointLocal) ∈ pCore 2 pointLocal := by
  rw [pointLocal_core_eq hF hn]
  change pointQuotient ⟨g,hgl⟩ = 1
  apply (mem_bot.mp : _ ∈ (⊥ : Subgroup SL(2,F)) → _)
  rw [←Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot]
  apply mem_center_iff.mpr
  intro y
  obtain ⟨x,rfl⟩ := pointQuotient_surjective y
  have hh := hc x x.property
  have hh' : ((⟨g,hgl⟩ : pointLocal)*x*⟨g,hgl⟩⁻¹)/x ∈ pCore 2 pointLocal :=
    (mem_map_iff_mem (pointLocal (F := F)).subtype_injective).mp hh
  rw [pointLocal_core_eq hF hn] at hh'
  rw [←pointQuotient_ker,MonoidHom.mem_ker] at hh'
  rw [map_div,div_eq_one,map_mul,map_mul,map_inv] at hh'
  exact (mul_inv_eq_iff_eq_mul.mp hh').symm

/-- Odd natural normalizers acting trivially on the point-local quotient are
trivial when their order is coprime to the field-unit order. -/
theorem odd_coprime_point_section_eq_one {n r : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1<n)
    (s : naturalNormalizer (F := F))
    (ho : Odd r) (hcop : Nat.Coprime r (Nat.card F - 1)) (hs : s^r=1)
    (hc : ∀ x ∈ pointLocal (F := F),
      conjugation (by rw [hF]; exact (show (2:ℕ)^1 < 2^n from Nat.pow_lt_pow_right (by decide) hn)) s x / x ∈
        (pointLocal (F := F)).pCoreIn 2) : s=1 := by
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact (show (2:ℕ)^1 < 2^n from Nat.pow_lt_pow_right (by decide) hn)
  let a := conjugation hlarge s
  change ∀ x ∈ pointLocal (F := F), a x / x ∈ (pointLocal (F := F)).pCoreIn 2 at hc
  have hK : pointLocal.map a.toMonoidHom = pointLocal := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      have hh := (pointLocal (F := F)).mul_mem (pCoreIn_le 2 _ (hc x hx)) hx
      change a x ∈ pointLocal
      simpa only [div_mul_cancel] using hh
    · exact (Subgroup.card_map_of_injective a.injective).ge
  obtain ⟨g,σ,he⟩ := conjugation_semilinear hlarge s
  change a = _ at he
  have hKg : pointLocal.map ((MulAut.conj g)*fieldAutomorphism σ).toMonoidHom = pointLocal := he ▸ hK
  have hag := quotient_trivial hF hn _ hKg (by simpa only [he] using hc)
  have hσ := pointSL2Action_semilinear_field_eq_refl hF hn g σ hKg hag
  have hf : fieldAutomorphism (RingEquiv.refl F) = 1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rfl
  have ha : a = MulAut.conj g := by
    rw [he,hσ,hf,mul_one]
  have hgr : g^r=1 := by
    apply InvolutionNormalForms.inner_injective
    rw [map_pow,←ha]
    change conjugation hlarge s ^ r = _
    rw [←map_pow,hs,map_one,map_one]
  have hg : g ∈ pointParabolic := point_semilinear_mem_parabolic hF hn g σ hKg
  have hχ : determinantCharacter (point F) ⟨g,hg⟩ = 1 := by
    apply unit_eq_one_of_coprime _ hcop
    rw [←map_pow,show (⟨g,hg⟩ : pointParabolic)^r=1 from Subtype.ext hgr,map_one]
  have hgl : g ∈ pointLocal := ⟨⟨g,hg⟩,hχ,rfl⟩
  have hgc := inner_mem_core g hgl hF hn (by simpa only [ha] using hc)
  have hg1 : g=1 := by
    let u : pCore 2 (pointLocal (F := F)) := ⟨⟨g,hgl⟩,hgc⟩
    obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := pointLocal (F := F))).exists_card_eq
    have hu : u=1 := by
      apply orderOf_eq_one_iff.mp
      apply Nat.eq_one_of_dvd_coprimes (ho.coprime_two_right.pow_right k)
        (orderOf_dvd_of_pow_eq_one (show u^r=1 from Subtype.ext (Subtype.ext hgr)))
      exact hk ▸ orderOf_dvd_natCard u
    exact congrArg (fun v : pCore 2 (pointLocal (F := F)) => v.val.val) hu
  have ha1 : conjugation hlarge s = 1 := by
    change a=1
    rw [ha,hg1,map_one]
  obtain ⟨c,hc⟩ := (conjugation_eq_one_iff_scalar hlarge s).mp ha1
  have hcr : c^r=1 := by
    have hp (k : ℕ) (v : Vector F) : (s^k).val v = c^k • v := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ']
        change s.val ((s^k).val v) = _
        rw [hc,ih,smul_smul,pow_succ']
    have hh := congrArg (fun t : naturalNormalizer (F := F) =>
      t.val (Pi.single (.inl 0) 1) (.inl 0)) hs
    rw [hp] at hh
    simpa using hh
  have hc0 : c≠0 := by intro he; simp [he,ho.pos.ne'] at hcr
  have hc1 : c=1 := by
    exact congrArg Units.val (unit_eq_one_of_coprime (Units.mk0 c hc0) hcop (Units.ext hcr))
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change s.val v = v
  simpa only [hc1,one_smul] using hc v

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.SymplecticAction

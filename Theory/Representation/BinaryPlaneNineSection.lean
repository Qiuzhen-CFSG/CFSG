module
public import Theory.GroupTheory.NineSectionCubicGeneration
public import Theory.Representation.BinaryPlaneCubic
-- Internal companion proof: unfold the cubic permutation construction only
-- in the private kernel comparison, without exposing its implementation.
import all Theory.Representation.BinaryPlaneCubic

/-!
# Cubic kernels on a binary plane

An elementary group of order nine acting nontrivially on a binary plane
has image of order three and kernel of order three. Any two-group
preserving that plane also preserves this kernel. Combined with coprime
complements, this produces two Sylow-index-three overgroups in the
Borel section of the determinant tensor.
-/

public noncomputable section
open Subgroup Module
namespace Representation.BinaryPlane
open BinaryLinear.SmallParabolicLevi
variable {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private theorem symmetricThreeHom_eq_one_iff [Finite A]
    (ρ : Representation (ZMod 2) A V) (hd : finrank (ZMod 2) V = 2) (a : A) :
    symmetricThreeHom ρ hd a = 1 ↔ ρ a = 1 := by
  let e : V ≃ₗ[ZMod 2] BinaryLinear.OuterCyclic.Space 2 :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using hd)
  change (linearGroupCongr e |>.trans linearTwoEquivSymmetricThree)
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V (ρ.asGroupHom a)) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff,MulEquiv.map_eq_one_iff]
  exact Units.ext_iff

variable [Finite A]

/-- A nontrivial action of an elementary nine-section on a binary plane
has a cubic kernel, invariant under every automorphism preserving the plane. -/
theorem nine_section_invariant_cubic
    (ρ : Representation (ZMod 2) A V) (S : Sylow 2 A) (B : Subgroup A)
    (hSB : (S : Subgroup A) ≤ normalizer (B : Set A))
    [IsElementaryAbelian 3 (B ⧸ pCore 2 B)]
    (hc : Nat.card (B ⧸ pCore 2 B) = 9)
    (W : Submodule (ZMod 2) V) (hd : finrank (ZMod 2) W = 2)
    (hBW : ∀ b ∈ B, ∀ w ∈ W, ρ b w ∈ W)
    (hSW : ∀ s ∈ (S : Subgroup A), ∀ w ∈ W, ρ s w ∈ W)
    (hQ : ∀ b ∈ pCore 2 B, ∀ w ∈ W, ρ (b:A) w = w)
    (hne : ∃ b ∈ B, ∃ w ∈ W, ρ b w ≠ w) :
    ∃ D : Subgroup (B ⧸ pCore 2 B), Nat.card D = 3 ∧
      ∀ s : S, ∀ x ∈ D, sylowCoreAction S B hSB s x ∈ D := by
  let Wb : Subrepresentation (ρ.comp B.subtype) := ⟨W,fun b _ hw => hBW b b.property _ hw⟩
  let σ := Wb.toRepresentation
  let f := symmetricThreeHom σ hd
  have hf (b : B) : f b = 1 ↔ ∀ w ∈ W, ρ (b:A) w = w := by
    rw [symmetricThreeHom_eq_one_iff]
    constructor
    · intro hb w hw
      exact congrArg Subtype.val (LinearMap.congr_fun hb ⟨w,hw⟩)
    · intro hb
      apply LinearMap.ext
      intro w
      exact Subtype.ext (hb w w.property)
  have hQf : pCore 2 B ≤ f.ker := fun b hb => (hf b).mpr (hQ b hb)
  let q := QuotientGroup.mk' (pCore 2 B)
  let fQ := QuotientGroup.lift (pCore 2 B) f hQf
  have hqf (b : B) : fQ (q b) = f b := rfl
  have hr : Nat.card fQ.range = 3 := by
    have hdiv : Nat.card fQ.range ∣ 6 := by
      have hh := fQ.range.card_subgroup_dvd_card
      simpa only [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin,
        show Nat.factorial 3 = 6 from rfl] using hh
    have hpg : IsPGroup 3 fQ.range :=
      (IsElementaryAbelian.isPGroup 3 (B ⧸ pCore 2 B)).of_surjective
        fQ.rangeRestrict fQ.rangeRestrict_surjective
    obtain ⟨n,hn⟩ := hpg.exists_card_eq
    have hnle : n ≤ 1 := by
      by_contra hh
      have hbad : 9 ∣ 6 := (pow_dvd_pow 3 (by omega : 2 ≤ n)).trans (hn ▸ hdiv)
      norm_num at hbad
    have hnzero : n ≠ 0 := by
      intro hn0
      have ht : fQ.range = ⊥ := (card_eq_one.mp (by simpa [hn0] using hn))
      obtain ⟨b,hb,w,hw,hmove⟩ := hne
      have he : f ⟨b,hb⟩ = 1 := by
        have hh : fQ (q ⟨b,hb⟩) ∈ fQ.range := ⟨q ⟨b,hb⟩,rfl⟩
        rwa [ht,mem_bot,hqf] at hh
      exact hmove ((hf _).mp he w hw)
    have he : n = 1 := by omega
    simpa only [he,pow_one] using hn
  have hD : Nat.card fQ.ker = 3 := by
    have hh := fQ.ker.card_mul_index
    rw [Subgroup.index_ker,hr,hc] at hh
    omega
  refine ⟨fQ.ker,hD,?_⟩
  intro s x hx
  obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) x
  have hb : ∀ w ∈ W, ρ (b:A) w = w := (hf b).mp hx
  let a := B.normalizerMonoidHom ⟨s,hSB s.property⟩
  rw [sylowCoreAction_mk]
  change f (a b) = 1
  apply (hf (a b)).mpr
  intro w hw
  have hsW : ρ (s:A)⁻¹ w ∈ W := hSW _ (S.inv_mem s.property) w hw
  have hh := congrArg (ρ (s:A)) (hb _ hsW)
  have hval : (a b : A) = (s:A) * (b:A) * (s:A)⁻¹ :=
    normalizerMonoidHom_apply_apply_coe B ⟨s,hSB s.property⟩ b
  rw [hval]
  simpa only [← Module.End.mul_apply,← map_mul,mul_inv_cancel,map_one,
    Module.End.one_apply,mul_assoc] using hh
end Representation.BinaryPlane

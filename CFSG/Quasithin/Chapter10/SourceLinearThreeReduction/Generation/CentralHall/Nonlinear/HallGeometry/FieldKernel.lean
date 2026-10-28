module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.Semilinear
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Module.Coprimality
public import Theory.SpecificGroups.SL2.SylowTorusKernel
public import Theory.GroupTheory.NormalizerQuotientInner

/-!
# The field-action kernel is the original Hall orbit intersection

The common Sylow and torus marking expresses the Hall action as diagonal
inner automorphisms followed by coefficient automorphisms. Traces show that
its coefficient kernel is precisely the subgroup inducing inner actions.
Its faithful diagonal characters restrict its prime divisors to those of
the component quotient. The original two-component rank bound makes the
literal section centralizer coprime to these primes. Coprime-kernel lifting
therefore places this subgroup inside L₀, proving ker(φ) = B_H ∩ L₀.

The final existence theorem supplies this equality, faithful characters and
their exponent bound in the same original component and Sylow marking.
It discharges the identification of B⁺ in the automorphism step of 10.2.3.
The complement construction, field-factor elimination and module-row
calculations remain with qt-d-10-nona5-central-hall-orders; the kernel
identification alone does not prove SourceNonnormalCentralHallAt.

Source: Aschbacher--Smith 10.2.3, printed p.745, using the prime-rank
section-centralizer consequence of 1.2.2, printed pp.503--504.
-/

public noncomputable section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
open Chapter3.Section02 Chapter4 Matrix.SpecialLinearGroup BenderSuzuki.ZD.Linear
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite G] in
private theorem quotient_action_kernel_le_section (R : Subgroup G) :
    (normalizerQuotientAction R (pCore 2 R)).ker.map
      (normalizer (R : Set G)).subtype ≤ sectionCentralizer R := by
  apply (le_sectionCentralizer_iff _ _).mpr
  refine ⟨map_subtype_le _,commutator_le.mpr ?_⟩
  rintro _ ⟨b,hb,rfl⟩ r hr
  have hbr := DFunLike.congr_fun (show normalizerQuotientAction R (pCore 2 R) b = 1 from hb)
    (QuotientGroup.mk' (pCore 2 R) ⟨r,hr⟩)
  change quotientAut (pCore 2 R) _ _ = _ at hbr
  rw [quotientAut_apply_mk] at hbr
  let r' : R := ⟨r,hr⟩
  let br := R.normalizerMonoidHom b r'
  have hh : br * r'⁻¹ ∈ pCore 2 R := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (pCore 2 R) (br * r'⁻¹) = 1
    rw [map_mul,map_inv]
    change QuotientGroup.mk' (pCore 2 R) br = QuotientGroup.mk' (pCore 2 R) r' at hbr
    rw [hbr,mul_inv_cancel]
  exact ⟨br * r'⁻¹,hh,rfl⟩

include D in
omit [Finite F] in
/-- An original Hall actor has trivial field coordinates exactly when it lies
in the original component orbit. The reverse inner-to-orbit implication uses
the actual section-centralizer coprimality, not faithfulness alone. -/
theorem hall_field_kernel_eq_orbit {H : Subgroup G} {B : Subgroup H}
    (c : Context D H B) (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (q : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃* (SL(2,F) × SL(2,F)))
    (φ : B →* ((F ≃+* F) × (F ≃+* F)))
    (hd : ∀ b, ∃ d : Fˣ × Fˣ, MulAut.congr q (action D B c.hall_le b) =
      (MulAut.conj (splitDiagonalHom d.1) * sl2FieldAut (φ b).1).prodCongr
        (MulAut.conj (splitDiagonalHom d.2) * sl2FieldAut (φ b).2)) :
    φ.ker = (localOrbit T L).comap (H.subtype.comp B.subtype) := by
  let R := localOrbit T L
  let f := H.subtype.comp B.subtype
  have hf : Function.Injective f := H.subtype_injective.comp B.subtype_injective
  let ρ := (MulAut.congr q).toMonoidHom.comp (action D B c.hall_le)
  have hρ : Function.Injective ρ := (MulAut.congr q).injective.comp
    (action_injective D B c.hall_le c.faithful)
  obtain ⟨χ,hχ⟩ := exists_pair_field_kernel_characters ρ φ hd
  have hχi := pair_field_kernel_characters_injective ρ hρ φ χ hχ
  have hinner (b : B) : φ b = 1 ↔ action D B c.hall_le b ∈
      MulAut.innerSubgroup (R ⧸ pCore 2 R) := by
    rw [pair_diagonal_field_inner_iff ρ φ hd b,←MulAut.map_innerSubgroup_congr q]
    exact mem_map_iff_mem (MulAut.congr q).injective
  let C := φ.ker.map f
  have hCM : C ≤ D.maximalLocal := by
    rintro _ ⟨b,_,rfl⟩
    exact c.hall_le b.property
  have hc : Nat.Coprime (Nat.card C) (Nat.card (sectionCentralizer R)) := by
    rw [show Nat.card C = Nat.card φ.ker from card_map_of_injective hf]
    apply Nat.coprime_of_dvd
    intro p hp hpK hpC
    let : Fact p.Prime := ⟨hp⟩
    have hpB := hpK.trans (card_subgroup_dvd_card φ.ker)
    have hp2 : p ≠ 2 := by
      intro he
      subst p
      exact (Nat.not_even_iff_odd.mpr (hall_odd D c)) (even_iff_two_dvd.mpr hpB)
    have hunit : p ∣ Nat.card Fˣ := by
      have hh := hpK.trans (card_dvd_of_injective χ hχi)
      rw [Nat.card_prod] at hh
      exact (hp.dvd_mul.mp hh).elim id id
    have hSL := hunit.trans (card_dvd_of_injective
      (splitDiagonalHom (F := F)) splitDiagonalHom_injective)
    have hL : p ∣ Nat.card (L ⧸ pCore 2 L) := by rwa [Nat.card_congr e.toEquiv]
    exact hp.coprime_iff_not_dvd.mp
      (source_nonnormal_sectionCentralizer_prime_coprime D c.nonnormal p hp2 hL) hpC
  have hkcard : Nat.card (normalizerQuotientAction R (pCore 2 R)).ker ∣
      Nat.card (sectionCentralizer R) := by
    rw [←card_map_of_injective (normalizer (R : Set G)).subtype_injective]
    exact card_dvd_of_le (quotient_action_kernel_le_section R)
  have hCR : C ≤ R := le_of_normalizerQuotientAction_inner R (pCore 2 R) C hCM
    (hc.coprime_dvd_right hkcard) (by
      rintro _ ⟨a,ha,rfl⟩
      obtain ⟨b,hb,hba⟩ := ha
      have he : a = (⟨f b,c.hall_le b.property⟩ : D.maximalLocal) := Subtype.ext hba.symm
      rw [he]
      exact (hinner b).mp hb)
  apply le_antisymm
  · intro b hb
    exact hCR (mem_map_of_mem f hb)
  · intro b hb
    apply (hinner b).mpr
    refine ⟨QuotientGroup.mk' (pCore 2 R) ⟨f b,hb⟩,?_⟩
    exact (normalizerPCoreQuotientAction_inner R ⟨f b,hb⟩).symm

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry

namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
open Chapter3.Section02 Chapter4 Matrix.SpecialLinearGroup BenderSuzuki.ZD.Linear
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type*} [Field F] [Finite F] [CharP F 2]
include D

/-- The coefficient action has exactly the original orbit intersection as
kernel. Its faithful diagonal characters retain the same component and Sylow
marking; their exponent is bounded by the field order minus one. -/
theorem exists_hall_field_kernel_coordinates {H : Subgroup G} {B : Subgroup H}
    (c : Context D H B) (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    ∃ (e' : (L ⧸ pCore 2 L) ≃* SL(2,F))
      (q : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃* (SL(2,F) × SL(2,F)))
      (φ : B →* ((F ≃+* F) × (F ≃+* F)))
      (χ : φ.ker →* Fˣ × Fˣ),
      (∀ l : L, q (QuotientGroup.mk' (pCore 2 (localOrbit T L))
        ⟨l,le_componentOrbit L T l.property⟩) =
          (e' (QuotientGroup.mk' (pCore 2 L) l),1)) ∧
      ((T : Subgroup G).subgroupOf (localOrbit T L)).map
        (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localOrbit T L)))) =
          (upperUnipotent F).prod (upperUnipotent F) ∧
      Odd (Nat.card φ.range) ∧
      φ.ker = (localOrbit T L).comap (H.subtype.comp B.subtype) ∧
      Function.Injective χ ∧
      Monoid.exponent φ.ker ∣ Nat.card F - 1 ∧
      (∀ (b : φ.ker) (x : localOrbit T L ⧸ pCore 2 (localOrbit T L)),
        q (action D B c.hall_le b x) =
          (diag2 ((χ b).1:F) (χ b).1.ne_zero,diag2 ((χ b).2:F) (χ b).2.ne_zero) * q x *
            (diag2 ((χ b).1:F) (χ b).1.ne_zero,diag2 ((χ b).2:F) (χ b).2.ne_zero)⁻¹) ∧
      ∀ b : B, ∃ d : Fˣ × Fˣ,
        MulAut.congr q (action D B c.hall_le b) =
          (MulAut.conj (diag2 (d.1:F) d.1.ne_zero) * sl2FieldAut (φ b).1).prodCongr
            (MulAut.conj (diag2 (d.2:F) d.2.ne_zero) * sl2FieldAut (φ b).2) := by
  obtain ⟨e',q,φ,hcomp,hS,ho,_hφ,hd⟩ := exists_hall_diagonal_field_action D c e
  let ρ := (MulAut.congr q).toMonoidHom.comp (action D B c.hall_le)
  have hρ : Function.Injective ρ := (MulAut.congr q).injective.comp
    (action_injective D B c.hall_le c.faithful)
  have hd' : ∀ b, ∃ d : Fˣ × Fˣ, ρ b =
      (MulAut.conj (splitDiagonalHom d.1) * sl2FieldAut (φ b).1).prodCongr
        (MulAut.conj (splitDiagonalHom d.2) * sl2FieldAut (φ b).2) := by
    intro b
    obtain ⟨d,he⟩ := hd b
    refine ⟨d,?_⟩
    change MulAut.congr q (action D B c.hall_le b) = _
    simpa only [splitDiagonalHom_apply] using he
  obtain ⟨χ,hχ⟩ := exists_pair_field_kernel_characters ρ φ hd'
  refine ⟨e',q,φ,χ,hcomp,hS,ho,hall_field_kernel_eq_orbit D c e' q φ hd',
    pair_field_kernel_characters_injective ρ hρ φ χ hχ,
    pair_field_kernel_exponent_dvd ρ hρ φ χ hχ,?_,hd⟩
  intro b x
  have hh := MulEquiv.congr_fun (DFunLike.congr_fun hχ b) (q x)
  change splitDiagonalPairAction (χ b) (q x) =
    q (action D B c.hall_le b (q.symm (q x))) at hh
  rw [q.symm_apply_apply,splitDiagonalPairAction_apply,splitDiagonalHom_apply,
    splitDiagonalHom_apply] at hh
  exact hh.symm

omit [Finite F] in
/-- Field-factor elimination places the actual original Hall subgroup inside
L₀. This uses the proved kernel equality, rather than assuming that an inner
quotient action already implies ambient subgroup containment. -/
theorem hall_le_orbit_of_field_action_trivial {H : Subgroup G} {B : Subgroup H}
    (c : Context D H B) (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (q : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃* (SL(2,F) × SL(2,F)))
    (φ : B →* ((F ≃+* F) × (F ≃+* F)))
    (hd : ∀ b, ∃ d : Fˣ × Fˣ, MulAut.congr q (action D B c.hall_le b) =
      (MulAut.conj (splitDiagonalHom d.1) * sl2FieldAut (φ b).1).prodCongr
        (MulAut.conj (splitDiagonalHom d.2) * sl2FieldAut (φ b).2))
    (hφ : φ = 1) : B.map H.subtype ≤ localOrbit T L := by
  have hk := hall_field_kernel_eq_orbit D c e q φ hd
  rintro _ ⟨b,hb,rfl⟩
  have hh : (⟨b,hb⟩ : B) ∈ φ.ker := by simp [hφ]
  change (⟨b,hb⟩ : B) ∈ (localOrbit T L).comap (H.subtype.comp B.subtype)
  rwa [←hk]

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry

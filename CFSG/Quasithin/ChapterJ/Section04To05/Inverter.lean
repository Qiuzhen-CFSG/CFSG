module

public import CFSG.Quasithin.ChapterJ.Section04To05.Setup.SourceChoice
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.FiveCore.SourceCompletion.Seed

/-!
# The unchanged source element inverts a Sylow five-subgroup

The element v selected in Uα minus Q is an involution in S, hence in K.
Its image in the actual K/Q = A₅ quotient is nontrivial. The proved
involution lifting argument constructs a subgroup of order five inverted
by this same v. Since the original H has five-part five, it is Sylow.
No conjugation or replacement of the source element is made.

Source: Aschbacher–Smith, J.4.1(2), first assertion, printed p.440.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} {p : Plane d}
private instance primeFive : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The selected source element is an actual involution. -/
theorem SourceChoice.v_order (s : SourceChoice p) : orderOf s.v = 2 := by
  let : IsElementaryAbelian 2 d.toTypeRuSetup.U := d.elementary_U
  apply orderOf_eq_prime
  · obtain ⟨u,hu,he⟩ := s.v_mem
    rw [← he,← map_pow,elemPow_eq_one_of_isElementaryAbelian u hu (p:=2),map_one]
  · exact fun h => s.v_not_Q (h ▸ d.toTypeRuSetup.Q.one_mem)

/-- The selected source element lies in the original two-residual K. -/
theorem SourceChoice.v_mem_K (s : SourceChoice p) : s.v ∈ d.toTypeRuSetup.K :=
  (d.S_le_L₁.trans (embedded_pResidual_mono 2 inf_le_right))
    (ConjugateIntersections.conjugateU_le_S d s.g (p.L₂_le_L s.in_residual) s.v_mem)

/-- J.4.1(2): the unchanged chosen v inverts an actual Sylow five-subgroup of H. -/
theorem SourceChoice.inverts_sylow_five (s : SourceChoice p) :
    ∃ B5 : Sylow 5 d.toTypeRuSetup.H,
      ∀ a ∈ (B5 : Subgroup d.toTypeRuSetup.H).map d.toTypeRuSetup.H.subtype,
        s.v * a * s.v⁻¹ = a⁻¹ := by
  let w : d.toTypeRuSetup.H := ⟨s.v,d.toTypeRuSetup.K_le_H s.v_mem_K⟩
  have hw : w ^ 2 = 1 := Subtype.ext (s.v_order ▸ pow_orderOf_eq_one s.v)
  obtain ⟨A,hA,hi⟩ := Centralizers.Choices.inverted_five_in_H w hw s.v_mem_K s.v_not_Q
  obtain ⟨B5,hAB⟩ := (IsPGroup.of_card (p:=5) (n:=1) hA).exists_le_sylow
  have hB5 : Nat.card B5 = 5 := by
    rw [B5.card_eq_multiplicity,d.ru2.card_H d.card_Z]
    decide +kernel
  have he : A = (B5 : Subgroup d.toTypeRuSetup.H) :=
    eq_of_le_of_card_ge hAB (by rw [hA,hB5])
  refine ⟨B5,?_⟩
  rintro a ⟨b,hb,rfl⟩
  have hh := hi b (he ▸ hb)
  exact congrArg (fun x : d.toTypeRuSetup.H => (x:G)) hh

end CFSG.Quasithin.ChapterJ.RuSubgroup

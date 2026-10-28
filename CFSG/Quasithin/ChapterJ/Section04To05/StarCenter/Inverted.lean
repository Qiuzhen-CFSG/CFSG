module

public import CFSG.Quasithin.ChapterJ.Section04To05.StarCenter
public import CFSG.Quasithin.ChapterJ.Section04To05.Inverter
public import Theory.SpecificGroups.SymmetricFive.StarCenterGeometry

/-!
# The exact two pentagons inverted by the original source element

The chosen v lies in K, so its nontrivial star image is an even involution
in the original S₅ quotient. The concrete pentagon count gives exactly two
inverted Sylow five-subgroups there. Together with the genuine unchanged-v
lifting theorem, this completes both assertions of J.4.1(2).

Source: Aschbacher–Smith, J.4.1(1–2), printed p.440.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} {p : Plane d}

/-- The original star image of v belongs to the marked alternating subgroup. -/
theorem SourceChoice.starInvolution_even (s : SourceChoice p) :
    s.starInvolution ∈ alternatingGroup (Fin 5) := by
  rw [s.starInvolution_eq,← d.toTypeRuSetup.quotientMap_K]
  exact ⟨⟨s.v,(s.conjugate_properties p).1 s.v_mem⟩,s.v_mem_K,rfl⟩

/-- J.4.1(2), second assertion, in the literal original quotient. -/
theorem SourceChoice.star_inverts_two (s : SourceChoice p) :
    Nat.card {P : Sylow 5 S5 // ∀ x ∈ (P : Subgroup S5),
      s.starInvolution*x*s.starInvolution⁻¹=x⁻¹} = 2 :=
  Theory.SpecificGroups.SymmetricFive.StarCenterGeometry.inverted_sylow_count
    s.starInvolution s.starInvolution_order s.starInvolution_even

/-- The full original-source center and inverter conclusions of J.4.1(1–2). -/
theorem SourceChoice.source_star_geometry (s : SourceChoice p) :
    zpowers s.starInvolution = centerIn
      (((d.T : Subgroup G).subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap) ∧
    Nat.card (centerIn
      (((d.T : Subgroup G).subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap)) = 2 ∧
    (∃ B5 : Sylow 5 d.toTypeRuSetup.H,
      ∀ a ∈ (B5 : Subgroup d.toTypeRuSetup.H).map d.toTypeRuSetup.H.subtype,
        s.v*a*s.v⁻¹=a⁻¹) ∧
    Nat.card {P : Sylow 5 S5 // ∀ x ∈ (P : Subgroup S5),
      s.starInvolution*x*s.starInvolution⁻¹=x⁻¹} = 2 := by
  refine ⟨s.starInvolution_generates.trans s.starPoint_eq_center,?_,
    s.inverts_sylow_five,s.star_inverts_two⟩
  rw [← s.starPoint_eq_center,s.starPoint_card]

end CFSG.Quasithin.ChapterJ.RuSubgroup

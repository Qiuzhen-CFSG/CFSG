module

public import CFSG.Quasithin.ChapterJ.Section04To05.StarCenter.Inverted
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveDecomposition.PlaneDisplacement
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveDecomposition.Center
public import CFSG.Quasithin.ChapterJ.Section01To02.SourceCompletion.Local

/-!
# All seven clauses of the original J.4.1

One Sylow five-subgroup is chosen inverted by the unchanged source element
v. The actual quotient center, finite Sylow count, quaternion centralizer,
coprime decomposition, conjugate intersection and both displacement clauses
are then assembled for this same choice. The source choices needed by the
earlier J.2 arguments are constructed from the original local setup.

Source: Aschbacher–Smith, J.4.1, printed p.440.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} {p : Plane d}

/-- The complete J.4.1, preserving the original d, plane, g, v and quotient maps. -/
theorem SourceChoice.source_lemma_J_4_1 (s : SourceChoice p) :
    ∃ B5 : Sylow 5 d.toTypeRuSetup.H,
      (zpowers s.starInvolution =
        (s.Uα.subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap ∧
       (s.Uα.subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap = centerIn
        (((d.T : Subgroup G).subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap) ∧
       Nat.card ((s.Uα.subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap) = 2) ∧
      ((∀ a ∈ B5Image B5, s.v*a*s.v⁻¹=a⁻¹) ∧
       Nat.card {P : Sylow 5 S5 // ∀ x ∈ (P : Subgroup S5),
         s.starInvolution*x*s.starInvolution⁻¹=x⁻¹} = 2) ∧
      (d.toTypeRuSetup.U ≤ Q₅ d B5 ∧
       IsElementaryAbelian 2 (hat d (Q₅ d B5)) ∧
       Nat.card (hat d (Q₅ d B5)) = 16 ∧
       Nonempty (CQ B5 ≃* QuaternionGroup 2) ∧
       hat d d.toTypeRuSetup.Q = hat d (CQ B5) ⊔ hat d (Q₅ d B5) ∧
       Disjoint (hat d (CQ B5)) (hat d (Q₅ d B5))) ∧
      Nat.card (center (Hat d)) = 2 ∧
      s.Uα ⊓ d.toTypeRuSetup.HC = d.V ∧
      (hat d s.Dα = ⁅hat d p.CQ₂,hat d s.Uα⁆ ∧
       hat d s.Dα ≤ hat d (Q₅ d B5) ∧ Nat.card (hat d s.Dα) = 2) ∧
      ⁅hat d d.toTypeRuSetup.Q,hat d s.Uα⁆ ≤ hat d (Q₅ d B5) := by
  obtain ⟨B5,hi,hline,hcard,hle,hseven⟩ := s.source_six_seven
  obtain ⟨c⟩ := SourceCompletion.exists_choices d
  refine ⟨B5,?_,⟨hi,s.star_inverts_two⟩,five_decomposition d B5 c,
    center_hat_card d,s.conjugate_properties.2.2,⟨hline,hle,hcard⟩,hseven⟩
  refine ⟨s.starInvolution_generates.trans s.starPoint_eq_image,?_,?_⟩
  · exact s.starPoint_eq_image.symm.trans s.starPoint_eq_center
  · exact s.starPoint_eq_image ▸ s.starPoint_card

end CFSG.Quasithin.ChapterJ.RuSubgroup

module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveNormalizer.Order
public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicCentralizers
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# The complete original first-parabolic source family

The proved ambient centralizer C_G(Q₅)=Z and Q₅≤O₂(F₁) make the
original two-core self-centralizing. Hence F₁ has characteristic two.
Together with the exact Suzuki quotient, common Sylow subgroup and
normalizer, this supplies the first endpoint for the source amalgam.
The final existence theorem chooses a Sylow five-subgroup inverted by the
unchanged source v, discharging the only intermediate selection condition.

Source: Aschbacher–Smith, J.4.4(3–4), J.4.5(3) and the setup of J.4.5,
printed pp.441–442. All subgroups remain in the original LocalSetup.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} (p:Plane d)

theorem SourceChoice.F₁_core_selfCentralizing (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    centralizer (pCore 2 (p.F₁ B5):Set (p.F₁ B5))≤pCore 2 (p.F₁ B5) := by
  intro x hx
  have hxc : (x:G)∈centralizer (Q₅ d B5:Set G) := by
    apply mem_centralizer_iff.mpr
    intro q hq
    let qF:p.F₁ B5:=⟨q,(show Q₅ d B5≤p.F₁ B5 from le_sup_right.trans le_sup_left) hq⟩
    have hqemb : (qF:G)∈(p.F₁ B5).pCoreIn 2 := by
      rw [s.F₁_core_eq_fiveHyperplane p B5 hi]
      exact (show Q₅ d B5≤fiveHyperplane d B5 from le_sup_right) hq
    have hqcore : qF∈pCore 2 (p.F₁ B5) :=
      (mem_map_iff_mem (p.F₁ B5).subtype_injective).mp hqemb
    exact congrArg (fun a:p.F₁ B5=>(a:G)) (mem_centralizer_iff.mp hx qF hqcore)
  have hxZ : (x:G)∈d.toTypeRuSetup.Z := centralizer_Q₅ d B5 ▸ hxc
  have hxemb : (x:G)∈(p.F₁ B5).pCoreIn 2 := by
    rw [s.F₁_core_eq_fiveHyperplane p B5 hi]
    exact (show Q₅ d B5≤fiveHyperplane d B5 from le_sup_right)
      (U_le_Q₅ d B5 (d.ru2.natural.kernel_le hxZ))
  exact (mem_map_iff_mem (p.F₁ B5).subtype_injective).mp hxemb

theorem SourceChoice.F₁_characteristic_two (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    generalizedFitting (p.F₁ B5)=pCore 2 (p.F₁ B5) :=
  Theory.GroupTheory.generalizedFitting_eq_pCore_of_selfCentralizing 2
    (s.F₁_core_selfCentralizing p B5 hi)

theorem SourceChoice.source_first_parabolic (s:SourceChoice p) :
    ∃ B5:Sylow 5 d.toTypeRuSetup.H,
      (∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) ∧
      p.A B5≤normalizer ((B5Image B5⊔Q₅ d B5:Subgroup G):Set G) ∧
      p.A B5≤normalizer (Q₅ d B5:Set G) ∧
      (p.T_F B5⊔d.toTypeRuSetup.S=(d.T:Subgroup G)) ∧
      Nat.card (p.F₁ B5)=20480 ∧
      (p.F₁ B5).pCoreIn 2=Q₀ d⊔Q₅ d B5 ∧
      Nonempty (((p.F₁ B5)⧸pCore 2 (p.F₁ B5))≃*BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∧
      (∃ T:Sylow 2 (p.F₁ B5), (T:Subgroup (p.F₁ B5))=(p.T_F B5).subgroupOf (p.F₁ B5)) ∧
      normalizer ((p.T_F B5).subgroupOf (p.F₁ B5):Set (p.F₁ B5))=
        (p.T_F B5).subgroupOf (p.F₁ B5) ∧
      generalizedFitting (p.F₁ B5)=pCore 2 (p.F₁ B5) := by
  obtain ⟨B5,hi⟩:=s.inverts_sylow_five
  exact ⟨B5,hi,s.A_normalizes_fiveProduct p B5 hi,s.A_normalizes_Q₅ p B5 hi,
    s.A_sup_Q₅_sup_S p B5 hi,s.card_F₁ p B5 hi,s.F₁_core_eq_fiveHyperplane p B5 hi,
    s.F₁_quotient p B5 hi,s.T_F_sylow_F₁ p B5 hi,s.T_F_selfNormalizing_F₁ p B5 hi,
    s.F₁_characteristic_two p B5 hi⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup

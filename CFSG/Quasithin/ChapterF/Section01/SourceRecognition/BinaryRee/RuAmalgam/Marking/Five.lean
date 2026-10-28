module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuAmalgam.Marking.Center
public import Theory.GroupTheory.SylowFiveKernelConjugacy

/-!
# Marking the original five-subgroup inside the common subgroup

The original first endpoint maps onto Sz(2), of order twenty. Its unique
Sylow-five image lets Sylow conjugacy be performed inside the kernel.
That kernel is the original five-hyperplane and lies in T_F. Consequently
the conjugator can adjust both endpoint maps and the middle simultaneously.

Source: Aschbacher–Smith J.4.7 and the marked application of F.1.12.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices FiveHexagon.MarkedInverter
open Tits.ExceptionalParabolics.FullRee Tits.ExceptionalParabolics.FullRee.LongRootPaths
local instance : Fact (Nat.Prime 5):=⟨by decide⟩
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} {p:Plane d}

 theorem SourceChoice.exists_first_marking_adjustment (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
    (e:first≃*p.F₁ B5) :
    ∃t:p.T_F B5,
      (zpowers modelRotation).map ((p.F₁ B5).subtype.comp
        (e.trans (MulAut.conj ⟨t,p.T_F_le_F₁ B5 t.property⟩)).toMonoidHom)=B5Image B5 := by
  let F:=p.F₁ B5
  have hBF:B5Image B5≤F:=le_sup_right
  let R:Subgroup F:=(B5Image B5).subgroupOf F
  have hR:Nat.card R=5:=(Nat.card_congr (subgroupOfEquivOfLe hBF).toEquiv).trans (B5Image_card d.card_Z B5)
  have hRi:R.index=4096:=by
    have hh:=R.card_mul_index
    rw [hR,s.card_F₁ p B5 hi] at hh
    omega
  have hRp:IsPGroup 5 R:=IsPGroup.of_card (show Nat.card R=5^1 from hR)
  let P:Sylow 5 F:=hRp.toSylow (by rw [hRi];decide)
  let C:Subgroup F:=(zpowers modelRotation).map e.toMonoidHom
  have hrot:orderOf modelRotation=5:=by rw [←orderOf_coe];exact rotation_order
  have hC:Nat.card C=5:=by rw [card_map_of_injective e.injective,Nat.card_zpowers,hrot]
  have hCp:IsPGroup 5 C:=IsPGroup.of_card (show Nat.card C=5^1 from hC)
  obtain ⟨q,hq,hker⟩:=s.F₁_projection p B5 hi
  obtain ⟨g,hg,hCg⟩:=P.exists_kernel_conjugate_le_of_card_twenty q hq
    BenderSuzuki.MatrixGroups.suzukiZero_card C hCp
  have hgQ:(g:G)∈d.toTypeRuSetup.Q:=by
    change g∈d.toTypeRuSetup.Q.subgroupOf F
    rw [←hker]
    exact hg
  have hgD:(g:G)∈fiveHyperplane d B5:=(s.F₁_inf_Q p B5 hi).le ⟨g.property,hgQ⟩
  have hDT:fiveHyperplane d B5≤p.T_F B5:=
    sup_le ((p.Q₀_le_S₂.trans (p.S₂_le_A B5)).trans le_sup_left) le_sup_right
  let t:p.T_F B5:=⟨g,hDT hgD⟩
  refine ⟨t,?_⟩
  change C.map (MulAut.conj g).toMonoidHom≤R at hCg
  have he:C.map (MulAut.conj g).toMonoidHom=R:=by
    apply eq_of_le_of_card_ge hCg
    rw [card_map_of_injective (MulAut.conj g).injective,hC,hR]
  have hh:=congrArg (fun A:Subgroup F=>A.map F.subtype) he
  rw [map_subgroupOf_eq_of_le hBF] at hh
  simp only [C,Subgroup.map_map] at hh
  convert hh using 1
  congr 1
end CFSG.Quasithin.ChapterJ.RuSubgroup

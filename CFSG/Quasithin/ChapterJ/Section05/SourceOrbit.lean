module

public import CFSG.Quasithin.ChapterJ.Section05.FirstOrbit
public import CFSG.Quasithin.ChapterJ.Section04To05.SourceAmalgam.FirstOvergroup
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FirstMaximal

/-!
# J.5.2–3 on the actual J.4 generated subgroup

The original endpoint orders and index-two Q-extension are already proved.
Native full-Ree parabolic maximality now supplies the remaining local-action
input. The sole earlier recognition datum is the marked J.4.7 equivalence,
with the unchanged subgroup F₁ mapping to the marked first Ree parabolic.
The actual conjugating element is selected from the original Q internally.

Source: Aschbacher–Smith J.5.2–3, printed p.445.
-/

public section
noncomputable section
open Subgroup MulAction
open scoped Pointwise
namespace CFSG.Quasithin.ChapterJ.Section05
open RuSubgroup Centralizers.Choices
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} (p:Plane d)

omit [Finite G] in
private theorem covBy_of_subgroupOf_coatom {M F:Subgroup G} (hle:M≤F)
    (hc:IsCoatom (M.subgroupOf F)) : M⋖F := by
  refine ⟨lt_of_le_of_ne hle ?_,?_⟩
  · intro he
    exact hc.1 (by rw [he,subgroupOf_self])
  · intro J hMJ hJF
    have hj:M.subgroupOf F<J.subgroupOf F:=by
      refine lt_of_le_of_ne (fun _ hx=>hMJ.le hx) ?_
      intro he
      have hh:=subgroupOf_inj.mp he
      rw [inf_eq_left.mpr hle,inf_eq_left.mpr hJF.le] at hh
      exact hMJ.ne hh
    exact hJF.not_ge (subgroupOf_eq_top.mp (hc.2 _ hj))

/-- The original J.4 subgroup yields J.5.2–3 from its genuine marked recognition. -/
theorem SourceChoice.source_J_5_2_3 (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
    (X:Sylow 3 p.parabolic) (e:p.F B5 X≃*ReeF4.Model 0)
    (hmark:((p.F₁ B5).subgroupOf (p.F B5 X)).map e.toMonoidHom=
      Tits.ExceptionalParabolics.FullRee.first) :
    ∃g:G,g∈d.toTypeRuSetup.Q ∧ g∉p.F B5 X ∧
      Nat.card (Cosets (p.F B5 X))=4060 ∧
      stabilizer (p.F B5 X) (g•basePoint (p.F B5 X))=(p.F₁ B5).subgroupOf (p.F B5 X) ∧
      Nat.card (orbit (p.F B5 X) (g•basePoint (p.F B5 X)))=1755 ∧
      stabilizer G ({basePoint (p.F B5 X),g•basePoint (p.F B5 X)}:Set (Cosets (p.F B5 X)))=
        p.F₁ B5⊔d.toTypeRuSetup.Q ∧
      (({basePoint (p.F B5 X)}:Set (Cosets (p.F B5 X)))∪
        orbit (p.F B5 X) (g•basePoint (p.F B5 X)))ᶜ.ncard=2304 := by
  have hm:IsCoatom ((p.F₁ B5).subgroupOf (p.F B5 X)):=by
    apply (e.mapSubgroup.isCoatom_iff _).mp
    change IsCoatom (((p.F₁ B5).subgroupOf (p.F B5 X)).map e.toMonoidHom)
    rw [hmark]
    exact Tits.ExceptionalParabolics.FullRee.first_isCoatom
  exact source_first_suborbit d B5 (p.F B5 X) (p.F₁ B5)
    (le_sup_right.trans (le_sup_left.trans le_sup_left)) e
    (covBy_of_subgroupOf_coatom (show p.F₁ B5≤p.F B5 X from le_sup_left) hm)
    (s.card_F₁ p B5 hi) (s.F₁_relIndex_sup_Q p B5 hi)

end CFSG.Quasithin.ChapterJ.Section05

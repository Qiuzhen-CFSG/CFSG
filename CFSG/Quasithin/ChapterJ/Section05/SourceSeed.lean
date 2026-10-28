module

public import CFSG.Quasithin.ChapterJ.Section05.FiveEscape

/-!
# The second source point from the actual J.4 subgroup

The first-orbit theorem supplies its exact stabilizer and2304-point
remainder. The Sylow-five normalizer construction then produces a point
in that remainder whose proper F-stabilizer contains the original Sylow
five-subgroup and has order at least15600. The only earlier input is the
marked J.4.7 equivalence, on the same F and first parabolic.

This is the genuine input for the native full-Ree Sylow-five overgroup
classification in J.5.4; no rank-three conclusion is assumed.
Source: Aschbacher–Smith J.5.4, printed pp.445–446.
-/

public section
noncomputable section
open Subgroup MulAction
namespace CFSG.Quasithin.ChapterJ.Section05
open RuSubgroup Centralizers.Choices
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} (p:Plane d)

private theorem stabilizer_coset_ne_top {F:Subgroup G} {g:G}
    (hn:g∉normalizer (F:Set G)) : stabilizer F (g•basePoint F)≠⊤ := by
  intro he
  have hF:F≤F.map (MulAut.conj g).toMonoidHom:=by
    intro x hx
    have hh:(⟨x,hx⟩:F)∈stabilizer F (g•basePoint F):=by rw [he];exact mem_top _
    change x∈stabilizer G (g•basePoint F) at hh
    rwa [stabilizer_smul_eq_stabilizer_map_conj,stabilizer_quotient] at hh
  have hc:Nat.card (F.map (MulAut.conj g).toMonoidHom)=Nat.card F:=
    (Nat.card_congr ((MulAut.conj g).subgroupMap F).toEquiv).symm
  have heq:F=F.map (MulAut.conj g).toMonoidHom:=eq_of_le_of_card_ge hF (by rw [hc])
  exact hn (mem_normalizer_iff_map_conj_eq.mpr heq.symm)

/-- The original source supplies the exact proper large Sylow-five overgroup needed in J.5.4. -/
theorem SourceChoice.source_second_seed (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
    (X:Sylow 3 p.parabolic) (e:p.F B5 X≃*ReeF4.Model 0)
    (hmark:((p.F₁ B5).subgroupOf (p.F B5 X)).map e.toMonoidHom=
      Tits.ExceptionalParabolics.FullRee.first) (P:Sylow 5 (p.F B5 X)) :
    ∃q g:G,q∈d.toTypeRuSetup.Q ∧ q∉p.F B5 X ∧
      g∈normalizer (((P:Subgroup (p.F B5 X)).map (p.F B5 X).subtype):Set G) ∧
      g∉p.F B5 X ∧ Nat.card (orbit (p.F B5 X) (q•basePoint (p.F B5 X)))=1755 ∧
      g•basePoint (p.F B5 X)∈(({basePoint (p.F B5 X)}:Set (Cosets (p.F B5 X)))∪
        orbit (p.F B5 X) (q•basePoint (p.F B5 X)))ᶜ ∧
      (P:Subgroup (p.F B5 X))≤stabilizer (p.F B5 X) (g•basePoint (p.F B5 X)) ∧
      stabilizer (p.F B5 X) (g•basePoint (p.F B5 X))≠⊤ ∧
      15600≤Nat.card (stabilizer (p.F B5 X) (g•basePoint (p.F B5 X))) := by
  obtain ⟨q,hq,hqF,_,hstab,horbit,_,hrem⟩:=SourceChoice.source_J_5_2_3 p s B5 hi X e hmark
  have hδ:Nat.card (stabilizer (p.F B5 X) (q•basePoint (p.F B5 X)))=20480:=by
    rw [hstab,Nat.card_congr (subgroupOfEquivOfLe
      (show p.F₁ B5≤p.F B5 X from le_sup_left)).toEquiv,s.card_F₁ p B5 hi]
  obtain ⟨g,hg,hgF,hP,hr,hcard⟩:=source_second_orbit_seed d (p.F B5 X) e P _ hδ hrem
  have hn:g∉normalizer (p.F B5 X:Set G):=by
    rwa [source_normalizer_eq_self d B5 (p.F B5 X)
      (le_sup_right.trans (le_sup_left.trans le_sup_left)) e]
  exact ⟨q,g,hq,hqF,hg,hgF,horbit,hr,hP,stabilizer_coset_ne_top hn,hcard⟩

end CFSG.Quasithin.ChapterJ.Section05

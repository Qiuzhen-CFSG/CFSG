module
public import Stellmacher.SectionNine.NineEightTerminalTransvection
public import Stellmacher.SectionNine.LemmaNineNine
public import Stellmacher.SectionFiveToSeven.SuppliedCriticalPathNormalization

/-!
# A transvection on a supplied commuting critical path

A complete supplied critical path of length greater than three, with commuting
endpoint centers, has its first module in the terminal stabilizer and supplies
an actor in that first module outside the terminal core. Its commutator on the
terminal module has order two and has nontrivial order-two displacement modulo
the terminal center. All vertices refer to the supplied path.

Normalize the entire path by one graph-action element. The actual (9.9)
distance bound excludes first-center containment in the terminal module.
The proved (9.8) fixed-coatom construction then provides a transvection in the
normalized first module, while (7.4) provides the full module containment.
Pull the actor, core exclusion, commutator, center, and two cardinal identities
back by the same conjugation equivalence. No coatom from a different
orientation is assumed or transported into this argument.

Source: the fixed-coatom argument in Stellmacher (9.8), combined with (9.9),
Journal of Algebra 190 (1997), pp.55–56. This is the full-path transvection
input for the reorientation before (9.10)(6), printed p.58.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_eight_transvection_of_supplied_critical_path
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (left right : ctx.Γ.Vertex)
    (hcritical : IsCriticalPair ctx.Γ left right)
    (hcomm : ⁅ZAt ctx.Γ left, ZAt ctx.Γ right⁆ = ⊥)
    (path : Fin (ctx.criticalPath.length + 1) → ctx.Γ.Vertex)
    (hstart : path 0 = left)
    (hend : path ⟨ctx.criticalPath.length, Nat.lt_succ_self _⟩ = right)
    (hadj : ∀ index : Fin ctx.criticalPath.length,
      ctx.Γ.adjacent (path index.castSucc) (path index.succ)) :
    VAt ctx.Γ (path ⟨1, by omega⟩) ≤ GAt ctx.Γ right ∧
      ∃ actor : G,
        actor ∈ VAt ctx.Γ (path ⟨1, by omega⟩) ∧ actor ∉ QAt ctx.Γ right ∧
        Nat.card (⁅VAt ctx.Γ right, Subgroup.zpowers actor⁆ : Subgroup G) = 2 ∧
        QuotientCardEq (⁅VAt ctx.Γ right, Subgroup.zpowers actor⁆ ⊔ ZAt ctx.Γ right)
          (ZAt ctx.Γ right) 2 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  obtain ⟨mover, normalized, hlength, hleft, hright, hnext, _⟩ :=
    exists_criticalPath_of_supplied_path ctx.sectionSeven Γ cp left right hcritical
      path hstart hend hadj
  let equiv := MulAut.conj mover⁻¹
  have hnormalizedComm : ⁅Γ.z normalized.a, Γ.z normalized.a'⁆ = ⊥ := by
    rw [hleft, hright, z_act, z_act, ← Subgroup.map_commutator]
    change (⁅ZAt Γ left, ZAt Γ right⁆).map _ = ⊥
    rw [hcomm, Subgroup.map_bot]
  let shifted : AmbientSectionNineContext H S0 S P1 P2 embedding T A B :=
    {ctx with criticalPath := normalized, commutator_eq := hnormalizedComm}
  have hlong : 3 < shifted.criticalPath.length := by
    change 3 < normalized.length
    rw [hlength]
    exact hb
  have hnot : ¬ ZAt Γ normalized.firstStep ≤ VAt Γ normalized.a' := by
    intro hcontain
    have hbound := lemma_nine_nine_ambient shifted hcontain
    omega
  have hshort : 1 < shifted.criticalPath.length := by omega
  obtain ⟨selected, hselected, houtside, hcard, hindex⟩ :=
    nine_eight_terminal_transvection_of_reverse_noncontainment shifted hshort hnot
  have hVright : (VAt Γ right).map equiv.toMonoidHom = VAt Γ normalized.a' := by
    rw [hright]
    exact (v_act Γ mover right).symm
  have hZright : (ZAt Γ right).map equiv.toMonoidHom = ZAt Γ normalized.a' := by
    rw [hright]
    exact (z_act Γ mover right).symm
  have hQright : (QAt Γ right).map equiv.toMonoidHom = QAt Γ normalized.a' := by
    rw [hright]
    exact (q_act Γ mover right).symm
  have hGright : (GAt Γ right).map equiv.toMonoidHom = GAt Γ normalized.a' := by
    rw [hright]
    exact (stabilizer_act Γ mover right).symm
  have hVnext : (VAt Γ (path ⟨1, by omega⟩)).map equiv.toMonoidHom =
      VAt Γ normalized.firstStep := by
    rw [hnext]
    exact (v_act Γ mover _).symm
  have hcontain : VAt Γ (path ⟨1, by omega⟩) ≤ GAt Γ right := by
    apply (Subgroup.map_le_map_iff_of_injective (f := equiv.toMonoidHom) equiv.injective).mp
    rw [hVnext, hGright]
    exact (lemma_seven_four shifted.sectionSeven Γ normalized).first_containment.2
  let actor : G := equiv.symm selected
  have hactor : actor ∈ VAt Γ (path ⟨1, by omega⟩) := by
    have hh : (selected : G) ∈ (VAt Γ (path ⟨1, by omega⟩)).map equiv.toMonoidHom := by
      rw [hVnext]
      exact hselected
    exact (Subgroup.mem_map_equiv.mp hh)
  have hactorNot : actor ∉ QAt Γ right := by
    intro hh
    apply houtside
    rw [← hQright]
    have hm := Subgroup.mem_map_of_mem equiv.toMonoidHom hh
    change equiv (equiv.symm (selected : G)) ∈ (QAt Γ right).map equiv.toMonoidHom at hm
    simpa only [MulEquiv.apply_symm_apply] using hm
  have hRmap : (⁅VAt Γ right, Subgroup.zpowers actor⁆).map equiv.toMonoidHom =
      ⁅VAt Γ normalized.a', Subgroup.zpowers (selected : G)⁆ := by
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers, hVright]
    change ⁅VAt Γ normalized.a', Subgroup.zpowers (equiv (equiv.symm (selected : G)))⁆ = _
    rw [MulEquiv.apply_symm_apply]
  have hcardBack : Nat.card (⁅VAt Γ right, Subgroup.zpowers actor⁆ : Subgroup G) = 2 := by
    rw [← hRmap, Subgroup.card_map_of_injective equiv.injective] at hcard
    exact hcard
  have hindexBack : QuotientCardEq
      (⁅VAt Γ right, Subgroup.zpowers actor⁆ ⊔ ZAt Γ right) (ZAt Γ right) 2 := by
    change Nat.card (_ : Subgroup G) = 2 * Nat.card (_ : Subgroup G) at hindex ⊢
    rw [← hRmap, ← hZright, ← Subgroup.map_sup,
      Subgroup.card_map_of_injective equiv.injective,
      Subgroup.card_map_of_injective equiv.injective] at hindex
    exact hindex
  exact ⟨hcontain, actor, hactor, hactorNot, hcardBack, hindexBack⟩

end Stellmacher.SectionNine

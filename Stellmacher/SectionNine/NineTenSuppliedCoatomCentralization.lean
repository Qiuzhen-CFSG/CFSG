module
public import Stellmacher.SectionNine.NineTenCoatomCentralization
public import Stellmacher.SectionNine.LemmaNineNine
public import Stellmacher.SectionFiveToSeven.SuppliedCriticalPathNormalization

/-!
# Center centralization on a supplied commuting critical path

At critical length greater than three, the initial center centralizes the
intersection of the terminal module with the initial stabilizer, for the
literal supplied endpoints. Normalize the supplied path by one graph action.
Actual (9.9) excludes first-center containment, and the plane/line argument
for the terminal coatom proves centralization; the same conjugation pulls
that equality back. No coatom index or unrelated extraction is assumed.

This is the centralization used after (9.10)(7), printed p.58, on the reversed
critical path from (9.10)(5). It isolates the geometric transfer so the later
long-distance exclusion can retain both original extraction packets.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_ten_supplied_initial_center_centralizes_terminal_intersection
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
    ⁅ZAt ctx.Γ left, VAt ctx.Γ right ⊓ GAt ctx.Γ left⁆ = ⊥ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  obtain ⟨mover, normalized, hlength, hleft, hright, _, _⟩ :=
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
  have hh := nine_ten_initial_center_centralizes_terminal_coatom shifted (by omega) hnot
  have hZleft : (ZAt Γ left).map equiv.toMonoidHom = ZAt Γ normalized.a := by
    rw [hleft]
    exact (z_act Γ mover left).symm
  have hGleft : (GAt Γ left).map equiv.toMonoidHom = GAt Γ normalized.a := by
    rw [hleft]
    exact (stabilizer_act Γ mover left).symm
  have hVright : (VAt Γ right).map equiv.toMonoidHom = VAt Γ normalized.a' := by
    rw [hright]
    exact (v_act Γ mover right).symm
  apply (Subgroup.map_injective (f := equiv.toMonoidHom) equiv.injective)
  rw [Subgroup.map_bot, Subgroup.map_commutator,
    Subgroup.map_inf _ _ _ equiv.injective, hZleft, hVright, hGleft]
  exact hh

end Stellmacher.SectionNine

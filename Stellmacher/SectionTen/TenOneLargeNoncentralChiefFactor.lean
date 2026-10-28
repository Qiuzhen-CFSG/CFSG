module
public import Stellmacher.SectionTen.TenOneFirstCoreNoncontainment
public import Stellmacher.SectionTen.TenOneLargeTerminalFullSupport
public import Theory.GroupAction.PGroupNoncentralChiefQuotient

/-!
# An intrinsic noncentral chief quotient above the terminal module

In the actual nontransvection branch of Section Ten, the terminal module V
is properly contained in the two-core U of the terminal residual E. There
is a subgroup D with V≤D<U, normalized by the whole terminal stabilizer P,
such that its literal quotient U/D is a nontrivial elementary abelian
irreducible P-module. The quotient-conjugation action has full E-image
support and E acts nontrivially. The subgroup and action are intrinsic to
the actual U/V section; no classification or quotient order is supplied.

The proved large-branch full-support identity V=[V,E] puts V inside U.
The transported residual-core escape at the terminal vertex makes this
containment strict. Residual perfection and the odd quotient over U imply
[U,E]=U. Apply the finite p-group maximal-denominator construction: adjoin
Phi(U) to V, choose a maximal proper invariant denominator, and retain its
literal quotient action, elementary structure and irreducibility.

This supplies the noncentral chief-factor assertion used before Stellmacher
(10.1)(15), printed p.63, from the obstruction (3) on printed p.60. The later
claim that the prescribed actor is not a transvection on this chief quotient
is a separate source13/source14 transfer.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_large_noncentral_chief_factor
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    let P := GAt ctx.Γ ctx.criticalPath.a'
    let E := EAt ctx.Γ ctx.criticalPath.a'
    let U := twoCoreIn E
    let V := VAt ctx.Γ ctx.criticalPath.a'
    ∃ hPU : P ≤ Subgroup.normalizer (U : Set G),
      ∃ D : Subgroup G, V ≤ D ∧ D < U ∧
        ∃ _hPD : P ≤ Subgroup.normalizer (D : Set G),
          ∃ hN : (D.subgroupOf U).Normal,
            let _ := hN
            ∃ action : P →* MulAut (U ⧸ D.subgroupOf U),
              (∀ mover : P, ∀ point : U,
                action mover (QuotientGroup.mk' (D.subgroupOf U) point) =
                  QuotientGroup.mk' (D.subgroupOf U)
                    ⟨(mover : G) * (point : G) * (mover : G)⁻¹,
                      (Subgroup.mem_normalizer_iff.mp (hPU mover.property) point).mp point.property⟩) ∧
              IsElementaryAbelian 2 (U ⧸ D.subgroupOf U) ∧
              Nontrivial (U ⧸ D.subgroupOf U) ∧
              (∀ K : Subgroup (U ⧸ D.subgroupOf U),
                (∀ mover : P, ∀ point, point ∈ K → action mover point ∈ K) →
                  K = ⊥ ∨ K = ⊤) ∧
              commutatorAction ((E.subgroupOf P).map action) (U ⧸ D.subgroupOf U) = ⊤ ∧
              ¬ E.subgroupOf P ≤ action.ker := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a'
  let E := EAt Γ cp.a'
  let U := twoCoreIn E
  let V := VAt Γ cp.a'
  let Q := QAt Γ cp.a'
  have hE : E = twoResidualIn P := Γ.twoResidualAt_def _
  have hEP : E ≤ P := hE ▸ twoResidualIn_le P
  have hUP : U ≤ P := (twoCoreIn_le E).trans hEP
  have hPU : P ≤ Subgroup.normalizer (U : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUP).mp
      (twoCoreIn_normal_of_normal E P hEP (hE ▸ twoResidualIn_normal P))
  have hPV : P ≤ Subgroup.normalizer (V : Set G) := stabilizer_le_normalizer_v Γ cp.a'
  have hshort : 1 < cp.length := by change 1 < ctx.criticalPath.length; rw [ctx.critical_length]; decide
  have hlong : 2 < cp.length := by change 2 < ctx.criticalPath.length; rw [ctx.critical_length]; decide
  obtain ⟨_, _, hterminal, _⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hVQ : V ≤ Q := neighbor_join_le_core_of_length_gt_one Γ cp hshort cp.a'
  have hVfull : ⁅V,E⁆ = V := ten_one_large_terminal_residual_full ctx middle hpath hno
  have hEQ : ⁅E,Q⁆ ≤ U := by
    change ⁅E, Γ.twoCoreAt cp.a'⁆ ≤ twoCoreIn E
    rw [hE, Γ.twoCoreAt_def]
    exact residual_commutator_core_le P
  have hVU : V ≤ U := by
    rw [← hVfull]
    exact (Subgroup.commutator_mono hVQ le_rfl).trans
      ((Subgroup.commutator_comm Q E).trans_le hEQ)
  obtain ⟨alignment, _, halignment⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have hescape := nine_seven_residual_core_escapes_neighbor
    ctx.toLocalContext.toSectionNineLocalContext cp.a' middle
      ⟨alignment,halignment⟩ (Γ.adjacent_symm hterminal)
  have hVmiddle : V ≤ QAt Γ middle :=
    (show V ≤ GeneratedNeighborhoodV Γ middle from le_sSup
      ⟨_, (mem_neighborhood_iff_adjacent Γ).mpr hterminal, rfl⟩).trans
        (nine_seven_neighborhood_le_own_core ctx.toLocalContext.toSectionNineLocalContext
          hlong middle)
  have hVlt : V < U := lt_of_le_of_ne hVU (fun heq => hescape (heq.symm.le.trans hVmiddle))
  have hperfect : BenderSuzuki.External.hktPResidual 2 E = ⊤ := by
    rw [hE]
    exact twoResidualAmbient_has_top_twoResidual P
  have hodd : Odd (Nat.card (E ⧸ pCore 2 E)) := by
    rw [hE]
    exact local_residual_core_quotient_odd ctx.sectionSeven Γ cp.a' middle
      ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hterminal)) P le_rfl
  have hfull : ⁅U,E⁆ = U := by
    have hh := congrArg (Subgroup.map E.subtype)
      (twoCore_eq_commutator_of_residual_perfect hperfect hodd)
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hh
    exact hh.symm
  have hU : IsPGroup 2 U := (pCore_isPGroup (p := 2) (G := E)).map E.subtype
  exact ⟨hPU, Subgroup.exists_noncentral_irreducible_quotient_above
    P U V E hUP hPU hPV hVlt hU hEP hfull⟩

end Stellmacher.SectionTen

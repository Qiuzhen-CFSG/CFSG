module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentAmbientUniqueness
public import Theory.SpecificGroups.Alternating.SevenFiveRestrictionLift
public import Theory.GroupTheory.SylowLocalCore

/-!
# The A.3.14 restriction in the original 12.3.12 configuration

The actual residual K has its supplied A₅ quotient by O₂(K), while the
maximal overcomponent Y has the marked quotient Y/O₂,Z(Y) ≃ A₇. Restrict
the original Sylow subgroup to Y and apply the finite A₇ restriction and
central-by-two-kernel lifting theorem to the literal images of K and E.
The alternatives are E = K or E = Y; strict containment excludes the first.

This constructs A314RestrictionInput from ResidualAnalysis and feeds the
existing ambient-uniqueness consumer. E remains a C-component of the point
centralizer throughout; no C-component membership in Y is asserted.
The natural coordinates, omega decomposition and cubic containment remain
with their earlier source producers and the final 12.3.12 assembly owner.

Source: Aschbacher–Smith A.3.14, printed pp.49–50, and its application in
12.3.12, printed p.811 (PDF p.828).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
variable {S : Setup T L V} {D : S.LocalAnalysis}
namespace TerminalPoint
variable (P : TerminalPoint S D)

/-- The actual A.3.14 restriction for the overcomponent in 12.3.12. -/
theorem intermediate_component_eq_maximal_source (R : P.ResidualAnalysis)
    (F : P.Overcomponents) (hKE : P.K < F.E) {W : Subgroup G}
    (SY : Setup T F.Y W) : F.E = F.Y := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKY : P.K ≤ F.Y := F.residual_le.trans F.le_maximal
  let B := P.K.subgroupOf F.Y
  let E := F.E.subgroupOf F.Y
  let : Group.IsPerfect P.K := Chapter1.mem_L_isPerfect R.local_mem
  let : Group.IsPerfect F.E := Chapter1.mem_L_isPerfect F.local_mem
  let : Group.IsPerfect F.Y := Chapter1.mem_L_isPerfect F.maximal.1
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKY).symm.toMonoidHom)
    (subgroupOfEquivOfLe hKY).symm.surjective
  let : Group.IsPerfect E := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe F.le_maximal).symm.toMonoidHom)
    (subgroupOfEquivOfLe F.le_maximal).symm.surjective
  let e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKY)
      (pCore_map_iso 2 _)).trans R.quotient
  have hTY := SY.chosen.sylow_normalizes_component
  obtain ⟨U,hU⟩ := (T.subtype
    (show (T : Subgroup G) ≤ F.Y ⊔ (T : Subgroup G) from le_sup_right)).exists_map_subtype_eq_inf_of_normalizes
      (show F.Y ≤ F.Y ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le F.Y.le_normalizer hTY)
  have hU' : (U : Subgroup F.Y).map F.Y.subtype = (T : Subgroup G) ⊓ F.Y := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using hU
  have hUT : (U : Subgroup F.Y) ≤ (T : Subgroup G).subgroupOf F.Y := by
    intro x hx
    have hm : (x : G) ∈ (T : Subgroup G) ⊓ F.Y :=
      hU' ▸ mem_map_of_mem F.Y.subtype hx
    exact hm.1
  have hUB : (U : Subgroup F.Y) ≤ normalizer (B : Set F.Y) :=
    (hUT.trans (comap_mono P.sylow_normalizes_residual)).trans
      (le_normalizer_comap F.Y.subtype)
  have hUE : (U : Subgroup F.Y) ≤ normalizer (E : Set F.Y) :=
    (hUT.trans (comap_mono (P.sylow_le_pointCentralizer.trans F.normalizes))).trans
      (le_normalizer_comap F.Y.subtype)
  have hker : SY.projection.ker = centralPreimage (pCore 2 F.Y) := by
    change (SY.quotient.toMonoidHom.comp (QuotientGroup.mk' _)).ker = _
    rw [MonoidHom.ker_comp_of_injective _ _ SY.quotient.injective,QuotientGroup.ker_mk']
    rfl
  rcases Theory.SpecificGroups.Alternating.SevenFivePlacement.perfect_overgroup_eq_or_top_of_centralPreimage
      SY.projection SY.projection_surjective hker B E e U hUB hUE
      (comap_mono F.residual_le) with he | he
  · have h := congrArg (map F.Y.subtype) he
    rw [map_subgroupOf_eq_of_le F.le_maximal,map_subgroupOf_eq_of_le hKY] at h
    exact False.elim (hKE.ne h.symm)
  · have h := congrArg (map F.Y.subtype) he
    simpa only [E,map_subgroupOf_eq_of_le F.le_maximal,
      ← MonoidHom.range_eq_map,range_subtype] using h

/-- Construct the existing restriction boundary from the actual residual
analysis, with no additional source premise. -/
theorem a314RestrictionInput (R : P.ResidualAnalysis) : A314RestrictionInput (P := P) := by
  refine ⟨?_⟩
  intro F hKE _ _ _ _ _ hsetup
  obtain ⟨W,⟨SY⟩⟩ := hsetup
  exact P.intermediate_component_eq_maximal_source R F hKE SY

/-- Discharge A.3.14 in the existing proper-component consumer. The earlier
natural coordinates, omega equality and cubic containment retain their
existing producers and remain with the final 12.3.12 assembly owner. -/
theorem proper_component_eq_residual_of_natural_omega_source
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (R : P.ResidualAnalysis) (F : P.Overcomponents)
    (hKY : P.K < F.Y) {W : Subgroup G} (SY : Setup T F.Y W)
    (DY : SY.NaturalCoordinates) (hsplit : SY.NaturalOmegaDecomposition)
    (hLe : F.E = F.Y → P.Le ≤ F.Y) : F.E = P.K :=
  P.proper_component_eq_residual_of_natural_omega structural R F hKY SY DY hsplit
    (P.a314RestrictionInput R) hLe

end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

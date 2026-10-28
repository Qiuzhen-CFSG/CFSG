module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Basic

/-!
# The actors in the selected-conjugator argument

Source 16.4.2(4) selects g with N_T(Kᵍ) ≤ Tᵍ; 16.4.11(3) then gives
R = T_Cᵍ. The former condition puts g⁻¹ z g in T, while the latter puts
g z g⁻¹ in R. These are different actors. Transporting the residual on Lᵍ
at z back to L gives the residual at g⁻¹ z g, with no change of convention.

The final equivalence below isolates the missing comparison between these
actors on the same component. It does not assert source 16.5.6(3). The
common-residual identities only identify the residuals at involutions in R;
they do not identify the residual at every involution in T.

The companion `Conjugator/A12.g` is a reproducible GAP diagnostic for the
insufficiency of these local inputs. It has L = A₈ and common residual A₄,
satisfies the selected Sylow transport and R = T_Cᵍ, but moves the common
residual. That ambient A₁₂ fails quasithinness, so it does not refute the
source theorem under Hypothesis 16.1.1. No computational result from GAP
is used in any Lean proof. See `Conjugator/Obstruction.md` for the precise
remaining source and assembly obligations.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
printed pp.1183, 1193–1194, 1197 (16.4.2(4), 16.4.11, 16.5.6(3)).
Conjugation in this module is left conjugation.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Conjugator
variable {G : Type*} [Group G] [Finite G]

private theorem z_mem_commuting {T : Sylow 2 G} {z g : G} {L R : Subgroup G}
    (h : IntersectionSetup T z L g R) : z ∈ commutingSylow T L := by
  refine ⟨h.mem_sylow, ?_⟩
  exact mem_centralizer_iff.mpr fun x hx =>
    mem_centralizer_singleton_iff.mp (h.component.1 hx)

/-- The forward actor is the conjugate of the distinguished central involution. -/
theorem forward_actor {T : Sylow 2 G} {z g : G} {L R : Subgroup G}
    (h : IntersectionSetup T z L g R)
    (hR : R = (commutingSylow T L).conjBy g) :
    MulAut.conj g z ∈ R ∧ orderOf (MulAut.conj g z) = 2 := by
  refine ⟨?_, ((MulAut.conj g).orderOf_eq z).trans h.involution⟩
  rw [hR]
  exact mem_map_of_mem (MulAut.conj g).toMonoidHom (z_mem_commuting h)

/-- The selected Sylow transport places the inverse actor in T. -/
theorem inverse_actor_mem_sylow {T : Sylow 2 G} {z g : G} {L R : Subgroup G}
    (h : IntersectionSetup T z L g R)
    (hT : (T : Subgroup G) ⊓
      normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
        (T : Subgroup G).conjBy g)
    (hR : R = (commutingSylow T L).conjBy g) :
    MulAut.conj g⁻¹ z ∈ T ∧ orderOf (MulAut.conj g⁻¹ z) = 2 := by
  obtain ⟨hu, hu2⟩ := forward_actor h hR
  have hRne : R ≠ ⊥ := by
    intro he
    have hu1 : MulAut.conj g z = 1 := by simpa only [he, mem_bot] using hu
    simp [hu1] at hu2
  have hzNR : z ∈ normalizer (R : Set G) := by
    apply centralizer_le_normalizer
    apply mem_centralizer_iff.mpr
    intro r hr
    exact mem_centralizer_singleton_iff.mp (h.sylow_centralizes (h.le_sylow hr))
  have hzTg := hT ⟨h.mem_sylow, h.normalizer_le hRne le_rfl hzNR⟩
  refine ⟨?_, ((MulAut.conj g⁻¹).orderOf_eq z).trans h.involution⟩
  change MulAut.conj g⁻¹ z ∈ (T : Subgroup G)
  simpa only [MulAut.conj_symm_apply, MulAut.conj_apply, inv_inv] using (mem_map_equiv.mp hzTg)

/-- Inverse transport returns the opposite residual to L, with inverse actor. -/
theorem inverse_residual_transport {L X : Subgroup G} {g i : G}
    (hXi : modifiedCentralizerResidual (L.conjBy g) i = X) :
    X.conjBy g⁻¹ = modifiedCentralizerResidual L (MulAut.conj g⁻¹ i) := by
  rw [← hXi]
  change (modifiedCentralizerResidual (L.conjBy g) i).map
    (MulAut.conj g⁻¹).toMonoidHom = _
  rw [modifiedCentralizerResidual_map]
  exact congrArg (fun J : Subgroup G =>
    modifiedCentralizerResidual J (MulAut.conj g⁻¹ i)) (L.conjBy_inv g)

/-- Exact missing actor comparison for the selected conjugator. This is a
transport diagnostic, not an assertion of source 16.5.6(3). -/
theorem normalizes_iff_inverse_actor_residual {T : Sylow 2 G} {z g : G}
    {L R X : Subgroup G} (h : IntersectionSetup T z L g R)
    (hR : R = (commutingSylow T L).conjBy g)
    (hforward : ∀ u ∈ R, orderOf u = 2 → modifiedCentralizerResidual L u = X)
    (hbackward : ∀ i ∈ commutingSylow T L, orderOf i = 2 →
      modifiedCentralizerResidual (L.conjBy g) i = X) :
    g ∈ normalizer (X : Set G) ↔
      modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) =
        modifiedCentralizerResidual L (MulAut.conj g z) := by
  obtain ⟨hu, hu2⟩ := forward_actor h hR
  have hi := hbackward z (z_mem_commuting h) h.involution
  rw [hforward _ hu hu2, ← inverse_residual_transport hi]
  exact ((normalizer (X : Set G)).inv_mem_iff).symm.trans
    mem_normalizer_iff_map_conj_eq

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Conjugator

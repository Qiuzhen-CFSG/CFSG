module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.Inputs
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ConjugatePlacement.LocalFamily

/-!
# Minimal local selection with the actual faithful action

Select a least-order member of the outside family below the initial overgroup,
before constructing its section action. The residual–Sylow supplement places
C_Y(V) in this selected group. Thus the uniform 15.3.48(3) input applies there;
we reconstruct its action on its own U_H/Z. Elementary spans and the theta
identity descend from the initial overgroup. The original ambient Sylow
subgroup carries the local two-core, and the residual computation proves the
literal standard edge intersection H ∩ YT = Y₀T.

`EarlierLocal` enumerates genuine earlier local inputs: the extraspecial
alternative and centralizer factorization of 15.3.7, normalization from the
standing setup, the normalizer bounds of 15.3.46, the uniform kernel statement
15.3.48(3), and 15.3.49(b),(d) at the initial overgroup. SQTK is required only
there and is inherited by the selected subgroup. No offender or component is
an input. The geometric construction and final contradiction remain separate.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1142–1144, proof of 15.3.48 and 15.3.49(b),(d),(i)–(j).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute

open Subgroup ComponentReduction FactorGeneration.ConjugatePlacement
open scoped IsMulCommutative

universe u
variable {G : Type u} [Group G] [Finite G]

/-- Earlier source data on the initial overgroup, including the uniform
kernel theorem with its genuine extraspecial side condition. -/
structure EarlierLocal (κ : GroupClass.{u})
    (M Y V Y0 ZS Z upper : Subgroup G) (T : Sylow 2 G) where
  eligible : upper ∈ outsideFamily Y0 (T : Subgroup G) M
  extraspecial : CosetSetup.ExtraspecialLocal.ExtraspecialCase M Y V
  residual : Y0 = Stellmacher.twoResidualAmbient (Y ⊓ centralizer (V : Set G))
  sqtk : IsSQTK κ upper
  t_le_m : (T : Subgroup G) ≤ M
  v_le_t : V ≤ (T : Subgroup G)
  y_le_m : Y ≤ M
  m_normalizes : M ≤ normalizer (V : Set G)
  t_normalizes_y : (T : Subgroup G) ≤ normalizer (Y : Set G)
  theta_eq : theta (M ⊓ upper) = Y0
  normalizer_eq : normalizer (Y0 : Set G) = M
  seed_le : ZS ≤ V
  line_le_seed : Z ≤ ZS
  seed_normalizer : normalizer (ZS : Set G) ≤ M
  centralizes : upper ≤ centralizer (Z : Set G)
  elementary : IsElementaryAbelian 2 (localSpan V upper)
  centralizer_factorization : ∀ x ∈ M ⊓ centralizer (Z : Set G),
    ∃ c ∈ M ⊓ centralizer (V : Set G), ∃ t ∈ (T : Subgroup G), c * t = x
  kernel : ∀ H : Subgroup G, H ∈ outsideFamily Y0 (T : Subgroup G) M →
    (hHU : H ≤ upper) → Y ⊓ centralizer (V : Set G) ≤ H →
    letI := CosetSetup.layer_normal H Z (hHU.trans centralizes)
    CosetSetup.quotientCentralizer H (localSpan ZS H) Z = pCore 2 H

namespace EarlierLocal
variable {κ : GroupClass.{u}} {M Y V Y0 ZS Z upper : Subgroup G} {T : Sylow 2 G}
    (d : EarlierLocal κ M Y V Y0 ZS Z upper T)

include d

omit [Finite G] in
theorem elementary_seed (H : Subgroup G) (hHU : H ≤ upper) :
    IsElementaryAbelian 2 (localSpan ZS H) := by
  let := d.elementary
  exact localSpan_elementary_of_le V ZS upper H d.seed_le hHU

omit [Finite G] in
theorem elementary_span (H : Subgroup G) (hHU : H ≤ upper) :
    IsElementaryAbelian 2 (localSpan V H) := by
  let := d.elementary
  exact localSpan_elementary_of_le V V upper H le_rfl hHU

/-- Reconstruct the faithful action at H from its own centralizer kernel.
This is not restriction of the action at `upper`. -/
noncomputable def localInput (H : Subgroup G)
    (hH : H ∈ outsideFamily Y0 (T : Subgroup G) M) (hHU : H ≤ upper) :
    letI := d.elementary_seed H hHU
    LocalInput κ H M Y V Y0 (T : Subgroup G) ZS Z := by
  let := d.elementary_seed H hHU
  have hbase := hH.1.2
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hbase
  have hTV := d.t_le_m.trans d.m_normalizes
  have hc := centralizer_le_intermediate Y V Y0 H T d.t_normalizes_y hTV
    d.residual hbase
  have hcore : localTwoCore H ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow H (T.subtype hTH)
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] at hh
    exact hh
  have hres : Y0 ≤ Y ⊓ centralizer (V : Set G) := by
    rw [d.residual]
    exact map_subtype_le _
  let := CosetSetup.layer_normal H Z (hHU.trans d.centralizes)
  exact {
    extraspecial := d.extraspecial
    residual := d.residual
    sqtk := (IsSQTK.equiv (subgroupOfEquivOfLe hHU)).mp
      (d.sqtk.subgroup (H.subgroupOf upper))
    base_le := hbase
    t_le_m := d.t_le_m
    theta_eq := theta_intermediate M upper H Y0 hHU (le_sup_left.trans hbase) d.theta_eq
    normalizer_eq := d.normalizer_eq
    core_le_m := hcore.trans d.t_le_m
    seed_le := d.seed_le
    line_le_seed := d.line_le_seed
    seed_centralized := (hres.trans inf_le_right).trans (centralizer_le d.seed_le)
    seed_normalizer := d.seed_normalizer
    action := intermediateSectionAction V ZS Z H d.line_le_seed d.seed_le
      (d.v_le_t.trans hTH) (hHU.trans d.centralizes) (d.kernel H hH hHU hc) }

/-- The edge subgroup is computed from the residual and the actual Sylow
supplement, rather than imposed as an extra local hypothesis. -/
theorem edge_eq (H : Subgroup G)
    (hH : H ∈ outsideFamily Y0 (T : Subgroup G) M) (hHU : H ≤ upper) :
    H ⊓ (Y ⊔ (T : Subgroup G)) = Y0 ⊔ (T : Subgroup G) := by
  have hr : CosetSetup.localL1 Y Z = Y0 := by
    rw [d.residual]
    exact localL1_eq_Y0 M Y V Z T d.y_le_m d.m_normalizes d.t_le_m
      (d.line_le_seed.trans d.seed_le) d.centralizer_factorization
  have he := base_edge_eq_localL1 Y H Z T (le_sup_right.trans hH.1.2)
    (hHU.trans d.centralizes) d.t_normalizes_y
    (hr.symm ▸ le_sup_left.trans hH.1.2)
  simpa only [hr] using he

/-- Minimality, both elementary spans, the local action, and the standard
edge intersection are constructed together before offender selection. -/
theorem exists_minimal_input :
    ∃ H : Subgroup G, ∃ hmin : MinimalLocal Y0 (T : Subgroup G) M upper H,
      letI := d.elementary_seed H hmin.le_upper
      IsElementaryAbelian 2 (localSpan V H) ∧
        Nonempty (LocalInput κ H M Y V Y0 (T : Subgroup G) ZS Z) ∧
        H ⊓ (Y ⊔ (T : Subgroup G)) = Y0 ⊔ (T : Subgroup G) := by
  obtain ⟨H, hm⟩ := exists_minimalLocal Y0 (T : Subgroup G) M upper d.eligible
  exact ⟨H, hm, d.elementary_span H hm.le_upper,
    ⟨d.localInput H hm.eligible hm.le_upper⟩, d.edge_eq H hm.eligible hm.le_upper⟩

end EarlierLocal
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute

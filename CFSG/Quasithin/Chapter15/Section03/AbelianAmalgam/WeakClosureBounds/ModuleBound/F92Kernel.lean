module

public import CFSG.Quasithin.ChapterF.Section09.Basic
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.ModuleBound.Source

/-!
# The F.9.2 kernel calculation in the E branch

The existing SourceF91 carries the original source assumptions with
Y,V,Z_S,Z,H in the roles of L,V,V_+,V₁,H. We convert it to F.9.1 and apply
the proved F.9.2(3). This gives the literal centralizerModulo equality on
⟨Z_S^H⟩/Z, discharging Earlier48Conclusions.centralizer_kernel without
assuming a stronger action-kernel bound.

Construction of SourceF91 from the earlier Section 15.3 hypotheses remains
with that source application. The adapter assumes none of its later
conclusions. The extra side condition in Earlier48Input is not needed by
this F.9.2 consequence.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
F.9.1–2, printed pp.317–318, and 15.3.48(1),(3), printed p.1142.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.ModuleBound
variable {G : Type*} [Group G] [Finite G]

/-- The literal E-branch groups, with distinct seeds for U_H and V_H. -/
def f91Setup (T : Sylow 2 G) (Y V ZS Z H : Subgroup G) :
    ChapterF.Section09.Setup G := ⟨T, Y, V, ZS, Z, H⟩

variable {T : Sylow 2 G} {Y V ZS Z H : Subgroup G} [IsElementaryAbelian 2 V]

/-- No conclusion of F.9.2 is a premise of this source conversion. -/
theorem SourceF91.toF91 (h : SourceF91 T Y V ZS Z H) :
    (f91Setup T Y V ZS Z H).Hypothesis := by
  have hv : V ≤ Y ⊔ (T : Subgroup G) := h.v_le_sylow.trans le_sup_right
  refine {
    elementary := (inferInstance : IsElementaryAbelian 2 V)
    residual := h.residual
    normalizes_L := h.normalizes_Y
    characteristic_L := h.characteristic_Y
    V_le_LT := hv
    reduced := ⟨h.v_reduced.choose, IsElementaryAbelian.subgroupOf (H := V) (K := Y ⊔ (T : Subgroup G)) hv, h.v_reduced.choose_spec⟩
    sylow_centralizer := h.sylow_centralizer
    point_card := h.z_card
    normalizes_point := h.normalizes_Z
    point_lt := h.z_lt
    plus_le := h.zs_le
    H_centralizes := h.a_centralizes
    local_le := h.a_contains
    characteristic_H := h.a_characteristic
    kernel_core := h.a_kernel
    local_normalizes := h.b_normalizes
    irreducible := h.b_irreducible
    normalizer_control := h.c_normalizer
    generated_core := h.d_core
    commutator_lifting := h.e_commutators }

/-- The consumed 15.3.48 conclusions, including the exact H/Z kernel equality. -/
theorem SourceF91.earlier48Conclusions (h : SourceF91 T Y V ZS Z H) :
    Earlier48Conclusions T Y V ZS Z H :=
  { toSourceF91 := h
    centralizer_kernel := h.toF91.centralizerModulo_UH_eq_pCore }

/-- Discharge the earlier-source implication used by the E module bound. -/
theorem SourceF91.earlier48Input (h : SourceF91 T Y V ZS Z H) :
    Earlier48Input T Y V ZS Z H := fun _ => h.earlier48Conclusions

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.ModuleBound

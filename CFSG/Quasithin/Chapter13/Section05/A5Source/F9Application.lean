module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.ThirdSpace
public import CFSG.Quasithin.Chapter13.Section05.A5Source.PointKernel
public import CFSG.Quasithin.Chapter13.Section05.A5Source.LocalAction
public import CFSG.Quasithin.Chapter13.Section05.A5Source.Commutator.Source
public import CFSG.Quasithin.Chapter13.Section05.A5Source.Spans

/-!
# F.9.1 on the original A₅ source overgroups

For each original H in H_z, the marked A₅ action supplies the faithful
kernel, perfection and characteristic two. The point-kernel argument
discharges (a), uniqueness discharges (d), and the two actual conjugate
actions discharge (e). The resulting SourceF91 is the literal input of
the existing Chapter13 kernel and conjugate-span consumers.

Reducedness and the Sylow kernel follow from the original five-point
action, and its nonabelian component image proves T-normality of L.
Local maximality, the unique maximal overgroup and the full module
normalizer are also constructed. Global seed-normalizer control remains
the explicit genuine earlier-source premise.
The flag quotient invariance and irreducibility are supplied by the proved
13.5.7(b) module calculation on the same marked Context.
Source: Aschbacher–Smith 13.5.7–10, printed pp.917–918.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]

/-- F.9.1 is proved from the original marked geometry once the earlier
global seed-normalizer control is supplied. -/
theorem sourceF91_of_earlier_geometry (d : Context T L V V₁ V₂ V₃)
    (hcontrol : centralizer (V₁ : Set G) ⊓ normalizer (V₃ : Set G) ≤ normalizer (V : Set G))
    (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
      (centralizer (V₁ : Set G)) (normalizer (L : Set G))) : SourceF91 T L V V₃ V₁ H := by
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hH.1.2
  have hctrl : H ⊓ normalizer (V₃ : Set G) ≤ normalizer (V : Set G) :=
    (inf_le_inf hH.2.1 le_rfl).trans hcontrol
  exact {
    residual := d.residual_eq_top
    normalizes_L := d.normalizes_L
    characteristic_L := d.characteristic_L
    v_le_sylow := d.chosen.le_sylow
    v_reduced := ⟨d.reduced.normal,d.reduced.quotient_pCore_eq_bot⟩
    sylow_centralizer := d.sylow_centralizer d.normalizes_L
    z_card := d.flag.one_card
    normalizes_V₁ := d.flag.one_invariant
    z_lt := d.third_strict
    v₃_le := d.third_le
    a_centralizes := hH.2.1
    a_contains := hH.1.2
    a_characteristic := d.characteristic_H H hTH hH.2.1
    a_kernel := normalCore_point_kernel d H d.third_strict.le hTH hH.2.1 hctrl hH.2.2
    b_normalizes := d.third_normalizes
    b_irreducible := d.third_irreducible
    c_normalizer := le_inf inf_le_left hctrl
    d_core := sup_twoCore_eq_bot_of_unique (L ⊔ (T : Subgroup G)) H
      (normalizer (L : Set G)) d.unique_maximal_overgroup hH.2.2
    e_commutators := Commutator.source_commutator_lifting d H hH.2.1 }

/-- The actual Chapter13 consumers: both closure equivalences and the
literal H/O₂(H) commutator-kernel identity follow from this source setup. -/
theorem span_and_kernel_of_earlier_geometry (d : Context T L V V₁ V₂ V₃)
    (hcontrol : centralizer (V₁ : Set G) ⊓ normalizer (V₃ : Set G) ≤ normalizer (V : Set G))
    (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
      (centralizer (V₁ : Set G)) (normalizer (L : Set G))) :
    ((IsMulCommutative (conjugateSpanBy V₃ H) ↔ IsMulCommutative (conjugateSpanBy V H)) ∧
      (IsMulCommutative (conjugateSpanBy V₃ H) ↔ V ≤ H.pCoreIn 2)) ∧
      commutatorPreimage H (Source.UH H V₃) V₁ = Source.QH H := by
  have h := sourceF91_of_earlier_geometry d hcontrol hH
  exact ⟨source_span_equivalences d h,h.commutatorPreimage_eq_QH⟩

end CFSG.Quasithin.Chapter13.Section05.A5Source

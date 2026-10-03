module
public import Stellmacher.SectionEight.EightSixSelectedOrbitIntersection
public import Stellmacher.SectionEight.EightSixNextResidualCoreAction

/-!
# Collapse of the selected fixed core in the high-cost branch

In the high-cost branch of (8.6), the centralizer V0 of the selected
residual in the next two-core equals the next center. The actual source14
containment V0≤Qa is retained as an explicit input, alongside the original
local geometric configuration and the uniform cost lower bound eight.

Source11 puts [V0,A] in the next center. An element w of V0 need not belong
to Vnext, so first factor w=v*d using the actual equality Qnext=Vnext join D.
Since D≤Qa, the module factor v belongs to Vnext∩Qa. The predecessor and
next commutator lines put [A,v] in Za. The general backward displacement
bound is therefore at most four. Cubic cost symmetry forces v into Qprev,
and hence w lies in D. The exact source10 identity V0∩D=Znext proves the
claimed equality. No involution hypothesis or raw orbit-action model is used.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.6), printed p.45,
first conclusion of assertion (18), `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
open scoped commutatorElement Pointwise
universe u

public theorem eight_six_selected_fixed_core_eq_next_center
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup G)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (E A0 : Subgroup G) (actor : G)
    (geom : SectionNine.NineThreeGeometricData ctx.Γ
      ctx.criticalPath.firstStep ctx.criticalPath.a
      (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) E A0 actor)
    (_hcore : conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E ≤
      QAt ctx.Γ ctx.criticalPath.a)
    (hedge : E ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
      GAt ctx.Γ ctx.criticalPath.firstStep)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (hhigh : ∀ mover : G, mover ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
      mover ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        8 ≤ eightSixCommutatorCost ctx.Γ ctx.criticalPath mover)
    (hV0Qa : QAt ctx.Γ ctx.criticalPath.firstStep ⊓
      Subgroup.centralizer (twoResidualIn E : Set G) ≤ QAt ctx.Γ ctx.criticalPath.a) :
    QAt ctx.Γ ctx.criticalPath.firstStep ⊓
      Subgroup.centralizer (twoResidualIn E : Set G) = ZAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  let V := VAt Γ cp.firstStep
  let R := QAt Γ cp.firstStep
  let V0 := R ⊓ Subgroup.centralizer (twoResidualIn E : Set G)
  let Z := ZAt Γ cp.firstStep
  let Za := ZAt Γ cp.a
  have hDprev : D ≤ QAt Γ previous := hD ▸ inf_le_left
  have hDR : D ≤ R := hD ▸ inf_le_right
  have hQaG : QAt Γ cp.a ≤ GAt Γ cp.a := by
    change Γ.twoCoreAt _ ≤ _
    rw [Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hRG : R ≤ GAt Γ cp.firstStep := by
    change Γ.twoCoreAt _ ≤ _
    rw [Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hQaPrev : QAt Γ cp.a ≤ GAt Γ previous :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.a previous hprev.1 default).2.2
  have hcontains := eight_six_rigidity_core_containments ctx.sectionSeven Γ cp previous D L Q hD data
  have hDQa : D ≤ QAt Γ cp.a := hcontains.1.trans hcontains.2.1
  have hZZa : Z ≤ Za := (eight_six_first_step_fixed_line_local ctx hcenter hcard).2
  have hprevZa : ZAt Γ previous ≤ Za :=
    (eight_six_neighbor_center_lines ctx hcenter hquot hlength hcard previous hprev).2.1
  have hcommPrevious := (eight_six_predecessor_commutator_and_center_bound
    ctx.sectionSeven Γ cp hcenter hcard previous hprev.1 D L Q data).1
  have hDA : ⁅D,A⁆ ≤ Za :=
    ((Subgroup.commutator_mono hDprev inf_le_left).trans_eq hcommPrevious).trans hprevZa
  have hVA : ⁅V0,A⁆ ≤ Z := by
    have h := (eight_six_selected_fixed_core_commutator_bounds ctx hcenter hquot hlength hcard
      previous D L Q hprev hD hL data E A0 actor geom hedge).1
    rwa [inf_eq_left.mpr hV0Qa] at h
  have hDNV : D ≤ Subgroup.normalizer (V : Set G) :=
    (hDR.trans hRG).trans (stabilizer_le_normalizer_v Γ cp.firstStep)
  have hRD : R = V ⊔ D := eight_six_next_core_eq_v_sup_intersection
    ctx hlength previous D L Q hprev.1 hD hL data
  have hlower := eight_six_actor_cost_bound_symmetry ctx hquot previous hprev 8 hhigh
  have hV0D : V0 ≤ D := by
    intro w hw
    have hwQa : w ∈ QAt Γ cp.a := hV0Qa hw
    have hwprod : w ∈ (V : Set G) * (D : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left V D hDNV]
      exact hRD ▸ hw.1
    obtain ⟨v,hv,d,hd,hvd⟩ := hwprod
    have hvQa : v ∈ QAt Γ cp.a := by
      have hh := (QAt Γ cp.a).mul_mem hwQa ((QAt Γ cp.a).inv_mem (hDQa hd))
      rw [← hvd] at hh
      simpa only [mul_inv_cancel_right] using hh
    have hvPrevN : v ∈ Subgroup.normalizer (VAt Γ previous : Set G) :=
      stabilizer_le_normalizer_v Γ previous (hQaPrev hvQa)
    have hvAN : v ∈ Subgroup.normalizer (A : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hvPrevN,(QAt Γ cp.a).le_normalizer hvQa⟩
    have hwZN : w ∈ Subgroup.normalizer (Za : Set G) :=
      stabilizer_le_normalizer_z Γ cp.a (hQaG hwQa)
    have hsingle (a : G) (ha : a ∈ A) : ⁅a,v⁆ ∈ Za := by
      have hvEq : v = w * d⁻¹ := by rw [← hvd]; group
      have hvComm : ⁅v,a⁆ ∈ Za := by
        rw [hvEq,commutatorElement_mul_left_eq_conj_mul]
        exact Za.mul_mem
          ((Subgroup.mem_normalizer_iff.mp hwZN _).mp
            (hDA (Subgroup.commutator_mem_commutator (D.inv_mem hd) ha)))
          (hZZa (hVA (Subgroup.commutator_mem_commutator hw ha)))
      rw [← commutatorElement_inv]
      exact Za.inv_mem hvComm
    have hsmallComm := Subgroup.commutator_zpowers_le_of_generator_normalizes A Za v hvAN hsingle
    have hsmall := eight_six_backward_cost_le_four_of_core_part_commutator ctx hcenter hquot
      hlength hcard previous D L Q hprev data v hvQa hsmallComm
    have hvPrev : v ∈ QAt Γ previous := by
      by_contra hout
      have hh := hlower v ⟨hv,hvQa⟩ hout
      omega
    rw [hD]
    exact ⟨hvd ▸ (QAt Γ previous).mul_mem hvPrev (hDprev hd),hw.1⟩
  have hinter := eight_six_selected_fixed_core_intersection ctx hcenter hquot hlength hcard
    previous D L Q hprev hD hL data E A0 actor geom hedge
  exact (inf_eq_left.mpr hV0D).symm.trans hinter

end Stellmacher.SectionEight

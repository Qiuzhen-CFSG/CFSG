module
public import Stellmacher.SectionNine.DistanceOneCenterResidual
public import Theory.GroupTheory.Commutator.ElementaryCentralLayer
/-!
# The elementary quotient of the maximal V₁ subgroup

In the ambient Section Nine configuration of critical length one, suppose
U lies in the terminal two-core Q, contains the terminal vertex center Z,
and satisfies [U,Q]=Z and [U,O²(G_terminal)]=U. Then Z is normal in U and
the literal quotient U/Z is elementary abelian at two. These are the
commutator properties of the maximal V₁ used before (9.1)(10); neither
maximality nor the later core equality is a hypothesis here.

By (7.5), Z is central in the terminal stabilizer, and it is elementary
abelian. The commutator identity therefore puts every square of U in
Z(Q). The core-center residual theorem, obtained from (3.5) and (7.5),
shows that O²(G_terminal) fixes these squares. The generic full-commutator
lemma makes U's image in G_terminal/Z elementary abelian. The quotient
map then transfers its exponent bound to U/Z; its commutativity follows
from [U,U] ≤ Z.

Source: Stellmacher, Journal of Algebra 190 (1997), p.47, the application
of (1.3) to V₁/Z_(alpha+1) immediately after relation (9).
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
open scoped Pointwise commutatorElement
universe u
/-- The actual terminal full-commutator subgroup has an elementary quotient
by the terminal vertex center. The normality instance is supplied. -/
public theorem distance_one_v1_quotient_elementary
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) (U : Subgroup G)
    (hUQ : U ≤ q ctx.Γ ctx.criticalPath.a')
    (hZU : z ctx.Γ ctx.criticalPath.a' ≤ U)
    (hUQc : ⁅U, q ctx.Γ ctx.criticalPath.a'⁆ = z ctx.Γ ctx.criticalPath.a')
    (hUE : ⁅U, twoResidualIn (stabilizer ctx.Γ ctx.criticalPath.a')⁆ = U) :
    ∃ hN : (z ctx.Γ ctx.criticalPath.a').subgroupOf U |>.Normal,
      let _ := hN
      IsElementaryAbelian 2 (U ⧸ (z ctx.Γ ctx.criticalPath.a').subgroupOf U) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := stabilizer Γ cp.a'
  let Q := q Γ cp.a'
  let Z := z Γ cp.a'
  let E := twoResidualIn P
  have hlen : cp.length = 1 := hb
  have hstep : cp.firstStep = cp.a' := by
    calc
      cp.firstStep = cp.path ⟨1, by omega⟩ := cp.path_first.symm
      _ = cp.path ⟨cp.length, Nat.lt_succ_self _⟩ := by
        congr 1
        apply Fin.ext
        exact hb.symm
      _ = cp.a' := cp.path_end
  have hQP : Q ≤ P := by
    change q Γ cp.a' ≤ stabilizer Γ cp.a'
    rw [q, Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hUP : U ≤ P := hUQ.trans hQP
  have hZP : Z ≤ P := hZU.trans hUP
  have hEP : E ≤ P := Subgroup.map_subtype_le _
  have hZcentral : Z ≤ Subgroup.centralizer (P : Set G) := by
    have h75 := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).next_center.2
    rw [hstep] at h75
    change z Γ cp.a' ≤ _
    rw [h75]
    exact (omegaOneCenter_le_centerAmbient P).trans (centerAmbient_le_centralizer P)
  have hPN : P ≤ Subgroup.normalizer (Z : Set G) := stabilizer_le_normalizer_z Γ cp.a'
  let _ : (Z.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZP).mpr hPN
  have hUN : (Z.subgroupOf U).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZU).mpr (hUP.trans hPN)
  have hneighbor : cp.a ∈ neighborhood Γ cp.a' := by
    rw [neighborhood, Γ.neighbors_def]
    exact cp.endpoint_distance.trans hb
  let _ : IsElementaryAbelian 2 Z := z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ hneighbor
  have hcentral : ⁅(Subgroup.center Q).map Q.subtype, E⁆ = ⊥ := by
    have heq := congrArg (fun b => ⁅(Subgroup.center (q Γ b)).map (q Γ b).subtype,
      twoResidualIn (stabilizer Γ b)⁆ = ⊥) hstep
    exact heq.mp (next_core_center_residual ctx.sectionSeven Γ cp ctx.commutator_eq)
  have hsquares (u : G) (hu : u ∈ U) : u ^ 2 ∈ Subgroup.centralizer (E : Set G) := by
    apply (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcentral)
    refine ⟨⟨u ^ 2, Q.pow_mem (hUQ hu) 2⟩, ?_, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro w
    apply Subtype.ext
    have hc : ⁅u, (w : G)⁆ ∈ Z := hUQc.le (Subgroup.commutator_mem_commutator hu w.property)
    have hfix : u * ⁅u, (w : G)⁆ * u⁻¹ = ⁅u, (w : G)⁆ := by
      have hh := Subgroup.mem_centralizer_iff.mp (hZcentral hc) u (hUP hu)
      rw [hh]
      simp only [mul_assoc, mul_inv_cancel, mul_one]
    have hp : ⁅u, (w : G)⁆ ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ hc
    have hh : ⁅u ^ 2, (w : G)⁆ = 1 := by
      rw [pow_two, commutatorElement_mul_left_eq_conj_mul, hfix, ← pow_two, hp]
    exact (commutatorElement_eq_one_iff_mul_comm.mp hh).symm
  have hd : ⁅U, U⁆ ≤ Z := (Subgroup.commutator_mono le_rfl hUQ).trans hUQc.le
  have hdP : ⁅U.subgroupOf P, U.subgroupOf P⁆ ≤ Z.subgroupOf P := by
    apply Subgroup.commutator_le.mpr
    intro x hx y hy
    exact hd (Subgroup.commutator_mem_commutator hx hy)
  have hfP : ⁅U.subgroupOf P, E.subgroupOf P⁆ = U.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hUP,
      Subgroup.map_subgroupOf_eq_of_le hEP, hUE]
  have hsP (u : P) (hu : u ∈ U.subgroupOf P) :
      u ^ 2 ∈ Subgroup.centralizer (E.subgroupOf P : Set P) := by
    intro e he
    exact Subtype.ext ((hsquares u hu) e he)
  let π := QuotientGroup.mk' (Z.subgroupOf P)
  let _ := Subgroup.elementaryAbelian_quotient_image_of_commutator_eq
    (U.subgroupOf P) (E.subgroupOf P) (Z.subgroupOf P) hdP hfP hsP
  let _ := hUN
  refine ⟨hUN, ?_⟩
  have hderU : commutator U ≤ Z.subgroupOf U := by
    rw [commutator_def]
    apply Subgroup.commutator_le.mpr
    intro x _ y _
    exact hd (Subgroup.commutator_mem_commutator x.property y.property)
  let _ : IsMulCommutative (U ⧸ Z.subgroupOf U) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hderU
  refine { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro x
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) x
  rw [← map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  have hp : π (⟨u, hUP u.property⟩ : P) ^ 2 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian _ (Subgroup.mem_map_of_mem π
      (show (⟨u, hUP u.property⟩ : P) ∈ U.subgroupOf P from u.property))
  rw [← map_pow] at hp
  have hm : (⟨u, hUP u.property⟩ : P) ^ 2 ∈ Z.subgroupOf P :=
    (QuotientGroup.eq_one_iff _).mp hp
  exact hm
end Stellmacher.SectionNine

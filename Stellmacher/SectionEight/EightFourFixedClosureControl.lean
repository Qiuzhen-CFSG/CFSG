module
public import Stellmacher.SectionEight.EightFourOppositeClosureImage
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts
public import Stellmacher.SectionFiveToSeven.NeighborJoinCore

/-!
# Fixed-center closure control in Stellmacher (8.4)

For a noncommuting critical pair in the actual local context with central
first-step center, let F be
Section One's J-fixed subgroup on the faithful initial-center module. Its
normal closure C in the first-step stabilizer lies in the opposite endpoint
core and intersects the initial center exactly in F. The witness and the
source's nontrivial-closure branch are kept explicit. The canonical public
statements remain exact wrappers through the same local graph.

The centrality hypothesis first excludes critical length one. The neighbor
module therefore lies in the first-step two-core. Since F lies in the
initial center and that center lies in the neighbor module, normality of the
neighbor module puts C in that two-core and in the terminal stabilizer.
Source (3) identifies F with the initial center intersected with the
centralizer of the opposite-center closure S1. Normality of S1 in the
first-step stabilizer makes its centralizer invariant there, so C still
centralizes S1. Embed the two-group C in a terminal Sylow subgroup and apply
(7.4)'s Sylow-centralizer equality to obtain C in the terminal core. The
intersection assertion now follows directly from source (3).

This proves source (4) directly from the normal-closure consequences of (3),
without needing the stronger displayed commutator identity on journal p.39.
It does not assert normality of F, which requires the remaining (8.4) proof.
Source: Stellmacher, Journal of Algebra 190 (1997), (8.4), printed pp.38–39,
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

/-- Centrality at the first step excludes critical distance one. -/
public theorem eight_four_centered_length_gt_one_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    1 < ctx.criticalPath.length := by
  let h := ctx.sectionSeven
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  change 1 < cp.length
  by_contra hlength
  have hone : cp.length = 1 := by have := cp.length_pos; omega
  have hfirst : cp.firstStep = cp.a' := by
    calc
      cp.firstStep = cp.path ⟨1, by omega⟩ := cp.path_first.symm
      _ = cp.path ⟨cp.length, Nat.lt_succ_self _⟩ := by
        congr 1
        apply Fin.ext
        exact hone.symm
      _ = cp.a' := cp.path_end
  change z Γ cp.firstStep ≤ CenterAmbient (stabilizer Γ cp.firstStep) at hcenter
  rw [hfirst] at hcenter
  have hcontain := (lemma_seven_four h Γ cp).first_containment
  apply ctx.commutator_ne
  rw [Subgroup.commutator_comm]
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
  exact hcenter.trans ((SevenSix.centerAmbient_le_centralizer _).trans
    (Subgroup.centralizer_le (hcontain.1.trans hcontain.2)))


private theorem closure_le_of_normalizes
    {H : Type u} [Group H] (F P K : Subgroup H)
    (hFK : F ≤ K) (hPK : P ≤ Subgroup.normalizer (K : Set H)) :
    (Subgroup.normalClosure (F.subgroupOf P : Set P)).map P.subtype ≤ K := by
  have hnormal : (K.subgroupOf P).Normal := by
    constructor
    intro x hx p
    exact (Subgroup.mem_normalizer_iff.mp (hPK p.property) x).mp hx
  let := hnormal
  have hsub : Subgroup.normalClosure (F.subgroupOf P : Set P) ≤ K.subgroupOf P :=
    Subgroup.normalClosure_le_normal (fun x hx => hFK hx)
  rintro _ ⟨x, hx, rfl⟩
  exact hsub hx

/-- Source (4): the first-step normal closure of the J-fixed center lies in
the terminal core and meets the initial center in precisely that fixed subgroup. -/
public theorem eight_four_fixed_closure_control_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S) :
    let C := (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype
    C ≤ QAt ctx.Γ ctx.criticalPath.a' ∧
      C ⊓ ZAt ctx.Γ ctx.criticalPath.a = w.oneJFixedPoints S := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := stabilizer Γ cp.firstStep
  let F := w.oneJFixedPoints S
  let K := oppositeClosureLocal ctx
  let C := (Subgroup.normalClosure (F.subgroupOf P : Set P)).map P.subtype
  change C ≤ q Γ cp.a' ∧ C ⊓ z Γ cp.a = F
  let h := ctx.sectionSeven
  have hlen := eight_four_centered_length_gt_one_local ctx hcenter
  have hVcore : v Γ cp.firstStep ≤ q Γ cp.firstStep :=
    SevenSix.neighbor_join_le_core_of_length_gt_one Γ cp hlen cp.firstStep
  have hcoreP : q Γ cp.firstStep ≤ P := by
    rw [q, Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have h74 := lemma_seven_four h Γ cp
  have hFV : F ≤ v Γ cp.firstStep :=
    (Subgroup.map_subtype_le _).trans h74.first_containment.1
  have hFP : F ≤ P := hFV.trans (hVcore.trans hcoreP)
  have hFC : F ≤ C := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hFP]
    exact Subgroup.map_mono Subgroup.le_normalClosure
  have hCV : C ≤ v Γ cp.firstStep :=
    closure_le_of_normalizes F P _ hFV (stabilizer_le_normalizer_v Γ cp.firstStep)
  have hCend : C ≤ stabilizer Γ cp.a' := hCV.trans h74.first_containment.2
  have hCp : IsPGroup 2 C := by
    have hp : IsPGroup 2 (q Γ cp.firstStep) := by
      rw [q, Γ.twoCoreAt_def]
      exact (pCore_isPGroup (p := 2) (G := P)).map P.subtype
    exact hp.to_le (hCV.trans hVcore)
  have hfixed : F = z Γ cp.a ⊓ Subgroup.centralizer (K : Set H) :=
    fixed_center_eq_opposite_closure_centralizer_of_image_local ctx w
      (eight_four_opposite_closure_image_local ctx hcenter w hbranch)
  have hKP : K ≤ P := (opposite_closure_normal_next_local ctx).1
  have hPK : P ≤ Subgroup.normalizer (K : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKP).mp
      (opposite_closure_normal_next_local ctx).2
  have hPC : P ≤ Subgroup.normalizer (Subgroup.centralizer (K : Set H) : Set H) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro p hp x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro k hk
    have hconj : p⁻¹ * k * p ∈ K := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hPK (P.inv_mem hp)) k).mp hk
    have heq := hx (p⁻¹ * k * p) hconj
    simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left,
      mul_inv_cancel_right, inv_mul_cancel_right, mul_inv_cancel, mul_one] using
      congrArg (fun y => p * y * p⁻¹) heq
  have hCcentral : C ≤ Subgroup.centralizer (K : Set H) :=
    closure_le_of_normalizes F P _ (hfixed ▸ inf_le_right) hPC
  refine ⟨?_, le_antisymm ?_ ?_⟩
  · obtain ⟨T, hT⟩ := (hCp.comap_subtype (K := stabilizer Γ cp.a')).exists_le_sylow
    have hCT : C ≤ sylowTwoAmbient (stabilizer Γ cp.a') T := by
      intro x hx
      exact ⟨⟨x, hCend hx⟩, hT hx, rfl⟩
    rw [← (h74.commutator_case ctx.commutator_ne).1 T]
    exact le_inf hCT (hCcentral.trans (Subgroup.centralizer_le
      (opposite_center_le_opposite_closure_local ctx)))
  · rw [hfixed]
    exact le_inf inf_le_right (inf_le_left.trans hCcentral)
  · exact le_inf hFC (hfixed ▸ inf_le_left)

public theorem eight_four_centered_length_gt_one
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    1 < ctx.criticalPath.length := by
  exact eight_four_centered_length_gt_one_local ctx.toLocalContext hcenter

public theorem eight_four_fixed_closure_control
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S) :
    let C := (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype
    C ≤ QAt ctx.Γ ctx.criticalPath.a' ∧
      C ⊓ ZAt ctx.Γ ctx.criticalPath.a = w.oneJFixedPoints S := by
  exact eight_four_fixed_closure_control_local ctx.toLocalContext hcenter w hbranch

end Stellmacher.SectionEight

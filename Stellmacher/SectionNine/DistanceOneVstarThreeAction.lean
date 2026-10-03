module

public import Stellmacher.SectionNine.DistanceOneReduction
public import Stellmacher.SectionFiveToSeven.Result7_6.CoreFacts
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts
public import Stellmacher.SectionNine.DistanceOneTerminalCenter
public import Stellmacher.SectionNine.DistanceOneVstarResidualCentralizer

/-!
# Literal fixed cosets for the distance-one order-three action

The terminal center lies in the exact conjugate closure Vstar: (7.5) identifies
it with the edge Sylow omega-center, which lies in the initial vertex center;
(7.3) places it in the terminal core. The commuting critical pair makes this
subgroup central in Vstar. The quaternion central-product center calculation
and nontriviality identify it with the entire center, of order two.

The module also converts a centralizer bound on Vstar into the fixed-coset
formulation needed in Stellmacher (9.1), journal p.48 (PDF p.38 of
`refs/files/stellmacher-n-group.pdf`). The stabilizer normalizes the terminal
center and hence fixes it pointwise, as does every actor in its residual.

If conjugation by an order-three actor changes an element by a member of that
denominator, three iterations show that the difference has cube one. Its
square is also one, so the difference is trivial. The element then belongs
to the denominator by the supplied centralizer bound. The principal theorem now supplies the centralizer bound and actual actor
existence from `DistanceOneVstarResidualCentralizer`. Its geometric proof
constructs a swap of the intrinsic quaternion factors and rules out action on
only one factor in the terminal conjugation range of order dividing384. This
assembly discharges the residual theorem's explicit center premise with the
center identification above and concludes the literal fixed-coset assertion
from the original ambient context and three explicit local hypotheses.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven

universe u

public theorem distance_one_terminal_center_le_vstar
    {G : Type*} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hlength : ctx.criticalPath.length = 1) :
    ZAt ctx.Γ ctx.criticalPath.a' ≤ conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a') := by
  have hend : ctx.criticalPath.a' = ctx.criticalPath.firstStep := by
    rw [← ctx.criticalPath.path_end, ← ctx.criticalPath.path_first]
    congr 1
    exact Fin.ext hlength
  have homega : ZAt ctx.Γ ctx.criticalPath.a' = omegaOneCenter T := by
    rw [hend]
    exact (lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath
      ctx.commutator_eq).next_center.1
  have hstart : ZAt ctx.Γ ctx.criticalPath.a' ≤ ZAt ctx.Γ ctx.criticalPath.a := by
    rw [homega]
    obtain ⟨_, sylow, hsylow⟩ :=
      (SevenSix.edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1
    change omegaOneCenter T ≤ ctx.Γ.zAt _
    rw [ctx.Γ.zAt_def]
    exact le_sSup ⟨sylow, congrArg omegaOneCenter hsylow.symm⟩
  have hcore : ZAt ctx.Γ ctx.criticalPath.a' ≤ QAt ctx.Γ ctx.criticalPath.a' := by
    have hneighbor : ctx.criticalPath.a ∈
        CosetGraphContext.neighborhood ctx.Γ ctx.criticalPath.a' := by
      apply (SevenSix.mem_neighborhood_iff_adjacent ctx.Γ).mpr
      rw [hend]
      exact ctx.Γ.adjacent_symm ctx.criticalPath.firstStep_adj
    exact ((lemma_seven_three ctx.sectionSeven ctx.Γ).center_core _ _ hneighbor).trans
      (Subgroup.map_subtype_le _)
  intro element hmem
  exact Subgroup.subset_closure ⟨1, ⟨element, hstart hmem, hcore hmem⟩, by simp⟩

public theorem distance_one_vstar_center
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hlength : ctx.criticalPath.length = 1)
    (hfaithful : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (hlocal : DistanceOneLocalConclusion ctx.toLocalContext) :
    let Vstar := conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a')
    CenterAmbient Vstar = ZAt ctx.Γ ctx.criticalPath.a' ∧
      Nat.card (ZAt ctx.Γ ctx.criticalPath.a') = 2 := by
  let Vstar := conjugateClosure
    (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
    (GAt ctx.Γ ctx.criticalPath.a')
  have hcontain := distance_one_terminal_center_le_vstar ctx.toLocalContext hlength
  have hcard := distance_one_terminal_center_card ctx hlength hfaithful hlocal hcontain
  refine ⟨?_, hcard⟩
  have hle : ZAt ctx.Γ ctx.criticalPath.a' ≤ CenterAmbient Vstar := by
    intro element helement
    refine ⟨⟨element, hcontain helement⟩, ?_, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro other
    apply Subtype.ext
    exact (distance_one_terminal_center_centralizes_closure ctx.toLocalContext
      other.property element helement).symm
  apply (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  have hcenter : Nat.card (Subgroup.center Vstar) = 2 := by
    obtain ⟨left, right, hleft, hright, hjoin, hinter, hcomm, _⟩ := hlocal.2.2.2.2
    change Vstar = left ⊔ right at hjoin
    rw [hjoin]
    exact Subgroup.quaternion_central_product_center_card left right
      hleft hright hinter hcomm
  simp only [CenterAmbient, Subgroup.card_map_of_injective Vstar.subtype_injective,
    hcenter, hcard, le_refl]

private theorem normalizer_centralizes_two
    {G : Type*} [Group G] (denominator : Subgroup G)
    (hcard : Nat.card denominator = 2) :
    Subgroup.normalizer (denominator : Set G) ≤
      Subgroup.centralizer (denominator : Set G) := by
  obtain ⟨nonidentity, hne, hunique⟩ :=
    (Nat.card_eq_two_iff' (1 : denominator)).mp hcard
  intro actor hactor
  rw [Subgroup.mem_centralizer_iff]
  intro element hmem
  by_cases hone : element = 1
  · simp [hone]
  have helement : (⟨element, hmem⟩ : denominator) = nonidentity :=
    hunique _ (fun heq => hone (congrArg Subtype.val heq))
  have hconj : actor * element * actor⁻¹ ∈ denominator :=
    (Subgroup.mem_normalizer_iff.mp hactor element).mp hmem
  have hconjne : actor * element * actor⁻¹ ≠ 1 := by
    intro heq
    have heq' := congrArg (fun value : G => actor⁻¹ * value * actor) heq
    exact hone (by simpa [mul_assoc] using heq')
  have hconjeq : (⟨actor * element * actor⁻¹, hconj⟩ : denominator) = nonidentity :=
    hunique _ (fun heq => hconjne (congrArg Subtype.val heq))
  have heq := congrArg (fun value : denominator => (value : G) * actor)
    (hconjeq.trans helement.symm)
  simpa [mul_assoc] using heq.symm

private theorem commute_of_commutator_mem_two
    {G : Type*} [Group G] (denominator : Subgroup G)
    (hcard : Nat.card denominator = 2) (actor element : G)
    (hactor : actor ∈ Subgroup.centralizer (denominator : Set G))
    (hthree : actor ^ 3 = 1)
    (hmem : actor * element * actor⁻¹ * element⁻¹ ∈ denominator) :
    Commute actor element := by
  let difference := actor * element * actor⁻¹ * element⁻¹
  have hfixed : actor * difference * actor⁻¹ = difference := by
    have heq := Subgroup.mem_centralizer_iff.mp hactor difference hmem
    calc
      actor * difference * actor⁻¹ = difference * actor * actor⁻¹ := by rw [heq]
      _ = difference := mul_inv_cancel_right _ _
  have hstep : actor * element * actor⁻¹ = difference * element := by
    simp [difference, mul_assoc]
  have hcube : difference ^ 3 = 1 := by
    have hiter : actor ^ 3 * element * (actor ^ 3)⁻¹ = difference ^ 3 * element := by
      calc
        actor ^ 3 * element * (actor ^ 3)⁻¹ =
            (MulAut.conj actor) ((MulAut.conj actor) ((MulAut.conj actor) element)) := by
          simp [MulAut.conj_apply, pow_succ, mul_assoc]
        _ = difference ^ 3 * element := by
          change (MulAut.conj actor) element = difference * element at hstep
          change (MulAut.conj actor) difference = difference at hfixed
          simp only [hstep, map_mul, hfixed]
          simp [pow_succ, mul_assoc]
    have heq : 1 * element = difference ^ 3 * element := by
      simpa only [hthree, inv_one, one_mul, mul_one] using hiter
    exact (mul_right_cancel heq).symm
  have hsquare : difference ^ 2 = 1 := by
    have heq := pow_card_eq_one' (x := (⟨difference, hmem⟩ : denominator))
    rw [hcard] at heq
    exact congrArg Subtype.val heq
  have hone : difference = 1 := by
    simpa [pow_succ, hsquare] using hcube
  show actor * element = element * actor
  have heq := congrArg (fun value : G => value * element * actor) hone
  simpa [difference, mul_assoc] using heq

public theorem distance_one_vstar_fixed_cosets_of_centralizer_bound
    {G : Type*} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a') = 2)
    (hcentralizer : ∀ actor : G, actor ∈ EAt ctx.Γ ctx.criticalPath.a' →
      orderOf actor = 3 → ∀ element : G,
      element ∈ conjugateClosure
        (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
        (GAt ctx.Γ ctx.criticalPath.a') →
      Commute actor element → element ∈ ZAt ctx.Γ ctx.criticalPath.a') :
    ∀ actor : G, actor ∈ EAt ctx.Γ ctx.criticalPath.a' → orderOf actor = 3 →
      ∀ element : G, element ∈ conjugateClosure
        (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
        (GAt ctx.Γ ctx.criticalPath.a') →
        actor * element * actor⁻¹ * element⁻¹ ∈ ZAt ctx.Γ ctx.criticalPath.a' →
          element ∈ ZAt ctx.Γ ctx.criticalPath.a' := by
  intro actor hactor horder element helement hfixed
  apply hcentralizer actor hactor horder element helement
  apply commute_of_commutator_mem_two _ hcard actor element ?_ ?_ hfixed
  · apply normalizer_centralizes_two _ hcard
    apply stabilizer_le_normalizer_z ctx.Γ ctx.criticalPath.a'
    apply SevenSix.twoResidualIn_le (GAt ctx.Γ ctx.criticalPath.a')
    simpa only [EAt, CosetGraphContext.e, ctx.Γ.twoResidualAt_def,
      GAt, CosetGraphContext.stabilizer] using hactor
  · rw [← horder]
    exact pow_orderOf_eq_one actor

public theorem distance_one_vstar_three_action
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hlength : ctx.criticalPath.length = 1)
    (hfaithful : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (hlocal : DistanceOneLocalConclusion ctx.toLocalContext) :
    let Vstar := Stellmacher.SectionsFiveToSeven.conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a')
    CenterAmbient Vstar = ZAt ctx.Γ ctx.criticalPath.a' ∧
      Nat.card (ZAt ctx.Γ ctx.criticalPath.a') = 2 ∧
      (∃ actor : G, actor ∈ EAt ctx.Γ ctx.criticalPath.a' ∧ orderOf actor = 3) ∧
      ∀ actor : G, actor ∈ EAt ctx.Γ ctx.criticalPath.a' → orderOf actor = 3 →
        ∀ element : G, element ∈ Vstar →
          actor * element * actor⁻¹ * element⁻¹ ∈ ZAt ctx.Γ ctx.criticalPath.a' →
            element ∈ ZAt ctx.Γ ctx.criticalPath.a' := by
  obtain ⟨hcenter, hcard⟩ := distance_one_vstar_center ctx hlength hfaithful hlocal
  obtain ⟨hexists, hcentralizer⟩ :=
    distance_one_vstar_residual_centralizer ctx hlength hfaithful hlocal hcenter
  exact ⟨hcenter, hcard, hexists,
    distance_one_vstar_fixed_cosets_of_centralizer_bound ctx.toLocalContext hcard hcentralizer⟩

end Stellmacher.SectionNine

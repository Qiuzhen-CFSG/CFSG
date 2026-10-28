module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Calculations

/-!
# Assembly of the first hat identity from the D calculations

The two forward configurations prove the identities at indices two and
four; their actual turn conjugators give six and eight. The reflected
configurations supply ten and twelve. No new path or selected vertex is
identified with the supplied path. The central application also proves
the ordered setwise-product equality consumed by the orbit-layer theorem.

This is conditional assembly: PreliminaryEstimatesOnPath and
ThirdContainmentOnPath must both be constructed from the source inputs
before (4.5.3)(i) is complete. Neither record is an input to the intended
unconditional source theorem.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.3)(i), pp.897--898.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity
open PathCentrality NormalizerTransfer
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem decomposition_le_join {a b t d e : Vertex R}
    (h : PreliminaryEstimates R a b t d e) : hatV R b a ≤ Vcirc R b ⊔ fixedSeed R b := by
  intro x hx
  have hx' : x ∈ (hatV R b a : Set (FreeAmalgam R)) := hx
  rw [h.decomposition_product] at hx'
  obtain ⟨v, hv, z, hz, rfl⟩ := hx'
  exact (Vcirc R b ⊔ fixedSeed R b).mul_mem (mem_sup_left hv) (mem_sup_right hz)

private theorem forward_identity [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a)
    (preliminary : PreliminaryEstimatesOnPath R p) (third : ThirdContainmentOnPath R p)
    {i : ℕ} (hi : Even i) (hi4 : 4 ≤ i) (hi6 : i ≤ 6) :
    hatV R (p.walk.getVert (i - 2)) (p.walk.getVert i) =
      Vcirc R (p.walk.getVert (i - 2)) ⊔ Z R (p.walk.getVert (i - 2)) := by
  by_contra hn
  have estimates := preliminary.forward i hi hi4 hi6 hn
  have hb : Even (i - 2) := by rw [Nat.even_iff] at hi ⊢; omega
  apply hn
  apply hat_eq_of_calculations common earlier (p.even_color hi (by omega))
    (p.even_color hb (by omega)) (p.even_color (hi.add (by decide : Even 8)) (by omega))
    (t := p.walk.getVert (i - 1))
  · exact adjacent_symm R (by
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using
        p.adjacent (i := i - 1) (by omega))
  · simpa only [show i - 2 + 1 = i - 1 by omega] using
      p.adjacent (i := i - 2) (by omega)
  · simpa only [Nat.sub_add_cancel (by omega : 2 ≤ i)] using
      (p.moving_neighbors source common earlier hb (by omega) (by omega)).2
  · exact forward_generation common earlier p (firstFactsOnPath source common earlier p)
      hi (by omega) hi6
  · exact decomposition_le_join estimates
  · exact estimates.span_commutator
  · exact third.forward i hi hi4 hi6 hn estimates

private theorem backward_identity [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a)
    (preliminary : PreliminaryEstimatesOnPath R p) (third : ThirdContainmentOnPath R p)
    {i : ℕ} (hi : Even i) (hi8 : 8 ≤ i) (hi10 : i ≤ 10) :
    hatV R (p.walk.getVert (i + 2)) (p.walk.getVert i) =
      Vcirc R (p.walk.getVert (i + 2)) ⊔ Z R (p.walk.getVert (i + 2)) := by
  by_contra hn
  have estimates := preliminary.backward i hi hi8 hi10 hn
  have hf : Even (i - 8) := by rw [Nat.even_iff] at hi ⊢; omega
  apply hn
  apply hat_eq_of_calculations common earlier (p.even_color hi (by omega))
    (p.even_color (hi.add (by decide : Even 2)) (by omega))
    (p.even_color hf (by omega)) (t := p.walk.getVert (i + 1))
  · exact p.adjacent (by omega)
  · exact adjacent_symm R (by
      simpa only [Nat.add_assoc] using p.adjacent (i := i + 1) (by omega))
  · simpa only [Nat.add_sub_cancel] using
      (p.moving_neighbors source common earlier (hi.add (by decide : Even 2))
        (by omega) (by omega)).1
  · exact backward_generation common earlier p (firstFactsOnPath source common earlier p)
      hi hi8 (by omega)
  · exact decomposition_le_join estimates
  · exact estimates.span_commutator
  · exact third.backward i hi hi8 hi10 hn estimates

private theorem hat_identity_act {a b : Vertex R} (g : FreeAmalgam R)
    (h : hatV R b a = Vcirc R b ⊔ Z R b) :
    hatV R (act R g b) (act R g a) = Vcirc R (act R g b) ⊔ Z R (act R g b) := by
  rw [hatV, LocalCommutator.CriticalCase.localZSpan_act, ← hatV,
    h, Subgroup.map_sup, ← Vcirc_act, ← Z_act]

/-- The printed symmetry step uses the supplied local turn and moves both
vertices in the hat layer. No independently chosen path is identified with p. -/
theorem identity_across_turn {a : Vertex R} (p : SourcePath R a) {i : ℕ}
    (hi : Even i) (hi2 : 2 ≤ i) (hi12 : i ≤ 12)
    (h : hatV R (p.walk.getVert (i - 2)) (p.walk.getVert i) =
      Vcirc R (p.walk.getVert (i - 2)) ⊔ Z R (p.walk.getVert (i - 2))) :
    hatV R (p.walk.getVert (i + 2)) (p.walk.getVert i) =
      Vcirc R (p.walk.getVert (i + 2)) ⊔ Z R (p.walk.getVert (i + 2)) := by
  obtain ⟨g, hg, ht⟩ := p.turns i hi hi2 hi12
  have hfix : act R g⁻¹ (p.walk.getVert i) = p.walk.getVert i :=
    (stabilizer R _).inv_mem hg
  have ht' := congrArg (act R g⁻¹) ht
  rw [← act_mul, mul_inv_cancel, act_one] at ht'
  simpa only [hfix, ← ht'] using hat_identity_act g⁻¹ h

/-- Assemble all six first-hat identities from the two independent D
calculation families. Both families remain explicit until their producers
are completed; this is the final assembly consumer of those obligations. -/
theorem identitiesOnPath_of_calculations [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a)
    (preliminary : PreliminaryEstimatesOnPath R p) (third : ThirdContainmentOnPath R p) :
    HatIdentitiesOnPath R p := by
  have h2 := forward_identity common earlier p preliminary third (i := 4)
    (by decide) (by decide) (by decide)
  have h4 := forward_identity common earlier p preliminary third (i := 6)
    (by decide) (by decide) (by decide)
  have h6 := identity_across_turn p (i := 4) (by decide) (by decide) (by decide) h2
  have h8 := identity_across_turn p (i := 6) (by decide) (by decide) (by decide) h4
  have h10 := backward_identity common earlier p preliminary third (i := 8)
    (by decide) (by decide) (by decide)
  have h12 := backward_identity common earlier p preliminary third (i := 10)
    (by decide) (by decide) (by decide)
  have h6' := (backward_hatV_eq_forward p (i := 6) (by decide) (by decide) (by decide)).symm.trans h6
  have h8' := (backward_hatV_eq_forward p (i := 8) (by decide) (by decide) (by decide)).symm.trans h8
  have h10' := (backward_hatV_eq_forward p (i := 10) (by decide) (by decide) (by decide)).symm.trans h10
  have h12' := (backward_hatV_eq_forward p (i := 12) (by decide) (by decide) (by decide)).symm.trans h12
  constructor
  intro i hi hi2 hi12
  have hc : i = 2 ∨ i = 4 ∨ i = 6 ∨ i = 8 ∨ i = 10 ∨ i = 12 := by
    rw [Nat.even_iff] at hi
    omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h2
  · exact h4
  · exact h6'
  · exact h8'
  · exact h10'
  · exact h12'

/-- Apply the assembled same-path identities to the literal centered hat
and its ordered setwise product, as required by the orbit-layer consumer. -/
theorem center_of_calculations [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a)
    (preliminary : PreliminaryEstimatesOnPath R p) (third : ThirdContainmentOnPath R p) :
    hatV R a (p.walk.getVert 6) = Vcirc R a ⊔ Z R a ∧
      (hatV R a (p.walk.getVert 6) : Set (FreeAmalgam R)) =
        (Vcirc R a : Set (FreeAmalgam R)) * (Z R a : Set (FreeAmalgam R)) := by
  have heq := (identitiesOnPath_of_calculations common earlier p preliminary third).center
  refine ⟨heq, hatV_product_of_eq common ?_ heq⟩
  simpa only [p.center_eq] using p.even_color (i := 4) (by decide) (by decide)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity

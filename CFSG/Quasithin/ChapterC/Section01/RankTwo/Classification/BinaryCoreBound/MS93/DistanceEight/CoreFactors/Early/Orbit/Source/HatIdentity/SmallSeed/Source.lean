module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Third.Opposite
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.SmallSeed.Descent
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity

/-!
# All first-hat identities from the source hypotheses

The contrary third-containment bound and the marked quotient-line
obstruction force the opposite hat identity. The original turn transfers
it back, and the actual hat-fixed seed then descends through the common
edge. Reflection retains the original walk and proves all six identities.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.3)(i), pp.897--898.
Only the genuine earlier source (4.4), recorded by Earlier, remains explicit.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.SmallSeed
open PathCentrality NormalizerTransfer Preliminary Preliminary.Decomposition
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem identity_reverse_turn {a : Vertex R} (p : SourcePath R a) {i : ℕ}
    (hi : Even i) (hi2 : 2 ≤ i) (hi12 : i ≤ 12)
    (h : hatV R (p.walk.getVert (i + 2)) (p.walk.getVert i) =
      Vcirc R (p.walk.getVert (i + 2)) ⊔ Z R (p.walk.getVert (i + 2))) :
    hatV R (p.walk.getVert (i - 2)) (p.walk.getVert i) =
      Vcirc R (p.walk.getVert (i - 2)) ⊔ Z R (p.walk.getVert (i - 2)) := by
  obtain ⟨g,hg,ht⟩ := p.turns i hi hi2 hi12
  have he : hatV R (act R g (p.walk.getVert (i+2))) (act R g (p.walk.getVert i)) =
      Vcirc R (act R g (p.walk.getVert (i+2))) ⊔ Z R (act R g (p.walk.getVert (i+2))) := by
    rw [hatV, LocalCommutator.CriticalCase.localZSpan_act, ← hatV,
      h, Subgroup.map_sup, ← Vcirc_act, ← Z_act]
  have hfix : act R g (p.walk.getVert i) = p.walk.getVert i := hg
  simpa only [hfix,ht] using he

/-- Failure of the smaller-seed third containment gives the opposite
hat identity on precisely the original path. -/
theorem opposite_identity_of_failure [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) {i : ℕ}
    (hi : Even i) (hi4 : 4 ≤ i) (hi6 : i ≤ 6)
    (hnot : ¬ (span R (p.walk.getVert i) (p.walk.getVert (i-2))
      (p.walk.getVert (i-1)) : Set (FreeAmalgam R)) ⊆
      (Z R (p.walk.getVert i) : Set (FreeAmalgam R)) *
        (Q R (p.walk.getVert (i+8)) : Set (FreeAmalgam R))) :
    hatV R (p.walk.getVert (i+2)) (p.walk.getVert i) =
      Vcirc R (p.walk.getVert (i+2)) ⊔ Z R (p.walk.getVert (i+2)) := by
  have hic : Even (i+2) := hi.add (by decide)
  have hid : Even (i+4) := hi.add (by decide)
  have hbound := (failure_natural_bound_forward common earlier p hi hi4 hi6 hnot).2
  apply Third.Opposite.hat_eq_of_natural_bound common earlier
    (u := p.walk.getVert (i+1)) (v := p.walk.getVert (i+3))
    (p.even_color hi (by omega)) (p.even_color hic (by omega))
    (p.even_color hid (by omega))
  · exact p.adjacent (by omega)
  · exact adjacent_symm R (by
      simpa only [Nat.add_assoc] using p.adjacent (i := i+1) (by omega))
  · exact adjacent_symm R (by
      simpa only [Nat.add_assoc] using p.adjacent (i := i+3) (by omega))
  · simpa only [Nat.add_assoc] using p.adjacent (i := i+2) (by omega)
  · simpa only [Nat.add_sub_cancel] using
      (p.moving_neighbors source common earlier hic (by omega) (by omega)).1
  · simpa only [Nat.add_assoc] using
      (p.moving_neighbors source common earlier hic (by omega) (by omega)).2
  · simpa only [show i+2-1=i+1 by omega, Nat.add_assoc] using
      p.edge_Z_ne (i+2) hic (by omega) (by omega)
  · exact hbound

/-- The third containment is forced whenever the target hat identity
has not already been obtained; no source-conclusion callback remains. -/
theorem third_containment_forward [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) {i : ℕ}
    (hi : Even i) (hi4 : 4 ≤ i) (hi6 : i ≤ 6)
    (hne : hatV R (p.walk.getVert (i-2)) (p.walk.getVert i) ≠
      Vcirc R (p.walk.getVert (i-2)) ⊔ Z R (p.walk.getVert (i-2))) :
    (span R (p.walk.getVert i) (p.walk.getVert (i-2)) (p.walk.getVert (i-1)) : Set (FreeAmalgam R)) ⊆
      (Z R (p.walk.getVert i) : Set (FreeAmalgam R)) *
        (Q R (p.walk.getVert (i+8)) : Set (FreeAmalgam R)) := by
  by_contra hnot
  exact hne (identity_reverse_turn p hi (by omega) (by omega)
    (opposite_identity_of_failure common earlier p hi hi4 hi6 hnot))

/-- Original source hypotheses prove the first two preceding hat identities. -/
theorem forward_identity [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) {i : ℕ}
    (hi : Even i) (hi4 : 4 ≤ i) (hi6 : i ≤ 6) :
    hatV R (p.walk.getVert (i-2)) (p.walk.getVert i) =
      Vcirc R (p.walk.getVert (i-2)) ⊔ Z R (p.walk.getVert (i-2)) := by
  by_contra hn
  apply hn
  let w := forwardWindow common earlier p hi hi4 hi6
  have est := estimates_forward common earlier p hi hi4 hi6
  apply hat_eq_of_product common earlier w.color_a w.color_b
    (p.even_color (hi.add (by decide : Even 8)) (by omega)) w.adjacent_a w.adjacent_b w.moving
  · exact forward_generation common earlier p (firstFactsOnPath source common earlier p) hi (by omega) hi6
  · intro x hx
    change x ∈ (hatV R (p.walk.getVert (i-2)) (p.walk.getVert i) : Set (FreeAmalgam R)) at hx
    rw [est.product] at hx
    obtain ⟨u,hu,z,hz,rfl⟩ := hx
    exact mul_mem (mem_sup_left hu) (mem_sup_right hz)
  · exact est.span_comm
  · exact third_containment_forward common earlier p hi hi4 hi6 hn

/-- Reflection supplies the terminal two identities without identifying
independently chosen paths or replacing their literal vertices. -/
theorem backward_identity [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) {i : ℕ}
    (hi : Even i) (hi8 : 8 ≤ i) (hi10 : i ≤ 10) :
    hatV R (p.walk.getVert (i+2)) (p.walk.getVert i) =
      Vcirc R (p.walk.getVert (i+2)) ⊔ Z R (p.walk.getVert (i+2)) := by
  obtain ⟨c,⟨q,hq⟩⟩ := PathExtension.reverse_sourcePath common earlier p
  have h := forward_identity common earlier q (i := 14-i)
    (by rw [Nat.even_iff] at hi ⊢; omega) (by omega) (by omega)
  simpa only [hq, show 14-(14-i-2)=i+2 by omega, show 14-(14-i)=i by omega] using h

/-- All six literal first-hat identities follow from CommonFacts and
Earlier. The latter is precisely the independently owned source (4.4). -/
theorem identitiesOnPath [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) : HatIdentitiesOnPath R p := by
  have h2 := forward_identity common earlier p (i := 4) (by decide) (by decide) (by decide)
  have h4 := forward_identity common earlier p (i := 6) (by decide) (by decide) (by decide)
  have h6 := identity_across_turn p (i := 4) (by decide) (by decide) (by decide) h2
  have h8 := identity_across_turn p (i := 6) (by decide) (by decide) (by decide) h4
  have h10 := backward_identity common earlier p (i := 8) (by decide) (by decide) (by decide)
  have h12 := backward_identity common earlier p (i := 10) (by decide) (by decide) (by decide)
  have h6' := (backward_hatV_eq_forward p (i := 6) (by decide) (by decide) (by decide)).symm.trans h6
  have h8' := (backward_hatV_eq_forward p (i := 8) (by decide) (by decide) (by decide)).symm.trans h8
  have h10' := (backward_hatV_eq_forward p (i := 10) (by decide) (by decide) (by decide)).symm.trans h10
  have h12' := (backward_hatV_eq_forward p (i := 12) (by decide) (by decide) (by decide)).symm.trans h12
  constructor
  intro i hi hi2 hi12
  have hc : i=2 ∨ i=4 ∨ i=6 ∨ i=8 ∨ i=10 ∨ i=12 := by rw [Nat.even_iff] at hi; omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl
  · exact h2
  · exact h4
  · exact h6'
  · exact h8'
  · exact h10'
  · exact h12'
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.SmallSeed

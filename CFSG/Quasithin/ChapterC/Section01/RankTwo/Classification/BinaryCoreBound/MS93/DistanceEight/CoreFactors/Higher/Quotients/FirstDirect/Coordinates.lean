module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.Complete

/-!
# Exact first-hat coordinates on the original quotient

The invariant hat subgroup contains a moving quotient vector. Transitivity
of the original SL3(2) action makes the restriction of V/B coordinates
surjective. The source index bound then identifies its kernel with exactly
Z, without a larger fixed-kernel assumption or a splitting of the radius.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.3)(i) and (4.5.4)(v),
pp.898--899. This constructs coordinates; their source-marked dual
orientation is handled separately.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.FirstDirect
open PathCentrality
open Early.Orbit.Source.HatIdentity.Third
open Escape.Propagation.Backward.Products.Selection.Choices

private theorem natural_transitive (v w : Fin 3 → ZMod 2) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : SL, g.val.mulVec v = w := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Matrix.PSL3Two.PSL
    (⟨v,hv⟩ : Matrix.PSL3Two.Fano.Point) (⟨w,hw⟩ : Matrix.PSL3Two.Fano.Point)
  obtain ⟨g,rfl⟩ := Matrix.PSL3Two.project_surjective g
  rw [Matrix.PSL3Two.Fano.project_smul_point] at hg
  exact ⟨g, congrArg Subtype.val hg⟩

private theorem restrict_onto {G : Type*} [Group G]
    {π : G →* SL} {V N A : Subgroup G}
    (n : RankOnePairing.NaturalFactor π ⊤ V N)
    (hπ : Function.Surjective π) (hA : A ≤ V)
    (hn : (⊤ : Subgroup G) ≤ normalizer A) (hnot : ¬ A ≤ N) :
    Function.Surjective (n.coordinates.comp (inclusion hA)) := by
  obtain ⟨x,hx,hxN⟩ := Set.not_subset.mp hnot
  let v : V := ⟨x,hA hx⟩
  have hv : (n.coordinates v).toAdd ≠ 0 := by
    intro hz
    have hk : v ∈ n.coordinates.ker := by exact hz
    rw [n.kernel] at hk
    exact hxN hk
  intro y
  by_cases hy : y = 1
  · exact ⟨1, by simp [hy]⟩
  obtain ⟨g,hg⟩ := natural_transitive _ _ hv (by
    intro h; exact hy h)
  obtain ⟨l,hl⟩ := hπ (n.marking.symm g)
  let z : A := ⟨l*x*l⁻¹, le_normalizer_iff.mp hn l (mem_top _) x hx⟩
  refine ⟨z, ?_⟩
  apply Multiplicative.toAdd.injective
  have h := n.action l (mem_top _) v ((inclusion hA) z) rfl
  rw [hl,n.marking.apply_symm_apply] at h
  exact h.trans hg

private theorem kernel_eq_of_index_le {G E : Type*} [Group G] [Finite G] [Group E]
    (f : G →* E) (hf : Function.Surjective f) (hE : Nat.card E = 8)
    (N : Subgroup G) (hN : N ≤ f.ker) (hindex : N.index ≤ 8) : f.ker = N := by
  have hk : f.ker.index = 8 := by
    rw [index_ker, f.range_eq_top_of_surjective hf, card_top, hE]
  have hmul := relIndex_mul_index hN
  rw [hk] at hmul
  have hpos : 0 < N.relIndex f.ker := by
    change 0 < (N.subgroupOf f.ker).index
    exact Nat.card_pos
  have he : N.relIndex f.ker = 1 := by omega
  exact le_antisymm (relIndex_eq_one.mp he) hN

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Literal restriction of the V/B coordinates to the actual first hat. -/
noncomputable def coordinates (common : CommonFacts R source geometry)
    (_earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R))
    (s : Escape.NaturalSectionAt (alpha R) (V R (alpha R)) (Z R (alpha R))) :
    hatV R (alpha R) (p.walk.getVert 6) →* Space := by
  let n := SourceLines.lineFactor common rfl s
  let S := stabilizer R (alpha R)
  have hv : hatV R (alpha R) (p.walk.getVert 6) ≤ V R (alpha R) :=
    hatV_le_radius R (by rw [SimpleGraph.dist_comm]; simpa only [p.center_eq] using
      (p.distance (geometry := geometry) (i := 4) (j := 6) (by decide) (by decide)).le)
  exact n.coordinates.comp
    (((subgroupOfEquivOfLe s.local_group).symm.toMonoidHom).comp (inclusion hv))

theorem coordinates_onto (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R))
    (s : Escape.NaturalSectionAt (alpha R) (V R (alpha R)) (Z R (alpha R))) :
    Function.Surjective (coordinates common earlier p s) := by
  let A := hatV R (alpha R) (p.walk.getVert 6)
  let S := stabilizer R (alpha R)
  have hv : A ≤ V R (alpha R) := hatV_le_radius R (by
    rw [SimpleGraph.dist_comm]
    simpa only [p.center_eq] using (p.distance (geometry := geometry) (i := 4) (j := 6) (by decide) (by decide)).le)
  have ha : A ≤ S := hv.trans s.local_group
  have hn : (⊤ : Subgroup S) ≤ normalizer (A.subgroupOf S : Set S) := by
    intro g _
    rw [← subgroupOf_normalizer_eq ha]
    exact hatV_normalized R _ _ g.property
  have hnot : ¬ A.subgroupOf S ≤ (B R (alpha R) (geometry.Z_normal (alpha R))).subgroupOf S := by
    intro h
    have hA : A ≤ B R (alpha R) (geometry.Z_normal (alpha R)) := by
      intro x hx
      exact h (show (⟨x,ha hx⟩ : S) ∈ A.subgroupOf S from hx)
    have hm := (p.moving_neighbors source common earlier (i := 4) (by decide) (by decide) (by decide)).2
    simp only [p.center_eq] at hm
    exact hm.2 ((Z_le_localZSpan R _ _).trans hA)
  have hsur := restrict_onto (SourceLines.lineFactor common rfl s)
    s.module_section.projection_surjective (subgroupOf_mono S hv) hn hnot
  intro y
  obtain ⟨x,hx⟩ := hsur y
  exact ⟨(subgroupOfEquivOfLe ha) x,hx⟩

theorem coordinates_kernel (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R))
    (s : Escape.NaturalSectionAt (alpha R) (V R (alpha R)) (Z R (alpha R))) :
    (coordinates common earlier p s).ker =
      (Z R (alpha R)).subgroupOf (hatV R (alpha R) (p.walk.getVert 6)) := by
  let A := hatV R (alpha R) (p.walk.getVert 6)
  let := finite_stabilizer R (alpha R)
  let : Finite A := Finite.of_injective
    (inclusion ((hatV_le_radius R (by rw [SimpleGraph.dist_comm]; simpa only [p.center_eq] using
      (p.distance (geometry := geometry) (i := 4) (j := 6) (by decide) (by decide)).le)).trans s.local_group)) (inclusion_injective _)
  apply kernel_eq_of_index_le _ (coordinates_onto common earlier p s)
    (by rw [Nat.card_eq_fintype_card]; decide : Nat.card Space = 8)
  · intro x hx
    change (SourceLines.lineFactor common rfl s).coordinates _ = 1
    apply MonoidHom.mem_ker.mp
    rw [(SourceLines.lineFactor common rfl s).kernel]
    exact Escape.EdgeTransfer.Z_le_B common.large_distance _ rfl hx
  · exact Early.Orbit.Source.Complete.first_hat_quotient_bound common earlier p
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.FirstDirect

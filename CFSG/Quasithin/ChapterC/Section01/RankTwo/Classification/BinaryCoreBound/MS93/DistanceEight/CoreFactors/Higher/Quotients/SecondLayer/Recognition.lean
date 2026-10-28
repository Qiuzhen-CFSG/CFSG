module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Actions
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Linear
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Gluing

/-!
# Conditional fixed-marking recognition of the two source orbit factors

The actual orbit modules and their SL3(2) actions are constructed from the
literal preceding commutator bound and orbit abelianness. Full movement,
faithfulness and a small involution give the three-dimensional alternatives;
an actor with different displacement on U_a fixes the dual orientation.
The resulting surjection has exactly the stated relative denominator kernel.

The final consumer applies the existing two-factor gluing proof to these
constructed sections. Source moving generation and faithfulness, and the
small-actor displacement comparison at d and at the selected delta, remain
explicit obligations. This module does not claim (4.5.4)(iii) from Earlier
alone. The source assembly remains here until both obligations are discharged.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.4)(iii), pp.898--899.
-/

public section
open scoped Pointwise

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open DistanceFour.Linear Escape.Initial.Natural.Splitting
variable {M : Type*} [Group M] [Finite M] {R L : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}
  {common : CommonFacts R source geometry}

/-- The source dynamics and displacement comparison construct the actual
surjection, its exact relative kernel, and the required fixed-marking action. -/
theorem OrbitModule.markedDualSection (earlier : Earlier R geometry)
    {p : Higher.SourcePath (alpha R)} {v : Vertex R}
    (hv : Z R v ≤ hatV R (p.walk.getVert 6) (p.walk.getVert 8))
    (s : OrbitModule source p v) :
    letI := s.normal
    Function.Injective s.action → HasSmallInvolution s.action →
    commutatorAction s.action.range (OrbitSpace p v) = ⊤ →
    DisplacementSeparation s.action common.natural.marking →
    Nonempty (MarkedDualSection source common (orbitFactor p v)
      (hatV R (alpha R) (p.walk.getVert 6))) := by
  let := s.normal
  let := s.finite
  let := s.elementary
  dsimp only
  intro hfaith hsmall hfull hsep
  obtain ⟨f, hf⟩ := dual_coordinates_of_dynamics s.action common.natural.marking
    hfaith hsmall hfull hsep
  let π := QuotientGroup.mk' ((hatV R (alpha R) (p.walk.getVert 6)).subgroupOf (orbitFactor p v))
  let q := f.toMonoidHom.comp π
  have hlocal : orbitFactor p v ≤ stabilizer R (alpha R) :=
    (orbitFactor_le_Q earlier p hv).trans (fun _ hx => hx.1)
  have hn : Mbar R ≤ normalizer (orbitFactor p v) := by
    simpa only [alpha, stabilizer_m_base] using orbitFactor_normalized p v
  have hk : q.ker = (hatV R (alpha R) (p.walk.getVert 6)).subgroupOf (orbitFactor p v) := by
    ext x
    change f (π x) = 1 ↔ _
    rw [map_eq_one_iff f f.injective]
    exact QuotientGroup.eq_one_iff x
  refine ⟨⟨hlocal, denominator_le p v, hn, q,
    f.surjective.comp (QuotientGroup.mk'_surjective _), hk, ?_⟩⟩
  intro m x y hy
  change (f (π y)).toAdd = _
  have hh : s.action (source.projection m) (π x) = π y := s.conjugation m x y hy
  exact (congrArg (fun z => (f z).toAdd) hh.symm).trans
    (hf (source.projection m) (π x))

/-- Conditional second-layer application. The two orbit modules are
constructed from the literal earlier commutator and orbit abelianness.
The independent source tasks must supply dynamics and displacement comparison
for every such constructed action. Selection and gluing are already available. -/
theorem markedPair_of_source_dynamics (earlier : Earlier R geometry)
    {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p)
    (hab : ∀ v, v = p.walk.getVert 8 ∨ v = δ.vertex →
      IsMulCommutative (NormalizerTransfer.conjugatesIn (Z R v) (stabilizer R (alpha R))))
    (hcomm : ⁅hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8), Q R (alpha R)⁆ ≤
      Z R (alpha R))
    (hdynamics : ∀ v, v = p.walk.getVert 8 ∨ v = δ.vertex →
      ∀ s : OrbitModule source p v, letI := s.normal
        Function.Injective s.action ∧ HasSmallInvolution s.action ∧
        commutatorAction s.action.range (OrbitSpace p v) = ⊤ ∧
        DisplacementSeparation s.action common.natural.marking)
    (horbit : NormalizerTransfer.conjugatesIn (Z R (p.walk.getVert 8))
      (stabilizer R (alpha R)) ≤ Q R (p.walk.getVert 8))
    (hprod : (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) : Set (FreeAmalgam R)) *
      (Q R (p.walk.getVert 8) : Set (FreeAmalgam R)) =
        (Q R (p.walk.getVert 7) : Set (FreeAmalgam R))) :
    Nonempty (MarkedPairSection source common
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))
      (hatV R (alpha R) (p.walk.getVert 6)) true) := by
  have hc : color R (p.walk.getVert 8) = false :=
    (PathCentrality.RegularPaths.walk_vertex_color p.start_color p.walk
      (by rw [p.length_eq]; decide)).mpr (by decide)
  obtain ⟨s⟩ := orbitModule source earlier p (first_seed_le p) hc
    (hab _ (Or.inl rfl)) hcomm
  obtain ⟨t⟩ := orbitModule source earlier p (delta_seed_le δ) (delta_color δ)
    (hab _ (Or.inr rfl)) hcomm
  obtain ⟨hf, hs, hm, ho⟩ := hdynamics _ (Or.inl rfl) s
  obtain ⟨first⟩ := s.markedDualSection earlier (first_seed_le p) hf hs hm ho
  obtain ⟨hf', hs', hm', ho'⟩ := hdynamics _ (Or.inr rfl) t
  obtain ⟨second⟩ := t.markedDualSection earlier (delta_seed_le δ) hf' hs' hm' ho'
  exact pair_of_generating_sections first second δ.factors_generate
    (δ.second_factor_not_le_first earlier horbit hprod)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition

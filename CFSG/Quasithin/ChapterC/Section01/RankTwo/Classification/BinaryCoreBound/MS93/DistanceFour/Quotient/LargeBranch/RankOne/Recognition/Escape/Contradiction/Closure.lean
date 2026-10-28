module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Sections

/-!
# Propagating the contained edge star modulo the recognized orbit span

The first parabolic and second ordered residual generate M: the two
ordered residuals generate L, the first intrinsic core is R, and M = LR.
If the edge-star image E lies in the second star A, the supplied bound on
[A, Ltilde_delta2] makes E + V0 invariant under the second residual. It
is also invariant under the first parabolic. Actual conjugate generation
then puts the full star in the preimage of E + V0. This gives the exact
second/full-star identities modulo V0, without a starred generation premise.

The literal preimage and kernel restore the ambient containment in Q_c.
The remaining B_alpha factor centralizes Z_c and hence also lies in Q_c.
The sole extra local input is E <= A; Geometry supplies it conditionally
on fixation of Y by the full first actor. No formula using the two base
cores to generate M is used.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.6.12)(4), printed p.911, with the conventions of p.905.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Escape
open Sections
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

omit [Finite M] in
private theorem residual_le (f : Seed.Frame source) (i : Bool) :
    f.residual i ≤ f.parabolic i := by
  exact (map_le_range _ _).trans_eq (f.parabolic i).range_subtype

private theorem generating_actors (s : CriticalSegment geometry) (f : Seed.Frame source)
    (hf : Seed.Compatible f s) : f.parabolic false ⊔ f.residual true = ⊤ := by
  have hcore : f.core false = R := by
    apply Subgroup.map_injective (embedM_injective R)
    exact hf.first_core.trans (Q_beta R)
  have hR : R ≤ f.parabolic false := by
    exact hcore.ge.trans (map_subtype_le _)
  have hL : L ≤ f.parabolic false ⊔ f.residual true := by
    exact f.residual_sup.ge.trans (sup_le_sup (residual_le f false) le_rfl)
  apply top_unique
  intro m _
  obtain ⟨l, hl, r, hr, rfl⟩ := source.product m
  exact (f.parabolic false ⊔ f.residual true).mul_mem (hL hl) ((show f.parabolic false ≤ f.parabolic false ⊔ f.residual true from le_sup_left) (hR hr))

omit [Finite M] in
private theorem radius_normalized (m : M) :
    embedM R m ∈ normalizer (V R (alpha R)) := by
  apply DistanceEight.V_normalized R (alpha R)
  rw [alpha, stabilizer_m_base]
  exact ⟨m, rfl⟩

omit [Finite M] in
private theorem preimage_mono (d : LayerModule source (V R (alpha R)))
    {A B : Submodule (ZMod 2) d.Space} (h : A ≤ B) : d.preimage A ≤ d.preimage B := by
  intro x hx
  obtain ⟨hxV, hxA⟩ := (d.mem_preimage_iff A x).mp hx
  exact (d.mem_preimage_iff B x).mpr ⟨hxV, h hxA⟩

/-- The genuine two-residual generation propagates the edge star modulo the
recognized orbit span. The edge-star inclusion remains explicit. -/
theorem star_le_preimage_edge_sup_span
    (s : CriticalSegment geometry) (d : LayerModule source (V R (alpha R)))
    (f : Seed.Frame source) (hf : Seed.Compatible f s)
    (hedge : d.subspace (edgeStar R geometry (alpha R) (beta R)) ≤
      Seed.secondTildeStar (geometry := geometry) d f 1)
    (hmoved : Seed.movedSpace d.representation ((f.residual true).map source.projection)
      (Seed.secondTildeStar (geometry := geometry) d f 1) ≤ d.subspace (orbitSpan s.middle)) :
    VStar R geometry (alpha R) (beta R) ≤
      d.preimage (d.subspace (edgeStar R geometry (alpha R) (beta R)) ⊔
        d.subspace (orbitSpan s.middle)) := by
  let E := d.subspace (edgeStar R geometry (alpha R) (beta R))
  let T := d.subspace (orbitSpan s.middle)
  let H := d.preimage (E ⊔ T)
  have hT (m : M) (v : d.Space) (hv : v ∈ T) :
      d.representation (source.projection m) v ∈ T :=
    d.subspace_invariant (orbitSpan s.middle) (DistanceEight.V_normalized R _)
      (orbitSpan_normalized s.middle) _ v hv
  have hfirst : (f.parabolic false).map (embedM R) ≤ normalizer H := by
    apply d.preimage_normalized
    · rintro _ ⟨m, _, rfl⟩; exact radius_normalized m
    · intro m hm v hv
      obtain ⟨e, he, t, ht, rfl⟩ := Submodule.mem_sup.mp hv
      rw [map_add]
      apply (E ⊔ T).add_mem
      · exact (show E ≤ E ⊔ T from le_sup_left) (d.subspace_invariant_of_mem _ m (radius_normalized m)
          (hf.first_star_normalized (mem_map_of_mem _ hm)) e he)
      · exact (show T ≤ E ⊔ T from le_sup_right) (hT m t ht)
  have hsecond : (f.residual true).map (embedM R) ≤ normalizer H := by
    apply d.preimage_normalized
    · rintro _ ⟨m, _, rfl⟩; exact radius_normalized m
    · intro m hm v hv
      obtain ⟨e, he, t, ht, rfl⟩ := Submodule.mem_sup.mp hv
      rw [map_add]
      apply (E ⊔ T).add_mem
      · have hdiff : d.representation (source.projection m) e - e ∈ T :=
          hmoved (Submodule.subset_span ⟨source.projection m, mem_map_of_mem _ hm,
            e, hedge he, rfl⟩)
        have hh := (E ⊔ T).add_mem ((show T ≤ E ⊔ T from le_sup_right) hdiff) ((show E ≤ E ⊔ T from le_sup_left) he)
        simpa only [sub_add_cancel] using hh
      · exact (show T ≤ E ⊔ T from le_sup_right) (hT m t ht)
  have hn : stabilizer R (alpha R) ≤ normalizer H := by
    rw [alpha, stabilizer_m_base]
    change (embedM R).range ≤ _
    rw [MonoidHom.range_eq_map, ← generating_actors s f hf, Subgroup.map_sup]
    exact sup_le hfirst hsecond
  apply iSup_conjugates_le_of_le_normalizer _ _ _ _ hn
  exact (Seed.LayerModule.le_preimage_subspace d _
    ((Flags.edgeStar_le_star geometry _ _).trans (Flags.star_le_radius geometry _ _))).trans
      (preimage_mono d le_sup_left)

/-- A local inclusion, together with the recognized moved space, suffices for
whole-radius containment. No full-star generation is assumed. -/
theorem radius_le_midpoint_of_edge_le_second
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (s : CriticalSegment geometry) (d : LayerModule source (V R (alpha R)))
    (f : Seed.Frame source) (hf : Seed.Compatible f s)
    (hcontained : d.preimage (Seed.secondTildeStar (geometry := geometry) d f 1) ≤ Q R s.middle)
    (hspan : orbitSpan s.middle ≤ Q R s.middle)
    (hmoved : Seed.movedSpace d.representation ((f.residual true).map source.projection)
      (Seed.secondTildeStar (geometry := geometry) d f 1) ≤ d.subspace (orbitSpan s.middle))
    (hedge : d.subspace (edgeStar R geometry (alpha R) (beta R)) ≤
      Seed.secondTildeStar (geometry := geometry) d f 1) :
    V R (alpha R) ≤ Q R s.middle := by
  have hZK := Sections.Z_le_intersection common s.first_distance
  have hAK : Seed.secondTildeStar (geometry := geometry) d f 1 ≤
      d.subspace (intersection s.middle) := by
    rw [← d.subspace_preimage (Seed.secondTildeStar (geometry := geometry) d f 1)]
    exact d.subspace_mono (le_inf (d.preimage_le _) hcontained)
  have hTK : d.subspace (orbitSpan s.middle) ≤ d.subspace (intersection s.middle) :=
    d.subspace_mono (le_inf (orbitSpan_le_radius _
      ((cosetGraph R).dist_comm.trans s.first_distance).le) hspan)
  have hstar : VStar R geometry (alpha R) (beta R) ≤ Q R s.middle := by
    apply (star_le_preimage_edge_sup_span s d f hf hedge hmoved).trans
    apply (preimage_mono d (sup_le (hedge.trans hAK) hTK)).trans
    rw [Seed.LayerModule.preimage_subspace_eq d _ (show intersection s.middle ≤ V R (alpha R) from inf_le_left)]
    exact sup_le (inf_le_left.trans (hZK.trans inf_le_right)) inf_le_right
  have hB : B R (alpha R) (geometry.Z_normal (alpha R)) ≤ Q R s.middle := by
    have hBV : B R (alpha R) (geometry.Z_normal (alpha R)) ≤ V R (alpha R) := by
      rw [radius.B_eq_center (alpha R) rfl]
      exact map_subtype_le _
    have hCZ : B R (alpha R) (geometry.Z_normal (alpha R)) ≤
        centralizer (Z R s.middle : Set (FreeAmalgam R)) := by
      rw [radius.B_eq_center (alpha R) rfl]
      rintro x ⟨z, hz, rfl⟩ y hy
      exact congrArg Subtype.val ((mem_center_iff.mp hz)
        ⟨y, ((Z_le_orbitSpan s.middle).trans (orbitSpan_le_radius _
          ((cosetGraph R).dist_comm.trans s.first_distance).le)) hy⟩)
    have hK : B R (alpha R) (geometry.Z_normal (alpha R)) ≤ intersection s.middle := by
      change _ ≤ V R (alpha R) ⊓ Q R s.middle
      rw [radius_inf_kernel common rfl s.first_distance]
      exact le_inf hBV hCZ
    exact hK.trans inf_le_right
  rw [Flags.radius_eq_B_sup_star geometry radius.toEarlyFacts common.large_distance
    (alpha R) (beta R) rfl (base_adjacent R)]
  exact sup_le hB hstar

/-- The full starred quotient is generated by the actual edge image and
recognized orbit span once the edge inclusion is established. -/
theorem star_subspace_eq_edge_sup_span
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source) (hf : Seed.Compatible f s)
    (hedge : d.subspace (edgeStar R geometry (alpha R) (beta R)) ≤
      Seed.secondTildeStar (geometry := geometry) d f 1)
    (hmoved : Seed.movedSpace d.representation ((f.residual true).map source.projection)
      (Seed.secondTildeStar (geometry := geometry) d f 1) ≤ d.subspace (orbitSpan s.middle)) :
    d.subspace (VStar R geometry (alpha R) (beta R)) =
      d.subspace (edgeStar R geometry (alpha R) (beta R)) ⊔ d.subspace (orbitSpan s.middle) := by
  apply le_antisymm
  · have hh := d.subspace_mono (star_le_preimage_edge_sup_span s d f hf hedge hmoved)
    rwa [d.subspace_preimage] at hh
  · exact sup_le (d.subspace_mono (Flags.edgeStar_le_star geometry _ _))
      (d.subspace_mono (orbitSpan_le_star geometry radius.toEarlyFacts _ _ (base_adjacent R)
        (midpoint_nu common radius hb s)))

/-- The second and full stars agree after adding the same recognized span. -/
theorem second_sup_span_eq_star_subspace
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source) (hf : Seed.Compatible f s)
    (hedge : d.subspace (edgeStar R geometry (alpha R) (beta R)) ≤
      Seed.secondTildeStar (geometry := geometry) d f 1)
    (hmoved : Seed.movedSpace d.representation ((f.residual true).map source.projection)
      (Seed.secondTildeStar (geometry := geometry) d f 1) ≤ d.subspace (orbitSpan s.middle)) :
    Seed.secondTildeStar (geometry := geometry) d f 1 ⊔ d.subspace (orbitSpan s.middle) =
      d.subspace (VStar R geometry (alpha R) (beta R)) := by
  have hgen := star_subspace_eq_edge_sup_span common radius hb s d f hf hedge hmoved
  apply le_antisymm
  · exact sup_le (Seed.secondTildeStar_le_star d f 1)
      (hgen.ge.trans' le_sup_right)
  · exact hgen.le.trans (sup_le_sup hedge le_rfl)
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Escape

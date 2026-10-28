module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Setup
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Sections
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Local.Geometry.Parabolics
public import Theory.Representation.BinaryOffender.CentralSectionAction

/-!
# The unstarred layer in the literal Y-span

The abelian incident layer V_beta lies in K = V_alpha intersect Q_c.
Its first ordered residual acts trivially modulo Z_alpha. A vector also
fixed by the second intrinsic core is consequently fixed by the first
full actor, since those two projected subgroups generate it. This places
the incident fixed layer in the actual Y. Transport by the second
parabolic gives the entire unstarred second layer inside the Y-span,
and the supplied starred escape then forces that span to escape Q_c.

The unstarred second layer itself is fixed by its second core. Separately,
normality of that core propagates fixation of Y to its conjugate span.
The source's full-first-actor fixation of Y supplies the two fixation
fields needed in Estimates; that initial fixation remains a premise here.
No endpoint bound, radius bound, or intersection-case estimate is asserted.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), notation on p.905 and (4.6.12)(5), printed p.911. The first
unstarred-image bound is at least q, which is two in this binary setting.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem radius_normalized (m : M) :
    embedM R m ∈ normalizer (V R (alpha R)) := by
  apply DistanceEight.V_normalized R (alpha R)
  rw [alpha, stabilizer_m_base]
  exact ⟨m, rfl⟩

private theorem secondCore_one (f : Seed.Frame source) :
    Seed.secondCore f 1 = f.core true := by
  have he : (MulAut.conj (1 : M)).toMonoidHom = MonoidHom.id M := by ext m; simp
  simp only [Seed.secondCore, he, map_id]

private theorem Z_le_edgeRadius : Z R (alpha R) ≤ V R (beta R) := by
  rw [Flags.RankOne.V_eq_neighborSpan (alpha R) (beta R) rfl (base_adjacent R)]
  exact le_iSup_of_le (alpha R)
    (le_iSup_of_le (adjacent_symm R (base_adjacent R)) le_rfl)

private theorem subspace_le_fixed_of_commutator
    (d : LayerModule source (V R (alpha R))) (T : Subgroup (FreeAmalgam R))
    (H : Subgroup M) (hc : ⁅T, H.map (embedM R)⁆ ≤ Z R (alpha R)) :
    d.subspace T ≤ fixedSpace d.representation (H.map source.projection) := by
  rw [commutator_comm] at hc
  intro v hv g
  obtain ⟨x, hx, rfl⟩ := (d.mem_subspace_iff T v).mp hv
  obtain ⟨m, hm, he⟩ := g.property
  change d.representation (g : SL) (d.projection x).toAdd = (d.projection x).toAdd
  rw [← he]
  exact (d.fixed_iff_commutator_mem m (radius_normalized m) x).mpr
    (hc (commutator_mem_commutator (mem_map_of_mem _ hm) hx))

private theorem fixed_by_join {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) SL W) (H K : Subgroup SL) (v : W)
    (hH : v ∈ fixedSpace ρ H) (hK : v ∈ fixedSpace ρ K) :
    v ∈ fixedSpace ρ (H ⊔ K) := by
  let F : Subgroup SL := {
    carrier := {a | ρ a v = v}
    one_mem' := by simp
    mul_mem' := by
      intro a b ha hb
      change ρ (a * b) v = v
      change ρ a v = v at ha
      change ρ b v = v at hb
      rw [map_mul, Module.End.mul_apply, hb, ha]
    inv_mem' := by
      intro a ha
      change ρ a⁻¹ v = v
      change ρ a v = v at ha
      simpa only [ρ.inv_self_apply] using (congrArg (ρ a⁻¹) ha).symm }
  have h : H ⊔ K ≤ F := sup_le (fun a ha => hH ⟨a, ha⟩) (fun a ha => hK ⟨a, ha⟩)
  exact fun g => h g.property

/-- The second-core fixed part of the incident unstarred layer lies in Y.
The ordered first residual and the second core generate the full first actor;
the first core therefore fixes this part. The abelian edge layer lies in K. -/
theorem incident_fixed_le_Y [Finite M]
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (hf : Seed.Compatible f s) :
    commutatorPreimage (V R (beta R)) ((f.core true).map (embedM R))
      (Z R (alpha R)) ≤ Sections.fixedPreimage s.middle := by
  let T := commutatorPreimage (V R (beta R)) ((f.core true).map (embedM R))
    (Z R (alpha R))
  have hTb : T ≤ V R (beta R) := commutatorPreimage_le _ _ _
  have hbV := Flags.RankOne.edgeRadius_le_radius (alpha R) (beta R) rfl (base_adjacent R)
  have hTV := hTb.trans hbV
  have hbZ : V R (beta R) ≤ normalizer (Z R (alpha R)) :=
    hbV.trans ((geometry.V_local (alpha R) rfl common.large_distance).trans (Z_normalized R _))
  obtain ⟨k⟩ := Sections.exists_frame common radius hb
  have hfirst := Flags.RankOne.flag_commutator_le_Z_of_Bzero source geometry
    common.large_distance radius.toEarlyFacts k.orientation k.edge_kernel k.triple
    (Sections.Bzero_eq_B common radius)
  rw [← f.first_residual_eq_flag s hf k.orientation k.edge_kernel] at hfirst
  have hres := subspace_le_fixed_of_commutator d T (f.residual false)
    ((commutator_mono hTb le_rfl).trans hfirst)
  have hsecond := subspace_le_fixed_of_commutator d T (f.core true)
    (commutator_commutatorPreimage_le _ _ _ hbZ)
  have hfull : d.subspace T ≤ fixedSpace d.representation
      ((f.actor false).map source.projection) := by
    rw [Seed.actor_image_generation]
    exact fun v hv => fixed_by_join d.representation _ _ v (hres hv) (hsecond hv)
  have hcore : d.subspace T ≤ fixedSpace d.representation
      ((f.core false).map source.projection) := by
    intro v hv g
    apply hfull hv ⟨g, ?_⟩
    apply map_mono (show f.core false ≤ f.actor false from ?_) g.property
    rw [f.actor_eq]
    exact map_subtype_le _
  have hcomm : ⁅T, Q R (beta R)⁆ ≤ Z R (alpha R) := by
    rw [← hf.first_core]
    apply (commutator_mono
      ((d.subspace_le_iff_le_preimage T hTV (d.subspace T)).mp le_rfl) le_rfl).trans
    exact d.preimage_commutator_le_Z _ _ (by
      rintro _ ⟨m, _, rfl⟩; exact radius_normalized m) hcore
  apply le_commutatorPreimage _ hcomm
  change T ≤ V R (alpha R) ⊓ Q R s.middle
  rw [radius_inf_kernel common rfl s.first_distance]
  refine le_inf hTV ?_
  have hZc : Z R s.middle ≤ V R (beta R) := by
    rw [Flags.RankOne.V_eq_neighborSpan (alpha R) (beta R) rfl (base_adjacent R)]
    exact le_iSup_of_le s.middle (le_iSup_of_le hbc le_rfl)
  exact hTb.trans ((le_centralizer_iff_isMulCommutative.mpr
    (Flags.RankOne.edgeRadius_abelian geometry common.large_distance
      (alpha R) (beta R) rfl (base_adjacent R))).trans (Subgroup.centralizer_le hZc))

/-- The unstarred second layer is fixed by the actual second intrinsic core. -/
theorem secondLayer_commutator_le_Z (d : LayerModule source (V R (alpha R)))
    (f : Seed.Frame source) :
    ⁅d.preimage (secondLayer d f 1), (f.core true).map (embedM R)⁆ ≤ Z R (alpha R) := by
  apply d.preimage_commutator_le_Z
  · rintro _ ⟨m, _, rfl⟩
    exact radius_normalized m
  · unfold secondLayer
    rw [secondCore_one]
    exact iSup_le fun _ => inf_le_right

private theorem base_fixed_preimage_le (d : LayerModule source (V R (alpha R)))
    (f : Seed.Frame source) :
    d.preimage (d.subspace (V R (beta R)) ⊓
      fixedSpace d.representation ((f.core true).map source.projection)) ≤
      commutatorPreimage (V R (beta R)) ((f.core true).map (embedM R)) (Z R (alpha R)) := by
  apply le_commutatorPreimage
  · intro x hx
    obtain ⟨hxV, hxA⟩ := (d.mem_preimage_iff _ x).mp hx
    exact (d.projection_mem_subspace_iff _ Z_le_edgeRadius ⟨x, hxV⟩).mp hxA.1
  · apply d.preimage_commutator_le_Z
    · rintro _ ⟨m, _, rfl⟩
      exact radius_normalized m
    · exact inf_le_right

/-- Containment of the single incident fixed layer in Y transports to all
second-parabolic conjugates, with the supplied quotient and its exact kernel. -/
private theorem secondLayer_le_ySpan_of_incident_fixed_le [Finite M]
    (common : CommonFacts R source geometry) (s : CriticalSegment geometry)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (hlocal : commutatorPreimage (V R (beta R)) ((f.core true).map (embedM R))
      (Z R (alpha R)) ≤ Sections.fixedPreimage s.middle) :
    d.preimage (secondLayer d f 1) ≤ ySpan f s.middle := by
  have hY : Sections.fixedPreimage s.middle ≤ ySpan f s.middle := le_conjugateSpanBy _ _
  have hZ : Z R (alpha R) ≤ ySpan f s.middle :=
    (Sections.Z_le_fixedPreimage common s.first_distance).trans hY
  have hnorm : (f.parabolic true).map source.projection ≤
      normalizer ((f.core true).map source.projection) :=
    (map_mono (f.core_normalized true)).trans (le_normalizer_map _)
  have hbase : d.subspace (V R (beta R)) ⊓
      fixedSpace d.representation ((f.core true).map source.projection) ≤
      d.subspace (Sections.fixedPreimage s.middle) := by
    rw [← d.subspace_preimage (d.subspace (V R (beta R)) ⊓
      fixedSpace d.representation ((f.core true).map source.projection))]
    exact d.subspace_mono ((base_fixed_preimage_le d f).trans hlocal)
  have hspan : secondLayer d f 1 ≤ d.subspace (ySpan f s.middle) := by
    apply iSup_le
    intro p v hv
    simp only [one_mul, secondCore_one, Submodule.mem_inf] at hv
    obtain ⟨x, hx, rfl⟩ := (d.mem_subspace_iff _ v).mp hv.1
    obtain ⟨t, ht, he⟩ := hx
    let t' : V R (alpha R) := ⟨t,
      Flags.RankOne.edgeRadius_le_radius (alpha R) (beta R) rfl (base_adjacent R) ht⟩
    have hact : (d.projection x).toAdd =
        d.representation (source.projection p) (d.projection t').toAdd :=
      d.action p t' x he.symm
    have htfix : (d.projection t').toAdd ∈
        fixedSpace d.representation ((f.core true).map source.projection) := by
      apply (fixedSpace_stable_of_normalizes d.representation hnorm
        (mem_map_of_mem _ p.property) _).mp
      rw [← hact]
      exact hv.2
    have htY := hbase ⟨(d.mem_subspace_iff _ _).mpr ⟨t', ht, rfl⟩, htfix⟩
    rw [hact]
    exact d.subspace_invariant_of_mem (ySpan f s.middle) p
      (radius_normalized (R := R) (p : M))
      (ySpan_normalized f s.middle (mem_map_of_mem _ (by
        simpa only [f.actor_eq] using p.property)))
      _ (d.subspace_mono hY htY)
  intro x hx
  obtain ⟨hxV, hxA⟩ := (d.mem_preimage_iff _ x).mp hx
  exact (d.projection_mem_subspace_iff _ hZ ⟨x, hxV⟩).mp (hspan hxA)

/-- The actual unstarred second layer is contained in the source's full-actor
span of Y, without any dimension or endpoint-index assumption. -/
theorem secondLayer_le_ySpan [Finite M]
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (hf : Seed.Compatible f s) :
    d.preimage (secondLayer d f 1) ≤ ySpan f s.middle :=
  secondLayer_le_ySpan_of_incident_fixed_le common s d f
    (incident_fixed_le_Y common radius hb s hbc d f hf)

/-- The explicit starred escape forces the literal Y-span to escape Q_c. -/
theorem ySpan_escape [Finite M]
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (hf : Seed.Compatible f s)
    (hescape : ¬ d.preimage (Seed.secondTildeStar (geometry := geometry) d f 1) ≤ Q R s.middle) :
    ¬ ySpan f s.middle ≤ Q R s.middle := by
  intro h
  exact secondLayer_escape d f s.middle hescape
    ((secondLayer_le_ySpan common radius hb s hbc d f hf).trans h)

/-- Normality of the second intrinsic core propagates fixation of Y modulo
Z_alpha to its full-second-actor conjugate span. -/
theorem ySpan_commutator_le_Z_of_Y_fixed [Finite M]
    (common : CommonFacts R source geometry) (f : Seed.Frame source) (c : Vertex R)
    (hY : ⁅Sections.fixedPreimage c, (f.core true).map (embedM R)⁆ ≤ Z R (alpha R)) :
    ⁅ySpan f c, (f.core true).map (embedM R)⁆ ≤ Z R (alpha R) := by
  have hVZ : V R (alpha R) ≤ normalizer (Z R (alpha R)) :=
    (geometry.V_local (alpha R) rfl common.large_distance).trans (Z_normalized R _)
  have hU : ySpan f c ≤ commutatorPreimage (V R (alpha R))
      ((f.core true).map (embedM R)) (Z R (alpha R)) := by
    apply conjugateSpanBy_le
      (le_commutatorPreimage ((commutatorPreimage_le _ _ _).trans inf_le_left) hY)
    apply commutatorPreimage_normalized _ _ _ _ hVZ
    · rintro _ ⟨m, _, rfl⟩
      exact radius_normalized m
    · rw [f.actor_eq]
      exact (map_mono (f.core_normalized true)).trans (le_normalizer_map _)
    · exact (map_le_range (embedM R) _).trans (by
        change Mbar R ≤ _
        simpa only [alpha, stabilizer_m_base] using Z_normalized R (alpha R))
  exact (commutator_mono hU le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ hVZ)

/-- The full first-actor fixation asserted on p.911 supplies both the
ordered-residual fixation and the second-core fixation of the actual Y-span.
The generation identity is used after the original projection, where it holds. -/
theorem first_actor_fixed_consequences [Finite M]
    (common : CommonFacts R source geometry)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source) (c : Vertex R)
    (hY : ⁅Sections.fixedPreimage c, (f.actor false).map (embedM R)⁆ ≤ Z R (alpha R)) :
    ⁅Sections.fixedPreimage c, (f.residual false).map (embedM R)⁆ ≤ Z R (alpha R) ∧
      ⁅ySpan f c, (f.core true).map (embedM R)⁆ ≤ Z R (alpha R) := by
  have hYV : Sections.fixedPreimage c ≤ V R (alpha R) :=
    (commutatorPreimage_le _ _ _).trans inf_le_left
  have hfull := subspace_le_fixed_of_commutator d _ (f.actor false) hY
  have hfix (H : Subgroup M)
      (hH : H.map source.projection ≤ (f.actor false).map source.projection) :
      ⁅Sections.fixedPreimage c, H.map (embedM R)⁆ ≤ Z R (alpha R) := by
    apply (commutator_mono
      ((d.subspace_le_iff_le_preimage _ hYV _).mp le_rfl) le_rfl).trans
    apply d.preimage_commutator_le_Z
    · rintro _ ⟨m, _, rfl⟩
      exact radius_normalized m
    · exact fun v hv g => hfull hv ⟨g, hH g.property⟩
  constructor
  · apply hfix
    rw [Seed.actor_image_generation]
    exact le_sup_left
  · apply ySpan_commutator_le_Z_of_Y_fixed common
    apply hfix
    rw [Seed.actor_image_generation]
    exact le_sup_right

/-- The printed lower bound is at least q (=2), without an equality claim. -/
theorem secondLayer_image_index_ge_two [Finite M]
    (common : CommonFacts R source geometry)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source) (c : Vertex R)
    (hescape : ¬ d.preimage (Seed.secondTildeStar (geometry := geometry) d f 1) ≤ Q R c) :
    2 ≤ (Q R c).relIndex (d.preimage (secondLayer d f 1)) := by
  let : Finite (V R (alpha R)) := Early.finite_radius common (alpha R) rfl
  let : Finite (d.preimage (secondLayer d f 1)) :=
    Finite.of_injective (inclusion (d.preimage_le _)) (inclusion_injective _)
  have hpos : (Q R c).relIndex (d.preimage (secondLayer d f 1)) ≠ 0 :=
    index_ne_zero_of_finite
  have hne : (Q R c).relIndex (d.preimage (secondLayer d f 1)) ≠ 1 := by
    intro h
    exact secondLayer_escape d f c hescape (relIndex_eq_one.mp h)
  omega

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension

module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.InitialSelection
/-!
# Whole-midpoint-radius fixed indices in the small-image selection branch

Suppose every critical image from the original base has order two. The
previous initial-selection reduction places each nearby whole-radius image
in a conjugate of the three-disjoint-transposition group. That group fixes
a subspace of codimension two on either moving cover. Monotonicity and the
literal symmetric projection therefore bound the midpoint radius's fixed
index on the starting moving cover by four.

The full starting seed is the moving cover joined with the incident central
seed. The midpoint radius lies in that incident edge kernel, so it fixes
the entire additional seed. The same index-four bound consequently holds
on the full starting seed. The endpoint seed lies in the midpoint radius;
hence its full critical kernel contains the radius-fixed subgroup. The
critical index is two, and the index product formula bounds the radius's
fixed index on this kernel by two. Conjugating the complete path transports
both bounds to every component vertex, including reverse orientations.

The final application supplies these whole-radius bounds in the still-open
small-image alternative to a nonabelian large-slice selection on the actual
minimum characteristic replacement. Both cover orders, all central
attachments and every radical image are retained. A fixed-index bound on
the kernel does not by itself bound its whole commutator by order two.
The remaining source (5.8) selection, the separately owned selected terminal
argument and unconditional DistanceFourInput assembly are not proved here.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the small-critical-image selection in (5.8), printed pp.919--920,
and its use at the start of (5.12), p.924. The fixed-space calculation uses
the existing natural and augmentation six-letter models and their full
central-cover transport.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)
open Representation Representation.BinaryOffender BinaryPermutation

private theorem cover_fixed_index_le_four_of_cube
    (A : Subgroup d.overgroup) (u : Equiv.Perm (Fin 6))
    (hA : A.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom) :
    (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) ≤ 4 := by
  let := replacementMoved_normal h d
  let T := (D 6).map (MulAut.conj u).toMonoidHom
  have hcodim : fixedCodim (coverAction s) T = 2 := by
    rcases cover_model s with ⟨E,hE⟩ | ⟨E,hE⟩
    · rw [fixedCodim_map_equivariant (coverAction s) (naturalRepresentation (Fin 6))
        (MonoidHom.id _) E hE T, map_id, fixedCodim_map_conj]
      exact fixedCodim_D.2.2.2
    · rw [fixedCodim_map_equivariant (coverAction s) (coreRepresentation (Fin 6))
        (MonoidHom.id _) E hE T, map_id, fixedCodim_map_conj]
      exact fixedCodim_D.2.2.1
  have hfix : fixedSpace (coverAction s) T ≤ fixedSpace (coverAction s) (A.map s.projection) := by
    intro v hv a
    exact hv ⟨a,hA a.property⟩
  have hca := fixedCodim_add_finrank (coverAction s) (A.map s.projection)
  have hct := fixedCodim_add_finrank (coverAction s) T
  have hfin := Submodule.finrank_mono hfix
  have hbound : fixedCodim (coverAction s) (A.map s.projection) ≤ 2 := by omega
  let := replacementMoved_normal h d
  rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim
    (replacementMoved d) s.projection s.surjective
    (s.projection_kernel.trans (moved_centralizer s).symm)]
  exact Nat.pow_le_pow_right (by decide) hbound


include s in
/-- The whole midpoint radius fixes a subgroup of index at most four in
the full starting seed, including the incident central attachment. -/
theorem small_images_midpoint_seed_fixed_index
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    (hsmall : ∀ z, ∀ _p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z,
      (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    (centralizer (V d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical))).relIndex
      (Z d.radical (alpha d.radical)) ≤ 4 := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let W := V d.radical c
  have hcCol : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hca : (cosetGraph d.radical).dist c (alpha d.radical) = 2 := by
    rw [SimpleGraph.dist_comm,p.dist_start (by omega)]
  have hat : Adjacent d.radical (alpha d.radical) t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical c t := by
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have htCol : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases he : color d.radical t <;> simp_all
  have hWt : W ≤ Q d.radical t := by
    apply V_le_Q_of_dist_add_two_lt d.radical hcCol
    have hdist : (cosetGraph d.radical).dist c t = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    change (cosetGraph d.radical).dist c t + 2 < replacementDistance h d
    omega
  have hWbase : W ≤ stabilizer d.radical (alpha d.radical) :=
    fun _ hx => (hWt hx).2 _ (adjacent_symm d.radical hat)
  let A := W.comap (embedM d.radical)
  have hmA : A.map (embedM d.radical) = W :=
    map_comap_eq_self (hWbase.trans_eq (stabilizer_m_base d.radical))
  obtain ⟨u,hu⟩ := radius_image_le_cube_of_small_critical_images s hc hb hsmall c hcCol hca.le
  have hbound := cover_fixed_index_le_four_of_cube s A u hu
  have hU : (centralizer (W : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical (alpha d.radical)) ≤ 4 := by
    rw [hc.U_eq_moved,←hmA,←inf_relIndex_right,inf_comm,
      map_inf_centralizer_of_injective _ (embedM_injective d.radical),
      relIndex_map_map_of_injective _ _ (embedM_injective d.radical),inf_relIndex_left]
    exact hbound
  let K := Z d.radical (alpha d.radical) ⊓ centralizer (W : Set (FreeAmalgam d.radical))
  have hFK : Z d.radical t ≤ K := by
    apply le_inf (adjacent_Z_le d.radical rfl hat)
    intro z hz w hw
    rw [Z,if_neg (by simp [htCol])] at hz
    exact (mem_omegaCenter_iff.mp hz).2.2 w (hWt hw)
  have hdecomp : U d.radical (alpha d.radical) ⊔ K = Z d.radical (alpha d.radical) := by
    apply le_antisymm (sup_le (DistanceEight.U_le_Z d.radical _) inf_le_left)
    calc
      Z d.radical (alpha d.radical) = U d.radical (alpha d.radical) ⊔ Z d.radical t :=
        DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d rfl hat
      _ ≤ U d.radical (alpha d.radical) ⊔ K := sup_le_sup_left hFK _
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) (alpha d.radical) rfl
  have hn : K ≤ normalizer (U d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) :=
    ((inf_le_left.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)).trans
      (centralizer_le (DistanceEight.U_le_Z d.radical _))).trans (Subgroup.centralizer_le_normalizer _)
  let := finite_Z d.radical (alpha d.radical)
  let : Finite K := Finite.of_injective (inclusion (show K ≤ Z d.radical (alpha d.radical) from inf_le_left))
    (inclusion_injective _)
  have hi := relIndex_sup_of_normalizes (U d.radical (alpha d.radical)) K hn
  rw [hdecomp] at hi
  have he : K ⊓ U d.radical (alpha d.radical) =
      centralizer (W : Set (FreeAmalgam d.radical)) ⊓ U d.radical (alpha d.radical) := by
    dsimp only [K]
    rw [inf_right_comm,inf_eq_right.mpr (DistanceEight.U_le_Z d.radical _)]
    exact inf_comm _ _
  have hKU : K.relIndex (U d.radical (alpha d.radical)) =
      (centralizer (W : Set (FreeAmalgam d.radical))).relIndex (U d.radical (alpha d.radical)) := by
    rw [←inf_relIndex_right K,he,inf_relIndex_right]
  have hout : K.relIndex (Z d.radical (alpha d.radical)) ≤ 4 := by
    rw [hi,hKU]
    exact hU
  simpa only [K,inf_relIndex_left] using hout

private theorem fixed_index_in_index_two {F : Type*} [Group F]
    (Z K C : Subgroup F) [Finite Z]
    (hK : K ≤ Z) (hF : Z ⊓ C ≤ K) (hi : K.relIndex Z = 2)
    (hbound : C.relIndex Z ≤ 4) : C.relIndex K ≤ 2 := by
  have he : Z ⊓ C = K ⊓ C :=
    le_antisymm (le_inf hF inf_le_right) (inf_le_inf_right _ hK)
  have hleft : (Z ⊓ C).relIndex K = C.relIndex K := by
    rw [he,inf_relIndex_left]
  have htotal : (Z ⊓ C).relIndex Z ≤ 4 := by simpa only [inf_relIndex_left] using hbound
  have hprod := relIndex_mul_relIndex (Z ⊓ C) K Z hF hK
  rw [hleft,hi] at hprod
  omega

include s in
/-- The same whole radius fixes an index-at-most-two subgroup of the
full critical kernel; no order bound for its commutator is inferred. -/
theorem small_images_midpoint_critical_kernel_fixed_index
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    (hsmall : ∀ z, ∀ _p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z,
      (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    (centralizer (V d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical))).relIndex
      (Z d.radical (alpha d.radical) ⊓ Q d.radical a') ≤ 2 := by
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hZW : Z d.radical a' ≤ V d.radical (p.walk.getVert 2) := by
    apply le_iSup_of_le a'
    apply le_iSup_of_le (show (cosetGraph d.radical).dist a' (p.walk.getVert 2) ≤ 2 from ?_)
    · exact le_rfl
    · rw [SimpleGraph.dist_comm,p.dist_end,hl]
  have hfixed : Z d.radical (alpha d.radical) ⊓
      centralizer (V d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical)) ≤
      Z d.radical (alpha d.radical) ⊓ Q d.radical a' := by
    apply le_inf inf_le_left
    rw [←C_eq_Q s hc a' p.end_color]
    exact le_inf (inf_le_left.trans (Z_le_stabilizer_of_dist_le (alpha d.radical) _ p.critical.1.le))
      (inf_le_right.trans (centralizer_le hZW))
  let := finite_Z d.radical (alpha d.radical)
  apply fixed_index_in_index_two _ _ _ inf_le_left hfixed
  · rw [inf_relIndex_left]
    exact (small_critical_indices s hc p (hsmall a' p)).1
  · exact small_images_midpoint_seed_fixed_index s hc hb hsmall p

private theorem centralizer_index_map {F H : Type*} [Group F] [Group H]
    (f : F →* H) (hf : Function.Injective f) (P A : Subgroup F) :
    (centralizer (A.map f : Set H)).relIndex (P.map f) = (centralizer (A : Set F)).relIndex P := by
  rw [←inf_relIndex_right,inf_comm,map_inf_centralizer_of_injective f hf,
    relIndex_map_map_of_injective _ _ hf,inf_relIndex_left]

include s in
/-- The full-seed and full-kernel bounds on an arbitrary literal critical
path. Conjugation transports the radius, both kernels and their indices together. -/
theorem small_images_midpoint_fixed_indices_at
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    (hsmall : ∀ z, ∀ _p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z,
      (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z) :
    (centralizer (V d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical))).relIndex
      (Z d.radical a) ≤ 4 ∧
    (centralizer (V d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical))).relIndex
      (Z d.radical a ⊓ Q d.radical z) ≤ 2 := by
  obtain ⟨j,hj⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical j⁻¹ a = alpha d.radical := by
    rw [hj,act_mVertex,mul_inv_cancel]
    rfl
  have base : ∀ q : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical j⁻¹ a) (act d.radical j⁻¹ z),
      (centralizer (V d.radical (q.walk.getVert 2) : Set (FreeAmalgam d.radical))).relIndex
        (Z d.radical (act d.radical j⁻¹ a)) ≤ 4 ∧
      (centralizer (V d.radical (q.walk.getVert 2) : Set (FreeAmalgam d.radical))).relIndex
        (Z d.radical (act d.radical j⁻¹ a) ⊓ Q d.radical (act d.radical j⁻¹ z)) ≤ 2 := by
    rw [hbase]
    intro q
    exact ⟨small_images_midpoint_seed_fixed_index s hc hb hsmall q,
      small_images_midpoint_critical_kernel_fixed_index s hc hb hsmall q⟩
  have hh := base (p.act j⁻¹)
  simp only [CriticalPath.act,actWalk_getVert,V_act,Z_act,Q_act,inv_inv] at hh
  rw [←Subgroup.map_inf _ _ _ (MulAut.conj j).injective] at hh
  simpa only [centralizer_index_map (MulAut.conj j).toMonoidHom (MulAut.conj j).injective] using hh

include e hz hn in
/-- The actual characteristic replacement either supplies the selected
nonabelian large-slice path or satisfies the whole-midpoint-radius fixed-index
bounds at every critical path. The remaining small-image exclusion is explicit. -/
theorem initial_selection_or_small_midpoint_kernels_knownSimple
    (hb : replacementDistance h d = 4) :
    (∃ z, ∃ p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z,
      ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (p.walk.getVert 2))) ∨
    (∀ (a z : Vertex d.radical) (p : CriticalPath d.radical (replacementGeometry h d) a z),
      (centralizer (V d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical))).relIndex
        (Z d.radical a) ≤ 4 ∧
      (centralizer (V d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical))).relIndex
        (Z d.radical a ⊓ Q d.radical z) ≤ 2) := by
  rcases initial_selection_or_cube_radius_knownSimple (e := e) (hz := hz) (hn := hn) hb with hsel | hsmall
  · exact Or.inl hsel
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  exact Or.inr fun a z p => small_images_midpoint_fixed_indices_at s hc hb
    (fun z p => by rw [(hsmall.2.1 z p).1]; decide) p

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

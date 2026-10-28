module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.CoreBounds
public import Theory.GroupTheory.Commutator.SmallNormalizedImage
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.NaturalRadius
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowKernelPair
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowNormalizer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeRadiusPlane
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubePaths
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowAdjacent

/-!
# Natural-cover whole-core movement at distance four

On the sixteen-element moving cover, the midpoint-core movement of a large
critical pair equals its entire critical commutator.

For a small critical pair, suppose the first edge moves its critical line.
Take the orbit of the endpoint seed under that edge. Its image has order at
least four: a smaller normal image would fix the original line. The midpoint
core fixes the orbit's displacement, so natural symplectic duality bounds its
whole movement by that displacement. Distinct conjugate critical kernels
then give the exact decomposition into the critical line and the full
kernel/core commutator. The whole movement is quadratic and has order at
most four.

A controlling actor fixes the critical line and normalizes the full kernel
joined with the midpoint seed. The decomposition makes the whole movement
invariant under that actor. Edge generation, the small-group automorphism
bound, and the small critical pair make it central in the midpoint
stabilizer, contradicting the strict Baumann slice.

The final application retains the original full endpoint restriction,
central attachment, critical commutator, whole-kernel join and relative
normalizer. In the radical-image-sixteen branch the proved relative
normalizer identity supplies edge generation. Its backward image is large,
and its selected-span/core movement equals the same critical commutator
and is fixed by the midpoint residual.

These are the natural-cover, full-radical-image-sixteen branches. The
thirty-two-element cover, other relative normalizers, and the surviving
large-image and large-slice terminal contradictions remain separate cases.
No equality between the two covers or between the natural and exceptional
graphs is used.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.3)(ii), (5.2)(ii), and (5.12)(1)--(2), printed
pp.867,914--915,924--926. Internal imports reuse the existing full-seed
attachment, orbit and coordinate proofs without changing their interfaces.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.GroupTheory Representation.NormalElementaryQuotient
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)


private theorem natural_quadratic_cover_control
    (hnat : Nat.card (replacementMoved d) = 16)
    (A Y : Subgroup d.overgroup)
    (hcard : 4 ≤ Nat.card (A.map s.projection))
    (hAA : ⁅replacementMoved d,A⁆ ≤ centralizer (A : Set d.overgroup))
    (hAY : ⁅replacementMoved d,A⁆ ≤ centralizer (Y : Set d.overgroup)) :
    ⁅replacementMoved d,Y⁆ ≤ ⁅replacementMoved d,A⁆ := by
  let := replacementMoved_normal h d
  let : IsElementaryAbelian 2 (A.map s.projection) :=
    elementary_of_faithful_quadratic (naturalRepresentation (Fin 6))
      (naturalRepresentation_injective (Fin 6) (by decide)) _
      (image_quadratic_of_commutator s A hAA)
  let π := coverMap (h := h) (e := e) (hz := hz) (hn := hn) (d := d)
  have hmap (B : Subgroup d.overgroup) :
      (NormalElementaryQuotient.commutatorSpace (replacementMoved d) B).map π =
        subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ (B.map s.projection) := by
    rw [NormalElementaryQuotient.commutatorSpace_eq (replacementMoved d) s.projection
      s.surjective (s.projection_kernel.trans (moved_centralizer s).symm)]
    have hh := subspaceCommutator_map_embedding (naturalRepresentation (Fin 6))
      (coverAction s) (MonoidHom.id S) π (fun g v => (coverMap_equivariant s g v).symm)
      (B.map s.projection) ⊤
    rw [Submodule.map_top,LinearMap.range_eq_top.mpr (coverMap_surjective
      (h := h) (e := e) (hz := hz) (hn := hn) (d := d)),Subgroup.map_id] at hh
    exact hh.symm
  have hspaces : NormalElementaryQuotient.commutatorSpace (replacementMoved d) Y ≤
      NormalElementaryQuotient.commutatorSpace (replacementMoved d) A := by
    apply (Submodule.map_le_map_iff_of_injective (f := π) (natural_coverMap_injective hnat) _ _).mp
    rw [hmap Y,hmap A]
    exact natural_moved_control _ _ hcard (image_quadratic_of_commutator s A hAA)
      (image_centralizes_moved s A Y hAY)
  intro x hx
  exact hspaces (show Additive.ofMul (⟨x,(commutator_le_left _ _) hx⟩ : replacementMoved d) ∈
    NormalElementaryQuotient.commutatorSpace (replacementMoved d) Y from hx)

include s in
private theorem embedded_natural_quadratic_control
    (hnat : Nat.card (replacementMoved d) = 16)
    {H : Type*} [Group H] (i : d.overgroup →* H) (hi : Function.Injective i)
    (A Y : Subgroup H)
    (hA : A ≤ i.range) (hY : Y ≤ i.range)
    (hcard : 4 ≤ ((pCore 2 d.overgroup).map i).relIndex A)
    (hAA : ⁅(replacementMoved d).map i,A⁆ ≤ centralizer (A : Set H))
    (hAY : ⁅(replacementMoved d).map i,A⁆ ≤ centralizer (Y : Set H)) :
    ⁅(replacementMoved d).map i,Y⁆ ≤ ⁅(replacementMoved d).map i,A⁆ := by
  let A₀ := A.comap i
  let Y₀ := Y.comap i
  have hmA : A₀.map i = A := map_comap_eq_self hA
  have hmY : Y₀.map i = Y := map_comap_eq_self hY
  have hcard₀ : 4 ≤ Nat.card (A₀.map s.projection) := by
    rw [←hmA,relIndex_map_map_of_injective _ _ hi,←s.projection_kernel,relIndex_ker] at hcard
    exact hcard
  have hfix (B : Subgroup H)
      (hc : ⁅(replacementMoved d).map i,A⁆ ≤ centralizer (B : Set H)) :
      ⁅replacementMoved d,A₀⁆ ≤ centralizer (B.comap i : Set d.overgroup) := by
    intro x hx b hb
    apply hi
    simp only [map_mul]
    apply hc
    · rw [←hmA,←map_commutator]
      exact mem_map_of_mem i hx
    · exact hb
  have hh := map_mono (f := i) (natural_quadratic_cover_control s hnat A₀ Y₀ hcard₀
    (hfix A hAA) (hfix Y hAY))
  rwa [map_commutator,map_commutator,hmA,hmY] at hh


include s in
/-- On the sixteen-element cover, the full midpoint-core movement is the
original critical commutator. No radical-image restriction is used. -/
theorem natural_large_midpoint_movement_eq
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    (hnat : Nat.card (replacementMoved d) = 16)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical a)) :
    ⁅Z d.radical a,Q d.radical (p.walk.getVert 2)⁆ = ⁅Z d.radical a,Z d.radical z⁆ := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hcol : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent d.radical a t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical c t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.start_color] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hPc : Q d.radical c ≤ Q d.radical t := Q_le_adjacent_h d.radical ht hct
  have hAz : Z d.radical z ≤ Q d.radical c := by
    apply Z_le_Q_of_dist_lt d.radical z ((replacementGeometry h d).exists_critical z p.end_color)
    rw [(replacementGeometry h d).distance_constant _ p.end_color,SimpleGraph.dist_comm,p.dist_end,hl]
    exact show 2 < replacementDistance h d by omega
  have hm := large_midpoint_movement s hc hb p hlarge
  apply le_antisymm ?_ hm.2.2.2
  rw [seed_commutator_eq_moving (h := h) (e := e) (hz := hz) p.start_color hat _ hPc]
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h := h) hc a p.start_color
  have hTG : Q d.radical t ≤ stabilizer d.radical a :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical hat)
  have hAY : ⁅U d.radical a,Z d.radical z⁆ ≤
      centralizer (Q d.radical c : Set (FreeAmalgam d.radical)) :=
    (commutator_mono (DistanceEight.U_le_Z d.radical a) hAz).trans
      (large_midpoint_core_quadratic s hc hb p hlarge)
  have hAA := hAY.trans (centralizer_le hAz)
  have hcontrol := embedded_natural_quadratic_control s hnat i hi
    (Z d.radical z) (Q d.radical c)
    ((hAz.trans hPc).trans hTG |>.trans_eq hir.symm)
    (hPc.trans hTG |>.trans_eq hir.symm)
    (hiQ.symm ▸ reverse_critical_image_four_le s hc (replacementDistance_pos h d) p hlarge)
    (hiU.symm ▸ hAA) (hiU.symm ▸ hAY)
  rw [hiU] at hcontrol
  exact hcontrol.trans (commutator_mono (DistanceEight.U_le_Z d.radical a) le_rfl)

private theorem quadratic_cover_fixedIndex_four_le (A : Subgroup d.overgroup)
    (hA : 4 ≤ Nat.card (A.map s.projection))
    (hquad : ⁅replacementMoved d,A⁆ ≤ centralizer (A : Set d.overgroup)) :
    4 ≤ (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) := by
  let := replacementMoved_normal h d
  let : IsElementaryAbelian 2 (A.map s.projection) :=
    elementary_of_faithful_quadratic (naturalRepresentation (Fin 6))
      (naturalRepresentation_injective (Fin 6) (by decide)) _
      (image_quadratic_of_commutator s A hquad)
  obtain ⟨a,haA,ha,heven⟩ := even_involution (A.map s.projection) hA
  have hact : coverAction s a ≠ 1 := by
    intro hzero
    have hn : BinaryPermutation.naturalRepresentation (Fin 6) a = 1 := by
      apply LinearMap.ext
      intro v
      obtain ⟨w,rfl⟩ := coverMap_surjective (h := h) (e := e) (hz := hz) (hn := hn) (d := d) v
      have heq := coverMap_equivariant s a w
      rw [hzero,Module.End.one_apply] at heq
      exact heq.symm
    have heq : a = 1 := BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide)
      (hn.trans (map_one _).symm)
    rw [heq,orderOf_one] at ha
    contradiction
  have hl := AlternatingSixInvolutionDisplacement.fixedCodim_lower_of_even_involution_mem
    (coverAction s) ⟨⟨a,heven⟩,hact⟩ a ha heven haA
  rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim
    (replacementMoved d) s.projection s.surjective
    (s.projection_kernel.trans (moved_centralizer s).symm)]
  exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hl


include s in
private theorem natural_small_orbit_movement
    (hc : DistanceTwo.CentralLayer d) (hnat : Nat.card (replacementMoved d) = 16)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (T P : Subgroup (FreeAmalgam d.radical))
    (hTG : T ≤ stabilizer d.radical a) (hTP : IsPGroup 2 T)
    (hTedge : T ≤ Q d.radical (p.walk.getVert 1))
    (hPT : P ≤ T) (hPN : T ≤ normalizer (P : Set (FreeAmalgam d.radical)))
    (hAP : Z d.radical z ≤ P)
    (hfix : P ≤ centralizer ((⁅Z d.radical a,Z d.radical z⁆ :
      Subgroup (FreeAmalgam d.radical)) : Set _))
    (hmove : ¬ T ≤ centralizer ((⁅Z d.radical a,Z d.radical z⁆ :
      Subgroup (FreeAmalgam d.radical)) : Set _)) :
    ⁅Z d.radical a,P⁆ = ⁅Z d.radical a,Z d.radical z⁆ ⊔
      ⁅Z d.radical a ⊓ Q d.radical z,P⁆ ∧
      ⁅Z d.radical a,P⁆ ≤ centralizer (P : Set (FreeAmalgam d.radical)) ∧
      Nat.card (⁅Z d.radical a,P⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 4 := by
  let Z₀ := Z d.radical a
  let A := Z d.radical z
  let K := Z₀ ⊓ Q d.radical z
  let D := ⁅Z₀,A⁆
  let E := componentOrbit A T
  let J := componentOrbit D T
  let := finite_stabilizer d.radical a
  let : Finite T := Finite.of_injective (inclusion hTG) (inclusion_injective _)
  let : Finite P := Finite.of_injective (inclusion hPT) (inclusion_injective _)
  have hTZ : T ≤ normalizer (Z₀ : Set (FreeAmalgam d.radical)) := hTG.trans (Z_normalized d.radical a)
  have hAZ : A ≤ normalizer (Z₀ : Set (FreeAmalgam d.radical)) := (hAP.trans hPT).trans hTZ
  have hEP : E ≤ P := by
    apply iSup_le
    intro x
    exact (map_mono hAP).trans_eq (mem_normalizer_iff_map_conj_eq.mp (hPN x.property))
  have hJG : ⁅Z₀,E⁆ = J := SylowKernelPair.orbit_commutator Z₀ A T hAZ hTZ
  have hJP : J ≤ centralizer (P : Set (FreeAmalgam d.radical)) := by
    apply iSup_le
    intro x
    have hn : T ≤ normalizer (centralizer (P : Set (FreeAmalgam d.radical)) : Set _) :=
      hPN.trans (normalizer_le_normalizer_centralizer P)
    exact (map_mono (le_centralizer_iff.mp hfix)).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (hn x.property))
  have hEA : ⁅U d.radical a,E⁆ ≤ J :=
    (commutator_mono (DistanceEight.U_le_Z d.radical a) le_rfl).trans_eq hJG
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h := h) hc a p.start_color
  have hEbound : E ≤ i.range := (hEP.trans (hPT.trans hTG)).trans_eq hir.symm
  have hEm : (E.comap i).map i = E := map_comap_eq_self hEbound
  have hTm : (T.comap i).map i = T := map_comap_eq_self (hTG.trans_eq hir.symm)
  have hEi : 4 ≤ ((pCore 2 d.overgroup).map i).relIndex E := by
    by_contra! hs
    have hiE : Nat.card ((E.comap i).map s.projection) < 4 := by
      rwa [←hEm,relIndex_map_map_of_injective _ _ hi,←s.projection_kernel,relIndex_ker] at hs
    have hpE : IsPGroup 2 ((E.comap i).map s.projection) :=
      (((hTP.to_le (hEP.trans hPT)).comap_of_injective i hi).map s.projection)
    obtain ⟨n,hn⟩ := hpE.exists_card_eq
    have hiE2 : Nat.card ((E.comap i).map s.projection) ≤ 2 := by
      rw [hn] at hiE ⊢
      have hn2 : n < 2 := (Nat.pow_lt_pow_iff_right (by decide)).mp hiE
      interval_cases n <;> decide
    have hEN : T.comap i ≤ normalizer (E.comap i : Set d.overgroup) :=
      (comap_mono (le_normalizer_componentOrbit A T)).trans (le_normalizer_comap i)
    have hTE : ⁅T,E⁆ ≤ Q d.radical a := by
      have hh := map_mono (f := i)
        (commutator_le_ker_of_normalized_image_card_le_two s.projection _ _ hEN hiE2)
      rwa [map_commutator,hTm,hEm,s.projection_kernel,hiQ] at hh
    have hTA : ⁅T,A⁆ ≤ centralizer (Z₀ : Set (FreeAmalgam d.radical)) :=
      ((commutator_mono le_rfl (le_componentOrbit A T)).trans hTE).trans
        (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
          (Z_centralizes_Q d.radical a p.start_color)))
    have hTD : T ≤ normalizer (D : Set (FreeAmalgam d.radical)) := by
      dsimp only [D]
      rw [commutator_comm]
      exact SylowNormalizer.fixed_mod_central_normalizes A Z₀ T hAZ hTZ hTA
    exact hmove (hTD.trans (normalizer_le_centralizer_of_card_two D
      (small_critical_commutator_card s hc p hsmall)))
  have hHP : ⁅U d.radical a,P⁆ ≤ J := by
    have hh := embedded_natural_quadratic_control s hnat i hi E P hEbound
      ((hPT.trans hTG).trans_eq hir.symm) hEi
      (hiU.symm ▸ ((hEA.trans hJP).trans (centralizer_le hEP)))
      (hiU.symm ▸ (hEA.trans hJP))
    rw [hiU] at hh
    exact hh.trans hEA
  have hwhole : ⁅Z₀,P⁆ ≤ J := by
    have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
    have hat : Adjacent d.radical a (p.walk.getVert 1) := by
      apply (cosetGraph_adj d.radical _ _).mp
      simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
    change ⁅Z d.radical a,P⁆ ≤ J
    rw [seed_commutator_eq_moving (h := h) (e := e) (hz := hz) p.start_color hat P (hPT.trans hTedge)]
    exact hHP
  let := finite_Z d.radical a
  let : Finite K := Finite.of_injective (inclusion (show K ≤ Z₀ from inf_le_left)) (inclusion_injective _)
  have hKF : J ≤ D ⊔ ⁅K,P⁆ := by
    apply iSup_le
    intro x
    let f := (MulAut.conj (x : FreeAmalgam d.radical)).toMonoidHom
    have hZmap : Z₀.map f = Z₀ := mem_normalizer_iff_map_conj_eq.mp (hTZ x.property)
    let : Finite (K.map f) := Finite.of_injective
      (inclusion ((map_mono (show K ≤ Z₀ from inf_le_left)).trans_eq hZmap)) (inclusion_injective _)
    have hDmap : D.map f = ⁅Z₀,A.map f⁆ := by rw [map_commutator,hZmap]
    have hAmP : A.map f ≤ P :=
      (map_mono hAP).trans_eq (mem_normalizer_iff_map_conj_eq.mp (hPN x.property))
    by_cases hxn : (x : FreeAmalgam d.radical) ∈ normalizer (K : Set (FreeAmalgam d.radical))
    · have hcD : (x : FreeAmalgam d.radical) ∈ centralizer (D : Set (FreeAmalgam d.radical)) := by
        have hh := (show (x : FreeAmalgam d.radical) ∈ stabilizer d.radical a ⊓
          normalizer (K : Set (FreeAmalgam d.radical)) from ⟨hTG x.property,hxn⟩)
        rw [small_critical_kernel_normalizer_eq_line_centralizer s hc p hsmall] at hh
        exact hh.2
      exact (mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _ hcD)).le.trans le_sup_left
    · have hKC : K = Z₀ ⊓ centralizer (A : Set (FreeAmalgam d.radical)) := by
        apply le_antisymm
        · exact le_inf inf_le_left (inf_le_right.trans (le_centralizer_iff.mp
            (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical z p.end_color))))
        · apply le_inf inf_le_left
          rw [←C_eq_Q s hc z p.end_color]
          exact le_inf (inf_le_left.trans (Z_le_stabilizer_of_dist_le a _ p.critical.1.le)) inf_le_right
      have hnon : ⁅K,A.map f⁆ ≠ ⊥ := by
        intro hz
        have hKK : K ≤ K.map f := by
          rw [hKC,←map_inf_centralizer_of_injective _ (MulAut.conj _).injective,hZmap]
          exact le_inf inf_le_left (by simpa only [hKC] using (commutator_eq_bot_iff_le_centralizer.mp hz))
        have hsame : K = K.map f := eq_of_le_of_card_ge hKK (by
          rw [card_map_of_injective (MulAut.conj _).injective])
        exact hxn (mem_normalizer_iff_map_conj_eq.mpr hsame.symm)
      have hle : ⁅K,A.map f⁆ ≤ D.map f := hDmap.symm ▸ commutator_mono inf_le_left le_rfl
      let := finite_Z d.radical a
      let : Finite (D.map f) := Finite.of_injective
        (inclusion ((map_mono (show D ≤ Z₀ from
          ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
            (DistanceEight.U_le_Z d.radical a))).trans_eq hZmap)) (inclusion_injective _)
      let : Finite (⁅K,A.map f⁆ : Subgroup (FreeAmalgam d.radical)) :=
        Finite.of_injective (inclusion hle) (inclusion_injective _)
      have he : ⁅K,A.map f⁆ = D.map f := eq_of_le_of_card_ge hle (by
        rw [card_map_of_injective (MulAut.conj _).injective]
        have hpos := (one_lt_card_iff_ne_bot _).mpr hnon
        have hcD := small_critical_commutator_card s hc p hsmall
        change Nat.card D = 2 at hcD
        omega)
      exact he.symm.le.trans ((commutator_mono le_rfl hAmP).trans le_sup_right)
  have hcardH : Nat.card (⁅Z₀,P⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 4 := by
    let H := ⁅Z₀,P⁆
    have hHU : H ≤ U d.radical a := by
      have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
      have hat : Adjacent d.radical a (p.walk.getVert 1) := by
        apply (cosetGraph_adj d.radical _ _).mp
        simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
      change ⁅Z d.radical a,P⁆ ≤ U d.radical a
      rw [seed_commutator_eq_moving (h := h) (e := e) (hz := hz) p.start_color hat P (hPT.trans hTedge)]
      exact le_normalizer_iff_commutator_le_left.mp ((hPT.trans hTG).trans (U_normalized a))
    have hPm : (P.comap i).map i = P := map_comap_eq_self ((hPT.trans hTG).trans_eq hir.symm)
    have hPcard : 4 ≤ Nat.card ((P.comap i).map s.projection) := by
      have hh := hEi.trans (relIndex_le_of_le_right hEP index_ne_zero_of_finite)
      rwa [←hPm,relIndex_map_map_of_injective _ _ hi,←s.projection_kernel,relIndex_ker] at hh
    have hq : ⁅replacementMoved d,P.comap i⁆ ≤ centralizer (P.comap i : Set d.overgroup) := by
      intro x hx y hy
      apply hi
      simp only [map_mul]
      have hxH : i x ∈ H := by
        have hh := mem_map_of_mem i hx
        rw [map_commutator,hiU,hPm] at hh
        exact commutator_mono (DistanceEight.U_le_Z d.radical a) le_rfl hh
      exact (hwhole.trans hJP) hxH (i y) hy
    have hhi : 4 ≤ H.relIndex (U d.radical a) := by
      rw [←hiU,←relIndex_comap]
      apply (quadratic_cover_fixedIndex_four_le s _ hPcard hq).trans
      apply relIndex_le_of_le_left _ index_ne_zero_of_finite
      intro x hx y hy
      apply hi
      simp only [map_mul]
      exact (hwhole.trans hJP) hx (i y) hy
    have hm := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam d.radical)) H
      (U d.radical a) bot_le hHU
    simp only [relIndex_bot_left] at hm
    have hUc : Nat.card (U d.radical a) = 16 := by
      rw [←hiU,card_map_of_injective hi,hnat]
    rw [hUc] at hm
    nlinarith
  exact ⟨le_antisymm (hwhole.trans hKF)
    (sup_le (commutator_mono le_rfl hAP) (commutator_mono inf_le_left le_rfl)),
    hwhole.trans hJP,hcardH⟩

include s in
/-- With the natural sixteen-element cover, a strict small backward kernel
cannot be controlled by an actor generating with its actual edge kernel. -/
theorem natural_strict_small_actor_false
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    (hnat : Nat.card (replacementMoved d) = 16)
    {c z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) c z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical c) < 4)
    (W : Subgroup (FreeAmalgam d.radical))
    (hgen : Q d.radical (p.walk.getVert 1) ⊔ W = stabilizer d.radical (p.walk.getVert 2))
    (hstrict : 2 < (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c))
    (hWne : ¬ W ≤ Q d.radical (p.walk.getVert 2))
    (hWbound : ⁅(Z d.radical c ⊓ Q d.radical z) ⊔ Z d.radical (p.walk.getVert 2),W⁆ ≤
      Z d.radical (p.walk.getVert 2))
    (hWfix : ⁅Z d.radical c,Z d.radical z⁆ ≤ centralizer (W : Set (FreeAmalgam d.radical))) : False := by
  let a := p.walk.getVert 2
  let t := p.walk.getVert 1
  let K := Z d.radical c ⊓ Q d.radical z
  let D := ⁅Z d.radical c,Z d.radical z⁆
  let H := ⁅Z d.radical c,Q d.radical a⁆
  let F := ⁅K,Q d.radical a⁆
  let J := K ⊔ Z d.radical a
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have ha : color d.radical a = false := (p.vertex_color (by omega)).mpr (by decide)
  have hct : Adjacent d.radical c t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hat : Adjacent d.radical a t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [ha] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hTGc : Q d.radical t ≤ stabilizer d.radical c := fun _ hx => hx.2 _ (adjacent_symm d.radical hct)
  have hTGa : Q d.radical t ≤ stabilizer d.radical a := fun _ hx => hx.2 _ (adjacent_symm d.radical hat)
  have hWG : W ≤ stabilizer d.radical a := le_sup_right.trans_eq hgen
  have hWN : W ≤ normalizer (J : Set (FreeAmalgam d.radical)) :=
    le_normalizer_iff_commutator_le_left.mpr (hWbound.trans le_sup_right)
  have hZcQ : Z d.radical c ≤ Q d.radical a := by
    apply Z_le_Q_of_dist_lt d.radical c ((replacementGeometry h d).exists_critical c p.start_color)
    rw [(replacementGeometry h d).distance_constant _ p.start_color,p.dist_start (by omega)]
    exact hb2
  have hZwQ : Z d.radical z ≤ Q d.radical a := by
    apply Z_le_Q_of_dist_lt d.radical z ((replacementGeometry h d).exists_critical z p.end_color)
    rw [(replacementGeometry h d).distance_constant _ p.end_color,SimpleGraph.dist_comm,p.dist_end,hl]
    exact hb2
  have hKV : K ≤ V d.radical a := inf_le_left.trans
    (le_iSup_of_le c (le_iSup_of_le (by rw [p.dist_start (by omega)]) le_rfl))
  have central_false (hcentral : D ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) : False := by
    have hTK : Q d.radical t ≤ normalizer (K : Set (FreeAmalgam d.radical)) := by
      have hh := le_inf hTGc (le_centralizer_iff.mp (hcentral.trans (centralizer_le hTGa)))
      rw [←small_critical_kernel_normalizer_eq_line_centralizer s hc p hsmall] at hh
      exact hh.trans inf_le_right
    have hTJ : Q d.radical t ≤ normalizer (J : Set (FreeAmalgam d.radical)) :=
      (le_inf hTK (hTGa.trans (Z_normalized d.radical a))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
    have hGJ : stabilizer d.radical a ≤ normalizer (J : Set (FreeAmalgam d.radical)) := by
      rw [←hgen]
      exact sup_le hTJ hWN
    have hJB := normalized_radius_le_slice_of_actor_at s hb2 ha J W
      (sup_le hKV (Z_le_VBall d.radical _ 2)) hGJ hWG hWne hWbound
    let := finite_Z d.radical c
    have hi := relIndex_le_of_le_left (le_sup_left.trans hJB : K ≤ B d.radical a _)
      (index_ne_zero_of_finite (H := K.subgroupOf (Z d.radical c)))
    change (B d.radical a _).relIndex (Z d.radical c) ≤
      (Z d.radical c ⊓ Q d.radical z).relIndex (Z d.radical c) at hi
    rw [inf_relIndex_left,(small_critical_indices s hc p hsmall).1] at hi
    have hsmallSlice := (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical c)
      index_ne_zero_of_finite).trans hi
    exact (not_le_of_gt hstrict) hsmallSlice
  have hmove : ¬ Q d.radical t ≤ centralizer (D : Set (FreeAmalgam d.radical)) := by
    intro hh
    apply central_false
    apply le_centralizer_iff.mp
    rw [←hgen]
    exact sup_le hh (le_centralizer_iff.mp hWfix)
  have hQt : IsPGroup 2 (Q d.radical t) := by
    obtain ⟨i,_,_,hiR,_,_⟩ := SylowAdjacent.edge_coordinates (h := h) hc p.start_color hct
    rw [←hiR]
    exact (replacement_radical_isPGroup h d).map i
  have hPQ : Q d.radical a ≤ Q d.radical t := Q_le_adjacent_h d.radical ht hat
  have hDX : D ≤ X d.radical a := by
    have hVc : Z d.radical c ≤ V d.radical a :=
      le_iSup_of_le c (le_iSup_of_le (by rw [p.dist_start (by omega)]) le_rfl)
    have hVz : Z d.radical z ≤ V d.radical a :=
      le_iSup_of_le z (le_iSup_of_le (by rw [SimpleGraph.dist_comm,p.dist_end,hl]) le_rfl)
    exact (commutator_mono hVc hVz).trans (radius_bounds_general s hc hb2 ha c z).2.1
  have hfix : Q d.radical a ≤ centralizer (D : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (hDX.trans (fun _ hx => (mem_omegaCenter_iff.mp hx).2.2))
  obtain ⟨hdecomp,hquad,hcard⟩ := natural_small_orbit_movement s hc hnat p hsmall
    (Q d.radical t) (Q d.radical a) hTGc hQt le_rfl hPQ
    (hTGa.trans (Q_normalized d.radical a)) hZwQ hfix hmove
  have hHU : H ≤ U d.radical c := by
    change ⁅Z d.radical c,Q d.radical a⁆ ≤ U d.radical c
    rw [seed_commutator_eq_moving (h := h) (e := e) (hz := hz) p.start_color hct _ hPQ]
    exact le_normalizer_iff_commutator_le_left.mp ((hPQ.trans hTGc).trans (U_normalized c))
  have hHQ : H ≤ Q d.radical a := (hHU.trans (DistanceEight.U_le_Z d.radical c)).trans hZcQ
  have hHX : H ≤ X d.radical a := by
    let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) c p.start_color
    intro x hx
    exact mem_omegaCenter_iff.mpr ⟨hHQ hx,
      elemPow_eq_one_of_isElementaryAbelian x ((hHU.trans (DistanceEight.U_le_Z d.radical c)) hx),hquad hx⟩
  have hTN : Q d.radical t ≤ normalizer (H : Set (FreeAmalgam d.radical)) := by
    intro x hx
    rw [mem_normalizer_iff_map_conj_eq]
    change (⁅Z d.radical c,Q d.radical a⁆).map _ = _
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical c (hTGc hx)),
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a (hTGa hx))]
  have hcore := critical_kernel_core_control s hc hb p W hWG hWN
  have hFN : W ≤ normalizer (F : Set (FreeAmalgam d.radical)) := hcore.2.2
  have hWH : W ≤ normalizer (H : Set (FreeAmalgam d.radical)) := by
    change W ≤ normalizer ((⁅Z d.radical c,Q d.radical a⁆ : Subgroup (FreeAmalgam d.radical)) : Set _)
    rw [hdecomp]
    exact (le_inf ((le_centralizer_iff.mp hWfix).trans (Subgroup.centralizer_le_normalizer _)) hFN).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hGH : stabilizer d.radical a ≤ normalizer (H : Set (FreeAmalgam d.radical)) := by
    rw [←hgen]
    exact sup_le hTN hWH
  have hfixed := small_core_residual_fixed_knownSimple (h := h) (e := e) ha H hHQ
    ((Ltilde_le_stabilizer a).trans hGH) ((show Nat.card H ≤ 4 from hcard).trans (by decide))
  exact central_false ((commutator_mono le_rfl hZwQ).trans
    ((le_inf hHX hfixed).trans (omega_fixed_central_of_small_critical s hc p hsmall a ha)))

include e hz hn in
/-- In the full sixteen-image original-Sylow branch with the natural cover,
the same endpoint restriction has a large backward image. The relative
normalizer is retained and is identified with the edge kernel by its proved
full-image theorem. -/
theorem natural_sixteen_full_seed_backward_large_knownSimple
    (hb : replacementDistance h d = 4)
    (hnat : Nat.card (replacementMoved d) = 16)
    (himage : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical))) :
    ∃ (W : Subgroup (FreeAmalgam d.radical)) (t c : Vertex d.radical),
      Z d.radical (p.walk.getVert 3) ≤ W ∧ W ≤ Z d.radical z ∧
      W.relIndex (Z d.radical z) ≤ 2 ∧
      ⁅Z d.radical (alpha d.radical),W⁆ = ⁅Z d.radical (alpha d.radical),Z d.radical z⁆ ∧
      (¬ W ≤ Q d.radical (alpha d.radical)) ∧
      Adjacent d.radical (alpha d.radical) t ∧ Adjacent d.radical c t ∧
      (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical (alpha d.radical)) ⊔ W = stabilizer d.radical (alpha d.radical) ∧
      ∃ q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2),
        q.walk.getVert 1 = t ∧ q.walk.getVert 2 = alpha d.radical ∧
        q.walk.getVert 3 = p.walk.getVert 1 ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical c) ∧
        ⁅(Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)) ⊔ Z d.radical (alpha d.radical),W⁆ =
          ⁅Z d.radical (alpha d.radical),Z d.radical z⁆ ∧
        W ≤ normalizer (((Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)) ⊔
          Z d.radical (alpha d.radical) : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
        4 ≤ (Q d.radical (p.walk.getVert 2)).relIndex (Z d.radical c) ∧
        ⁅Z d.radical c,Q d.radical (alpha d.radical)⁆ =
          ⁅Z d.radical c,Z d.radical (p.walk.getVert 2)⁆ ∧
        ⁅localZSpan d.radical c (alpha d.radical),Q d.radical (alpha d.radical)⁆ =
          ⁅Z d.radical c,Z d.radical (p.walk.getVert 2)⁆ ∧
        ⁅Z d.radical c,Z d.radical (p.walk.getVert 2)⁆ ≤ fixedCore d.radical (alpha d.radical) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨W,hFE,hWZ,hi,hcomm,hWne,_,t,c,hat,hct,hgen,_,q,hq1,hq2,hq3,
    _,hstrict,_,_,hDexact,hWN,hfix,_,_⟩ :=
    large_image_full_seed_backward_knownSimple (e := e) (hz := hz) (hn := hn) hb p hlarge
  have hgenQ : Q d.radical t ⊔ W = stabilizer d.radical (alpha d.radical) := by
    have hh := SylowLarge.sixteen_edge_relative_normalizer_knownSimple
      (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) himage rfl hat
    rwa [hh] at hgen
  have hback : 4 ≤ (Q d.radical (p.walk.getVert 2)).relIndex (Z d.radical c) := by
    by_contra! hs
    apply natural_strict_small_actor_false s hc hb hnat q hs W
    · rwa [hq1,hq2]
    · rwa [hq2]
    · rwa [hq2]
    · rw [hq2,hDexact]
      exact ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
        (DistanceEight.U_le_Z d.radical _)
    · exact hfix
  let D := ⁅Z d.radical c,Z d.radical (p.walk.getVert 2)⁆
  have heq := natural_large_midpoint_movement_eq s hc hb hnat q hback
  rw [hq2] at heq
  have hdata := large_midpoint_movement s hc hb q hback
  rw [hq1,hq2,heq] at hdata
  have hcard := large_midpoint_movement_card s hc hb q hback
  rw [hq2,heq] at hcard
  have hGN : stabilizer d.radical (alpha d.radical) ≤ normalizer (D : Set (FreeAmalgam d.radical)) := by
    rw [←hgenQ]
    exact sup_le hdata.2.2.1 ((le_centralizer_iff.mp hfix).trans (Subgroup.centralizer_le_normalizer _))
  have hfixed : D ≤ fixedCore d.radical (alpha d.radical) :=
    small_core_residual_fixed_knownSimple (h := h) (e := e) rfl D
      (hdata.2.1.trans (omegaCenter_le _)) ((Ltilde_le_stabilizer _).trans hGN) hcard
  have hspan : ⁅localZSpan d.radical c (alpha d.radical),Q d.radical (alpha d.radical)⁆ = D := by
    apply le_antisymm
    · have hql : q.walk.length = 4 := q.length_eq_b.trans hb
      have hZcG : Z d.radical c ≤ stabilizer d.radical (alpha d.radical) := by
        have hZcQ : Z d.radical c ≤ Q d.radical (alpha d.radical) := by
          have hdist := q.dist_start (show 2 ≤ q.walk.length by omega)
          rw [hq2] at hdist
          apply Z_le_Q_of_dist_lt d.radical c ((replacementGeometry h d).exists_critical c q.start_color)
          rw [(replacementGeometry h d).distance_constant _ q.start_color,hdist]
          exact show 2 < replacementDistance h d by omega
        exact fun _ hx => (hZcQ hx).1
      rw [localZSpan_eq_conjugates]
      apply commutator_iSup_le_of_relative_normal (stabilizer d.radical (alpha d.radical))
        (Q d.radical (alpha d.radical)) D _ hGN
      · intro g
        exact (map_mono hZcG).trans_eq (mem_normalizer_iff_map_conj_eq.mp
          ((stabilizer d.radical (alpha d.radical)).le_normalizer
            ((stabilizer d.radical (alpha d.radical)).inv_mem g.property)))
      · intro g
        have hh := congrArg (Subgroup.map (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom) heq
        have hQ : (Q d.radical (alpha d.radical)).map
            (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom = Q d.radical (alpha d.radical) :=
          mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical _
            ((stabilizer d.radical (alpha d.radical)).inv_mem g.property))
        have hD : D.map (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom = D :=
          mem_normalizer_iff_map_conj_eq.mp (hGN
            ((stabilizer d.radical (alpha d.radical)).inv_mem g.property))
        change (⁅Z d.radical c,Q d.radical (alpha d.radical)⁆ : Subgroup (FreeAmalgam d.radical)).map
          (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom = D.map
          (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom at hh
        rw [map_commutator,hQ,hD] at hh
        exact hh.le
    · exact heq.symm.le.trans (commutator_mono (Z_le_localZSpan d.radical _ _) le_rfl)
  exact ⟨W,t,c,hFE,hWZ,hi,hcomm,hWne,hat,hct,hgen,q,hq1,hq2,hq3,hstrict,hDexact,hWN,hback,
    heq,hspan,hfixed⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

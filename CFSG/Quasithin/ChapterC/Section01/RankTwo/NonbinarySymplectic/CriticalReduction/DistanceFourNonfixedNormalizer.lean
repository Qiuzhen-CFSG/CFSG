module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourNonfixedCommutator
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.TerminalKernelSaturation

/-!
# The literal first edge cannot generate in the nonfixed large-back branch

For the actual backward path u--w--a--t--e, the large critical image gives
[Z_u,Z_e] = [Z_u,Q_a]. Thus the full edge kernel Q_w normalizes this
commutator. If L_a were contained in Q_w joined with the original Z_z,
the commutator would be normal at a. The opposite core Q_u centralizes it
and escapes Q_a, so simplicity of the actual quotient at a makes it fixed
by L_a, contradicting the nonfixed radius branch.

The full central attachments remain present. In particular no containment
of the smaller mover in Q_u, or mover fixed-space identification, is used.
This supplies a generation obstruction for MS93 (5.12)(2), printed p.925.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

private theorem normal_centralizer_of_simple_kernel_escape
    {G J : Type*} [Group G] [Group J] [IsSimpleGroup J]
    (S Q W A : Subgroup G) (f : S →* J) (hf : Function.Surjective f)
    (hk : f.ker.map S.subtype=Q) (hWS : W ≤ S)
    (hWn : S ≤ normalizer (W : Set G))
    (hQW : Q ≤ centralizer (W : Set G))
    (hAS : A ≤ S) (hAQ : ¬ A ≤ Q) (hAW : A ≤ centralizer (W : Set G)) :
    W ≤ centralizer (S : Set G) := by
  let W₀ := W.subgroupOf S
  let C := centralizer (W₀ : Set S)
  let : W₀.Normal := normal_subgroupOf_of_le_normalizer hWn
  let : C.Normal := inferInstance
  have hker : f.ker ≤ C := by
    intro k hk₀ w hw
    apply Subtype.val_injective
    exact hQW (hk ▸ mem_map_of_mem S.subtype hk₀) w.val hw
  have hAC : A.subgroupOf S ≤ C := by
    intro x hx w hw
    apply Subtype.val_injective
    exact hAW hx w.val hw
  have hnker : ¬ C ≤ f.ker := by
    intro hCk
    apply hAQ
    intro x hx
    exact hk ▸ mem_map_of_mem S.subtype
      (hCk (hAC (show (⟨x,hAS hx⟩ : S) ∈ A.subgroupOf S from hx)))
  have hmap : C.map f=⊤ := by
    rcases (Normal.map (inferInstance : C.Normal) f hf).eq_bot_or_eq_top with hz | ht
    · exact False.elim (hnker ((map_eq_bot_iff C).mp hz))
    · exact ht
  have hCtop : C=⊤ := by
    have hh := congrArg (Subgroup.comap f) hmap
    simpa only [comap_map_eq,comap_top,sup_eq_left.mpr hker] using hh
  intro x hx y hy
  have hxy : (⟨y,hy⟩ : S) ∈ C := hCtop ▸ mem_top _
  exact (congrArg Subtype.val (hxy (⟨x,hWS hx⟩ : S) hx)).symm

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- With a nonfixed radius and a large actual backward image, even the full
literal first edge kernel joined with the original endpoint seed cannot
contain the residual at the midpoint. -/
theorem Input.replacement_distance_four_nonfixed_edge_generation_obstruction
    {geometry : Geometry d.radical} {a z u : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hmid : back.walk.getVert 2=a)
    (hlarge : Nat.card F < (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical u))
    (hnot : ¬ ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    ¬ Ltilde d.radical a ≤ Q d.radical (back.walk.getVert 1) ⊔ Z d.radical z := by
  let e := path.walk.getVert 2
  let w := back.walk.getVert 1
  let C := ⁅Z d.radical u,Z d.radical e⁆
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  have hb0 : 0 < geometry.b d.radical := by omega
  have hl := path.length_eq_b
  have hbl := back.length_eq_b
  have he : color d.radical e=false := (path.vertex_color (by omega)).mpr (by decide)
  have hae : (cosetGraph d.radical).dist a e=2 := path.dist_start (by omega)
  have hua : (cosetGraph d.radical).dist u a=2 := by
    rw [←hmid]
    exact back.dist_start (by omega)
  have hut : Adjacent d.radical u w := by
    have hh := (cosetGraph_adj d.radical _ _).mp
      (back.walk.adj_getVert_succ (by omega : 0 < back.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  have hwa : Adjacent d.radical w a := by
    rw [←hmid]
    exact (cosetGraph_adj d.radical _ _).mp (back.walk.adj_getVert_succ (by omega))
  obtain ⟨hCX,hCQa,hCD⟩ :=
    h.replacement_distance_four_nonfixed_critical_commutator d path hb back hmid hlarge hnot
  have hQC : Q d.radical a ≤ centralizer (C : Set (FreeAmalgam d.radical)) :=
    (Q_le_centralizer_X d.radical a).trans (centralizer_le hCX)
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d)
  let rev := (show CriticalSegment geometry from ⟨u,e,back⟩).reverse hedge hb0
  have hlarge₂ : Nat.card F^2 ≤ (Q d.radical e).relIndex (Z d.radical u) := by
    by_contra! hs
    have hi := (h.replacement_small_critical_indices_eq_field d back hb0 hs).1
    exact (ne_of_gt hlarge) hi
  have hseed : ⁅Z d.radical u,Q d.radical a⁆ ≤ C := by
    by_contra hbad
    have hs := h.replacement_critical_index_lt_square_of_escape d rev.path hb0
      (Q d.radical a)
      (Q_le_stabilizer_of_dist_two d.radical a u path.start_color (by
        rwa [SimpleGraph.dist_comm]))
      (by
        change Q d.radical a ≤ centralizer
          ((⁅Z d.radical e,Z d.radical u⁆ : Subgroup (FreeAmalgam d.radical)) : Set _)
        rw [commutator_comm]
        exact hQC)
      (by
        change ¬ ⁅Z d.radical u,Q d.radical a⁆ ≤ ⁅Z d.radical e,Z d.radical u⁆
        rw [commutator_comm (Z d.radical e)]
        exact hbad)
    change (Q d.radical u).relIndex (Z d.radical e) < Nat.card F^2 at hs
    rw [←h.replacement_critical_indices_equal d back hb4] at hs
    exact (not_lt_of_ge hlarge₂) hs
  have heQa : Z d.radical e ≤ Q d.radical a := by
    apply Z_le_Q_of_dist_lt _ e (geometry.exists_critical e he)
    rw [geometry.distance_constant e he]
    change (cosetGraph d.radical).dist e a < geometry.b d.radical
    rw [SimpleGraph.dist_comm,hae]
    omega
  have hCeq : C=⁅Z d.radical u,Q d.radical a⁆ :=
    le_antisymm (commutator_mono le_rfl heQa) hseed
  have hQwN : Q d.radical w ≤ normalizer (C : Set (FreeAmalgam d.radical)) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq,hCeq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp
        (Z_normalized d.radical u (hg.2 u (adjacent_symm d.radical hut))),
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a (hg.2 a hwa))]
  have heQz : Z d.radical e ≤ Q d.radical z := by
    apply Z_le_Q_of_dist_lt _ e (geometry.exists_critical e he)
    rw [geometry.distance_constant e he]
    have hd := path.dist_end 2
    change (cosetGraph d.radical).dist e z < geometry.b d.radical
    rw [hd,hl,hb]
    decide
  have hCZe : C ≤ Z d.radical e := critical_commutator_le_endpoint_seed back
  have hzC : Z d.radical z ≤ centralizer (C : Set (FreeAmalgam d.radical)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes z path.end_color)).trans
      (centralizer_le (hCZe.trans heQz))
  intro hgen
  have hLN : Ltilde d.radical a ≤ normalizer (C : Set (FreeAmalgam d.radical)) :=
    hgen.trans (sup_le hQwN (hzC.trans (Subgroup.centralizer_le_normalizer _)))
  have hlocal : Ltilde d.radical a ⊔ Q d.radical a=stabilizer d.radical a := by
    obtain ⟨i,hinj,hir,hiL,hiU,hiQ⟩ := Sp4Four.SourceComparison.vertex_coordinates_with_kernel
      d.radical (h.replacement_two_group d) (h.replacement_core_le d) path.start_color
    rw [←hiL,←hiQ,←Subgroup.map_sup,h.replacement_residual d,
      h.replacement_inner_of_four_le d geometry hb4,←MonoidHom.range_eq_map,hir]
  have hSN : stabilizer d.radical a ≤ normalizer (C : Set (FreeAmalgam d.radical)) :=
    hlocal.ge.trans (sup_le hLN (hQC.trans (Subgroup.centralizer_le_normalizer _)))
  have hQuS : Q d.radical u ≤ stabilizer d.radical a :=
    Q_le_stabilizer_of_dist_two d.radical u a back.start_color hua
  have hQuC : Q d.radical u ≤ centralizer (C : Set (FreeAmalgam d.radical)) :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes u back.start_color))).trans
        (centralizer_le (critical_commutator_le_start_seed back))
  have hQuQa : ¬ Q d.radical u ≤ Q d.radical a := by
    intro hle
    let : Finite (stabilizer d.radical a) := finite_stabilizer d.radical a
    let : Finite (Q d.radical a) := Finite.of_injective
      (inclusion (show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1))
      (inclusion_injective _)
    have hcard : Nat.card (Q d.radical a)=Nat.card (Q d.radical u) := by
      obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical path.start_color
      obtain ⟨j,hj⟩ := exists_mVertex_of_color d.radical back.start_color
      have hy : act d.radical (g⁻¹*j) a=u := by
        rw [hg,act_mVertex,mul_inv_cancel_left,←hj]
      rw [←hy,Q_act,card_map_of_injective (MulAut.conj (g⁻¹*j)⁻¹).injective]
    have heq := eq_of_le_of_card_ge hle hcard.le
    exact rev.path.critical.2 (heQa.trans heq.ge)
  obtain ⟨E,hE,f,hf,hfQ,_⟩ :=
    h.replacement_inner_natural_action d geometry hb4 path.start_color
  have hfield : 3 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact (by decide : 3 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
  let := Theory.SpecificGroups.SymplecticFour.SimpleQuotients.isSimpleGroup hfield
  let : IsSimpleGroup (Sp E.Carrier) :=
    Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.isSimpleGroup
  have hCQ : C ≤ Q d.radical a := hCX.trans (omegaCenter_le _)
  have hCS : C ≤ stabilizer d.radical a := hCQ.trans (fun _ hx => hx.1)
  have hcentral := normal_centralizer_of_simple_kernel_escape
    (stabilizer d.radical a) (Q d.radical a) C (Q d.radical u)
    f hf hfQ hCS hSN hQC hQuS hQuQa hQuC
  exact hCD (le_inf hCQ (hcentral.trans (centralizer_le (Ltilde_le_stabilizer a))))

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

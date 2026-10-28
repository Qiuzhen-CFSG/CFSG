module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.PairedOriginalFixedSelection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourNeighbor
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourNonfixedNormalizer
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.TrappedTransport

/-!
# A root backward member of the actual smaller-mover pair

The paired selector retains its extra conjugated endpoint. If a chosen
backward member has a large image, a high or trapped companion makes that
extra endpoint normalize the full critical commutator. The actual triple
then makes the commutator vertex-normal, contradicting nonfixedness. Thus
one actual member has a root backward image.

Private imports reuse the verified simple-centralizer argument and the
central-join commutator identity. All full cores and central attachments
remain; no individual-generation premise replaces the actual triple.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem large_back_commutator_normality
    {geometry : Geometry d.radical} {a z u : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hmid : back.walk.getVert 2=a)
    (hlarge : Nat.card F < (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical u))
    (hnot : ¬ ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    let C := ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆
    C=⁅Z d.radical u,Q d.radical a⁆ ∧
      Q d.radical (back.walk.getVert 1) ≤ normalizer (C : Set (FreeAmalgam d.radical)) ∧
      ¬ stabilizer d.radical a ≤ normalizer (C : Set (FreeAmalgam d.radical)) := by
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
  refine ⟨hCeq,hQwN,?_⟩
  intro hSN
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


private theorem trapped_seed_join_normalized
    {geometry : Geometry d.radical} {a z v w : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (haw : Adjacent d.radical a w) (hvw : Adjacent d.radical v w)
    (hlarge : Nat.card F^2 ≤ (Q d.radical a).relIndex (Z d.radical z))
    (htrap : Z d.radical v ≤ Q d.radical (path.walk.getVert 2)) :
    Z d.radical z ≤ normalizer
      ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
  have hlen : path.walk.length-2=2 := by have hh := path.length_eq_b; omega
  have hYV : Z d.radical v ≤ V d.radical a :=
    le_sup_left.trans (neighbor_seed_join_le_radius haw hvw)
  have hYQ := hYV.trans (geometry.V_le_Q (by omega) a path.start_color)
  have hYS : Z d.radical v ≤ stabilizer d.radical z :=
    (le_inf hYV (by simpa only [hlen] using htrap)).trans
      (CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.truncated_radius_le_endpoint_stabilizer path (by omega))
  have hnorm : Z d.radical z ≤ normalizer
      ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    by_contra hn
    have hi := (h.replacement_critical_indices_eq_field_of_seed_escape d path
      (by omega) (Z d.radical v) hYS hYQ hn).2
    have hq : 1 < Nat.card F := Finite.one_lt_card
    nlinarith
  exact hnorm

private theorem trapped_seed_core_normalized
    {geometry : Geometry d.radical} {a z v w : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (haw : Adjacent d.radical a w) (hvw : Adjacent d.radical v w)
    (hlarge : Nat.card F^2 ≤ (Q d.radical a).relIndex (Z d.radical z))
    (htrap : Z d.radical v ≤ Q d.radical (path.walk.getVert 2)) :
    Z d.radical z ≤ normalizer
      ((⁅Z d.radical v,Q d.radical a⁆ : Subgroup (FreeAmalgam d.radical)) : Set _) := by
  have hYV : Z d.radical v ≤ V d.radical a :=
    le_sup_left.trans (neighbor_seed_join_le_radius haw hvw)
  have hYQ := hYV.trans (geometry.V_le_Q (by omega) a path.start_color)
  have hnorm := trapped_seed_join_normalized h d path hb haw hvw hlarge htrap
  have hZaQ : Z d.radical a ≤ centralizer (Q d.radical a : Set (FreeAmalgam d.radical)) :=
    commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a path.start_color)
  have heq : ⁅Z d.radical v ⊔ Z d.radical a,Q d.radical a⁆ = ⁅Z d.radical v,Q d.radical a⁆ := by
    rw [commutator_comm (Z d.radical v ⊔ Z d.radical a),commutator_comm (Z d.radical v)]
    exact commutator_sup_of_central (Q d.radical a) (Z d.radical v) (Z d.radical a)
      (hZaQ.trans (centralizer_le hYQ)) hZaQ
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq,←heq,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hnorm hg),
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a
      (path.endpoint_Z_le_start_stabilizer (by omega) hg))]


private theorem companion_root_or_normalizes
    {geometry : Geometry d.radical} {a z v w : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (haw : Adjacent d.radical a w) (hvw : Adjacent d.radical v w)
    (hlarge : Nat.card F^2 ≤ (Q d.radical a).relIndex (Z d.radical z))
    (hnot : ¬ ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    (∃ back : CriticalPath d.radical geometry v (path.walk.getVert 2),
      back.walk.getVert 1=w ∧
      (∀ i ≤ 2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
      (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical v)=Nat.card F ∧
      (Q d.radical v).relIndex (Z d.radical (path.walk.getVert 2))=Nat.card F) ∨
    Z d.radical z ≤ normalizer
      ((⁅Z d.radical v,Q d.radical a⁆ : Subgroup (FreeAmalgam d.radical)) : Set _) := by
  by_cases htrap : Z d.radical v ≤ Q d.radical (path.walk.getVert 2)
  · exact Or.inr (trapped_seed_core_normalized h d path hb haw hvw hlarge htrap)
  have hlen : path.walk.length-2=2 := by have hh := path.length_eq_b; omega
  have hex := exists_backward_path_of_not_le geometry (by omega) path haw hvw
    (by simpa only [hlen] using htrap)
  rw [hlen] at hex
  obtain ⟨back,hback,hover⟩ := hex
  by_cases hi : (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical v) ≤ Nat.card F
  · have hsmall : (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical v) < Nat.card F^2 := by
      have hq : 1 < Nat.card F := Finite.one_lt_card
      nlinarith
    obtain ⟨h1,h2⟩ := h.replacement_small_critical_indices_eq_field d back (by omega) hsmall
    exact Or.inl ⟨back,hback,hover,h1,h2⟩
  have hmid : back.walk.getVert 2=a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (by omega)
  obtain ⟨hCeq,_,_⟩ := large_back_commutator_normality h d path hb back hmid (lt_of_not_ge hi) hnot
  right
  rw [←hCeq]
  apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
  have he : color d.radical (path.walk.getVert 2)=false :=
    (path.vertex_color (by rw [path.length_eq_b]; omega)).mpr (by decide)
  have heQ : Z d.radical (path.walk.getVert 2) ≤ Q d.radical z := by
    apply Z_le_Q_of_dist_lt _ _ (geometry.exists_critical _ he)
    rw [geometry.distance_constant _ he]
    change (cosetGraph d.radical).dist (path.walk.getVert 2) z < geometry.b d.radical
    rw [path.dist_end,path.length_eq_b,hb]
    decide
  exact (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes z path.end_color)).trans
    (centralizer_le ((critical_commutator_le_endpoint_seed back).trans heQ))


private theorem paired_root_choice
    {geometry : Geometry d.radical} {a z v w : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (haw : Adjacent d.radical a w) (hvw : Adjacent d.radical v w)
    (hlarge : Nat.card F^2 ≤ (Q d.radical a).relIndex (Z d.radical z))
    (hnot : ¬ ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical a)
    (J : Subgroup (FreeAmalgam d.radical)) (hJw : J ≤ Q d.radical w)
    (hgen : (J ⊔ Z d.radical z) ⊔ (Z d.radical z).map (MulAut.conj x).toMonoidHom =
      stabilizer d.radical a)
    (hn : ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    ∃ u t, (u=v ∧ t=w ∨ u=act d.radical x v ∧ t=act d.radical x w) ∧
      ∃ back : CriticalPath d.radical geometry u (path.walk.getVert 2),
        back.walk.getVert 1=t ∧
        (∀ i ≤ 2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
        (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical u)=Nat.card F ∧
        (Q d.radical u).relIndex (Z d.radical (path.walk.getVert 2))=Nat.card F := by
  let v' := act d.radical x v
  let w' := act d.radical x w
  have hxa : act d.radical x a=a := hx
  have haw' : Adjacent d.radical a w' := by
    rw [←hxa]
    exact (adjacent_act_iff _ _ _ _).mpr haw
  have hvw' : Adjacent d.radical v' w' := (adjacent_act_iff _ _ _ _).mpr hvw
  rcases companion_root_or_normalizes h d path hb haw hvw hlarge hnot with hroot | hN
  · exact ⟨v,w,Or.inl ⟨rfl,rfl⟩,hroot⟩
  rcases companion_root_or_normalizes h d path hb haw' hvw' hlarge hnot with hroot | hN'
  · exact ⟨v',w',Or.inr ⟨rfl,rfl⟩,hroot⟩
  let C := ⁅Z d.radical v,Q d.radical a⁆
  let C' := ⁅Z d.radical v',Q d.radical a⁆
  have hQaMap : (Q d.radical a).map (MulAut.conj x).toMonoidHom=Q d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a hx)
  have hQaMapInv : (Q d.radical a).map (MulAut.conj x⁻¹).toMonoidHom=Q d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a
      ((stabilizer d.radical a).inv_mem hx))
  have hCback : C'.map (MulAut.conj x).toMonoidHom=C := by
    have hZ : (Z d.radical v').map (MulAut.conj x).toMonoidHom=Z d.radical v := by
      have hh := Z_act d.radical x⁻¹ v'
      have hvback : act d.radical x⁻¹ v'=v := by
        dsimp only [v']
        rw [←act_mul,mul_inv_cancel,act_one]
      rw [hvback,inv_inv] at hh
      exact hh.symm
    change (⁅Z d.radical v',Q d.radical a⁆).map _=C
    rw [map_commutator,hZ,hQaMap]
  have hCforward : C.map (MulAut.conj x⁻¹).toMonoidHom=C' := by
    change (⁅Z d.radical v,Q d.radical a⁆).map _=C'
    rw [map_commutator,←Z_act d.radical x v,hQaMapInv]
  have hNx : (Z d.radical z).map (MulAut.conj x).toMonoidHom ≤ normalizer (C : Set _) := by
    have hh := map_mono (f := (MulAut.conj x).toMonoidHom) hN'
    rw [map_normalizer_eq_of_bijective _ (MulAut.conj x).bijective,hCback] at hh
    exact hh
  have hQw : Q d.radical w ≤ normalizer (C : Set (FreeAmalgam d.radical)) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq]
    change (⁅Z d.radical v,Q d.radical a⁆).map _=C
    rw [map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical v
        (hg.2 v (adjacent_symm _ hvw))),
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a
        (hg.2 a (adjacent_symm _ haw)))]
  have hSC : stabilizer d.radical a ≤ normalizer (C : Set (FreeAmalgam d.radical)) :=
    hgen.ge.trans (sup_le (sup_le (hJw.trans hQw) hN) hNx)
  have hSC' : stabilizer d.radical a ≤ normalizer (C' : Set (FreeAmalgam d.radical)) := by
    have hh := map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hSC
    have hSmap : (stabilizer d.radical a).map (MulAut.conj x⁻¹).toMonoidHom=
        stabilizer d.radical a := mem_normalizer_iff_map_conj_eq.mp
      ((stabilizer d.radical a).le_normalizer ((stabilizer d.radical a).inv_mem hx))
    rw [map_normalizer_eq_of_bijective _ (MulAut.conj x⁻¹).bijective,hCforward,
      hSmap] at hh
    exact hh
  have hlen : path.walk.length-2=2 := by have hh := path.length_eq_b; omega
  have finish (u t : Vertex d.radical) (hat : Adjacent d.radical a t)
      (hut : Adjacent d.radical u t)
      (hSN : stabilizer d.radical a ≤ normalizer
        ((⁅Z d.radical u,Q d.radical a⁆ : Subgroup (FreeAmalgam d.radical)) : Set _))
      (hu : ¬ Z d.radical u ≤ Q d.radical (path.walk.getVert 2)) :
      ∃ back : CriticalPath d.radical geometry u (path.walk.getVert 2),
        back.walk.getVert 1=t ∧
        (∀ i ≤ 2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
        (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical u)=Nat.card F ∧
        (Q d.radical u).relIndex (Z d.radical (path.walk.getVert 2))=Nat.card F := by
    have hex := exists_backward_path_of_not_le geometry (by omega) path hat hut
      (by simpa only [hlen] using hu)
    rw [hlen] at hex
    obtain ⟨back,hback,hover⟩ := hex
    have hmid : back.walk.getVert 2=a := by
      simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (by omega)
    have hi : (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical u) ≤ Nat.card F := by
      by_contra! hi
      obtain ⟨hCeq,_,hbad⟩ := large_back_commutator_normality h d path hb back hmid hi hnot
      exact hbad (hCeq.symm ▸ hSN)
    have hsmall : (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical u) < Nat.card F^2 := by
      have hq : 1 < Nat.card F := Finite.one_lt_card
      nlinarith
    obtain ⟨h1,h2⟩ := h.replacement_small_critical_indices_eq_field d back (by omega) hsmall
    exact ⟨back,hback,hover,h1,h2⟩
  by_cases hv : Z d.radical v ≤ Q d.radical (path.walk.getVert 2)
  · have hv' : ¬ Z d.radical v' ≤ Q d.radical (path.walk.getVert 2) := by
      intro hv'
      have hnorm := trapped_seed_join_normalized h d path hb haw hvw hlarge hv
      have hnorm' := trapped_seed_join_normalized h d path hb haw' hvw' hlarge hv'
      have hxnorm := paired_endpoint_normalizes_first_join x hx hnorm'
      apply hn
      rw [←hgen]
      refine sup_le (sup_le (hJw.trans (edge_normalizes_neighbor_seed_join haw hvw)) hnorm) ?_
      simpa only [Z_act,inv_inv] using hxnorm
    exact ⟨v',w',Or.inr ⟨rfl,rfl⟩,finish v' w' haw' hvw' hSC' hv'⟩
  · exact ⟨v,w,Or.inl ⟨rfl,rfl⟩,finish v w haw hvw hSC hv⟩


omit h d in
private theorem original_mover_act {M : Type*} [Group M] [Finite M]
    (R : Subgroup M) (g : FreeAmalgam R) (a t : Vertex R) (q : ℕ) :
    Subgroup.SmallMover.join (U R (act R g a)) (Q R (act R g a))
      (Q R (act R g t)) q =
      (Subgroup.SmallMover.join (U R a) (Q R a) (Q R t) q).map
        (MulAut.conj g⁻¹).toMonoidHom := by
  rw [U_act,Q_act,Q_act,Subgroup.SmallMover.join_map _ (MulAut.conj g⁻¹).injective]

/-- One member of the actual prescribed smaller-mover pair has a root
backward path in the nonfixed branch. The original pair, both triples and
all three whole-seed fixed identities use the same g and x. -/
theorem Input.replacement_distance_four_paired_nonfixed_root_backward_path
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hlarge : Nat.card F^2 ≤ (Q d.radical a).relIndex (Z d.radical z))
    (hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2)
    (hnot : ¬ ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    ∃ g ∈ Ltilde d.radical a, ∃ x ∈ Ltilde d.radical a,
      let v := act d.radical g⁻¹ (path.walk.getVert 2)
      let w := act d.radical g⁻¹ (path.walk.getVert 1)
      let v' := act d.radical x v
      let w' := act d.radical x w
      let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (path.walk.getVert 1)) (Nat.card F^2)
      let J₁ := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical w) (Nat.card F^2)
      let J₂ := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical w') (Nat.card F^2)
      Adjacent d.radical a w ∧ Adjacent d.radical v w ∧
      Adjacent d.radical a w' ∧ Adjacent d.radical v' w' ∧
      (J₁ ⊔ Z d.radical z) ⊔ (Z d.radical z).map (MulAut.conj x).toMonoidHom =
        stabilizer d.radical a ∧
      (J₂ ⊔ Z d.radical z) ⊔ (Z d.radical z).map (MulAut.conj x⁻¹).toMonoidHom =
        stabilizer d.radical a ∧
      ((Z d.radical a ⊓ centralizer (J₁ : Set (FreeAmalgam d.radical))) ⊓
        centralizer (J₂ : Set (FreeAmalgam d.radical)) =
          Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
      ((Z d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical))) ⊓
        centralizer (J₁ : Set (FreeAmalgam d.radical)) =
          Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
      ((Z d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical))) ⊓
        centralizer (J₂ : Set (FreeAmalgam d.radical)) =
          Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
      ∃ u t, (u=v ∧ t=w ∨ u=v' ∧ t=w') ∧
        ∃ back : CriticalPath d.radical geometry u (path.walk.getVert 2),
          back.walk.getVert 1=t ∧
          (∀ i ≤ 2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
          (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical u)=Nat.card F ∧
          (Q d.radical u).relIndex (Z d.radical (path.walk.getVert 2))=Nat.card F := by
  let t := path.walk.getVert 1
  let c := path.walk.getVert 2
  have hat : Adjacent d.radical a t := by
    simpa only [SimpleGraph.Walk.getVert_zero] using (cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by rw [path.length_eq_b]; omega : 0 < path.walk.length))
  have hfirst : path.walk.getVert 1=t := rfl
  have hct : Adjacent d.radical c t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by rw [path.length_eq_b]; omega : 1 < path.walk.length)))
  have hnormal := h.replacement_path_neighbor_join_not_normal_of_four_le d path (by omega)
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  obtain ⟨E,hE,f,hf,hfQ,hTf,hindex,hcore,hTP,hquad,hmax⟩ :=
    h.replacement_maximizing_parabolic d geometry hb4 path.start_color hat
  have hJP := h.replacement_small_mover_le_maximizing_plane_of_index_le d
    geometry hb4 path.start_color hat E hE f hfQ hTf hindex hmax hJm
  obtain ⟨g,hg,x,hx,hgen,_,hfixed,hxn,hxp,hO₁,hO₂⟩ :=
    h.replacement_smaller_mover_original_fixed_selection d path hb4 hat hfirst
      E hE f hf hfQ hTf hindex hJP
  let v := act d.radical g⁻¹ c
  let w := act d.radical g⁻¹ t
  let v' := act d.radical x v
  let w' := act d.radical x w
  let J₁ := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical w) (Nat.card F^2)
  let J₂ := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical w') (Nat.card F^2)
  have hgS := Ltilde_le_stabilizer a hg
  have hxS := Ltilde_le_stabilizer a hx
  have hga : act d.radical g⁻¹ a=a := (stabilizer d.radical a).inv_mem hgS
  have hxa : act d.radical x a=a := hxS
  have haw : Adjacent d.radical a w := by
    rw [←hga]
    exact (adjacent_act_iff _ _ _ _).mpr hat
  have hvw : Adjacent d.radical v w := (adjacent_act_iff _ _ _ _).mpr hct
  have haw' : Adjacent d.radical a w' := by
    rw [←hxa]
    exact (adjacent_act_iff _ _ _ _).mpr haw
  have hvw' : Adjacent d.radical v' w' := (adjacent_act_iff _ _ _ _).mpr hvw
  have hJ₁ : J₁=J.map (MulAut.conj g).toMonoidHom := by
    simpa only [hga,inv_inv] using original_mover_act d.radical g⁻¹ a t (Nat.card F^2)
  have hJ₂ : J₂=J₁.map (MulAut.conj x⁻¹).toMonoidHom := by
    simpa only [hxa] using original_mover_act d.radical x a w (Nat.card F^2)
  have hgen₁ : (J₁ ⊔ Z d.radical z) ⊔ (Z d.radical z).map (MulAut.conj x).toMonoidHom =
      stabilizer d.radical a := by rwa [hJ₁]
  have hO₁' : (Z d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical))) ⊓
      centralizer (J₁ : Set (FreeAmalgam d.radical)) =
      Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    rwa [hJ₁]
  have hO₂' : (Z d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical))) ⊓
      centralizer (J₂ : Set (FreeAmalgam d.radical)) =
      Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    rwa [hJ₂,hJ₁]
  have hn : ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    intro hn
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hn
    rw [map_normalizer_eq_of_bijective _ (MulAut.conj g⁻¹).bijective,Subgroup.map_sup] at hh
    have hS : (stabilizer d.radical a).map (MulAut.conj g⁻¹).toMonoidHom=stabilizer d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp ((stabilizer d.radical a).le_normalizer
        ((stabilizer d.radical a).inv_mem hgS))
    have hvc : act d.radical g v=c := by
      dsimp only [v]
      rw [←act_mul,inv_mul_cancel,act_one]
    have hga' : act d.radical g a=a := hgS
    rw [hS,←Z_act,←Z_act,hvc,hga'] at hh
    exact hnormal hh
  have hgen₂ : (J₂ ⊔ Z d.radical z) ⊔ (Z d.radical z).map (MulAut.conj x⁻¹).toMonoidHom =
      stabilizer d.radical a := by
    have hh := congrArg (Subgroup.map (MulAut.conj x⁻¹).toMonoidHom) hgen₁
    have hS : (stabilizer d.radical a).map (MulAut.conj x⁻¹).toMonoidHom=stabilizer d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp ((stabilizer d.radical a).le_normalizer
        ((stabilizer d.radical a).inv_mem hxS))
    have hcomp : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
        MonoidHom.id (FreeAmalgam d.radical) := by
      apply MonoidHom.ext
      intro y
      change x⁻¹*(x*y*x⁻¹)*(x⁻¹)⁻¹=y
      group
    rw [Subgroup.map_sup,Subgroup.map_sup,Subgroup.map_map,hcomp,Subgroup.map_id,hS,←hJ₂] at hh
    rw [sup_assoc,sup_comm (Z d.radical z),←sup_assoc]
    exact hh
  have hfixed' : (Z d.radical a ⊓ centralizer (J₁ : Set (FreeAmalgam d.radical))) ⊓
      centralizer (J₂ : Set (FreeAmalgam d.radical)) =
      Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    rwa [hJ₂,hJ₁]
  exact ⟨g,hg,x,hx,haw,hvw,haw',hvw',hgen₁,hgen₂,hfixed',hO₁',hO₂',
    paired_root_choice h d path hb haw hvw hlarge hnot x hxS J₁
      (Subgroup.SmallMover.join_le _ _ _ _) hgen₁ hn⟩


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

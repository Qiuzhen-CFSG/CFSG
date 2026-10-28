module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.OverlapComparison

/-!
# The shared center and the original radical overlap

In the field-sized branch the full edge center is C_U(T) times the center
of the complete fixed factor C_Q(L). The latter centralizes L and Q,
hence the entire replacement overgroup M = LQ. Therefore every actor in M
has the same displacement on the full edge center as on C_U(T).

The normalizer-selected overlaps can consequently be compared on the same
center, retaining all fixed attachments. For the literal original radical,
D = [Z(T), R intersect M] has order q, is disjoint from the full C_U(K),
and supplements it in [U,T]. Both factors are normalized by the FULL
original R, and R intersect M centralizes their product. In the unequal
case the paired center displacements are the opposite full fixed kernels.

This removes the dependence of the displaced subgroup on the chosen endpoint.
It does not identify the two normalizer actions. Excluding exchanged kernels,
radical saturation, the original Sylow branch and the degree-two restriction
remain necessary for final recognition.
Source: Meierfrankenfeld--Stellmacher (1993), (3.7), pp.872--877, especially
the fixed-part and kernel comparisons on pp.874--875.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition

private theorem fixed_center_centralizes
    {G : Type*} [Group G] (S L Q U D : Subgroup G)
    (hS : L ⊔ Q=S) (hQ : Q=U ⊔ D)
    (hU : U ≤ centralizer (Q : Set G)) (hD : D ≤ centralizer (L : Set G)) :
    D ⊓ centralizer (D : Set G) ≤ centralizer (S : Set G) := by
  have hDQ : D ≤ Q := hQ.symm ▸ le_sup_right
  apply le_centralizer_iff.mpr
  rw [←hS]
  apply sup_le (le_centralizer_iff.mp (inf_le_left.trans hD))
  rw [hQ]
  apply sup_le
  · exact hU.trans (centralizer_le (show D ⊓ centralizer (D : Set G) ≤ Q from inf_le_left.trans hDQ))
  · exact le_centralizer_iff.mp inf_le_right

private theorem center_decomposition_of_fixed_factor
    {G : Type*} [Group G] (S T Q U D : Subgroup G)
    (hT : T ≤ S) (hQT : Q ≤ T) (hQ : Q=U ⊔ D)
    (hU : U ≤ centralizer (Q : Set G))
    (hZ : T ⊓ centralizer (T : Set G) ≤ Q)
    (hD : D ⊓ centralizer (D : Set G) ≤ centralizer (S : Set G)) :
    T ⊓ centralizer (T : Set G) =
      (U ⊓ centralizer (T : Set G)) ⊔ (D ⊓ centralizer (D : Set G)) := by
  have hUQ : U ≤ Q := hQ.symm ▸ le_sup_left
  have hDQ : D ≤ Q := hQ.symm ▸ le_sup_right
  have hDT := hD.trans (centralizer_le hT)
  apply le_antisymm _ (sup_le (inf_le_inf (hUQ.trans hQT) le_rfl)
    (le_inf (inf_le_left.trans (hDQ.trans hQT)) hDT))
  intro x hx
  have hxQ := hZ hx
  rw [hQ,←SetLike.mem_coe,coe_mul_of_left_le_normalizer_right _ _
    (hU.trans (centralizer_le hDQ) |>.trans (Subgroup.centralizer_le_normalizer _))] at hxQ
  obtain ⟨u,hu,c,hc,rfl⟩ := hxQ
  have hxc : u*c ∈ centralizer (D : Set G) :=
    centralizer_le (hDQ.trans hQT) hx.2
  have hcc : c ∈ centralizer (D : Set G) :=
    (centralizer (D : Set G)).mul_mem_cancel_left (hU.trans (centralizer_le hDQ) hu) |>.mp hxc
  have hut : u ∈ centralizer (T : Set G) := by
    have hh := (centralizer (T : Set G)).mul_mem hx.2
      ((centralizer (T : Set G)).inv_mem (hDT ⟨hc,hcc⟩))
    simpa only [mul_inv_cancel_right] using hh
  exact mul_mem_sup ⟨hu,hut⟩ ⟨hc,hcc⟩

private theorem commutator_of_central_factor
    {G : Type*} [Group G] (E V C B : Subgroup G)
    (he : E=V ⊔ C) (hc : C ≤ centralizer (B : Set G))
    (hvc : V ≤ centralizer (C : Set G)) : ⁅E,B⁆=⁅V,B⁆ := by
  apply le_antisymm _ (commutator_mono (he.symm ▸ le_sup_left) le_rfl)
  apply commutator_le.mpr
  intro x hx b hb
  rw [he,←SetLike.mem_coe,coe_mul_of_left_le_normalizer_right _ _
    (hvc.trans (Subgroup.centralizer_le_normalizer _))] at hx
  obtain ⟨v,hv,c,hc',rfl⟩ := hx
  have hcb : Commute c b := (hc hc' b hb).symm
  rw [commutatorElement_mul_left_eq_conj_mul,commutatorElement_eq_one_iff_commute.mpr hcb]
  simpa only [mul_one,mul_inv_cancel,one_mul] using commutator_mem_commutator hv hb

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The whole center of the edge retains its full fixed central factor. -/
theorem replacement_field_sized_center_decomposition
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    let C := fixedCore d.radical a ⊓
      centralizer (fixedCore d.radical a : Set (FreeAmalgam d.radical))
    Q d.radical t ⊓ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) =
      (U d.radical a ⊓ centralizer (Q d.radical t : Set (FreeAmalgam d.radical))) ⊔ C ∧
    C ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  obtain ⟨i,hi,hir,hiL,hiU,hiQ⟩ :=
    Sp4Four.SourceComparison.vertex_coordinates_with_kernel d.radical
      (replacement_isPGroup h d) (replacement_core_le h d) path.start_color
  have hS : Ltilde d.radical a ⊔ Q d.radical a=stabilizer d.radical a := by
    rw [←hiL,←hiQ,←Subgroup.map_sup,replacement_residual h d,
      replacement_inner_of_positive h d g (by omega),←MonoidHom.range_eq_map,hir]
  have hQ := replacement_field_sized_Q_decomposition h d path hb hat hzt hsize
  have hU : U d.radical a ≤ centralizer (Q d.radical a : Set (FreeAmalgam d.radical)) :=
    (U_le_Z a).trans (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a path.start_color))
  have hD := fixed_center_centralizes _ _ _ _ _ hS hQ hU
    (show fixedCore d.radical a ≤ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) from inf_le_right)
  refine ⟨?_,hD⟩
  have hT : Q d.radical t ≤ stabilizer d.radical a := fun _ hx =>
    hx.2 a (adjacent_symm d.radical hat)
  have hQT : Q d.radical a ≤ Q d.radical t :=
    le_sup_left.trans_eq (replacement_field_sized_paired_edges h d path hb hat hzt hsize).1
  have hZaT : Z d.radical a ≤ Q d.radical t :=
    le_sup_right.trans_eq (replacement_field_sized_paired_edges h d path hb hat hzt hsize).2
  apply center_decomposition_of_fixed_factor _ _ _ _ _ hT hQT hQ hU _ hD
  rw [←MSCentralOrbit.C_eq_Q d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d) a path.start_color]
  exact le_inf (inf_le_left.trans hT) (inf_le_right.trans (centralizer_le hZaT))

/-- Every original-vertex actor has exactly the same displacement on the
whole shared center as on the moving root centralizer. -/
theorem replacement_field_sized_shared_center_displacement
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n)
    (B : Subgroup (FreeAmalgam d.radical)) (hB : B ≤ stabilizer d.radical a) :
    ⁅Q d.radical t ⊓ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)),B⁆ =
      ⁅U d.radical a ⊓ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)),B⁆ := by
  obtain ⟨he,hC⟩ := replacement_field_sized_center_decomposition h d path hb hat hzt hsize
  apply commutator_of_central_factor _ _ _ _ he (hC.trans (centralizer_le hB))
  have hQ : fixedCore d.radical a ⊓
      centralizer (fixedCore d.radical a : Set (FreeAmalgam d.radical)) ≤ Q d.radical a :=
    inf_le_left.trans inf_le_left
  exact (inf_le_left.trans (U_le_Z a)).trans
    ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a path.start_color)).trans
      (centralizer_le hQ))


/-- The shared-center identity on the literal replacement, for every actor
in its original overgroup. -/
theorem replacement_field_sized_radical_center_displacement
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n)
    (B : Subgroup d.overgroup) :
    ⁅d.radical ⊓ centralizer (d.radical : Set d.overgroup),B⁆ =
      ⁅⁅pCore 2 d.overgroup,K.subgroupOf d.overgroup⁆ ⊓
        centralizer (d.radical : Set d.overgroup),B⁆ := by
  obtain ⟨z,⟨path⟩⟩ := CriticalPath.exists_from (R := d.radical) (geometry := g)
    (a := alpha d.radical) rfl
  have hd : (cosetGraph d.radical).dist (alpha d.radical) z = 2 :=
    path.critical.1.trans ((g.distance_constant _ path.start_color).trans hb)
  obtain ⟨t,hat,hzt⟩ := exists_common_neighbor_of_dist_two d.radical (alpha d.radical) z hd
  have hab : Adjacent d.radical (alpha d.radical) (beta d.radical) :=
    (adjacent_iff_exists_common d.radical _ _).mpr ⟨1,Or.inl ⟨rfl,rfl⟩⟩
  obtain ⟨v,hv,hvt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical) hab hat
  let f := (MulAut.conj v⁻¹).toMonoidHom.comp (embedM d.radical)
  have hf : Function.Injective f := (MulAut.conj v⁻¹).injective.comp (embedM_injective d.radical)
  have hmT : d.radical.map f=Q d.radical t := by
    dsimp only [f]
    rw [←Subgroup.map_map,←Q_beta,←Q_act,hvt]
  have hmU : (⁅pCore 2 d.overgroup,K.subgroupOf d.overgroup⁆).map f =
      U d.radical (alpha d.radical) := by
    dsimp only [f]
    rw [←Subgroup.map_map,←core_alpha d.radical (replacement_isPGroup h d)
      (replacement_core_le h d) (replacement_residual h d),
      replacement_core_eq_U_of_distance_two h d g hb rfl,←U_act,hv]
  have hfr : f.range=stabilizer d.radical (alpha d.radical) := by
    dsimp only [f]
    rw [MonoidHom.range_comp,show (embedM d.radical).range=stabilizer d.radical (alpha d.radical)
      from (stabilizer_m_base d.radical).symm,←stabilizer_act,hv]
  apply map_injective hf
  rw [map_commutator,map_commutator,←map_inf_centralizer_of_injective f hf,
    ←map_inf_centralizer_of_injective f hf,hmT,hmU]
  exact replacement_field_sized_shared_center_displacement h d path hb hat hzt hsize
    (B.map f) (hfr ▸ map_le_range f B)

/-- The ORIGINAL radical restriction moves the whole replacement center in
an order-q complement of the entire component-fixed moving kernel. -/
theorem replacement_proper_nonsylow_center_overlap
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F),
      (S : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)) =
        (R.subgroupOf K).map (componentProjection h))
    (hne : (d.ambient.subgroupOf K).map (componentProjection h) ≠
      (R.subgroupOf K).map (componentProjection h)) :
    let U := ⁅pCore 2 d.overgroup,K.subgroupOf d.overgroup⁆
    let D := ⁅d.radical ⊓ centralizer (d.radical : Set d.overgroup),R.subgroupOf d.overgroup⁆
    Disjoint D (U ⊓ centralizer (K.subgroupOf d.overgroup : Set d.overgroup)) ∧
      Nat.card D=2^n ∧ D ≤ ⁅U,d.radical⁆ ∧
      D ⊔ (U ⊓ centralizer (K.subgroupOf d.overgroup : Set d.overgroup))=⁅U,d.radical⁆ := by
  dsimp only
  rw [replacement_field_sized_radical_center_displacement h d g hb
    (replacement_proper_nonsylow_card h d g hb hnsyl hne)]
  exact replacement_proper_nonsylow_original_overlap h d g hb hnsyl hne

/-- In the original ambient group the selected overlap is the displacement
of the FULL replacement center by R intersect M. All embeddings are literal. -/
theorem original_proper_nonsylow_center_overlap
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F),
      (S : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)) =
        (R.subgroupOf K).map (componentProjection h))
    (hne : (d.ambient.subgroupOf K).map (componentProjection h) ≠
      (R.subgroupOf K).map (componentProjection h)) :
    let U := (blockU K).map K.subtype
    let D := ⁅d.ambient ⊓ centralizer (d.ambient : Set H),R ⊓ d.overgroup⁆
    Disjoint D (U ⊓ centralizer (K : Set H)) ∧ Nat.card D=2^n ∧ D ≤ ⁅U,d.ambient⁆ ∧
      D ⊔ (U ⊓ centralizer (K : Set H))=⁅U,d.ambient⁆ := by
  let := h.component_normal
  have hperfect : IsPPerfect 2 K := by
    rw [←h.residual_eq]
    exact isPPerfect_pResidual 2
  have hmU := d.commutatorCore_eq_intrinsic_of_sup (original_sup h) hperfect
  have hmT : d.radical.map d.overgroup.subtype=d.ambient := map_subgroupOf_eq_of_le le_sup_right
  have he := congrArg (fun A : Subgroup d.overgroup => A.map d.overgroup.subtype)
    (replacement_field_sized_radical_center_displacement h d g hb
      (replacement_proper_nonsylow_card h d g hb hnsyl hne) (R.subgroupOf d.overgroup))
  rw [map_commutator,map_commutator,
    ←map_inf_centralizer_of_injective _ d.overgroup.subtype_injective,
    ←map_inf_centralizer_of_injective _ d.overgroup.subtype_injective,
    hmT,hmU,subgroupOf_map_subtype] at he
  dsimp only
  rw [he]
  exact original_proper_nonsylow_overlap_displacement h d g hb hnsyl hne

/-- In the unequal case the two opposite kernels are displacements of the
SAME full edge center under the respective original normalizer cores. -/
theorem replacement_field_sized_unequal_shared_center_actions
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n)
    (hne : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≠
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))) :
    let C := Q d.radical t ⊓ centralizer (Q d.radical t : Set (FreeAmalgam d.radical))
    let B := fun v : Vertex d.radical =>
      ((normalizer ((Q d.radical t).subgroupOf (stabilizer d.radical v) :
        Set (stabilizer d.radical v))).pCoreIn 2).map (stabilizer d.radical v).subtype
    ⁅C,B a⁆ = U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) ∧
      ⁅C,B z⁆ = U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ∧
      Disjoint ⁅C,B a⁆ ⁅C,B z⁆ ∧ ⁅C,B a⁆ ⊔ ⁅C,B z⁆=⁅Z d.radical a,Z d.radical z⁆ := by
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
  dsimp only
  rw [replacement_field_sized_shared_center_displacement h d path hb hat hzt hsize _ (map_subtype_le _),
    replacement_field_sized_shared_center_displacement h d rev hb hzt hat hsize _ (map_subtype_le _)]
  exact replacement_field_sized_unequal_paired_overlaps h d path hb hat hzt hsize hne


/-- Both complementary factors are preserved by the FULL ORIGINAL radical;
its intersection with the replacement fixes their product pointwise. -/
theorem original_proper_nonsylow_center_overlap_action
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F),
      (S : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)) =
        (R.subgroupOf K).map (componentProjection h))
    (hne : (d.ambient.subgroupOf K).map (componentProjection h) ≠
      (R.subgroupOf K).map (componentProjection h)) :
    let U := (blockU K).map K.subtype
    let D := ⁅d.ambient ⊓ centralizer (d.ambient : Set H),R ⊓ d.overgroup⁆
    let A := U ⊓ centralizer (K : Set H)
    R ≤ normalizer (D : Set H) ⊓ normalizer (A : Set H) ∧
      R ⊓ d.overgroup ≤ centralizer ((D ⊔ A : Subgroup H) : Set H) := by
  let := h.component_normal
  let := replacement_normal h d
  let := d.characteristic
  have hT : R ≤ normalizer (d.ambient : Set H) :=
    R.le_normalizer.trans (normalizer_le_normalizer_characteristic_image R d.subgroup)
  have hK : R ≤ normalizer (K : Set H) := by rw [normalizer_eq_top]; exact le_top
  have hU : R ≤ normalizer ((blockU K).map K.subtype : Set H) :=
    hK.trans (normalizer_le_normalizer_characteristic_image K (blockU K))
  dsimp only
  refine ⟨?_,?_⟩
  · intro r hr
    refine ⟨?_,?_⟩
    · apply mem_normalizer_iff_map_conj_eq.mpr
      rw [map_commutator,
        ←map_inf_centralizer_of_injective _ (MulAut.conj r).injective,
        map_inf _ _ _ (MulAut.conj r).injective,
        mem_normalizer_iff_map_conj_eq.mp (hT hr),
        mem_normalizer_iff_map_conj_eq.mp (R.le_normalizer hr),
        mem_normalizer_iff_map_conj_eq.mp (show r ∈ normalizer (d.overgroup : Set H) by
          rw [normalizer_eq_top]; trivial)]
    · apply mem_normalizer_iff_map_conj_eq.mpr
      rw [←map_inf_centralizer_of_injective _ (MulAut.conj r).injective,
        mem_normalizer_iff_map_conj_eq.mp (hU hr),
        mem_normalizer_iff_map_conj_eq.mp (hK hr)]
  · rw [(original_proper_nonsylow_center_overlap h d g hb hnsyl hne).2.2.2]
    have hh := (replacement_proper_nonsylow_original_action h d g hb hnsyl hne).2
    rw [replacement_field_sized_original_moving_inf_frattini h d g hb
      (replacement_proper_nonsylow_card h d g hb hnsyl hne)] at hh
    exact hh

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition

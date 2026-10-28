module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StrictIndexIntersection
public import Theory.GroupTheory.ConjugateSpanNilpotent

/-!
# Exact R₃ and its smaller-mover centralizer on the selected path

The full H₂-centralizer preserves T₂ modulo the entire Q_c kernel: equality
of whole-U displacements gives equality of fixed subgroups, and the actual
critical witness saturates the field-sized image. If the smaller second
span joined with Z_c were locally normal, the simple quotient would fix it
modulo its Q_c-displacement and Z_c. Nilpotent span collapse would then
identify it with the original neighboring seed joined with Z_c. Its order
bound puts that seed in B_c, contrary to the same selected witness.

This nonnormality supplies the full-cover hyperplane bound |R₃| ≤ q.
Together with the existing lower bound it gives |R₃| = q. One conjugate
under the original whole-H₂ centralizer already has the entire commutator,
on both Z and U. Its U-fixed index and the literal image of A₀ modulo its
vertex kernel are both q. The maximum small-mover join at the transformed
original edge centralizes all of R₃, including its central attachment.
The simultaneous source selector retains both second spans, every overlap,
the original field degree and the whole quotient kernels.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3), (5.4), and (5.9), printed pp.866--867, 915 and 921.
The two smaller-mover branches proving R₃ ≤ D_c, the displacement
comparison, strict-index contradiction, later terminal exclusions and actual
minimum-replacement distance-two witness remain required. The independent
original-radical characteristic-control gap is unchanged.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.StrictIndex
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The centralizer of a saturated field-sized displacement preserves the
actor's full image preimage, with its entire Q-kernel. -/
theorem Input.replacement_field_displacement_normalizes_image
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a : Vertex d.radical} (ha : color d.radical a=false)
    (T : Subgroup (FreeAmalgam d.radical)) (hTS : T ≤ stabilizer d.radical a)
    (hi : (centralizer (T : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) ≤ Nat.card F)
    (hlo : Nat.card F ≤ (Q d.radical a).relIndex T) :
    stabilizer d.radical a ⊓ centralizer ((⁅U d.radical a,T⁆ :
      Subgroup (FreeAmalgam d.radical)) : Set _) ≤
      normalizer ((T ⊔ Q d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
  apply le_normalizer_iff.mpr
  rintro g ⟨hg,hgc⟩ x hx
  let Tg := T.map (MulAut.conj g).toMonoidHom
  have hTgS : Tg ≤ stabilizer d.radical a := by
    rw [←mem_normalizer_iff_map_conj_eq.mp ((stabilizer d.radical a).le_normalizer hg)]
    exact map_mono hTS
  have he : ⁅U d.radical a,Tg⁆=⁅U d.radical a,T⁆ := by
    have hh := mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.centralizer_le_normalizer _) hgc)
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp (U_normalized a hg)] at hh
    exact hh
  have hf := h.replacement_moving_fixed_antitone_of_commutator_le d geometry hb ha
    Tg T hTgS hTS (by rw [commutator_comm Tg,commutator_comm T]; exact he.le)
  have hfix : U d.radical a ⊓ centralizer ((T ⊔ Tg : Subgroup (FreeAmalgam d.radical)) : Set _) =
      U d.radical a ⊓ centralizer (T : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm (inf_le_inf_left _ (centralizer_le (show T ≤ T ⊔ Tg from le_sup_left)))
    apply le_inf inf_le_left
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp inf_le_right)
      (le_centralizer_iff.mp (hf.trans inf_le_right))
  have hsmall : (centralizer ((T ⊔ Tg : Subgroup (FreeAmalgam d.radical)) : Set _)).relIndex
      (U d.radical a) ≤ Nat.card F := by
    rw [←inf_relIndex_left,hfix,inf_relIndex_left]
    exact hi
  have hs := (h.replacement_field_index_actor_saturates d geometry hb ha T (T ⊔ Tg)
    le_sup_left (sup_le hTS hTgS) hsmall hlo).1
  have hm : (T ⊔ Q d.radical a).map (MulAut.conj g).toMonoidHom ≤ T ⊔ Q d.radical a := by
    rw [Subgroup.map_sup,MulEquiv.toMonoidHom_eq_coe,mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a hg)]
    exact sup_le ((le_sup_right.trans le_sup_left).trans_eq hs.symm) le_sup_right
  exact hm (mem_map_of_mem (MulAut.conj g).toMonoidHom hx)

omit h in
private theorem normal_span_eq_seed_of_kernel_escape
    {G S : Type*} [Group G] [Group S] [IsSimpleGroup S]
    (V C Q Z T G₀ : Subgroup G) [Finite G₀]
    (q : G₀ →* S) (hq : Function.Surjective q) (hk : q.ker=Q.subgroupOf G₀)
    (hQ : IsPGroup 2 Q) (hQG : Q ≤ G₀) (hVQ : V ≤ Q) (hZV : Z ≤ V)
    (hCG : C ≤ G₀) (hTG : T ≤ G₀) (hTQ : ¬ T ≤ Q)
    (hGQ : G₀ ≤ normalizer (Q : Set G)) (hGZ : G₀ ≤ normalizer (Z : Set G))
    (hQV : Q ≤ normalizer (V : Set G))
    (hCT : C ≤ normalizer ((T ⊔ Q : Subgroup G) : Set G))
    (hVT : ⁅V,T⁆ ≤ Z)
    (hGW : G₀ ≤ normalizer (conjugateSpanBy V C : Set G))
    (hgen : (pResidual 2 G₀).map G₀.subtype ⊔ Q=G₀) :
    conjugateSpanBy V C=V := by
  let W := conjugateSpanBy V C
  let D := ⁅W,Q⁆ ⊔ Z
  have hWQ : W ≤ Q := conjugateSpanBy_le hVQ (hCG.trans hGQ)
  have hWG : W ≤ G₀ := hWQ.trans hQG
  have hGD : G₀ ≤ normalizer (D : Set G) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq,Subgroup.map_sup,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hGW hg),
      mem_normalizer_iff_map_conj_eq.mp (hGQ hg),
      mem_normalizer_iff_map_conj_eq.mp (hGZ hg)]
  have hVall : ⁅V,T ⊔ Q⁆ ≤ D := by
    rw [commutator_comm]
    exact commutator_sup_le_of_relative_normal G₀ T Q V D hGD hTG hQG
      (by rw [commutator_comm]; exact hVT.trans le_sup_right)
      (by rw [commutator_comm]; exact
        (commutator_mono (le_conjugateSpanBy V C) le_rfl).trans le_sup_left)
  have hWall : ⁅W,T ⊔ Q⁆ ≤ D := by
    rw [show W=⨆ g : C, V.map (MulAut.conj (g : G)).toMonoidHom from
      conjugateSpanBy_eq_iSup_conj V C]
    apply commutator_iSup_le_of_relative_normal G₀ (T ⊔ Q) D _ hGD
    · intro g
      rw [←mem_normalizer_iff_map_conj_eq.mp (G₀.le_normalizer (hCG g.property))]
      exact map_mono (hVQ.trans hQG)
    · intro g
      have hh := map_mono (f := (MulAut.conj (g : G)).toMonoidHom) hVall
      rwa [map_commutator,MulEquiv.toMonoidHom_eq_coe,mem_normalizer_iff_map_conj_eq.mp (hCT g.property),
        mem_normalizer_iff_map_conj_eq.mp (hGD (hCG g.property))] at hh
  have hWT : ⁅W,T⁆ ≤ D := (commutator_mono le_rfl le_sup_left).trans hWall
  let W₀ := W.subgroupOf G₀
  let D₀ := D.subgroupOf G₀
  let T₀ := T.subgroupOf G₀
  let : W₀.Normal := normal_subgroupOf_of_le_normalizer hGW
  let : D₀.Normal := normal_subgroupOf_of_le_normalizer hGD
  have hp : IsPGroup 2 q.ker := by rw [hk]; exact hQ.comap_subtype
  have hnot : ¬ T₀ ≤ q.ker := by
    intro hh
    apply hTQ
    intro t ht
    have hh' := hh (show (⟨t,hTG ht⟩ : G₀) ∈ T₀ from ht)
    rwa [hk] at hh'
  have hcomm : ⁅W₀,T₀⁆ ≤ D₀ := commutator_le.mpr fun _ hw _ ht =>
    hWT (commutator_mem_commutator hw ht)
  have hh := map_mono (f := G₀.subtype)
    (commutator_pResidual_le_of_simple_kernel_escape 2 q hq hp W₀ D₀ T₀ hnot hcomm)
  rw [map_commutator,map_subgroupOf_eq_of_le hWG] at hh
  have hWL : ⁅W,(pResidual 2 G₀).map G₀.subtype⁆ ≤ D := hh.trans (map_comap_le _ _)
  let : Finite Q := Finite.of_injective (inclusion hQG) (inclusion_injective _)
  exact conjugateSpanBy_eq_of_nilpotent_local_generation V C Q Z
    ((pResidual 2 G₀).map G₀.subtype) G₀ hQ.isNilpotent hWQ hQV hZV hCG hgen hGW hGQ hGZ hWL

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic


namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem strict_span_not_normalized
    {geometry : Geometry d.radical} {a z e : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hsmall : (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)) ≤ Nat.card F)
    (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical (path.walk.getVert 2))
    (selected : CriticalPath d.radical geometry (path.walk.getVert 2) e)
    (hi : (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical e)=Nat.card F)
    (hnotB : ¬ Z d.radical (act d.radical y a) ≤
      B d.radical (path.walk.getVert 2) (geometry.Z_normal _))
    (hgen : (stabilizer d.radical (path.walk.getVert 2) ⊓ centralizer
      (conjugatedKernelCommutator geometry a (path.walk.getVert 2) y : Set (FreeAmalgam d.radical))) ⊔
      Z d.radical e=stabilizer d.radical (path.walk.getVert 2)) :
    let c := path.walk.getVert 2
    let mu := act d.radical y a
    let C₀ := stabilizer d.radical c ⊓ centralizer
      (conjugatedKernelCommutator geometry a c y : Set (FreeAmalgam d.radical))
    ¬ Z d.radical e ≤ normalizer
      ((conjugateSpanBy (Z d.radical mu) C₀ ⊔ Z d.radical c : Subgroup (FreeAmalgam d.radical)) : Set _) := by
  dsimp only
  let c := path.walk.getVert 2
  let mu := act d.radical y a
  let T₀ := kernelCentralizer geometry a c
  let T₂ := T₀.map (MulAut.conj y⁻¹).toMonoidHom
  let H₂ := conjugatedKernelCommutator geometry a c y
  let C₀ := stabilizer d.radical c ⊓ centralizer (H₂ : Set (FreeAmalgam d.radical))
  let J := Z d.radical mu ⊔ Z d.radical c
  let W := conjugateSpanBy J C₀
  have hc := selected.start_color
  have hmu : color d.radical mu=false := by rw [action_preserves_color]; exact path.start_color
  have hdist : (cosetGraph d.radical).dist mu c=2 := by
    have hh := dist_act d.radical y a c
    rw [show act d.radical y c=c from hy] at hh
    exact hh.trans (path.dist_start (by rw [path.length_eq_b]; omega))
  obtain ⟨t,hmut,hct⟩ := exists_common_neighbor_of_dist_two d.radical mu c hdist
  have hJV : J ≤ V d.radical c := by
    rw [show J=Z d.radical mu ⊔ Z d.radical c from rfl]
    exact neighbor_seed_join_le_radius hct hmut
  have hQcS : Q d.radical c ≤ stabilizer d.radical c := fun _ hx => hx.1
  have hQSmu : Q d.radical c ≤ stabilizer d.radical mu :=
    Q_le_stabilizer_of_dist_le_two c mu hc hmu (by rw [SimpleGraph.dist_comm]; exact hdist.le)
  have hQJ : Q d.radical c ≤ normalizer (J : Set (FreeAmalgam d.radical)) :=
    (le_inf (hQSmu.trans (Z_normalized d.radical mu))
      (hQcS.trans (Z_normalized d.radical c))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hW : W=conjugateSpanBy (Z d.radical mu) C₀ ⊔ Z d.radical c := by
    apply le_antisymm
    · apply conjugateSpanBy_le (sup_le (le_conjugateSpanBy _ _ |>.trans le_sup_left) le_sup_right)
      exact (le_inf (le_normalizer_conjugateSpanBy _ _)
        (inf_le_left.trans (Z_normalized d.radical c))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · exact sup_le (conjugateSpanBy_mono le_sup_left le_rfl)
        (le_sup_right.trans (le_conjugateSpanBy _ _))
  intro hnorm
  have hGW : stabilizer d.radical c ≤ normalizer (W : Set (FreeAmalgam d.radical)) := by
    rw [←hgen]
    exact sup_le (le_normalizer_conjugateSpanBy _ _) (hW ▸ hnorm)
  have hTS : T₀ ≤ stabilizer d.radical c := by
    exact inf_le_left.trans (Q_le_stabilizer_of_dist_le_two a c path.start_color hc
      (by exact (path.dist_start (by rw [path.length_eq_b]; omega)).le))
  have hTsmall := (kernelCentralizer_moving_index_le geometry a c).trans hsmall
  obtain ⟨v,back,_,hvT⟩ := h.replacement_kernelCentralizer_critical_witness d path hb.le
  let := finite_stabilizer d.radical c
  let : Finite T₀ := Finite.of_injective (inclusion hTS) (inclusion_injective _)
  have hTlo : Nat.card F ≤ (Q d.radical c).relIndex T₀ :=
    (h.replacement_critical_indices_ge_field d back (by omega)).1.trans
      (relIndex_le_of_le_right hvT (by
        change Nat.card (T₀ ⧸ (Q d.radical c).subgroupOf T₀) ≠ 0
        exact Nat.card_pos.ne'))
  have hmapU : (U d.radical c).map (MulAut.conj y⁻¹).toMonoidHom=U d.radical c := by
    rw [←U_act,show act d.radical y c=c from hy]
  have hmapQ : (Q d.radical c).map (MulAut.conj y⁻¹).toMonoidHom=Q d.radical c := by
    rw [←Q_act,show act d.radical y c=c from hy]
  have hT₂small : (centralizer (T₂ : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical c) ≤ Nat.card F := by
    rw [←hmapU,Subgroup.SmallMover.centralizer_index_map _ (MulAut.conj y⁻¹).injective]
    exact hTsmall
  have hT₂lo : Nat.card F ≤ (Q d.radical c).relIndex T₂ := by
    rw [←hmapQ,relIndex_map_map_of_injective _ _ (MulAut.conj y⁻¹).injective]
    exact hTlo
  have hT₂S := kernelCentralizer_conjugate_le_stabilizer geometry path (by omega) y hy
  obtain ⟨hT,hH,_,_,_,_,_,_,_,_⟩ := h.replacement_strict_index_conjugated_span d path hb hsmall y hy
  have hCT : C₀ ≤ normalizer ((T₂ ⊔ Q d.radical c : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    have hh := h.replacement_field_displacement_normalizes_image d geometry hb.le hc T₂ hT₂S hT₂small hT₂lo
    have he : ⁅U d.radical c,T₂⁆=H₂ := by
      change ⁅U d.radical c,(kernelCentralizer geometry a c).map (MulAut.conj y⁻¹).toMonoidHom⁆=_
      rw [←hT]; exact hH
    rwa [he] at hh
  have hT₂Qmu : T₂ ≤ Q d.radical mu := by
    change (kernelCentralizer geometry a c).map (MulAut.conj y⁻¹).toMonoidHom ≤ _
    rw [←hT]
    exact inf_le_left
  have hJdisp : ⁅J,T₂⁆ ≤ Z d.radical c :=
    commutator_sup_le_of_relative_normal (stabilizer d.radical c)
      (Z d.radical mu) (Z d.radical c) T₂ (Z d.radical c)
      (Z_normalized d.radical c)
      ((le_sup_left.trans hJV).trans ((geometry.V_le_Q (by omega) c hc).trans hQcS))
      (Z_le_stabilizer d.radical c)
      ((commutator_mono le_rfl hT₂Qmu).trans (geometry.centralizes mu hmu).le |>.trans bot_le)
      (le_normalizer_iff_commutator_le_left.mp (hT₂S.trans (Z_normalized d.radical c)))
  obtain ⟨E,hE,f,hf,hfQ,_⟩ := h.replacement_inner_natural_action d geometry hb.le hc
  have hlarge : 3 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact (by decide : 3 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
  let := Theory.SpecificGroups.SymplecticFour.SimpleQuotients.isSimpleGroup hlarge
  let : IsSimpleGroup (Sp E.Carrier) :=
    Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.isSimpleGroup
  have hk : f.ker=(Q d.radical c).subgroupOf (stabilizer d.radical c) := by
    apply map_injective (stabilizer d.radical c).subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le hQcS]
  have hlocal : Ltilde d.radical c ⊔ Q d.radical c=stabilizer d.radical c := by
    obtain ⟨i,hinj,hir,hiL,hiU,hiQ⟩ := Sp4Four.SourceComparison.vertex_coordinates_with_kernel d.radical
      (h.replacement_two_group d) (h.replacement_core_le d) hc
    rw [←hiL,←hiQ,←Subgroup.map_sup,h.replacement_residual d,
      h.replacement_inner_of_four_le d geometry hb.le,←MonoidHom.range_eq_map,hir]
  have hne : ¬ T₂ ≤ Q d.radical c := by
    intro hh
    rw [relIndex_eq_one.mpr hh] at hT₂lo
    have hq : 1 < Nat.card F := Finite.one_lt_card
    omega
  have hcollapse := normal_span_eq_seed_of_kernel_escape J C₀ (Q d.radical c) (Z d.radical c)
    T₂ (stabilizer d.radical c) f hf hk
    (Q_isPGroup d.radical (h.replacement_two_group d) (h.replacement_core_le d) c hc)
    hQcS (hJV.trans (geometry.V_le_Q (by omega) c hc)) le_sup_right inf_le_left hT₂S hne
    (Q_normalized d.radical c) (Z_normalized d.radical c) hQJ hCT hJdisp hGW hlocal
  have hJN : stabilizer d.radical c ≤ normalizer (J : Set (FreeAmalgam d.radical)) := hcollapse ▸ hGW
  have hidx := (neighbor_seed_join_index_le geometry (by omega) hc hct hmut).trans
    (h.replacement_root_neighbor_seed_index_le_cube d selected hb.le hct hmut (by
      rw [hi]; have hq : 1 < Nat.card F := Finite.one_lt_card; nlinarith))
  have hJB := h.replacement_small_radius_le_B d geometry (by omega) hc J hJV
    ((Ltilde_le_stabilizer c).trans hJN) (hidx.trans_lt (by
      exact pow_lt_pow_right₀ Finite.one_lt_card (by decide : 3 < 4)))
  exact hnotB (le_sup_left.trans hJB)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open ChapterB.QuasisimpleSource MSCentralOrbit
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem radius_intersection_card_le_field
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (Y₀ : Subgroup (FreeAmalgam d.radical))
    (hYV : Y₀ ⊔ Z d.radical a ≤ V d.radical a)
    (hYtr : Y₀ ⊔ Z d.radical a ≤ V d.radical a ⊓ Q d.radical (path.walk.getVert (path.walk.length-2)))
    (hAn : X d.radical z ⊓ Q d.radical a ≤ normalizer
      ((Y₀ ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hn : ¬ Z d.radical z ≤ normalizer
      ((Y₀ ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hi : (Q d.radical z).relIndex (Z d.radical a)=Nat.card F)
    (hi' : (Q d.radical a).relIndex (Z d.radical z)=Nat.card F) :
    Nat.card (⁅Y₀,X d.radical z ⊓ Q d.radical a⁆ : Subgroup (FreeAmalgam d.radical)) ≤ Nat.card F := by
  let Y := Y₀ ⊔ Z d.radical a
  let A := X d.radical z ⊓ Q d.radical a
  have hYQ : Y ≤ Q d.radical a := hYV.trans (geometry.V_le_Q (by omega) a path.start_color)
  have hYS : Y ≤ stabilizer d.radical z := hYtr.trans
    (truncated_radius_le_endpoint_stabilizer path (by omega))
  have hsmall : (Q d.radical z).relIndex (Z d.radical a) < Nat.card F^2 := by
    rw [hi]; have hq : 1 < Nat.card F := Finite.one_lt_card; nlinarith
  have hCa := MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) a path.start_color
  have hUS : U d.radical z ≤ stabilizer d.radical a :=
    (U_le_Z z).trans (path.endpoint_Z_le_start_stabilizer (by omega))
  have hAU : U d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) =
      U d.radical z ⊓ Q d.radical a := by
    rw [←hCa]
    ext x
    exact ⟨fun hx => ⟨hx.1,hUS hx.1,hx.2⟩,fun hx => ⟨hx.1,hx.2.2⟩⟩
  have hZX : Z d.radical z ≤ X d.radical z := geometry.omega_bound z path.end_color
    (by rw [geometry.distance_constant z path.end_color]; exact lt_of_lt_of_le (by decide : 0 < 4) hb)
  have hUA : U d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) ≤ A := by
    rw [hAU]
    exact inf_le_inf ((U_le_Z z).trans hZX) le_rfl
  have hquad : ⁅⁅A,Y⁆,Y⁆=⊥ := le_bot_iff.mp
    ((commutator_mono (commutator_mono le_rfl hYtr) hYtr).trans_eq
      (h.replacement_radius_commutator_bounds d geometry hb path.start_color z
        (path.walk.getVert (path.walk.length-2))).2)
  have hpos : 0 < geometry.b d.radical := by omega
  let rev : CriticalPath d.radical geometry z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical geometry
        (MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
          (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d))
        a path.start_color (by rwa [geometry.distance_constant a path.start_color]) z path.end_color path.critical }
  let D := X d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))
  have hsplit : X d.radical z=U d.radical z ⊔ D :=
    h.replacement_root_X_decomposition_center d rev hb hsmall
  have hDY : D ≤ centralizer (Y : Set (FreeAmalgam d.radical)) :=
    inf_le_right.trans (centralizer_le hYS)
  have hbadU : ¬ U d.radical z ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
    intro hh
    exact hn (hZX.trans (hsplit ▸ sup_le hh (hDY.trans (Subgroup.centralizer_le_normalizer _))))
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let C := (K.subgroupOf d.overgroup).map q
  let : C.Normal := (h.replacement_component_image_structure d).2.1
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 d.overgroup)) := omegaCenterIn_elementary _
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 d.overgroup)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩ :=
    h.replacement_ambient_initial_cover_at_vertex d path.end_color
  have hFc : Nat.card E.Carrier=Nat.card F := by rw [E.card_eq,hE,h.field_card]
  have hFl : 2 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact (by decide : 2 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hCtop : C=⊤ := by
    have hh : C.comap q=⊤ := by
      rw [show C=(K.subgroupOf d.overgroup).map q from rfl,comap_map_eq,QuotientGroup.ker_mk']
      exact h.replacement_inner_of_four_le d geometry hb
    rw [←map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) C,hh,
      ←MonoidHom.range_eq_map,MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  let κC := κ.codRestrict C (fun x => hCtop ▸ mem_top (κ x))
  let β := (e.groupEquiv.toMonoidHom.comp κC).comp (inclusion hYS)
  let σ := MovedSection.coverAction s e
  let p := MovedSection.coverProjection s e
  have hact (y : Y) (w : s.space.toSubmodule) : j (Multiplicative.ofAdd (σ (β y) w))=
      y.val*j (Multiplicative.ofAdd w)*y.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC (inclusion hYS y)))) w))=_
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj (inclusion hYS y) w
  let βT := β.comp (inclusion (show Z d.radical a ≤ Y from le_sup_right))
  have hcard : Nat.card βT.range=Nat.card E.Carrier := by
    have hmark : βT.ker=(Q d.radical z).subgroupOf (Z d.radical a) := by
      ext x
      change e.groupEquiv (κC (inclusion hYS (inclusion le_sup_right x)))=1 ↔ x.val ∈ Q d.radical z
      rw [e.groupEquiv.map_eq_one_iff]
      have heq : κC (inclusion hYS (inclusion le_sup_right x))=1 ↔
          inclusion hYS (inclusion le_sup_right x) ∈ κ.ker := Subtype.ext_iff
      rw [heq]
      constructor
      · intro hx
        exact hκQ ▸ mem_map_of_mem (stabilizer d.radical z).subtype hx
      · intro hx
        obtain ⟨y,hy,hyx⟩ := hκQ.symm ▸ hx
        have he : y=inclusion hYS (inclusion le_sup_right x) := Subtype.ext hyx
        exact he ▸ hy
    rw [←index_ker,hmark]
    exact hi.trans hFc.symm
  have hactT (x : Z d.radical a) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (σ (βT x) w))=x.val*j (Multiplicative.ofAdd w)*x.val⁻¹ :=
    hact (inclusion le_sup_right x) w
  obtain ⟨hd,hrootquad⟩ := critical_root_coordinates_of_reciprocal_index_field path hpos hCa hFl
    σ p he j hj hjr βT hactT hcard (hi'.trans hFc.symm)
  have hcomm : ⁅Z d.radical a,j.range⁆ ≤ Z d.radical a := by
    rw [hjr]
    exact (commutator_mono le_rfl (U_le_Z z)).trans (critical_commutator_le_start_seed path)
  have hcent : Y ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    hYQ.trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a path.start_color)))
  have hbound := HyperplaneMovement.embedded_root_hyperplane_bound hFl p he j hj Y
    (Z d.radical a) le_sup_right β hact hcard hd hrootquad hcomm hcent
    (by rw [hjr]; exact le_bot_iff.mp ((commutator_mono (commutator_mono hUA le_rfl) le_rfl).trans_eq hquad))
    (by rw [hjr]; exact hUA.trans hAn) (by rwa [hjr])
  rw [hjr,hFc] at hbound
  have hle : ⁅Y₀,A⁆ ≤
      ⁅Y,U d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical))⁆ := by
    rw [(h.replacement_root_intersection_fixed_and_commutator d path hb hsmall Y₀
      (le_sup_left.trans hYS)).1, hAU]
    exact commutator_mono le_sup_left le_rfl
  let := finite_Z d.radical z
  let : Finite (U d.radical z) := Finite.of_injective (inclusion (U_le_Z z)) (inclusion_injective _)
  have hCU : ⁅Y,U d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical))⁆ ≤ U d.radical z := by
    rw [commutator_comm]
    exact (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hYS.trans (U_normalized z)))
  let : Finite (⁅Y,U d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical))⁆ :
      Subgroup (FreeAmalgam d.radical)) := Finite.of_injective (inclusion hCU) (inclusion_injective _)
  exact (Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective _)).trans hbound
end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The actual small-mover join fixes the whole field-sized displacement,
including its central attachment. -/
theorem Input.replacement_small_mover_join_centralizes_field_displacement
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t)
    (A : Subgroup (FreeAmalgam d.radical)) (hAT : A ≤ Q d.radical t)
    (hsmall : (centralizer (A : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) ≤ Nat.card F) :
    ⁅U d.radical a,A⁆ ≤ centralizer
      (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical)) := by
  obtain ⟨E,hE,f,hf,hfQ,hTf,hidx⟩ := h.replacement_small_mover_coordinates d geometry hb ha hat
  have hcard : Nat.card E.Carrier = Nat.card F := by rw [E.card_eq,hE,h.field_card]
  let S := stabilizer d.radical a
  let U₀ := (U d.radical a).subgroupOf S
  let T := (Q d.radical t).subgroupOf S
  let A₀ := A.subgroupOf S
  let := finite_stabilizer d.radical a
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  have hTS : Q d.radical t ≤ S := by
    change Q d.radical t ≤ stabilizer d.radical a
    rw [←hjr,←hjR]
    exact map_le_range j _
  have hQT : Q d.radical a ≤ Q d.radical t := by
    rw [←hjQ,←hjR]
    exact map_mono (h.replacement_core_le d)
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer d.radical a)
  have hQeq : f.ker = (Q d.radical a).subgroupOf S := by
    apply map_injective S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le (show Q d.radical a ≤ S from fun _ hx => hx.1)]
  have hkT : f.ker ≤ T := by rw [hQeq]; exact comap_mono hQT
  have hUK : U₀ ≤ centralizer (f.ker : Set S) := by
    intro u hu k hk
    apply Subtype.val_injective
    have hkQ : k.val ∈ Q d.radical a := hfQ ▸ mem_map_of_mem S.subtype hk
    exact ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a ha))
      (U_le_Z a hu) k.val hkQ)
  have hiA : (centralizer (A₀ : Set S)).relIndex U₀ ≤ Nat.card E.Carrier := by
    rw [←Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective U₀ A₀,
      map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le (hAT.trans hTS),hcard]
    exact hsmall
  have hc := Degree.Quotient.join_image_centralizes_field_actor U₀ T f unipotent.subtype
    Subtype.val_injective hkT hUK (by simpa only [range_subtype] using hTf)
    hidx A₀ (comap_mono hAT) hiA
  have hn : Subgroup.SmallMover.join U₀ f.ker T (Nat.card E.Carrier^2) ≤
      normalizer ((A₀ ⊔ f.ker : Subgroup S) : Set S) := by
    have hh := (map_le_iff_le_comap.mp hc).trans
      ((comap_mono (Subgroup.centralizer_le_normalizer _)).trans (le_normalizer_comap f))
    rwa [comap_map_eq] at hh
  have hm := (map_mono (f := S.subtype) hn).trans
    (le_normalizer_map S.subtype)
  rw [Subgroup.SmallMover.join_map S.subtype S.subtype_injective,
    map_subgroupOf_eq_of_le hUS,hfQ,map_subgroupOf_eq_of_le hTS,
    Subgroup.map_sup,map_subgroupOf_eq_of_le (hAT.trans hTS),hfQ,hcard] at hm
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  have hJS : J ≤ S := (Subgroup.SmallMover.join_le _ _ _ _).trans hTS
  have hQtwo : IsPGroup 2 (Q d.radical t) := by
    rw [←hjR]
    exact (h.replacement_two_group d).map j
  have hJtwo : IsPGroup 2 J := hQtwo.to_le (Subgroup.SmallMover.join_le _ _ _ _)
  have hTsmall : (centralizer ((A ⊔ Q d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)).relIndex
      (U d.radical a) ≤ Nat.card F := by
    rw [sup_comm A,←inf_relIndex_left,Subgroup.SmallMover.fixed_inf_sup,
      inf_relIndex_left]
    · exact hsmall
    · exact (U_le_Z a).trans (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a ha))
  have hh := h.replacement_two_normalizer_centralizes_field_displacement d geometry hb ha
    (A ⊔ Q d.radical a) J (sup_le (hAT.trans hTS) (fun _ hx => hx.1))
    hJS hJtwo hm hTsmall
  exact le_centralizer_iff.mp (hh.trans (centralizer_le (commutator_mono le_rfl le_sup_left)))

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The same source selection has exact R₃ of order q, realized by one
conjugate. Both local indices are q, and the smaller-mover join on the
literal transformed original edge centralizes the complete R₃. -/
theorem Input.replacement_strict_index_selected_field_intersection
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hsmall : (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)) ≤ Nat.card F) :
    (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2))=Nat.card F ∧
    ∃ y ∈ stabilizer d.radical (path.walk.getVert 2),
    let c := path.walk.getVert 2
    let mu := act d.radical y a
    let T₂ := (kernelCentralizer geometry a c).map (MulAut.conj y⁻¹).toMonoidHom
    let H₂ := conjugatedKernelCommutator geometry a c y
    let C₀ := stabilizer d.radical c ⊓ centralizer (H₂ : Set (FreeAmalgam d.radical))
    let Z₀ := conjugateSpanBy (Z d.radical mu) C₀
    let W := sourceCentralizerSpan d.radical c mu H₂
    ¬ Z d.radical mu ≤ B d.radical c (geometry.Z_normal c) ∧
    ¬ T₂ ≤ Q d.radical c ∧
    ¬ H₂ ≤ centralizer (V d.radical z : Set (FreeAmalgam d.radical)) ∧
    ∃ e, ∃ selected : CriticalPath d.radical geometry c e,
      (cosetGraph d.radical).dist e z=2 ∧
      (∀ i ≤ path.walk.length-2, selected.walk.getVert i=path.walk.getVert (i+2)) ∧
      ¬ H₂ ≤ centralizer (Z d.radical e : Set (FreeAmalgam d.radical)) ∧
      C₀ ⊔ Z d.radical e=stabilizer d.radical c ∧
      Z₀ ≤ W ∧ W ≤ Q d.radical c ∧
      W ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) ∧ W ≤ Q d.radical z ∧
      (Q d.radical e).relIndex (Z d.radical c)=Nat.card F ∧
      (Q d.radical c).relIndex (Z d.radical e)=Nat.card F ∧
      let A₀ := X d.radical e ⊓ Q d.radical c
      let R₃ := ⁅Z₀,A₀⁆
      ¬ ⁅Z₀,Z d.radical e⁆ ≤ Z d.radical c ∧
      R₃ ≠ ⊥ ∧ Nat.card F ≤ Nat.card R₃ ∧
      R₃=⁅Z₀,U d.radical e ⊓ Q d.radical c⁆ ∧
      R₃ ≤ Z₀ ⊓ U d.radical e ∧
      ¬ Z d.radical e ≤ normalizer ((Z₀ ⊔ Z d.radical c : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      Nat.card R₃=Nat.card F ∧
      R₃ ≤ centralizer (V d.radical c : Set (FreeAmalgam d.radical)) ∧
      ∃ t ∈ C₀, ⁅Z d.radical (act d.radical t mu),A₀⁆=R₃ ∧
        ⁅U d.radical (act d.radical t mu),A₀⁆=R₃ ∧
        (centralizer (A₀ : Set (FreeAmalgam d.radical))).relIndex
          (U d.radical (act d.radical t mu))=Nat.card F ∧
        (Q d.radical (act d.radical t mu)).relIndex A₀=Nat.card F ∧
        R₃ ≤ centralizer (Subgroup.SmallMover.join
          (U d.radical (act d.radical t mu)) (Q d.radical (act d.radical t mu))
          (Q d.radical (act d.radical t (act d.radical y (path.walk.getVert 1))))
          (Nat.card F^2) : Set (FreeAmalgam d.radical)) := by
  obtain ⟨hi,y,hy,hnotB,hT,hmove,e,selected,hez,hover,hmoveE,hgen,hZW,hWQ,hWp,hWz,
      hic,hie,hbad,hne,hcard,heq,hRU,t,ht,htne⟩ :=
    h.replacement_strict_index_selected_intersection d path hb hsmall
  let c := path.walk.getVert 2
  let mu := act d.radical y a
  let H₂ := conjugatedKernelCommutator geometry a c y
  let C₀ := stabilizer d.radical c ⊓ centralizer (H₂ : Set (FreeAmalgam d.radical))
  let Z₀ := conjugateSpanBy (Z d.radical mu) C₀
  let A₀ := X d.radical e ⊓ Q d.radical c
  have hc := selected.start_color
  have hdist : (cosetGraph d.radical).dist mu c=2 := by
    have hh := dist_act d.radical y a c
    rw [show act d.radical y c=c from hy] at hh
    exact hh.trans (path.dist_start (by rw [path.length_eq_b]; omega))
  have hZmuV : Z d.radical mu ≤ V d.radical c :=
    le_iSup_of_le _ (le_iSup_of_le hdist.le le_rfl)
  have hZV : Z₀ ≤ V d.radical c := conjugateSpanBy_le hZmuV
    (inf_le_left.trans (DistanceEight.V_normalized d.radical c))
  have hlen : selected.walk.length=path.walk.length := by rw [selected.length_eq_b,path.length_eq_b]
  have hpen : selected.walk.getVert (selected.walk.length-2)=z := by
    rw [hlen,hover _ le_rfl,show path.walk.length-2+2=path.walk.length by
      have he := path.length_eq_b; omega,SimpleGraph.Walk.getVert_length]
  have hZcQ : Z d.radical c ≤ Q d.radical z := by
    apply Z_le_Q_of_dist_lt d.radical c (geometry.exists_critical c hc)
    rw [geometry.distance_constant c hc,←hpen,selected.dist_start (Nat.sub_le _ _),selected.length_eq_b]
    change geometry.b d.radical-2 < geometry.b d.radical
    omega
  have hJtr : Z₀ ⊔ Z d.radical c ≤ V d.radical c ⊓
      Q d.radical (selected.walk.getVert (selected.walk.length-2)) := by
    rw [hpen]
    exact le_inf (sup_le hZV (Z_le_VBall d.radical c 2))
      (sup_le (hZW.trans hWz) hZcQ)
  obtain ⟨_,_,_,_,_,_,_,_,hH₂Z,_⟩ :=
    h.replacement_strict_index_conjugated_span d path hb hsmall y hy
  have hQC : Q d.radical c ≤ C₀ := le_inf (fun _ hx => hx.1)
    ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes c hc))).trans (centralizer_le hH₂Z))
  have hAN : A₀ ≤ normalizer ((Z₀ ⊔ Z d.radical c : Subgroup (FreeAmalgam d.radical)) : Set _) :=
    (le_inf ((inf_le_right.trans hQC).trans (le_normalizer_conjugateSpanBy _ _))
      ((inf_le_right.trans (fun _ hx => hx.1)).trans (Z_normalized d.radical c))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hnotn := strict_span_not_normalized h d path hb hsmall y hy selected hie hnotB hgen
  have hupper := radius_intersection_card_le_field h d selected hb.le Z₀
    (sup_le hZV (Z_le_VBall d.radical c 2)) hJtr hAN hnotn hic hie
  have hsize : Nat.card (⁅Z₀,A₀⁆ : Subgroup (FreeAmalgam d.radical))=Nat.card F :=
    le_antisymm hupper hcard
  have hcentral : ⁅Z₀,A₀⁆ ≤ centralizer (V d.radical c : Set (FreeAmalgam d.radical)) :=
    (commutator_mono hZV inf_le_right).trans
      (h.replacement_radius_commutator_central d geometry hb.le hc)
  have htZ : Z d.radical (act d.radical t mu) ≤ Z₀ := by
    rw [Z_act]
    rintro _ ⟨u,hu,rfl⟩
    exact subset_closure ⟨t⁻¹,C₀.inv_mem ht,u,hu,rfl⟩
  have htS : Z d.radical (act d.radical t mu) ≤ stabilizer d.radical e :=
    (htZ.trans (hZW.trans hWz)).trans
      (Q_le_stabilizer_of_dist_le_two z e path.end_color selected.end_color
        (by rw [SimpleGraph.dist_comm]; exact hez.le))
  have hlo := h.replacement_root_intersection_commutator_card_ge_field d selected hb.le
    (by rw [hic]; have hq : 1 < Nat.card F := Finite.one_lt_card; nlinarith)
    (Z d.radical (act d.radical t mu)) htS htne
  let := finite_Z d.radical e
  let : Finite (U d.radical e) := Finite.of_injective (inclusion (U_le_Z e)) (inclusion_injective _)
  let : Finite (⁅Z₀,A₀⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion (hRU.trans inf_le_right)) (inclusion_injective _)
  have htEq : ⁅Z d.radical (act d.radical t mu),A₀⁆=⁅Z₀,A₀⁆ :=
    eq_of_le_of_card_ge (commutator_mono htZ le_rfl) (hsize.le.trans hlo)
  let nu := act d.radical t mu
  have hnu : color d.radical nu=false := by
    rw [action_preserves_color,action_preserves_color]; exact path.start_color
  have hnuDist : (cosetGraph d.radical).dist c nu ≤ 2 := by
    have hh := dist_act d.radical t c mu
    rw [show act d.radical t c=c from ht.1,SimpleGraph.dist_comm (u := c) (v := mu),hdist] at hh
    exact hh.le
  have hAS : A₀ ≤ stabilizer d.radical nu := inf_le_right.trans
    (Q_le_stabilizer_of_dist_le_two c nu hc hnu hnuDist)
  have htU : ⁅U d.radical nu,A₀⁆=⁅Z₀,A₀⁆ :=
    (h.replacement_Z_commutator_eq_U d geometry hb.le hnu A₀ hAS).symm.trans htEq
  have hupp := h.replacement_moving_index_le_commutator_card d geometry hb.le hnu A₀ hAS
  rw [commutator_comm A₀,htU,hsize] at hupp
  have hnA : ¬ A₀ ≤ Q d.radical nu := by
    intro hh
    exact htne (le_bot_iff.mp ((commutator_mono le_rfl hh).trans (geometry.centralizes nu hnu).le))
  have hidx := le_antisymm hupp
    (h.replacement_natural_fixed_index_lower d geometry hb.le hnu A₀ hAS hnA)
  have hUS : U d.radical e ≤ stabilizer d.radical c :=
    (U_le_Z e).trans (selected.endpoint_Z_le_start_stabilizer (by omega))
  have hCa := MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) c hc
  have hAU : U d.radical e ⊓ centralizer (Z d.radical c : Set (FreeAmalgam d.radical)) =
      U d.radical e ⊓ Q d.radical c := by
    rw [←hCa]
    ext x
    exact ⟨fun hx => ⟨hx.1,hUS hx.1,hx.2⟩,fun hx => ⟨hx.1,hx.2.2⟩⟩
  have hfixlower := h.replacement_fixed_U_moving_index_lower d geometry hb.le selected.end_color
    (Z d.radical nu) (Z d.radical c) htS
    (Z_le_stabilizer_of_dist_le c (geometry.exists_critical c hc) selected.critical.1.le) (by
      rw [hAU,←(h.replacement_root_intersection_fixed_and_commutator d selected hb.le
        (by rw [hic]; have hq : 1 < Nat.card F := Finite.one_lt_card; nlinarith)
        (Z d.radical nu) htS).1]
      exact htne)
  rw [hAU] at hfixlower
  have hUA : U d.radical e ⊓ Q d.radical c ≤ A₀ := inf_le_inf_right _
    ((U_le_Z e).trans (geometry.omega_bound e selected.end_color (by
      rw [geometry.distance_constant e selected.end_color]; change 0 < geometry.b d.radical; omega)))
  let := finite_stabilizer d.radical nu
  let : Finite A₀ := Finite.of_injective (inclusion hAS) (inclusion_injective _)
  have hCn : A₀ ⊓ centralizer (Z d.radical nu : Set (FreeAmalgam d.radical))=A₀ ⊓ Q d.radical nu := by
    rw [←MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
      (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) nu hnu]
    ext x
    exact ⟨fun hx => ⟨hx.1,hAS hx.1,hx.2⟩,fun hx => ⟨hx.1,hx.2.2⟩⟩
  have hQlo := hfixlower.trans (relIndex_le_of_le_right hUA index_ne_zero_of_finite)
  rw [←inf_relIndex_left,hCn,inf_relIndex_left] at hQlo
  have hQidx := le_antisymm
    (h.replacement_field_fixed_index_image_bound d geometry hb.le hnu A₀ hAS hidx.le) hQlo
  let r := act d.radical t (act d.radical y (path.walk.getVert 1))
  have hat : Adjacent d.radical a (path.walk.getVert 1) := by
    have hh := (cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (i := 0) (by rw [path.length_eq_b]; omega))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  have hct : Adjacent d.radical c (path.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (i := 1) (by rw [path.length_eq_b]; omega)))
  have hnur : Adjacent d.radical nu r :=
    (adjacent_act_iff d.radical t _ _).mpr ((adjacent_act_iff d.radical y _ _).mpr hat)
  have hcr : Adjacent d.radical c r := by
    have hh := (adjacent_act_iff d.radical t _ _).mpr
      ((adjacent_act_iff d.radical y _ _).mpr hct)
    rwa [show act d.radical y c=c from hy,show act d.radical t c=c from ht.1] at hh
  have hr : color d.radical r=true := by
    cases hr : color d.radical r
    · exact ((adjacent_color_ne d.radical hcr) (hc.trans hr.symm)).elim
    · rfl
  have hAT : A₀ ≤ Q d.radical r := inf_le_right.trans (Q_le_adjacent_h d.radical hr hcr)
  have hfixed := h.replacement_small_mover_join_centralizes_field_displacement d geometry hb.le
    hnu hnur A₀ hAT hidx.le
  rw [htU] at hfixed
  exact ⟨hi,y,hy,hnotB,hT,hmove,e,selected,hez,hover,hmoveE,hgen,hZW,hWQ,hWp,hWz,
    hic,hie,hbad,hne,hcard,heq,hRU,hnotn,hsize,hcentral,t,ht,htEq,htU,hidx,hQidx,hfixed⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

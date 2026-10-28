module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.CoordinatedChoices
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.PointMovement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Rigidity.Moving
public import Theory.GroupTheory.MutualBinaryActions

/-!
# Native inputs to the small backward-critical branch

The invariant symplectic pairing identifies the index of a fixed subgroup
in the original natural module with the order of its commutator. The equality
is transported through the actual source embedding to every M-type vertex.
A small forward critical image forces both images to have order two; mutual
abelian actions then make the actual critical commutator a line.

For the same coordinated backward choice, a commutator line and placement of
its centralizer in B contradict the original index bound. The final native
application uses precisely X_e intersect Q_alpha as actor and proves its
stabilizer placement from the recorded edge. The line and B-placement for
this different commutator remain explicit earlier-source obligations; the
critical commutator line does not discharge them.

Source: Meierfrankenfeld--Stellmacher (1993), (3.3)(ii) and (5.7), printed
pp.866--867 and 919; Aschbacher--Smith C.1.37 and 13.7.4(1).
-/

public section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory BinaryPermutation Representation.BinaryOffender
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

/-- Fixed index equals moved order on the literal source natural module. -/
theorem module_fixedIndex_eq_commutator_card (hq : Function.Surjective s.projection)
    (A : Subgroup M) :
    (centralizer (A : Set M)).relIndex W = Nat.card (⁅W,A⁆ : Subgroup M) := by
  let : IsElementaryAbelian 2 W := s.module_elementary
  let : IsElementaryAbelian 2 (⁅W,A⁆ : Subgroup M) :=
    IsElementaryAbelian.of_le (commutator_le_left W A)
  let d : NaturalAction W := ⟨s.projection,hq,s.projection_kernel,s.coordinates,s.action⟩
  have he := Nat.card_congr (Representation.NormalElementaryQuotient.movedEquiv
    W d.q d.onto d.kernel_centralizer A).toEquiv
  change Nat.card (⁅W,A⁆ : Subgroup M) =
    Nat.card (subspaceCommutator d.ρ ⊤ (A.map d.q)) at he
  rw [he,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  have hd := moved_finrank_equivariant d.ρ Model.rho (MonoidHom.id Model.S)
    d.linearCoordinates d.equivariant (A.map d.q)
  rw [map_id] at hd
  rw [hd,NaturalPairing.moved_finrank_eq_fixedCodim]
  exact s.fixed_index A

/-- The same equality through a faithful embedding and its actual actor. -/
theorem embedded_fixedIndex_eq_commutator_card (hq : Function.Surjective s.projection)
    {G : Type*} [Group G] (i : M →* G) (hi : Function.Injective i)
    (A : Subgroup G) (hA : A ≤ i.range) :
    (centralizer (A : Set G)).relIndex (W.map i) = Nat.card (⁅W.map i,A⁆ : Subgroup G) := by
  let A₀ := A.comap i
  have hmap : A₀.map i = A := map_comap_eq_self hA
  have hc : (centralizer (A : Set G)).comap i = centralizer (A₀ : Set M) := by
    ext m
    constructor
    · intro hm a ha
      apply hi
      simpa only [map_mul] using hm (i a) ha
    · intro hm a ha
      obtain ⟨x,hx,rfl⟩ := hA ha
      exact (by simpa only [map_mul] using congrArg i (hm x ha))
  rw [←relIndex_comap,hc,←hmap,←map_commutator,card_map_of_injective hi]
  exact s.module_fixedIndex_eq_commutator_card hq A₀

/-- The fixed-index equality at every actual original-group vertex. -/
theorem moving_fixedIndex_eq_commutator_card (h : NativeCentralLayer s)
    (hq : Function.Surjective s.projection) (a : Vertex R) (ha : color R a = false)
    (A : Subgroup (FreeAmalgam R)) (hA : A ≤ stabilizer R a) :
    (centralizer (A : Set (FreeAmalgam R))).relIndex (U R a) =
      Nat.card (⁅U R a,A⁆ : Subgroup (FreeAmalgam R)) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color R ha
  let j := (MulAut.conj g⁻¹).toMonoidHom
  let i := j.comp (embedM R)
  have hi : Function.Injective i := (MulAut.conj g⁻¹).injective.comp (embedM_injective R)
  have hact : act R g (alpha R) = a := by rw [hg]; simp only [alpha,act_mVertex,one_mul]
  have hU : W.map i = U R a := by
    rw [←hact,U_act,h.U_eq_module,map_map]
  have hG : i.range = stabilizer R a := by
    rw [←hact,stabilizer_act]
    change (j.comp (embedM R)).range = (stabilizer R (mVertex R 1)).map j
    rw [stabilizer_m_base,MonoidHom.range_comp]
    rfl
  rw [←hU]
  exact s.embedded_fixedIndex_eq_commutator_card hq i hi A (hA.trans_eq hG.symm)

/-- A line and its B-contained centralizer contradict the prescribed index,
retaining the same transported backward vertex. -/
theorem small_backward_contradiction_of_commutator_line (h : NativeCentralLayer s)
    (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < s.geometry.b R) {e : Vertex R}
    {p : DistanceEight.PathCentrality.CriticalPath R s.geometry (alpha R) e}
    {delta : Vertex R} (c : s.CoordinatedChoice p delta)
    (hindex : 2 < (B R (alpha R) (s.geometry.Z_normal _)).relIndex (U R delta))
    (A : Subgroup (FreeAmalgam R)) (hA : A ≤ stabilizer R c.alpha1)
    (hcard : Nat.card (⁅Z R c.alpha1,A⁆ : Subgroup (FreeAmalgam R)) ≤ 2)
    (hfixed : Z R c.alpha1 ⊓ centralizer (A : Set (FreeAmalgam R)) ≤
      B R (alpha R) (s.geometry.Z_normal _)) : False := by
  have hcol : color R c.alpha1 = false := by
    have h1 := adjacent_color_ne R c.adjacent_start
    have h2 := adjacent_color_ne R c.adjacent_back
    change false ≠ color R c.beta1 at h1
    cases hc : color R c.alpha1 <;> cases hc' : color R c.beta1 <;> simp_all
  let : Finite (stabilizer R c.alpha1) := finite_stabilizer R c.alpha1
  let : Finite (Z R c.alpha1) := Finite.of_injective
    (inclusion (Z_le_stabilizer R c.alpha1)) (inclusion_injective _)
  let : Finite (U R c.alpha1) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z R c.alpha1)) (inclusion_injective _)
  have hcZ : ⁅Z R c.alpha1,A⁆ ≤ Z R c.alpha1 := by
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_right.mp (hA.trans (Z_normalized R c.alpha1))
  let : Finite (⁅Z R c.alpha1,A⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hcZ) (inclusion_injective _)
  have hm : Nat.card (⁅U R c.alpha1,A⁆ : Subgroup (FreeAmalgam R)) ≤ 2 :=
    (card_le_of_le (commutator_mono (DistanceEight.U_le_Z R c.alpha1) le_rfl)).trans hcard
  have hf : U R c.alpha1 ⊓ centralizer (A : Set (FreeAmalgam R)) ≤
      B R (alpha R) (s.geometry.Z_normal _) :=
    (inf_le_inf_right _ (DistanceEight.U_le_Z R c.alpha1)).trans hfixed
  have hbound := relIndex_le_of_le_left hf (index_ne_zero_of_finite
    (H := (U R c.alpha1 ⊓ centralizer (A : Set (FreeAmalgam R))).subgroupOf (U R c.alpha1)))
  rw [inf_relIndex_left,
    s.moving_fixedIndex_eq_commutator_card h
      (s.projection_surjective_of_radical_image_le_conjugate u hfull.le) _ hcol A hA] at hbound
  have hBmap : (B R (alpha R) (s.geometry.Z_normal _)).map
      (MulAut.conj c.transporter⁻¹).toMonoidHom = B R (alpha R) (s.geometry.Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      (geometry := s.geometry) hb (alpha R) rfl ((stabilizer R (alpha R)).inv_mem c.transporter_mem))
  have hsmall := hbound.trans hm
  rw [c.alpha1_eq,U_act,←hBmap,relIndex_map_map_of_injective _ _
    (MulAut.conj c.transporter⁻¹).injective] at hsmall
  omega


private theorem binary_index_two {G : Type*} [Group G]
    (A K : Subgroup G) [Finite A] [IsElementaryAbelian 2 A]
    (hsmall : K.relIndex A < 4) (hne : ¬ A ≤ K) : K.relIndex A = 2 := by
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 A).index (K.subgroupOf A)
  change K.relIndex A = 2^n at hn
  have hlt : n < 2 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (hn ▸ hsmall)
  have hn0 : n ≠ 0 := by
    intro he
    rw [he,pow_zero] at hn
    exact hne (relIndex_eq_one.mp hn)
  have he : n = 1 := by omega
  simpa only [he,pow_one] using hn

/-- Both literal critical images have order two in the small-image branch. -/
theorem small_critical_indices (h : NativeCentralLayer s) {a e : Vertex R}
    (p : CriticalPath R s.geometry a e)
    (hsmall : (Q R e).relIndex (Z R a) < 4) :
    (Q R e).relIndex (Z R a) = 2 ∧ (Q R a).relIndex (Z R e) = 2 := by
  have hb : 0 < criticalDistance R a (s.geometry.exists_critical a p.start_color) := by
    rw [s.geometry.distance_constant a p.start_color]
    exact s.criticalDistance_pos
  have hr := critical_reverse R s.geometry s.edgeCentralizerCondition
    a p.start_color hb e p.end_color p.critical
  let p' : CriticalPath R s.geometry e a := CriticalPath.ofPair p.end_color hr
  have hrs : (Q R a).relIndex (Z R e) < 4 := by
    by_contra hn
    exact (Nat.not_le_of_gt hsmall)
      (s.reverse_critical_image_four_le h s.criticalDistance_pos p' (by omega))
  let := finite_Z R a
  let := finite_Z R e
  let := s.geometry.Z_elementary s.criticalDistance_pos a p.start_color
  let := s.geometry.Z_elementary s.criticalDistance_pos e p.end_color
  exact ⟨binary_index_two _ _ hsmall p.critical.2,binary_index_two _ _ hrs hr.2⟩

private theorem centralizer_index_map {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) (A B : Subgroup G) :
    (centralizer (A.map f : Set H)).relIndex (B.map f) =
      (centralizer (A : Set G)).relIndex B := by
  rw [←inf_relIndex_right,inf_comm,map_inf_centralizer_of_injective f hf,
    relIndex_map_map_of_injective _ _ hf,inf_relIndex_left]

/-- The genuine critical commutator has order two. -/
theorem small_critical_commutator_card (h : NativeCentralLayer s) {a e : Vertex R}
    (p : CriticalPath R s.geometry a e)
    (hsmall : (Q R e).relIndex (Z R a) < 4) :
    Nat.card (⁅Z R a,Z R e⁆ : Subgroup (FreeAmalgam R)) = 2 := by
  obtain ⟨ha2,he2⟩ := s.small_critical_indices h p hsmall
  have hb : 0 < criticalDistance R a (s.geometry.exists_critical a p.start_color) := by
    rw [s.geometry.distance_constant a p.start_color]
    exact s.criticalDistance_pos
  let J := stabilizer R a
  let A := (Z R a).subgroupOf J
  let E := (Z R e).subgroupOf J
  let := finite_stabilizer R a
  let := finite_Z R a
  let := finite_Z R e
  let := s.geometry.Z_elementary s.criticalDistance_pos a p.start_color
  let := s.geometry.Z_elementary s.criticalDistance_pos e p.end_color
  have hAJ : Z R a ≤ J := Z_le_stabilizer R a
  have hEJ : Z R e ≤ J :=
    critical_Z_le_stabilizer R s.geometry a p.start_color hb p.critical
  have hAe : Z R a ≤ stabilizer R e :=
    Z_le_stabilizer_of_dist_le a _ p.critical.1.le
  have hEA : Z R e ≤ normalizer (Z R a : Set (FreeAmalgam R)) :=
    hEJ.trans (Z_normalized R a)
  have hAE : Z R a ≤ normalizer (Z R e : Set (FreeAmalgam R)) :=
    hAe.trans (Z_normalized R e)
  have hmA : A.map J.subtype = Z R a := map_subgroupOf_eq_of_le hAJ
  have hmE : E.map J.subtype = Z R e := map_subgroupOf_eq_of_le hEJ
  have hidxA : (centralizer (Z R e : Set (FreeAmalgam R))).relIndex (Z R a) ≤ 2 := by
    have hle : Q R e ≤ centralizer (Z R e : Set (FreeAmalgam R)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R e p.end_color))
    exact (relIndex_le_of_le_left hle index_ne_zero_of_finite).trans_eq ha2
  have hidxE : (centralizer (Z R a : Set (FreeAmalgam R))).relIndex (Z R e) ≤ 2 := by
    have hle : Q R a ≤ centralizer (Z R a : Set (FreeAmalgam R)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R a p.start_color))
    exact (relIndex_le_of_le_left hle index_ne_zero_of_finite).trans_eq he2
  have hcard : Nat.card (⁅A,E⁆ : Subgroup J) ≤ 2 := by
    apply commutator_card_le_two_of_mutual_centralizer_indices A E
    · rw [←subgroupOf_normalizer_eq hAJ]
      exact fun _ he => hEA he
    · rw [←subgroupOf_normalizer_eq hEJ]
      exact fun _ ha => hAE ha
    · rw [←centralizer_index_map J.subtype J.subtype_injective,hmA,hmE]
      exact hidxE
    · rw [←centralizer_index_map J.subtype J.subtype_injective,hmE,hmA]
      exact hidxA
  have hm : (⁅A,E⁆ : Subgroup J).map J.subtype = ⁅Z R a,Z R e⁆ := by
    rw [map_commutator,hmA,hmE]
  have hcard' : Nat.card (⁅Z R a,Z R e⁆ : Subgroup (FreeAmalgam R)) ≤ 2 := by
    rw [←hm,card_map_of_injective J.subtype_injective]
    exact hcard
  have hn := critical_noncommutation R s.geometry s.edgeCentralizerCondition
    a p.start_color hb p.critical
  let : Finite (⁅Z R a,Z R e⁆ : Subgroup (FreeAmalgam R)) := by
    exact Finite.of_injective (inclusion
      ((s.critical_Z_commutator_le_moving p).trans inf_le_left |>.trans
        (DistanceEight.U_le_Z R a))) (inclusion_injective _)
  have hone : 1 < Nat.card (⁅Z R a,Z R e⁆ : Subgroup (FreeAmalgam R)) :=
    (one_lt_card_iff_ne_bot _).mpr hn
  omega

/-- The source actor `X_e ∩ Q_alpha` already lies in the selected backward
stabilizer. Only its commutator-line and centralizer-placement premises remain. -/
theorem small_backward_false_of_line_and_fixed (h : NativeCentralLayer s)
    (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < s.geometry.b R) {e : Vertex R}
    {p : CriticalPath R s.geometry (alpha R) e}
    {delta : Vertex R} (c : s.CoordinatedChoice p delta)
    (hindex : 2 < (B R (alpha R) (s.geometry.Z_normal _)).relIndex (U R delta))
    (hcard : Nat.card (⁅Z R c.alpha1,X R e ⊓ Q R (alpha R)⁆ :
      Subgroup (FreeAmalgam R)) ≤ 2)
    (hfixed : Z R c.alpha1 ⊓ centralizer
      (X R e ⊓ Q R (alpha R) : Set (FreeAmalgam R)) ≤
        B R (alpha R) (s.geometry.Z_normal _)) : False := by
  have hcol : color R c.beta1 = true := by
    have hc := adjacent_color_ne R c.adjacent_start
    change false ≠ color R c.beta1 at hc
    cases ht : color R c.beta1 <;> simp_all
  have hA : X R e ⊓ Q R (alpha R) ≤ stabilizer R c.alpha1 :=
    (inf_le_right.trans (Q_le_adjacent_h R hcol c.adjacent_start)).trans
      (fun _ hx => hx.2 c.alpha1 (adjacent_symm R c.adjacent_back))
  exact s.small_backward_contradiction_of_commutator_line h u hfull hb c hindex
    (X R e ⊓ Q R (alpha R)) hA hcard hfixed

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K]
  {L W : Subgroup K} [L.Normal] [W.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L W T) (hm : IntrinsicMSPair d)
local notation "J" => (L ⊔ d.B : Subgroup K)
local notation "R" => d.B.subgroupOf J

/-- Original characteristic replacements have both order-two images and the
literal critical commutator line; no independent reverse-image premise remains. -/
theorem reducedSource_small_critical_line
    (r : CharacteristicReduction (L.subgroupOf J) R) {a e : Vertex r.radical}
    (p : CriticalPath r.radical ((originalSource d hm).reduce r).geometry a e)
    (hsmall : (Q r.radical e).relIndex (Z r.radical a) < 4) :
    (Q r.radical e).relIndex (Z r.radical a) = 2 ∧
    (Q r.radical a).relIndex (Z r.radical e) = 2 ∧
    Nat.card (⁅Z r.radical a,Z r.radical e⁆ : Subgroup (FreeAmalgam r.radical)) = 2 := by
  let s := (originalSource d hm).reduce r
  have h := reduced_nativeCentralLayer d hm r
  exact ⟨(s.small_critical_indices h p hsmall).1,
    (s.small_critical_indices h p hsmall).2,s.small_critical_commutator_card h p hsmall⟩

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData

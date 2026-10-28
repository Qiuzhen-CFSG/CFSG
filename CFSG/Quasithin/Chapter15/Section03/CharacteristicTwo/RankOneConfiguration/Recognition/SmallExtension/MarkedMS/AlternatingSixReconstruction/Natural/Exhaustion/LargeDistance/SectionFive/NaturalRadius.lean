module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.RadiusImage
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalOrthogonality

/-!
# Radius centrality for every radical image on the natural cover

A quadratic elementary actor of order at least four moves a Lagrangian plane
in the natural six-letter module. Any actor fixing that plane has its movement
inside the same plane. The actual order-sixteen cover transports this inclusion
to the original group commutators, with no restriction on the radical image.

At a critical pair, the reverse moving layer itself has image of order at
least four, for either cover order. Using this layer as the chief-factor actor
avoids an unjustified splitting of the full seed. On the natural cover, its
radius commutator lies in the initial seed, and the all-image radius bound
then proves the residual dichotomy and radius centrality. The derived-radius
and triple-commutator conclusions follow at every component vertex.

The known-simple application retains the original minimum characteristic
replacement. The order-thirty-two exceptional actor and both distance
exclusions remain with qt-e-ms-small-a6-exhaustion-large-distance; these
radius estimates do not establish the final critical-distance bound.
Source: MS93 (3.3), (5.2)(i)--(iii), printed pp.866--867 and 914--915.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u

private theorem even_involution (A : Subgroup S) [IsElementaryAbelian 2 A]
    (hA : 4 ≤ Nat.card A) :
    ∃ a ∈ A, orderOf a = 2 ∧ a ∈ alternatingGroup (Fin 6) := by
  have hex : ∃ a ∈ A, a ≠ 1 ∧ a ∈ alternatingGroup (Fin 6) := by
    by_contra hn
    push Not at hn
    let f := (Equiv.Perm.sign (α := Fin 6)).comp A.subtype
    have hf : Function.Injective f := by
      apply (injective_iff_map_eq_one f).mpr
      intro a ha
      by_contra hne
      exact hn a a.property (fun hh => hne (Subtype.ext hh)) ha
    have hc := Nat.card_le_card_of_injective f hf
    have htwo : Nat.card ℤˣ = 2 := by rw [Nat.card_eq_fintype_card,Fintype.card_units_int]
    rw [htwo] at hc
    omega
  obtain ⟨a,ha,hne,heven⟩ := hex
  exact ⟨a,ha,orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian a ha) hne,heven⟩

/-- A quadratic large actor moves a Lagrangian plane; its pointwise fixer
moves the natural module into that same plane. -/
theorem natural_moved_control (A Y : Subgroup S) [IsElementaryAbelian 2 A]
    (hcard : 4 ≤ Nat.card A) (hquad : QuadraticPointCore.Quadratic A)
    (hfix : Y ≤ subspaceKernel (naturalRepresentation (Fin 6))
      (subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ A) ⊤) :
    subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ Y ≤
      subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ A := by
  let ρ := naturalRepresentation (Fin 6)
  let P := subspaceCommutator ρ ⊤ A
  have hfixed (a : S) (ha : a ∈ A) : ∀ v ∈ P, ρ a v = v := by
    have hh : P ≤ LinearMap.ker (ρ a - LinearMap.id) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨b,hb,v,_,rfl⟩
      change ρ a (ρ b v-v) - (ρ b v-v) = 0
      exact sub_eq_zero.mpr (hquad a ha b hb v)
    intro v hv
    simpa only [LinearMap.mem_ker,LinearMap.sub_apply,LinearMap.id_apply,sub_eq_zero] using hh hv
  have hperp : P ≤ NaturalPairing.form.orthogonal P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,v,_,rfl⟩
    exact (NaturalOrthogonality.fixes_iff_displacement a P).mp (hfixed a ha) v
  obtain ⟨a,haA,ha,heven⟩ := even_involution A hcard
  have hlow := AlternatingSixInvolutionDisplacement.displacement_lower
    (ρ.comp (alternatingGroup (Fin 6)).subtype)
    ((naturalRepresentation_injective (Fin 6) (by decide)).comp Subtype.val_injective)
    ⟨a,heven⟩
    ((orderOf_injective (alternatingGroup (Fin 6)).subtype Subtype.val_injective ⟨a,heven⟩).symm.trans ha)
  have hrange : LinearMap.range (ρ a - LinearMap.id) ≤ P := by
    rintro _ ⟨v,rfl⟩
    exact Submodule.subset_span ⟨a,haA,v,Submodule.mem_top,rfl⟩
  have hlowP : 2 ≤ Module.finrank (ZMod 2) P :=
    hlow.trans (Submodule.finrank_mono hrange)
  have hdim := Submodule.finrank_mono hperp
  have hperpdim := LinearMap.BilinForm.finrank_orthogonal NaturalPairing.form_nondegenerate P
  rw [finrank_natural_even (Fin 6) (by decide)] at hperpdim
  simp only [Fintype.card_fin] at hperpdim
  have heq : P = NaturalPairing.form.orthogonal P :=
    Submodule.eq_of_le_of_finrank_eq hperp (by omega)
  change subspaceCommutator ρ ⊤ Y ≤ P
  rw [heq]
  apply Submodule.span_le.mpr
  rintro _ ⟨y,hy,v,_,rfl⟩
  exact (NaturalOrthogonality.fixes_iff_displacement y P).mp (hfix hy).2 v

variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  {h : SmallMSPair κ L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

private theorem natural_coverMap_injective
    (hnat : Nat.card (replacementMoved d) = 16) :
    Function.Injective (coverMap (h := h) (e := e) (hz := hz) (hn := hn) (d := d)) := by
  have hle : Nat.card (Additive (replacementMoved d)) ≤ Nat.card (natural (Fin 6)) := by
    change Nat.card (replacementMoved d) ≤ Nat.card (natural (Fin 6))
    rw [hnat,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      finrank_natural_even (Fin 6) (by decide)]
    decide
  exact ((coverMap_surjective (h := h) (e := e) (hz := hz) (hn := hn) (d := d)).bijective_of_nat_card_le hle).1

theorem natural_cover_commutator_control
    (hnat : Nat.card (replacementMoved d) = 16)
    (A Y : Subgroup d.overgroup) [IsElementaryAbelian 2 A]
    (hcard : 4 ≤ Nat.card (A.map s.projection))
    (hAA : ⁅replacementMoved d,A⁆ ≤ centralizer (A : Set d.overgroup))
    (hAY : ⁅replacementMoved d,A⁆ ≤ centralizer (Y : Set d.overgroup)) :
    ⁅replacementMoved d,Y⁆ ≤ ⁅replacementMoved d,A⁆ := by
  let := replacementMoved_normal h d
  let := IsElementaryAbelian.map (p := 2) (A := A) s.projection
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
theorem embedded_natural_commutator_control
    (hnat : Nat.card (replacementMoved d) = 16)
    {H : Type*} [Group H] (i : d.overgroup →* H) (hi : Function.Injective i)
    (A Y : Subgroup H) [IsElementaryAbelian 2 A]
    (hA : A ≤ i.range) (hY : Y ≤ i.range)
    (hcard : 4 ≤ ((pCore 2 d.overgroup).map i).relIndex A)
    (hAA : ⁅(replacementMoved d).map i,A⁆ ≤ centralizer (A : Set H))
    (hAY : ⁅(replacementMoved d).map i,A⁆ ≤ centralizer (Y : Set H)) :
    ⁅(replacementMoved d).map i,Y⁆ ≤ ⁅(replacementMoved d).map i,A⁆ := by
  let A₀ := A.comap i
  let Y₀ := Y.comap i
  let := IsElementaryAbelian.comap_of_injective (p := 2) i hi A
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
  have hh := map_mono (f := i) (natural_cover_commutator_control s hnat A₀ Y₀ hcard₀
    (hfix A hAA) (hfix Y hAY))
  rwa [map_commutator,map_commutator,hmA,hmY] at hh

include h in
/-- Coordinates on the original moved cover and two-core at any component
vertex, through the same injective ambient realization. -/
theorem vertex_coordinates (hc : DistanceTwo.CentralLayer d)
    (a : Vertex d.radical) (ha : color d.radical a = false) :
    ∃ i : d.overgroup →* FreeAmalgam d.radical, Function.Injective i ∧
      i.range = stabilizer d.radical a ∧
      (pCore 2 d.overgroup).map i = Q d.radical a ∧
      (replacementMoved d).map i = U d.radical a := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical ha
  let j := (MulAut.conj g⁻¹).toMonoidHom
  let i := j.comp (embedM d.radical)
  have hact : act d.radical g (alpha d.radical) = a := by
    rw [hg]
    simp only [alpha,act_mVertex,one_mul]
  refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective d.radical),?_,?_,?_⟩
  · rw [←hact,stabilizer_act]
    change (j.comp (embedM d.radical)).range = (stabilizer d.radical (mVertex d.radical 1)).map j
    rw [stabilizer_m_base,MonoidHom.range_comp]
    rfl
  · rw [←hact,Q_act,Q_alpha d.radical (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d),map_map]
  · rw [←hact,U_act,hc.U_eq_moved,map_map]

include s in
/-- The reverse image of the moving layer itself has order at least four.
This retains both possible cover orders and does not impose a radical image. -/
theorem reverse_critical_moving_image_four_le (hc : DistanceTwo.CentralLayer d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hforward : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    4 ≤ (Q d.radical a).relIndex (U d.radical a') := by
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h := h) hc a' p.end_color
  have hA : Z d.radical a ≤ i.range := by
    rw [hir]
    exact Z_le_stabilizer_of_dist_le a _ p.critical.1.le
  have hB : Q d.radical a ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a p.start_color))
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color
  rw [←hiU]
  apply embedded_centralizing_index_four_le s i hi (Z d.radical a) (Q d.radical a) hA hB
  rwa [hiQ]

include s in
/-- All radical images satisfy the critical radius commutator bound on the
order-sixteen cover. Its actor is the actual opposite moving layer. -/
theorem critical_radius_moving_commutator_le_Z_of_natural
    (hc : DistanceTwo.CentralLayer d) (hnat : Nat.card (replacementMoved d) = 16)
    (hb : 2 < replacementDistance h d) {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hcard : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    ⁅V d.radical a ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)),U d.radical a'⁆ ≤
      Z d.radical a := by
  have hl : 2 < p.walk.length := by rw [p.length_eq_b]; exact hb
  let t := p.walk.getVert (p.walk.length-1)
  have hct : Adjacent d.radical a' t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1 = p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hct
    rw [p.end_color] at hh
    cases he : color d.radical t <;> simp_all
  have het : Adjacent d.radical (p.walk.getVert (p.walk.length-2)) t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1 = p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  let Y := V d.radical a ⊓ Q d.radical (p.walk.getVert (p.walk.length-2))
  have hYt : Y ≤ Q d.radical t := inf_le_right.trans (Q_le_adjacent_h d.radical ht het)
  have hY : Y ≤ stabilizer d.radical a' := fun _ hx =>
    (hYt hx).2 _ (adjacent_symm d.radical hct)
  have hcomm : ⁅U d.radical a',Z d.radical a⁆ ≤ ⁅Z d.radical a,Z d.radical a'⁆ := by
    rw [commutator_comm]
    exact commutator_mono le_rfl (DistanceEight.U_le_Z d.radical a')
  have hRZa : ⁅Z d.radical a,Z d.radical a'⁆ ≤ Z d.radical a :=
    ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
      (DistanceEight.U_le_Z d.radical a)
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color
  have hAA : ⁅U d.radical a',Z d.radical a⁆ ≤
      centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    (hcomm.trans hRZa).trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hAY : ⁅U d.radical a',Z d.radical a⁆ ≤
      centralizer (Y : Set (FreeAmalgam d.radical)) :=
    hcomm.trans (le_centralizer_iff.mp (critical_radius_intersection_centralizes (h := h) p hb))
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h := h) hc a' p.end_color
  have hA : Z d.radical a ≤ i.range := by
    rw [hir]
    exact Z_le_stabilizer_of_dist_le a _ p.critical.1.le
  have hcontrol : ⁅U d.radical a',Y⁆ ≤ ⁅U d.radical a',Z d.radical a⁆ := by
    rw [←hiU]
    apply embedded_natural_commutator_control s hnat i hi (Z d.radical a) Y hA
      (hY.trans_eq hir.symm)
    · rwa [hiQ]
    · rwa [hiU]
    · rwa [hiU]
  rw [commutator_comm]
  exact hcontrol.trans (hcomm.trans hRZa)

/-- The chief-factor actor can be taken in the opposite moving layer,
including for the order-thirty-two central cover. -/
theorem critical_moving_even_actor (hc : DistanceTwo.CentralLayer d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hforward : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    ∃ a ∈ graphImage s (U d.radical a'), orderOf a = 2 ∧ a ∈ alternatingGroup (Fin 6) := by
  have hU : U d.radical a' ≤ stabilizer d.radical (alpha d.radical) :=
    (DistanceEight.U_le_Z d.radical a').trans
      (critical_Z_le_stabilizer d.radical (replacementGeometry h d) (alpha d.radical) rfl
        (replacementDistance_pos h d) p.critical)
  have hcard : 4 ≤ Nat.card (graphImage s (U d.radical a')) := by
    rw [graphImage_card s _ hU]
    exact reverse_critical_moving_image_four_le s hc p hforward
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a' p.end_color
  let := IsElementaryAbelian.of_le (p := 2) (DistanceEight.U_le_Z d.radical a')
  let := IsElementaryAbelian.comap_of_injective (p := 2) (embedM d.radical)
    (embedM_injective d.radical) (U d.radical a')
  let := IsElementaryAbelian.map (p := 2)
    (A := (U d.radical a').comap (embedM d.radical)) s.projection
  exact even_involution (((U d.radical a').comap (embedM d.radical)).map s.projection) hcard

include s in
/-- The actual order-sixteen radius is central under its two-core for every
radical image. All critical indices and local commutator premises are discharged. -/
theorem radius_commutator_central_of_natural
    (hc : DistanceTwo.CentralLayer d) (hnat : Nat.card (replacementMoved d) = 16)
    (hb : 2 < replacementDistance h d) :
    ⁅V d.radical (alpha d.radical),Q d.radical (alpha d.radical)⁆ ≤
      centralizer (V d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
  by_contra hnon
  have hfour := CFSG.Quasithin.ChapterC.BinaryMS.MS93.SectionFive.distance_eq_four_of_radius_commutator_not_central
    d.radical (replacementGeometry h d) hb rfl hnon
  obtain ⟨a',p,hforward⟩ := exists_base_large_critical_path (h := h) (r := d) hfour hnon
  obtain ⟨a,haA,ha,heven⟩ := critical_moving_even_actor s hc p hforward
  apply hnon
  apply radius_commutator_central_of_residual_dichotomy (h := h) (r := d) hb
  apply radius_residual_dichotomy_of_index s hb s.surjective
    (U d.radical a') (Q d.radical (p.walk.getVert (p.walk.length-2)))
    ((DistanceEight.U_le_Z d.radical a').trans
      (critical_Z_le_stabilizer d.radical (replacementGeometry h d) (alpha d.radical) rfl
        (replacementDistance_pos h d) p.critical)) a ha heven haA
  · exact critical_radius_moving_commutator_le_Z_of_natural s hc hnat hb p hforward
  · exact critical_radius_image_index_le_eight_general s hc hb p

include s in
/-- Conjugation carries the all-image natural radius conclusion to every
component vertex of the original replacement graph. -/
theorem radius_commutator_central_at_of_natural
    (hc : DistanceTwo.CentralLayer d) (hnat : Nat.card (replacementMoved d) = 16)
    (hb : 2 < replacementDistance h d) (a : Vertex d.radical) (ha : color d.radical a = false) :
    ⁅V d.radical a,Q d.radical a⁆ ≤ centralizer (V d.radical a : Set (FreeAmalgam d.radical)) := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color d.radical ha
  have hV : V d.radical (mVertex d.radical g) =
      (V d.radical (alpha d.radical)).map (MulAut.conj g⁻¹).toMonoidHom := by
    simpa only [alpha,act_mVertex,one_mul] using V_act d.radical g (alpha d.radical)
  have hQ : Q d.radical (mVertex d.radical g) =
      (Q d.radical (alpha d.radical)).map (MulAut.conj g⁻¹).toMonoidHom := by
    simpa only [alpha,act_mVertex,one_mul] using Q_act d.radical g (alpha d.radical)
  rw [hV,hQ,←map_commutator]
  exact (map_mono (radius_commutator_central_of_natural s hc hnat hb)).trans
    (map_centralizer_le_centralizer_image (V d.radical (alpha d.radical) : Set (FreeAmalgam d.radical))
      (MulAut.conj g⁻¹).toMonoidHom)

include s in
/-- Source (5.2)(ii)--(iii) on the natural cover, with no point-core condition. -/
theorem radius_bounds_of_natural
    (hc : DistanceTwo.CentralLayer d) (hnat : Nat.card (replacementMoved d) = 16)
    (hb : 2 < replacementDistance h d) {a : Vertex d.radical} (ha : color d.radical a = false)
    (a' c : Vertex d.radical) :
    ⁅V d.radical a,Q d.radical a⁆ ≤ centralizer (V d.radical a : Set (FreeAmalgam d.radical)) ∧
      ⁅V d.radical a,V d.radical a⁆ ≤ X d.radical a ∧
      ⁅⁅X d.radical a' ⊓ Q d.radical a,V d.radical a ⊓ Q d.radical c⁆,
        V d.radical a ⊓ Q d.radical c⁆ = ⊥ := by
  have hc := radius_commutator_central_at_of_natural s hc hnat hb a ha
  exact ⟨hc,CFSG.Quasithin.ChapterC.BinaryMS.MS93.SectionFive.radius_derived_le_X
    d.radical (replacementGeometry h d) hb ha hc,
    CFSG.Quasithin.ChapterC.BinaryMS.MS93.SectionFive.critical_radius_triple_commutator d.radical hc⟩

/-- Application to the actual minimum characteristic replacement of the
original MS2(a) radical. The symmetric marking and central layer are proved. -/
theorem radius_bounds_knownSimple_of_natural
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hnat : Nat.card (replacementMoved d) = 16)
    (hb : 2 < replacementDistance h d) {a : Vertex d.radical} (ha : color d.radical a = false)
    (a' c : Vertex d.radical) :
    ⁅V d.radical a,Q d.radical a⁆ ≤ centralizer (V d.radical a : Set (FreeAmalgam d.radical)) ∧
      ⁅V d.radical a,V d.radical a⁆ ≤ X d.radical a ∧
      ⁅⁅X d.radical a' ⊓ Q d.radical a,V d.radical a ⊓ Q d.radical c⁆,
        V d.radical a ⊓ Q d.radical c⁆ = ⊥ :=
  radius_bounds_of_natural (fullSymmetricAction_knownSimple h e hz hn d hb)
    (DistanceTwo.centralLayer_knownSimple G L R h e hz hn d) hnat hb ha a' c

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

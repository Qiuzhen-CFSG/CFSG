module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CoreMovement
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.NaturalRadius

/-!
# Restricting the moving actor on the original symmetric cover

If a quadratic elementary actor has image of order at least four, its
commutator controls the movement of its pointwise fixer on a subgroup of
index at most two in the original moved cover. For the natural cover this
is the entire cover. In augmentation coordinates, either the commutator
contains the central line, or the two-transposition exception restricts to
the fixed hyperplane of the third transposition. The full central cover and
the given S₆ projection are retained throughout.

The subgroup and its index are transported through injective ambient maps.
At an actual critical endpoint, the radius intersection centralizes the
critical commutator, so the restricted moving actor has its commutator in
the initial seed. Its reverse image has order at least two. The stronger
restriction also preserves the entire commutator with the initial seed;
the exceptional hyperplane retains the order-four moved plane. Fixers on
either cover have fully controlled movement outside the two-transposition
exception. The known-simple
application uses the minimum characteristic replacement of the original
MS2(a) radical, with no point-core or Sylow condition.

This constructs a controlled subactor of the moving layer U. Source (5.0)
uses the full restricted seed Z-hat; its adequate image/even-actor assertion
and the two distance exclusions (5.11)--(5.12) remain with
qt-e-ms-small-a6-exhaustion-large-distance. These results do not assert the
final distance bound or the full exceptional (5.2) argument.
Source: MS93 (3.3)(ii)(1), pp.866--867, (5.0)--(5.2), pp.912--915.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterB.Offenders
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u

private theorem core_moved_map (A : Subgroup S) :
    (subspaceCommutator (coreRepresentation (Fin 6)) ⊤ A).map (coreToNatural (Fin 6)) =
      subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ A := by
  have hh := subspaceCommutator_map_embedding (naturalRepresentation (Fin 6))
    (coreRepresentation (Fin 6)) (MonoidHom.id S) (coreToNatural (Fin 6))
    (fun g v => (coreToNatural_equivariant g v).symm) A ⊤
  rw [Submodule.map_top,LinearMap.range_eq_top.mpr coreToNatural_surjective,Subgroup.map_id] at hh
  exact hh.symm

private theorem core_image_quadratic (A : Subgroup S) (hq : CoreActor.Quadratic A) :
    QuadraticPointCore.Quadratic A := by
  intro a ha b hb v
  obtain ⟨w,rfl⟩ := coreToNatural_surjective v
  have hh := congrArg (coreToNatural (Fin 6)) (hq a ha b hb w)
  simpa only [coreToNatural_equivariant,map_sub] using hh

private theorem core_image_fixer (A Y : Subgroup S)
    (hfix : Y ≤ subspaceKernel (coreRepresentation (Fin 6))
      (subspaceCommutator (coreRepresentation (Fin 6)) ⊤ A) ⊤) :
    Y ≤ subspaceKernel (naturalRepresentation (Fin 6))
      (subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ A) ⊤ := by
  intro y hy
  refine ⟨mem_top _,?_⟩
  intro v hv
  rw [←core_moved_map A] at hv
  obtain ⟨w,hw,rfl⟩ := hv
  rw [←coreToNatural_equivariant,(hfix hy).2 w hw]

private theorem core_moved_control (A Y : Subgroup S) [IsElementaryAbelian 2 A]
    (hcard : 4 ≤ Nat.card A) (hq : CoreActor.Quadratic A)
    (hk : (coreToNatural (Fin 6)).ker ≤ subspaceCommutator (coreRepresentation (Fin 6)) ⊤ A)
    (hfix : Y ≤ subspaceKernel (coreRepresentation (Fin 6))
      (subspaceCommutator (coreRepresentation (Fin 6)) ⊤ A) ⊤) :
    subspaceCommutator (coreRepresentation (Fin 6)) ⊤ Y ≤
      subspaceCommutator (coreRepresentation (Fin 6)) ⊤ A := by
  have hh := natural_moved_control A Y hcard (core_image_quadratic A hq) (core_image_fixer A Y hfix)
  rw [←core_moved_map A,←core_moved_map Y,Submodule.map_le_iff_le_comap,
    Submodule.comap_map_eq, sup_eq_left.mpr hk] at hh
  exact hh

/-- The source exceptional restriction, with codimension at most one, on the
entire augmentation cover. Every subgroup fixing the original commutator
has controlled movement on this same restricted actor. -/
theorem core_restriction (A : Subgroup S) [IsElementaryAbelian 2 A]
    (hcard : 4 ≤ Nat.card A) (hq : CoreActor.Quadratic A) :
    ∃ W : Submodule (ZMod 2) (core (Fin 6)), 4 ≤ Module.finrank (ZMod 2) W ∧
      ∀ Y : Subgroup S, Y ≤ subspaceKernel (coreRepresentation (Fin 6))
          (subspaceCommutator (coreRepresentation (Fin 6)) ⊤ A) ⊤ →
        subspaceCommutator (coreRepresentation (Fin 6)) W Y ≤
          subspaceCommutator (coreRepresentation (Fin 6)) ⊤ A := by
  rcases CoreActor.kernel_or_two_transpositions A hcard hq with hk | ⟨g,rfl⟩
  · refine ⟨⊤,?_,fun Y hf => core_moved_control A Y hcard hq hk hf⟩
    rw [finrank_top,finrank_core]
    decide
  · exact ⟨CoreCrossing.hyperplane.map (coreRepresentation (Fin 6) g),
      (CoreActor.conjugate_hyperplane_finrank g).ge,fun Y hf => CoreActor.exceptional_conjugate_control g Y hf⟩

variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  {h : SmallMSPair κ L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

private theorem cover_fixed_moved (A Y : Subgroup d.overgroup)
    (hfix : ⁅replacementMoved d,A⁆ ≤ centralizer (Y : Set d.overgroup)) :
    Y.map s.projection ≤ subspaceKernel (coverAction s)
      (subspaceCommutator (coverAction s) ⊤ (A.map s.projection)) ⊤ := by
  let := replacementMoved_normal h d
  intro y hy
  obtain ⟨x,hx,rfl⟩ := hy
  refine ⟨mem_top _,?_⟩
  intro v hv
  have hm := NormalElementaryQuotient.commutatorSpace_eq (replacementMoved d) s.projection
    s.surjective (s.projection_kernel.trans (moved_centralizer s).symm) A
  change NormalElementaryQuotient.commutatorSpace (replacementMoved d) A =
    subspaceCommutator (coverAction s) ⊤ (A.map s.projection) at hm
  rw [←hm] at hv
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [coverAction_conjugate]
  have hh : x * (v.toMul : d.overgroup) = (v.toMul : d.overgroup) * x := hfix hv x hx
  rw [hh,mul_inv_cancel_right]

private theorem cover_space_map {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (τ : Representation (ZMod 2) S V) (E : Additive (replacementMoved d) ≃ₗ[ZMod 2] V)
    (hE : ∀ g v, E (coverAction s g v) = τ g (E v)) (A : Subgroup d.overgroup) :
    (NormalElementaryQuotient.commutatorSpace (replacementMoved d) A).map E.toLinearMap =
      subspaceCommutator τ ⊤ (A.map s.projection) := by
  let := replacementMoved_normal h d
  rw [NormalElementaryQuotient.commutatorSpace_eq (replacementMoved d) s.projection
    s.surjective (s.projection_kernel.trans (moved_centralizer s).symm)]
  have hh := subspaceCommutator_map_embedding τ (coverAction s) (MonoidHom.id S) E.toLinearMap
    (fun g v => (hE g v).symm) (A.map s.projection) ⊤
  rw [Submodule.map_top,LinearMap.range_eq_top.mpr E.surjective,Subgroup.map_id] at hh
  exact hh.symm

private theorem coordinates_fixer {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (τ : Representation (ZMod 2) S V) (E : Additive (replacementMoved d) ≃ₗ[ZMod 2] V)
    (hE : ∀ g v, E (coverAction s g v) = τ g (E v)) (A Y : Subgroup d.overgroup)
    (hfix : ⁅replacementMoved d,A⁆ ≤ centralizer (Y : Set d.overgroup)) :
    Y.map s.projection ≤ subspaceKernel τ (subspaceCommutator τ ⊤ (A.map s.projection)) ⊤ := by
  let := replacementMoved_normal h d
  intro y hy
  refine ⟨mem_top _,?_⟩
  intro v hv
  rw [←cover_space_map s τ E hE A] at hv
  obtain ⟨w,hw,rfl⟩ := hv
  have hh := cover_fixed_moved s A Y hfix hy
  have hm := NormalElementaryQuotient.commutatorSpace_eq (replacementMoved d) s.projection
    s.surjective (s.projection_kernel.trans (moved_centralizer s).symm) A
  change NormalElementaryQuotient.commutatorSpace (replacementMoved d) A =
    subspaceCommutator (coverAction s) ⊤ (A.map s.projection) at hm
  change τ y (E w) = E w
  rw [←hE,hh.2 w (hm ▸ hw)]

private theorem coordinates_commutator_le {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (τ : Representation (ZMod 2) S V) (E : Additive (replacementMoved d) ≃ₗ[ZMod 2] V)
    (hE : ∀ g v, E (coverAction s g v) = τ g (E v))
    (P : Submodule (ZMod 2) (Additive (replacementMoved d))) (W : Submodule (ZMod 2) V)
    (hP : P.map E.toLinearMap ≤ W) (A Y : Subgroup d.overgroup)
    (hc : subspaceCommutator τ W (Y.map s.projection) ≤ subspaceCommutator τ ⊤ (A.map s.projection)) :
    ⁅P.toAddSubgroup.toSubgroup'.map (replacementMoved d).subtype,Y⁆ ≤ ⁅replacementMoved d,A⁆ := by
  let := replacementMoved_normal h d
  rw [commutator_comm]
  apply commutator_le.mpr
  rintro y hy _ ⟨v,hv,rfl⟩
  have hvW : E (Additive.ofMul v) ∈ W := hP (Submodule.mem_map_of_mem hv)
  have hdiff : τ (s.projection y) (E (Additive.ofMul v))-E (Additive.ofMul v) ∈
      subspaceCommutator τ ⊤ (A.map s.projection) :=
    hc (Submodule.subset_span ⟨_,mem_map_of_mem s.projection hy,_,hvW,rfl⟩)
  rw [←cover_space_map s τ E hE A] at hdiff
  have hm : coverAction s (s.projection y) (Additive.ofMul v)-Additive.ofMul v ∈
      NormalElementaryQuotient.commutatorSpace (replacementMoved d) A := by
    obtain ⟨w,hw,he⟩ := hdiff
    have he' : w = coverAction s (s.projection y) (Additive.ofMul v)-Additive.ofMul v := by
      apply E.injective
      rw [map_sub,hE]
      exact he
    exact he' ▸ hw
  change (((coverAction s (s.projection y) (Additive.ofMul v)).toMul / v : replacementMoved d) : d.overgroup) ∈
    ⁅replacementMoved d,A⁆ at hm
  simp only [div_eq_mul_inv,Subgroup.coe_mul,Subgroup.coe_inv] at hm
  rw [coverAction_conjugate] at hm
  exact hm

/-- A subgroup of index at most two in the original moved cover controls
all centralizers of the critical commutator. Both cover orders are retained. -/
theorem cover_restriction (A : Subgroup d.overgroup) [IsElementaryAbelian 2 A]
    (hcard : 4 ≤ Nat.card (A.map s.projection))
    (hquad : ⁅replacementMoved d,A⁆ ≤ centralizer (A : Set d.overgroup)) :
    ∃ W : Subgroup d.overgroup, W ≤ replacementMoved d ∧
      W.relIndex (replacementMoved d) ≤ 2 ∧
      ∀ Y : Subgroup d.overgroup, ⁅replacementMoved d,A⁆ ≤ centralizer (Y : Set d.overgroup) →
        ⁅W,Y⁆ ≤ ⁅replacementMoved d,A⁆ := by
  let := replacementMoved_normal h d
  let := IsElementaryAbelian.map (p:=2) (A:=A) s.projection
  rcases cover_model s with ⟨E,hE⟩ | ⟨E,hE⟩
  · refine ⟨replacementMoved d,le_rfl,by simp,?_⟩
    intro Y hY
    have hh := natural_moved_control _ _ hcard (image_quadratic_of_commutator s A hquad)
      (coordinates_fixer s _ E hE A Y hY)
    have hm : NormalElementaryQuotient.commutatorSpace (replacementMoved d) Y ≤
        NormalElementaryQuotient.commutatorSpace (replacementMoved d) A := by
      apply (Submodule.map_le_map_iff_of_injective (f:=E.toLinearMap) E.injective _ _).mp
      rwa [cover_space_map s _ E hE Y,cover_space_map s _ E hE A]
    intro x hx
    exact hm (show Additive.ofMul (⟨x,(commutator_le_left _ _) hx⟩ : replacementMoved d) ∈
      NormalElementaryQuotient.commutatorSpace (replacementMoved d) Y from hx)
  · have hq : CoreActor.Quadratic (A.map s.projection) := by
      intro a ha b hb v
      exact (coordinates_fixer s _ E hE A A hquad ha).2 _
        (Submodule.subset_span ⟨b,hb,v,Submodule.mem_top,rfl⟩)
    obtain ⟨W,hW,hcontrol⟩ := core_restriction _ hcard hq
    let P := W.comap E.toLinearMap
    let F := P.toAddSubgroup.toSubgroup'
    refine ⟨F.map (replacementMoved d).subtype,(map_le_range (replacementMoved d).subtype F).trans_eq (range_subtype _),?_,?_⟩
    · have hP : Module.finrank (ZMod 2) P = Module.finrank (ZMod 2) W := by
        have hm : P.map E.toLinearMap = W := Submodule.map_comap_eq_of_surjective E.surjective W
        rw [←hm,E.finrank_map_eq]
      have hF : 16 ≤ Nat.card F := by
        change 16 ≤ Nat.card P
        rw [Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod,hP]
        exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hW
      have hU : Nat.card (replacementMoved d) = 32 := by
        change Nat.card (Additive (replacementMoved d)) = 32
        rw [Nat.card_congr E.toEquiv,Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod,finrank_core]
        decide
      have hc := F.card_mul_index
      rw [hU] at hc
      have hm : (⊤ : Subgroup (replacementMoved d)).map (replacementMoved d).subtype = replacementMoved d := by
        rw [←MonoidHom.range_eq_map,range_subtype]
      have hidx := relIndex_map_map_of_injective F ⊤ (replacementMoved d).subtype_injective
      rw [hm,relIndex_top_right] at hidx
      rw [hidx]
      have hpos := Nat.card_pos (α:=F)
      nlinarith
    · intro Y hY
      apply coordinates_commutator_le s _ E hE P W
      · exact (Submodule.map_comap_eq_of_surjective E.surjective W).le
      · exact hcontrol (Y.map s.projection) (coordinates_fixer s _ E hE A Y hY)

include s in
/-- The restriction commutes with every injective ambient realization,
including conjugated vertex stabilizers in the actual amalgam. -/
theorem embedded_cover_restriction {H : Type*} [Group H]
    (i : d.overgroup →* H) (hi : Function.Injective i)
    (A : Subgroup H) [IsElementaryAbelian 2 A] (hA : A ≤ i.range)
    (hcard : 4 ≤ ((pCore 2 d.overgroup).map i).relIndex A)
    (hquad : ⁅(replacementMoved d).map i,A⁆ ≤ centralizer (A : Set H)) :
    ∃ W : Subgroup H, W ≤ (replacementMoved d).map i ∧
      W.relIndex ((replacementMoved d).map i) ≤ 2 ∧
      ∀ Y : Subgroup H, Y ≤ i.range →
        ⁅(replacementMoved d).map i,A⁆ ≤ centralizer (Y : Set H) →
        ⁅W,Y⁆ ≤ ⁅(replacementMoved d).map i,A⁆ := by
  let A₀ := A.comap i
  let := IsElementaryAbelian.comap_of_injective (p:=2) i hi A
  have hmA : A₀.map i = A := map_comap_eq_self hA
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
  obtain ⟨W,hW,hindex,hcontrol⟩ := cover_restriction s A₀ hcard₀ (hfix A hquad)
  refine ⟨W.map i,map_mono hW,?_,?_⟩
  · rwa [relIndex_map_map_of_injective _ _ hi]
  · intro Y hY hc
    have hh := map_mono (f:=i) (hcontrol (Y.comap i) (hfix Y hc))
    rwa [map_commutator,map_commutator,map_comap_eq_self hY,hmA] at hh

include s in
/-- The restricted moving actor at an actual critical endpoint controls the
radius intersection, for every radical image and both cover orders. -/
theorem critical_radius_restricted_commutator
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hforward : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    ∃ W : Subgroup (FreeAmalgam d.radical), W ≤ U d.radical a' ∧
      W.relIndex (U d.radical a') ≤ 2 ∧
      2 ≤ (Q d.radical a).relIndex W ∧
      ⁅V d.radical a ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)),W⁆ ≤ Z d.radical a := by
  have hl : 2 < p.walk.length := by rw [p.length_eq_b]; exact hb
  let t := p.walk.getVert (p.walk.length-1)
  have hct : Adjacent d.radical a' t := by
    have hh := p.walk.adj_getVert_succ (i:=p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hct
    rw [p.end_color] at hh
    cases he : color d.radical t <;> simp_all
  have het : Adjacent d.radical (p.walk.getVert (p.walk.length-2)) t := by
    have hh := p.walk.adj_getVert_succ (i:=p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  let Y := V d.radical a ⊓ Q d.radical (p.walk.getVert (p.walk.length-2))
  have hYt : Y ≤ Q d.radical t := inf_le_right.trans (Q_le_adjacent_h d.radical ht het)
  have hY : Y ≤ stabilizer d.radical a' := fun _ hx =>
    (hYt hx).2 _ (adjacent_symm d.radical hct)
  have hcomm : ⁅U d.radical a',Z d.radical a⁆ ≤ ⁅Z d.radical a,Z d.radical a'⁆ := by
    rw [commutator_comm]
    exact commutator_mono le_rfl (DistanceEight.U_le_Z d.radical a')
  have hRZa : ⁅Z d.radical a,Z d.radical a'⁆ ≤ Z d.radical a :=
    ((critical_Z_commutator_le_moving (h:=h) p).trans inf_le_left).trans (DistanceEight.U_le_Z d.radical a)
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color
  have hAA : ⁅U d.radical a',Z d.radical a⁆ ≤
      centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    (hcomm.trans hRZa).trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hAY : ⁅U d.radical a',Z d.radical a⁆ ≤ centralizer (Y : Set (FreeAmalgam d.radical)) :=
    hcomm.trans (le_centralizer_iff.mp (critical_radius_intersection_centralizes (h:=h) p hb))
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h:=h) hc a' p.end_color
  have hA : Z d.radical a ≤ i.range := by
    rw [hir]
    exact Z_le_stabilizer_of_dist_le a _ p.critical.1.le
  obtain ⟨W,hW,hindex,hcontrol⟩ := embedded_cover_restriction s i hi (Z d.radical a) hA
    (hiQ.symm ▸ hforward) (hiU.symm ▸ hAA)
  have hWU : W ≤ U d.radical a' := hiU ▸ hW
  have hWi : W.relIndex (U d.radical a') ≤ 2 := hiU ▸ hindex
  have hreverse := reverse_critical_moving_image_four_le s hc p hforward
  let : Finite (U d.radical a') := by
    apply Nat.finite_of_card_ne_zero
    rw [←hiU,card_map_of_injective hi]
    exact Nat.card_pos.ne'
  have hmul := relIndex_inf_mul_relIndex (Q d.radical a) W (U d.radical a')
  rw [inf_eq_left.mpr hWU] at hmul
  have hle : (Q d.radical a).relIndex (U d.radical a') ≤
      (Q d.radical a ⊓ W).relIndex (U d.radical a') :=
    relIndex_le_of_le_left inf_le_left index_ne_zero_of_finite
  have htwo : 2 ≤ (Q d.radical a).relIndex W := by
    rw [←hmul] at hle
    by_contra hn
    have hu : (Q d.radical a).relIndex W ≤ 1 := by omega
    have hh := Nat.mul_le_mul hu hWi
    omega
  refine ⟨W,hWU,hWi,htwo,?_⟩
  rw [commutator_comm]
  have hh := hcontrol Y (hY.trans_eq hir.symm) (hiU.symm ▸ hAY)
  rw [hiU] at hh
  exact hh.trans (hcomm.trans hRZa)

/-- Application of the exceptional-actor calculation to the minimum
characteristic replacement of the original MS2(a) radical. -/
theorem critical_radius_restricted_commutator_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hforward : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    ∃ W : Subgroup (FreeAmalgam d.radical), W ≤ U d.radical a' ∧
      W.relIndex (U d.radical a') ≤ 2 ∧
      2 ≤ (Q d.radical a).relIndex W ∧
      ⁅V d.radical a ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)),W⁆ ≤ Z d.radical a :=
  critical_radius_restricted_commutator (fullSymmetricAction_knownSimple h e hz hn d hb)
    (DistanceTwo.centralLayer_knownSimple G L R h e hz hn d) hb p hforward

/-- The source restriction controls all fixers and preserves the critical
commutator itself. -/
theorem core_restriction_preserving (A : Subgroup S) [IsElementaryAbelian 2 A]
    (hcard : 4 ≤ Nat.card A) (hq : CoreActor.Quadratic A) :
    ∃ W : Submodule (ZMod 2) (core (Fin 6)), 4 ≤ Module.finrank (ZMod 2) W ∧
      subspaceCommutator (coreRepresentation (Fin 6)) W A =
        subspaceCommutator (coreRepresentation (Fin 6)) ⊤ A ∧
      ∀ Y : Subgroup S, Y ≤ subspaceKernel (coreRepresentation (Fin 6))
          (subspaceCommutator (coreRepresentation (Fin 6)) ⊤ A) ⊤ →
        subspaceCommutator (coreRepresentation (Fin 6)) W Y ≤
          subspaceCommutator (coreRepresentation (Fin 6)) ⊤ A := by
  rcases CoreActor.kernel_or_two_transpositions A hcard hq with hk | ⟨g,rfl⟩
  · refine ⟨⊤,?_,rfl,fun Y hf => core_moved_control A Y hcard hq hk hf⟩
    rw [finrank_top,finrank_core]
    decide
  · exact ⟨CoreCrossing.hyperplane.map (coreRepresentation (Fin 6) g),
      (CoreActor.conjugate_hyperplane_finrank g).ge,
      CoreMovement.conjugate_restricted_moved_eq g,
      fun Y hf => CoreActor.exceptional_conjugate_control g Y hf⟩

private theorem coordinates_movement_preserved {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (τ : Representation (ZMod 2) S V) (E : Additive (replacementMoved d) ≃ₗ[ZMod 2] V)
    (hE : ∀ g v, E (coverAction s g v) = τ g (E v))
    (P : Submodule (ZMod 2) (Additive (replacementMoved d))) (W : Submodule (ZMod 2) V)
    (hP : P.map E.toLinearMap = W) (A : Subgroup d.overgroup)
    (hm : subspaceCommutator τ W (A.map s.projection) = subspaceCommutator τ ⊤ (A.map s.projection)) :
    ⁅P.toAddSubgroup.toSubgroup'.map (replacementMoved d).subtype,A⁆ = ⁅replacementMoved d,A⁆ := by
  let := replacementMoved_normal h d
  let F := P.toAddSubgroup.toSubgroup'.map (replacementMoved d).subtype
  have hFU : F ≤ replacementMoved d := (map_le_range _ _).trans_eq (range_subtype _)
  let N := ⁅F,A⁆
  let C := AddSubgroup.toZModSubmodule 2 (N.subgroupOf (replacementMoved d)).toAddSubgroup
  have hbound : subspaceCommutator τ W (A.map s.projection) ≤ C.map E.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨_,⟨a,ha,rfl⟩,v,hv,rfl⟩
    rw [←hP] at hv
    obtain ⟨w,hw,rfl⟩ := hv
    refine ⟨coverAction s (s.projection a) w-w,?_,by
      change E (coverAction s (s.projection a) w-w) = _
      exact (map_sub E.toLinearMap _ _).trans
        (congrArg (fun z => z-E w) (hE (s.projection a) w))⟩
    change (((coverAction s (s.projection a) w).toMul / w.toMul : replacementMoved d) : d.overgroup) ∈ N
    simp only [div_eq_mul_inv,Subgroup.coe_mul,Subgroup.coe_inv]
    rw [coverAction_conjugate]
    change ⁅a,(w.toMul : d.overgroup)⁆ ∈ ⁅F,A⁆
    rw [commutator_comm]
    exact commutator_mem_commutator ha (mem_map_of_mem _ hw)
  rw [hm,←cover_space_map s τ E hE A] at hbound
  have hh : NormalElementaryQuotient.commutatorSpace (replacementMoved d) A ≤ C :=
    (Submodule.map_le_map_iff_of_injective E.injective _ _).mp hbound
  apply le_antisymm (commutator_mono hFU le_rfl)
  intro x hx
  exact hh (show Additive.ofMul (⟨x,(commutator_le_left _ _) hx⟩ : replacementMoved d) ∈
    NormalElementaryQuotient.commutatorSpace (replacementMoved d) A from hx)


/-- A controlling subactor retaining the complete original commutator. -/
theorem cover_restriction_preserving (A : Subgroup d.overgroup) [IsElementaryAbelian 2 A]
    (hcard : 4 ≤ Nat.card (A.map s.projection))
    (hquad : ⁅replacementMoved d,A⁆ ≤ centralizer (A : Set d.overgroup)) :
    ∃ W : Subgroup d.overgroup, W ≤ replacementMoved d ∧
      W.relIndex (replacementMoved d) ≤ 2 ∧
      ⁅W,A⁆ = ⁅replacementMoved d,A⁆ ∧
      ∀ Y : Subgroup d.overgroup, ⁅replacementMoved d,A⁆ ≤ centralizer (Y : Set d.overgroup) →
        ⁅W,Y⁆ ≤ ⁅replacementMoved d,A⁆ := by
  let := replacementMoved_normal h d
  let := IsElementaryAbelian.map (p:=2) (A:=A) s.projection
  rcases cover_model s with ⟨E,hE⟩ | ⟨E,hE⟩
  · refine ⟨replacementMoved d,le_rfl,by simp,rfl,?_⟩
    intro Y hY
    have hh := natural_moved_control _ _ hcard (image_quadratic_of_commutator s A hquad)
      (coordinates_fixer s _ E hE A Y hY)
    have hm : NormalElementaryQuotient.commutatorSpace (replacementMoved d) Y ≤
        NormalElementaryQuotient.commutatorSpace (replacementMoved d) A := by
      apply (Submodule.map_le_map_iff_of_injective (f:=E.toLinearMap) E.injective _ _).mp
      rwa [cover_space_map s _ E hE Y,cover_space_map s _ E hE A]
    intro x hx
    exact hm (show Additive.ofMul (⟨x,(commutator_le_left _ _) hx⟩ : replacementMoved d) ∈
      NormalElementaryQuotient.commutatorSpace (replacementMoved d) Y from hx)
  · have hq : CoreActor.Quadratic (A.map s.projection) := by
      intro a ha b hb v
      exact (coordinates_fixer s _ E hE A A hquad ha).2 _
        (Submodule.subset_span ⟨b,hb,v,Submodule.mem_top,rfl⟩)
    obtain ⟨W,hW,hpres,hcontrol⟩ := core_restriction_preserving _ hcard hq
    let P := W.comap E.toLinearMap
    let F := P.toAddSubgroup.toSubgroup'
    refine ⟨F.map (replacementMoved d).subtype,(map_le_range (replacementMoved d).subtype F).trans_eq (range_subtype _),?_,?_,?_⟩
    · have hP : Module.finrank (ZMod 2) P = Module.finrank (ZMod 2) W := by
        have hm : P.map E.toLinearMap = W := Submodule.map_comap_eq_of_surjective E.surjective W
        rw [←hm,E.finrank_map_eq]
      have hF : 16 ≤ Nat.card F := by
        change 16 ≤ Nat.card P
        rw [Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod,hP]
        exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hW
      have hU : Nat.card (replacementMoved d) = 32 := by
        change Nat.card (Additive (replacementMoved d)) = 32
        rw [Nat.card_congr E.toEquiv,Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod,finrank_core]
        decide
      have hc := F.card_mul_index
      rw [hU] at hc
      have hm : (⊤ : Subgroup (replacementMoved d)).map (replacementMoved d).subtype = replacementMoved d := by
        rw [←MonoidHom.range_eq_map,range_subtype]
      have hidx := relIndex_map_map_of_injective F ⊤ (replacementMoved d).subtype_injective
      rw [hm,relIndex_top_right] at hidx
      rw [hidx]
      have hpos := Nat.card_pos (α:=F)
      nlinarith
    · exact coordinates_movement_preserved s _ E hE P W
        (Submodule.map_comap_eq_of_surjective E.surjective W) A hpres
    · intro Y hY
      apply coordinates_commutator_le s _ E hE P W
      · exact (Submodule.map_comap_eq_of_surjective E.surjective W).le
      · exact hcontrol (Y.map s.projection) (coordinates_fixer s _ E hE A Y hY)

include s in
/-- The restriction commutes with every injective ambient realization,
including conjugated vertex stabilizers in the actual amalgam. -/
theorem embedded_cover_restriction_preserving {H : Type*} [Group H]
    (i : d.overgroup →* H) (hi : Function.Injective i)
    (A : Subgroup H) [IsElementaryAbelian 2 A] (hA : A ≤ i.range)
    (hcard : 4 ≤ ((pCore 2 d.overgroup).map i).relIndex A)
    (hquad : ⁅(replacementMoved d).map i,A⁆ ≤ centralizer (A : Set H)) :
    ∃ W : Subgroup H, W ≤ (replacementMoved d).map i ∧
      W.relIndex ((replacementMoved d).map i) ≤ 2 ∧
      ⁅W,A⁆ = ⁅(replacementMoved d).map i,A⁆ ∧
      ∀ Y : Subgroup H, Y ≤ i.range →
        ⁅(replacementMoved d).map i,A⁆ ≤ centralizer (Y : Set H) →
        ⁅W,Y⁆ ≤ ⁅(replacementMoved d).map i,A⁆ := by
  let A₀ := A.comap i
  let := IsElementaryAbelian.comap_of_injective (p:=2) i hi A
  have hmA : A₀.map i = A := map_comap_eq_self hA
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
  obtain ⟨W,hW,hindex,hpres,hcontrol⟩ := cover_restriction_preserving s A₀ hcard₀ (hfix A hquad)
  refine ⟨W.map i,map_mono hW,?_,?_,?_⟩
  · rwa [relIndex_map_map_of_injective _ _ hi]
  · have hh := congrArg (fun B : Subgroup d.overgroup => B.map i) hpres
    simpa only [map_commutator,hmA] using hh
  · intro Y hY hc
    have hh := map_mono (f:=i) (hcontrol (Y.comap i) (hfix Y hc))
    rwa [map_commutator,map_commutator,map_comap_eq_self hY,hmA] at hh


include s in
/-- The restricted moving actor at an actual critical endpoint controls the
radius intersection, for every radical image and both cover orders. -/
theorem critical_radius_restricted_commutator_preserving
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hforward : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    ∃ W : Subgroup (FreeAmalgam d.radical), W ≤ U d.radical a' ∧
      W.relIndex (U d.radical a') ≤ 2 ∧
      2 ≤ (Q d.radical a).relIndex W ∧
      ⁅W,Z d.radical a⁆ = ⁅U d.radical a',Z d.radical a⁆ ∧
      ⁅V d.radical a ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)),W⁆ ≤ Z d.radical a := by
  have hl : 2 < p.walk.length := by rw [p.length_eq_b]; exact hb
  let t := p.walk.getVert (p.walk.length-1)
  have hct : Adjacent d.radical a' t := by
    have hh := p.walk.adj_getVert_succ (i:=p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hct
    rw [p.end_color] at hh
    cases he : color d.radical t <;> simp_all
  have het : Adjacent d.radical (p.walk.getVert (p.walk.length-2)) t := by
    have hh := p.walk.adj_getVert_succ (i:=p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  let Y := V d.radical a ⊓ Q d.radical (p.walk.getVert (p.walk.length-2))
  have hYt : Y ≤ Q d.radical t := inf_le_right.trans (Q_le_adjacent_h d.radical ht het)
  have hY : Y ≤ stabilizer d.radical a' := fun _ hx =>
    (hYt hx).2 _ (adjacent_symm d.radical hct)
  have hcomm : ⁅U d.radical a',Z d.radical a⁆ ≤ ⁅Z d.radical a,Z d.radical a'⁆ := by
    rw [commutator_comm]
    exact commutator_mono le_rfl (DistanceEight.U_le_Z d.radical a')
  have hRZa : ⁅Z d.radical a,Z d.radical a'⁆ ≤ Z d.radical a :=
    ((critical_Z_commutator_le_moving (h:=h) p).trans inf_le_left).trans (DistanceEight.U_le_Z d.radical a)
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color
  have hAA : ⁅U d.radical a',Z d.radical a⁆ ≤
      centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    (hcomm.trans hRZa).trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hAY : ⁅U d.radical a',Z d.radical a⁆ ≤ centralizer (Y : Set (FreeAmalgam d.radical)) :=
    hcomm.trans (le_centralizer_iff.mp (critical_radius_intersection_centralizes (h:=h) p hb))
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h:=h) hc a' p.end_color
  have hA : Z d.radical a ≤ i.range := by
    rw [hir]
    exact Z_le_stabilizer_of_dist_le a _ p.critical.1.le
  obtain ⟨W,hW,hindex,hpres,hcontrol⟩ := embedded_cover_restriction_preserving s i hi (Z d.radical a) hA
    (hiQ.symm ▸ hforward) (hiU.symm ▸ hAA)
  have hWU : W ≤ U d.radical a' := hiU ▸ hW
  have hWi : W.relIndex (U d.radical a') ≤ 2 := hiU ▸ hindex
  have hreverse := reverse_critical_moving_image_four_le s hc p hforward
  let : Finite (U d.radical a') := by
    apply Nat.finite_of_card_ne_zero
    rw [←hiU,card_map_of_injective hi]
    exact Nat.card_pos.ne'
  have hmul := relIndex_inf_mul_relIndex (Q d.radical a) W (U d.radical a')
  rw [inf_eq_left.mpr hWU] at hmul
  have hle : (Q d.radical a).relIndex (U d.radical a') ≤
      (Q d.radical a ⊓ W).relIndex (U d.radical a') :=
    relIndex_le_of_le_left inf_le_left index_ne_zero_of_finite
  have htwo : 2 ≤ (Q d.radical a).relIndex W := by
    rw [←hmul] at hle
    by_contra hn
    have hu : (Q d.radical a).relIndex W ≤ 1 := by omega
    have hh := Nat.mul_le_mul hu hWi
    omega
  refine ⟨W,hWU,hWi,htwo,hiU ▸ hpres,?_⟩
  rw [commutator_comm]
  have hh := hcontrol Y (hY.trans_eq hir.symm) (hiU.symm ▸ hAY)
  rw [hiU] at hh
  exact hh.trans (hcomm.trans hRZa)

/-- Application of the exceptional-actor calculation to the minimum
characteristic replacement of the original MS2(a) radical. -/
theorem critical_radius_restricted_commutator_preserving_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hforward : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    ∃ W : Subgroup (FreeAmalgam d.radical), W ≤ U d.radical a' ∧
      W.relIndex (U d.radical a') ≤ 2 ∧
      2 ≤ (Q d.radical a).relIndex W ∧
      ⁅W,Z d.radical a⁆ = ⁅U d.radical a',Z d.radical a⁆ ∧
      ⁅V d.radical a ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)),W⁆ ≤ Z d.radical a :=
  critical_radius_restricted_commutator_preserving (fullSymmetricAction_knownSimple h e hz hn d hb)
    (DistanceTwo.centralLayer_knownSimple G L R h e hz hn d) hb p hforward

/-- Outside the two-transposition exception, every fixer of the original
commutator has its movement in that commutator, for either cover order. -/
theorem cover_commutator_control_of_nonexceptional
    (A Y : Subgroup d.overgroup) [IsElementaryAbelian 2 A]
    (hcard : 4 ≤ Nat.card (A.map s.projection))
    (hnot : ¬ CFSG.Quasithin.ChapterB.Offenders.IsConjugateTo
      (A.map s.projection) (CFSG.Quasithin.ChapterB.Offenders.disjointTranspositions 6 2))
    (hquad : ⁅replacementMoved d,A⁆ ≤ centralizer (A : Set d.overgroup))
    (hfix : ⁅replacementMoved d,A⁆ ≤ centralizer (Y : Set d.overgroup)) :
    ⁅replacementMoved d,Y⁆ ≤ ⁅replacementMoved d,A⁆ := by
  let := replacementMoved_normal h d
  let := IsElementaryAbelian.map (p:=2) (A:=A) s.projection
  have transfer {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
      (τ : Representation (ZMod 2) S V) (E : Additive (replacementMoved d) ≃ₗ[ZMod 2] V)
      (hE : ∀ g v, E (coverAction s g v) = τ g (E v))
      (hm : subspaceCommutator τ ⊤ (Y.map s.projection) ≤
        subspaceCommutator τ ⊤ (A.map s.projection)) :
      ⁅replacementMoved d,Y⁆ ≤ ⁅replacementMoved d,A⁆ := by
    have hh : NormalElementaryQuotient.commutatorSpace (replacementMoved d) Y ≤
        NormalElementaryQuotient.commutatorSpace (replacementMoved d) A := by
      apply (Submodule.map_le_map_iff_of_injective (f:=E.toLinearMap) E.injective _ _).mp
      rwa [cover_space_map s τ E hE Y,cover_space_map s τ E hE A]
    intro x hx
    exact hh (show Additive.ofMul (⟨x,(commutator_le_left _ _) hx⟩ : replacementMoved d) ∈
      NormalElementaryQuotient.commutatorSpace (replacementMoved d) Y from hx)
  rcases cover_model s with ⟨E,hE⟩ | ⟨E,hE⟩
  · exact transfer _ E hE (natural_moved_control _ _ hcard
      (image_quadratic_of_commutator s A hquad) (coordinates_fixer s _ E hE A Y hfix))
  · have hq : CoreActor.Quadratic (A.map s.projection) := by
      intro a ha b hb v
      exact (coordinates_fixer s _ E hE A A hquad ha).2 _
        (Submodule.subset_span ⟨b,hb,v,Submodule.mem_top,rfl⟩)
    have hk := (CoreActor.kernel_or_two_transpositions (A.map s.projection) hcard hq).resolve_right hnot
    exact transfer _ E hE (core_moved_control _ _ hcard hq hk (coordinates_fixer s _ E hE A Y hfix))


end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.HallPlacement.SingleComparison
public import CFSG.Quasithin.ChapterB.QuasisimpleOffenderModels
public import Theory.GroupTheory.ReducedNormal.CentralSeedOvergroup
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.Containing

/-!
# The literal comparison action before Hall placement

Let I be the actual common overcomponent and J = IT. The normal closure
of the original omega-center seed in J is reduced. It contains the
original H-orbit, so its conjugation action has the original Thompson
movement. The complete B.5.1 theorem therefore applies to the actual
centralizer quotient and the image of I. The smaller comparison image
is nontrivial and remains a local C-component under its marked Sylow.
A proper smaller image gives actual containing-model isomorphisms.

The orbit here is the full normal closure, including any fixed summands;
no equality with the commutator module or with a two-core quotient is
assumed. The generic B.5.1 model sieve is reused from Containing; no
point-control conclusion is used. The Hall consumer is ActionPlacement.
Source: Aschbacher–Smith 10.2.3, printed pp.745–746, and B.5.1.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
open Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {H : Subgroup G} {B : Subgroup H} {ctx : Context D H B}

/-- The actual join of the containing component and the original full Sylow. -/
abbrev ComparisonConfiguration.join (c : ComparisonConfiguration D ctx) : Subgroup G :=
  c.overcomponent ⊔ (T : Subgroup G)

/-- The original omega-center orbit, intrinsic in the actual join. -/
abbrev ComparisonConfiguration.orbit (c : ComparisonConfiguration D ctx) : Subgroup (c.join D) :=
  (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (c.join D)).subgroupOf (c.join D)

/-- The actual comparison join stays in its supplied common maximal two-local. -/
theorem ComparisonConfiguration.join_le_ambient (c : ComparisonConfiguration D ctx) :
    c.join D ≤ c.ambient :=
  sup_le c.overcomponent_mem.1
    ((show (T : Subgroup G) ≤ H from ctx.hstar.1.1.2).trans
      (le_sup_right.trans c.borel_overgroup))

/-- The component–Sylow generation identity embeds the original H in the join. -/
theorem ComparisonConfiguration.original_le_join (c : ComparisonConfiguration D ctx) :
    H ≤ c.join D := by
  have hg := congrArg (Subgroup.map H.subtype) c.generates
  have hS : (T.subtype ctx.hstar.1.1.2 : Subgroup H).map H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le ctx.hstar.1.1.2
  rw [Subgroup.map_sup, hS,
    ←MonoidHom.range_eq_map,range_subtype] at hg
  exact hg.ge.trans (sup_le_sup_right c.component_le _)

/-- The original common maximal two-local supplies the genuine SQTK hypothesis. -/
theorem ComparisonConfiguration.join_sqtk (c : ComparisonConfiguration D ctx) :
    IsSQTK KnownSimple.IsKnownSimple (c.join D) :=
  (IsSQTK.equiv (subgroupOfEquivOfLe (c.join_le_ambient D))).mp
    ((D.simpleQTKE.twoLocal_sqtk c.maximal.1).subgroup _)

/-- The full Sylow makes the actual join a group of characteristic two. -/
theorem ComparisonConfiguration.join_characteristic_two (c : ComparisonConfiguration D ctx) :
    centralizer (pCore 2 (c.join D) : Set (c.join D)) ≤ pCore 2 (c.join D) := by
  have hTM : (T : Subgroup G) ≤ c.ambient :=
    le_sup_right.trans (c.join_le_ambient D)
  have hc := centralizer_pCore_le_of_sylow_le (T.subtype hTM)
    ((c.join D).subgroupOf c.ambient)
    (show (T.subtype hTM : Subgroup c.ambient) ≤ (c.join D).subgroupOf c.ambient from
      fun _ hx => (show (T : Subgroup G) ≤ c.join D from le_sup_right) hx)
    (D.simpleQTKE.evenCharacteristic T c.ambient c.maximal hTM)
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2
    (subgroupOfEquivOfLe (c.join_le_ambient D))).mp hc

/-- The original central Sylow seed has a reduced normal closure in the join. -/
theorem ComparisonConfiguration.orbit_reduced (c : ComparisonConfiguration D ctx) :
    IsPReduced 2 (c.orbit D) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let : IsElementaryAbelian 2 Z := omegaOneCenterAmbient_elementaryAbelian _
  exact reduced_conjugateSpan_of_sylow_central T (c.join D) Z le_sup_right
    (fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
    (fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2)
    (c.join_characteristic_two D)

/-- The single comparison makes the containing component normal in the join. -/
theorem ComparisonConfiguration.single_component_normal (c : ComparisonConfiguration D ctx)
    (hsingle : c.component = pResidual 2 H) :
    (c.overcomponent.subgroupOf (c.join D)).Normal :=
  normal_subgroupOf_of_le_normalizer
    (sup_le c.overcomponent.le_normalizer (c.single_overcomponent_normalized D hsingle))

/-- Movement on the original H-orbit persists on the larger literal orbit. -/
theorem ComparisonConfiguration.orbit_thompson_moves (c : ComparisonConfiguration D ctx)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    ¬ elementaryAbelianMaxJ (T.subtype (show (T : Subgroup G) ≤ c.join D from le_sup_right) :
      Subgroup (c.join D)) ≤ centralizer (c.orbit D : Set (c.join D)) := by
  let J := c.join D
  let P := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  let S := T.subtype ctx.hstar.1.1.2
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  have hP : (elementaryAbelianMaxJ (P : Subgroup J)).map J.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective J.subtype J.subtype_injective]
    exact congrArg elementaryAbelianMaxJ (map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ J from le_sup_right))
  have hS : (elementaryAbelianMaxJ (S : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective]
    exact congrArg elementaryAbelianMaxJ (map_subgroupOf_eq_of_le ctx.hstar.1.1.2)
  intro hc
  apply ctx.hstar_thompson_moves_omega_orbit D n hn hF e
  intro x hx w hw
  have hxT : (x : G) ∈ elementaryAbelianMaxJ (T : Subgroup G) :=
    hS ▸ mem_map_of_mem H.subtype hx
  obtain ⟨y,hy,he⟩ := hP.symm ▸ hxT
  have hwJ : (w : G) ∈ J := c.original_le_join D w.property
  have hwO : (⟨w,hwJ⟩ : J) ∈ c.orbit D :=
    conjugateSpanBy_mono le_rfl (c.original_le_join D) hw
  have hh := congrArg J.subtype (hc hy ⟨w,hwJ⟩ hwO)
  change (w : G) * (y : G) = (y : G) * w at hh
  change (y : G) = (x : G) at he
  rw [he] at hh
  exact Subtype.ext hh

/-- The actual centralizer quotient and component image satisfy complete B.5.1. -/
theorem ComparisonConfiguration.single_ff_action (c : ComparisonConfiguration D ctx)
    (hsingle : c.component = pResidual 2 H)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    letI := (c.orbit_reduced D).normal
    letI := (c.orbit_reduced D).elementary
    let A := (c.overcomponent.subgroupOf (c.join D)).map (actionMk (c.orbit D))
    let N := offenderSubgroup (action (c.orbit D))
    IsQuasisimple A ∧ A ≤ N ∧ IsFFModule (action (c.orbit D)) ∧
      Function.Injective (action (c.orbit D)) ∧
      Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        ((action (c.orbit D)).comp N.subtype) (A.subgroupOf N)) := by
  let J := c.join D
  let W := c.orbit D
  let I := c.overcomponent.subgroupOf J
  let P := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  let := (c.orbit_reduced D).normal
  let := (c.orbit_reduced D).elementary
  let := c.single_component_normal D hsingle
  have hI' : I.IsCComponent := (c.local_components D).2.1
  have hIP : I ⊔ (P : Subgroup J) = ⊤ := by
    change c.overcomponent.subgroupOf J ⊔ (T : Subgroup G).subgroupOf J = ⊤
    rw [←subgroupOf_sup (show c.overcomponent ≤ J from le_sup_left)
      (show (T : Subgroup G) ≤ J from le_sup_right),subgroupOf_self]
  have hm := c.orbit_thompson_moves D n hn hF e
  have hcore := (c.orbit_reduced D).quotient_pCore_eq_bot
  have hq := quasisimple_of_thompson_movement
    ChapterB.SourceInduction.adequateClassification_knownSimple (c.join_sqtk D) P I W hI' hIP hcore hm
  let := hq
  exact ⟨hq,component_le_offenderSubgroup P I W hIP hcore hm,
    isFFModule_of_thompson_movement P W hm,action_faithful W,
    quasisimple_source_conclusion_of_thompson_movement (c.join_sqtk D) P I W hI' hIP hcore hm⟩

end CFSG.Quasithin.Chapter10.MovingHall.HallPlacement

namespace CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
open Chapter3.Section02 ChapterB.InternalThompsonAction ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {H : Subgroup G} {B : Subgroup H} {ctx : Context D H B}

/-- The original comparison acts nontrivially on the actual containing orbit. -/
theorem ComparisonConfiguration.small_image_ne_bot (c : ComparisonConfiguration D ctx) :
    letI := (c.orbit_reduced D).normal
    ((c.component.map H.subtype).subgroupOf (c.join D)).map (actionMk (c.orbit D)) ≠ ⊥ := by
  let J := c.join D
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let K := c.component.map H.subtype
  let := (c.orbit_reduced D).normal
  let q := actionMk (c.orbit D)
  have hKJ : K ≤ J := c.component_le.trans le_sup_left
  have hZT : Z ≤ (T : Subgroup G) :=
    fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hZJ : Z ≤ J := hZT.trans le_sup_right
  intro hz
  have hk : K.subgroupOf J ≤ q.ker := (Subgroup.map_eq_bot_iff _).mp hz
  have hKC : K ≤ centralizer (Z : Set G) := by
    intro k hk' z hz'
    have hc : (⟨k,hKJ hk'⟩ : J) ∈ centralizer (c.orbit D : Set J) :=
      (QuotientGroup.eq_one_iff _).mp (hk (show (⟨k,hKJ hk'⟩ : J) ∈ K.subgroupOf J from hk'))
    exact congrArg J.subtype (hc ⟨z,hZJ hz'⟩ (le_conjugateSpanBy Z J hz'))
  have hTC : (T : Subgroup G) ≤ centralizer (Z : Set G) := by
    intro t ht z hz
    exact (((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht).symm
  have hg := congrArg (Subgroup.map H.subtype) c.generates
  have hS : (T.subtype ctx.hstar.1.1.2 : Subgroup H).map H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le ctx.hstar.1.1.2
  rw [Subgroup.map_sup,hS,←MonoidHom.range_eq_map,range_subtype] at hg
  have hHC : H ≤ centralizer (Z : Set G) := hg.ge.trans (sup_le hKC hTC)
  exact ctx.moving (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hHC))

/-- The actual action kernel inside the containing C-component is solvable. -/
theorem ComparisonConfiguration.action_kernel_solvable (c : ComparisonConfiguration D ctx) :
    letI := (c.orbit_reduced D).normal
    Group.IsSolvable ((actionMk (c.orbit D)).subgroupMap
      (c.overcomponent.subgroupOf (c.join D))).ker := by
  let J := c.join D
  let I := c.overcomponent.subgroupOf J
  let K := (c.component.map H.subtype).subgroupOf J
  let := (c.orbit_reduced D).normal
  let q := actionMk (c.orbit D)
  let f := q.subgroupMap I
  have hI : I.IsCComponent := (c.local_components D).2.1
  have hn : I.map q ≠ ⊥ := by
    intro hz
    exact c.small_image_ne_bot D (bot_unique ((map_mono (comap_mono c.component_le)).trans hz.le))
  have hp : f.ker ≠ ⊤ := by
    intro he
    apply hn
    apply (Subgroup.eq_bot_iff_forall _).mpr
    rintro _ ⟨i,hi,rfl⟩
    have hm : (⟨i,hi⟩ : I) ∈ f.ker := he ▸ mem_top _
    exact congrArg Subtype.val (show f ⟨i,hi⟩ = 1 from hm)
  exact hI.isSolvable_of_subnormal_lt_top (inferInstance : f.ker.Normal).isSubnormal hp

/-- The smaller image is local for the image of the original Sylow intersection. -/
theorem ComparisonConfiguration.single_small_image_local (c : ComparisonConfiguration D ctx)
    (hsingle : c.component = pResidual 2 H) :
    let J := c.join D
    letI := (c.orbit_reduced D).normal
    let I := c.overcomponent.subgroupOf J
    let q := actionMk (c.orbit D)
    let K := (c.component.map H.subtype).subgroupOf J
    ∃ S : Sylow 2 I,
      (S : Subgroup I) = ((T : Subgroup G).subgroupOf J).subgroupOf I ∧
      (K.map q).subgroupOf (I.map q) ∈
        localCComponents (S.mapSurjective (q.subgroupMap_surjective I)) := by
  let J := c.join D
  let I := c.overcomponent.subgroupOf J
  let K := (c.component.map H.subtype).subgroupOf J
  let := (c.orbit_reduced D).normal
  let := c.single_component_normal D hsingle
  let q := actionMk (c.orbit D)
  let f := q.subgroupMap I
  let P := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  have hKJ : c.component.map H.subtype ≤ J := c.component_le.trans le_sup_left
  have hKP : K ∈ localCComponents P := SourceEmbeddings.local_restrict
    (c.local_components D).1.1 hKJ
  have hKI : K ≤ I := comap_mono c.component_le
  obtain ⟨S,hS,hl⟩ := SourceEmbeddings.exists_local_sylow_restriction P hKP hKI
    (inferInstance : I.Normal).isSubnormal
  let : Group.IsSolvable f.ker := c.action_kernel_solvable D
  have hl' := Chapter1.Section02.localCComponents_map_of_solvable_ker hl f
  have hm : (K.subgroupOf I).map f = (K.map q).subgroupOf (I.map q) := by
    ext x
    constructor
    · rintro ⟨k,hk,rfl⟩
      exact mem_map.mpr ⟨k,hk,rfl⟩
    · rintro ⟨k,hk,he⟩
      exact ⟨⟨k,hKI hk⟩,hk,Subtype.ext he⟩
  exact ⟨S,hS,by simpa only [hm,Sylow.coe_mapSurjective] using hl'⟩

/-- The actual smaller and containing images coincide, or the containing action has a source model. -/
theorem ComparisonConfiguration.single_action_model_or_full (c : ComparisonConfiguration D ctx)
    (hsingle : c.component = pResidual 2 H)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    let J := c.join D
    letI := (c.orbit_reduced D).normal
    let q := actionMk (c.orbit D)
    let I := c.overcomponent.subgroupOf J
    let K := (c.component.map H.subtype).subgroupOf J
    K.map q = I.map q ∨ PointControl.Constrained.ContainingModel (I.map q) := by
  let J := c.join D
  let I := c.overcomponent.subgroupOf J
  let K := (c.component.map H.subtype).subgroupOf J
  let := (c.orbit_reduced D).normal
  let := (c.orbit_reduced D).elementary
  let q := actionMk (c.orbit D)
  let A := I.map q
  let Kb := (K.map q).subgroupOf A
  let ρ := action (c.orbit D)
  let N := offenderSubgroup ρ
  by_cases he : K.map q = A
  · exact Or.inl he
  right
  have hKA : K.map q ≤ A := map_mono (comap_mono c.component_le)
  have hp : Kb ≠ ⊤ := fun ht => he (le_antisymm hKA (subgroupOf_eq_top.mp ht))
  obtain ⟨hA,hAN,_,_,⟨h⟩⟩ := c.single_ff_action D hsingle n hn hF e
  let : IsQuasisimple A := hA
  obtain ⟨S,_,hK⟩ := c.single_small_image_local D hsingle
  let E : A ≃* A.subgroupOf N := (subgroupOfEquivOfLe hAN).symm
  let : IsQuasisimple (A.subgroupOf N) := IsQuasisimple.of_mulEquiv E
  let : Group.IsSolvable E.toMonoidHom.ker := by
    rw [E.toMonoidHom.ker_eq_bot_iff.mpr E.injective]
    exact Group.isSolvable_of_comm (fun x y => by
      have hx : x = 1 := Subtype.ext (mem_bot.mp x.property)
      rw [hx,one_mul,mul_one])
  have hlocal := Chapter1.Section02.localCComponents_map_of_solvable_ker hK E.toMonoidHom
  have hp' : Kb.map E.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hp
    apply map_injective (f := E.toMonoidHom) E.injective
    rw [ht,map_top_of_surjective _ E.surjective]
  exact PointControl.Constrained.ContainingModel.of_equiv E
    (PointControl.Constrained.containingModel_of_source_case _ _ h.sectionData h.clause_one
      ((S.mapSurjective (q.subgroupMap_surjective I)).mapSurjective E.surjective) _ hlocal hp')

end CFSG.Quasithin.Chapter10.MovingHall.HallPlacement


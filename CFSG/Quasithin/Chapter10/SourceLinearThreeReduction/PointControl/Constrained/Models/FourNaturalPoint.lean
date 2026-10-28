module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.FourNaturalActions
public import Theory.Representation.BinaryPermutation.AlternatingEightSylowFixed
public import Theory.Representation.BinaryFivePointStabilizers
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Thompson
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Source


/-!
# Local fixed points in the retained four-natural row

The half-Sylow fixes the unique nonzero vector of the local point-fixed line.
Its actual component orbit has a two-group action kernel. An SL₅(2) actor
gives a maximal point parabolic with the literal intrinsic two-core quotient.
This forces escape at a conjugate local point and constructs a new original
constrained context, with the original full module retained.

The augmentation seven-space is excluded directly: a Sylow-fixed vector is
component-fixed, contrary to vanishing of the original moved fixed kernel.
The smaller orbit and the original full four-copy moved subgroup remain distinct.
Source: Aschbacher--Smith, 10.2.9, printed pp.752--753; B.5.1.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Chapter3.Section02 ChapterB.InternalThompsonAction ChapterB.QuasisimpleSource
open BinaryNaturalDual.VectorStabilizers
open scoped MatrixGroups IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- The unique local point-fixed line is fixed by the entire half-Sylow. -/
theorem Context.local_seed_fixed_by_halfSylow_of_four_natural_cover
    (c : Context D t v I) (h : FourNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G)) :
    u ∈ centralizer (((T : Subgroup G) ⊓ normalizer (L : Set G)) : Set G) := by
  let W := ⁅D.moduleSubgroup,L⁆
  let S := (T : Subgroup G) ⊓ normalizer (L : Set G)
  let F := W ⊓ centralizer (pointSylow T v : Set G)
  let F₀ := W ⊓ centralizer (S : Set G)
  have hSF : F₀ ≤ F := inf_le_inf_left _
    (centralizer_le (le_inf inf_le_left c.escaping.sylow_normalizes))
  have hne : F₀ ≠ ⊥ := inf_centralizer_ne_bot_of_pGroups S W
    (T.isPGroup'.to_le inf_le_left)
    ((source_original_full_moved_elementary D).isPGroup.to_le
      (commutator_mono (le_componentOrbit _ _) le_rfl))
    ((le_sup_right : S ≤ halfJoin T L).trans c.halfJoin_normalizes_local_moved)
    (Selection.ModuleChoice.local_moved_ne_bot D)
  have hlo := (one_lt_card_iff_ne_bot F₀).mpr hne
  have hcard : Nat.card F = 2 := c.local_point_fixed_card_of_four_natural_cover h
  have he : F₀ = F := eq_of_le_of_card_ge hSF (by omega)
  exact (show u ∈ F₀ from he.symm ▸ hu).2

/-- The entire smaller-orbit action kernel is a two-group, including the
point-Sylow supplement to the component. -/
theorem Context.local_seed_action_kernel_two_of_four_natural_cover
    (c : Context D t v I) (h : FourNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) :
    let U := (conjugateSpanBy (zpowers u) I).subgroupOf (pointJoin T v I)
    letI := (c.local_seed_orbit_reduced hu).normal
    IsPGroup 2 (actionMk U).ker := by
  let H := pointJoin T v I
  let K := I.subgroupOf H
  let S := (pointSylow T v).subgroupOf H
  let U := (conjugateSpanBy (zpowers u) I).subgroupOf H
  let := (c.local_seed_orbit_reduced hu).normal
  let q := actionMk U
  let f := q.subgroupMap K
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le I.le_normalizer (inf_le_right.trans c.escaping.normalizes))
  have hKS : K ⊔ S = ⊤ := by
    rw [←subgroupOf_sup (show I ≤ H from le_sup_left)
      (show pointSylow T v ≤ H from le_sup_right),subgroupOf_self]
  have hquot : IsPGroup 2 (H ⧸ K) := isPGroup_quotient_of_sup_eq_top K S
    ((T.isPGroup'.to_le inf_le_left).comap_subtype) hKS
  change IsPGroup 2 q.ker
  intro x
  obtain ⟨n,hn⟩ := hquot (QuotientGroup.mk' K (x : H))
  have hxK : (x : H) ^ (2 ^ n) ∈ K := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' K) ((x : H) ^ (2 ^ n)) = 1
    simpa only [map_pow] using hn
  let y : K := ⟨(x : H) ^ (2 ^ n),hxK⟩
  have hy : y ∈ f.ker := by
    apply Subtype.ext
    change q ((x : H) ^ (2 ^ n)) = 1
    rw [map_pow,show q (x : H) = 1 from x.property,one_pow]
  rw [show f.ker = pCore 2 K from c.local_seed_component_kernel_of_four_natural_cover h hu hne] at hy
  obtain ⟨r,hr⟩ := (pCore_isPGroup (p := 2) (G := K)) ⟨y,hy⟩
  refine ⟨n+r,Subtype.ext ?_⟩
  have he := congrArg (fun a : pCore 2 K => ((a : K) : H)) hr
  change ((x : H) ^ (2 ^ n)) ^ (2 ^ r) = 1 at he
  change (x : H) ^ (2 ^ (n+r)) = 1
  simpa only [←pow_mul,←pow_add] using he

theorem Context.local_seed_point_structure_of_binary_five
    (c : Context D t v I) (h : FourNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) :
    let H := pointJoin T v I
    let U := (conjugateSpanBy (zpowers u) I).subgroupOf H
    letI := (c.local_seed_orbit_reduced hu).normal
    letI := (c.local_seed_orbit_reduced hu).elementary
    let A := (I.subgroupOf H).map (actionMk U)
    ∀ (_E : A ≃* SL(5,ZMod 2)),
    let C := H ⊓ centralizer ({u} : Set G)
    IsCoatom (C.subgroupOf H) ∧
      (Nonempty ((C ⧸ pCore 2 C) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)) ∨
       Nonempty ((C ⧸ pCore 2 C) ≃*
         (SL(2,ZMod 2) × SL(3,ZMod 2)))) := by
  let H := pointJoin T v I
  let R := conjugateSpanBy (zpowers u) I
  let U := R.subgroupOf H
  let C := H ⊓ centralizer ({u} : Set G)
  let := (c.local_seed_orbit_reduced hu).normal
  let := (c.local_seed_orbit_reduced hu).elementary
  let A := (I.subgroupOf H).map (actionMk U)
  dsimp only
  intro E
  obtain ⟨ht,hi,hd⟩ := c.local_seed_irreducible_of_binary_five h hu hne E
  change A = ⊤ at ht
  have hAsur : Function.Surjective A.subtype := by
    intro a
    exact ⟨⟨a,ht.symm ▸ mem_top a⟩,rfl⟩
  let : IsIrreducible (action U) := (irreducible_comp_surjective_iff A.subtype hAsur _).mp hi
  let e : ActionQuotient U ≃* SL(5,ZMod 2) :=
    (topEquiv.symm.trans (MulEquiv.subgroupCongr ht.symm)).trans E
  have huR : u ∈ R := le_conjugateSpanBy _ _ (mem_zpowers u)
  have hRVI : R ≤ orbitModule D v I := conjugateSpanBy_mono (zpowers_le.mpr
    ⟨(commutator_mono (le_componentOrbit _ _) le_rfl) hu.1,hu.2⟩) le_rfl
  have hRH : R ≤ H := hRVI.trans c.orbit_le_join
  let w : Additive U := Additive.ofMul ⟨⟨u,hRH huR⟩,huR⟩
  have hw : w ≠ 0 := fun he => hne (congrArg (fun a : Additive U => ((a.toMul : H) : G)) he)
  let q := actionMk U
  let B := representationStabilizer (action U) w
  have hfix (x : H) : q x ∈ B ↔ (x:G) ∈ C := by
    change action U (q x) w = w ↔ (x:G) ∈ C
    constructor
    · intro hx
      refine ⟨x.property,mem_centralizer_singleton_iff.mpr ?_⟩
      have he := congrArg (fun a : Additive U => ((a.toMul : H) : G)) hx
      have ha := congrArg H.subtype (action_apply U x w)
      exact mul_inv_eq_iff_eq_mul.mp (ha.symm.trans he)
    · intro hx
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Subtype.ext
      have ha := congrArg H.subtype (action_apply U x w)
      exact ha.trans (mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hx.2))
  let f : C →* B := (q.comp (inclusion inf_le_left)).codRestrict B
    (fun x => (hfix (inclusion inf_le_left x)).mpr x.property)
  have hf : Function.Surjective f := by
    intro b
    obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective (centralizer (U : Set H)) b.val
    have hxC : (x:G) ∈ C := (hfix x).mp (by rw [show q x = b.val from hx]; exact b.property)
    exact ⟨⟨x,hxC⟩,Subtype.ext hx⟩
  have hk : IsPGroup 2 f.ker := by
    let j : f.ker →* q.ker := {
      toFun x := ⟨inclusion inf_le_left x.val,congrArg Subtype.val x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    exact (c.local_seed_action_kernel_two_of_four_natural_cover h hu hne).of_injective j (by
      intro x y he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : q.ker => ((z:H):G)) he)
  let eqQ := f.pCoreQuotientEquiv hf hk
  have hc : C.subgroupOf H = B.comap q := by ext x; exact (hfix x).symm
  have hs : ∃ S : Sylow 2 (ActionQuotient U), (S : Subgroup _) ≤ B := by
    obtain ⟨S,hS⟩ := c.join_sylow
    refine ⟨S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _),?_⟩
    rintro _ ⟨x,hx,rfl⟩
    apply (hfix x).mpr
    refine ⟨x.property,mem_centralizer_singleton_iff.mpr ?_⟩
    exact hu.2 x (hS ▸ mem_map_of_mem H.subtype hx)
  rcases hd with hd | hd
  · obtain ⟨hm,⟨a⟩⟩ := BinaryFivePointStabilizers.natural_structure
      (action U) (action_faithful U) e hd w hw
    exact ⟨hc ▸ isCoatom_comap_of_surjective (QuotientGroup.mk'_surjective _) hm,
      Or.inl ⟨eqQ.trans a⟩⟩
  · obtain ⟨S,hS⟩ := hs
    obtain ⟨hm,⟨a⟩⟩ := BinaryFivePointStabilizers.exterior_structure
      (action U) e hd S w hw hS
    exact ⟨hc ▸ isCoatom_comap_of_surjective (QuotientGroup.mk'_surjective _) hm,
      Or.inr ⟨eqQ.trans a⟩⟩

/-- A maximal local point parabolic escapes the original maximal local subgroup. -/
theorem Context.local_seed_point_escapes_of_maximal
    (c : Context D t v I) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆) (hne : u ≠ 1)
    (hm : IsCoatom (((pointJoin T v I) ⊓ centralizer ({u} : Set G)).subgroupOf
      (pointJoin T v I))) :
    ¬ (pointJoin T v I) ⊓ centralizer ({u} : Set G) ≤ D.maximalLocal := by
  let H := pointJoin T v I
  let C := H ⊓ centralizer ({u} : Set G)
  have hLH : L ≤ H := c.escaping.strict.le.trans le_sup_left
  have hLC : ¬ L ≤ C := by
    intro hh
    have hz : u ∈ sourceMovedFixed D :=
      ⟨(commutator_mono (le_componentOrbit _ _) le_rfl) hu,
        fun l hl => mem_centralizer_singleton_iff.mp (hh hl).2⟩
    rw [c.moved_fixed_eq_bot] at hz
    exact hne (mem_bot.mp hz)
  have hstrict : C.subgroupOf H < (L ⊔ C).subgroupOf H := by
    apply lt_iff_le_not_ge.mpr
    refine ⟨comap_mono le_sup_right,?_⟩
    intro hh
    apply hLC
    intro x hx
    exact hh (show (⟨x,hLH hx⟩ : H) ∈ (L ⊔ C).subgroupOf H from
      (le_sup_left : L ≤ L ⊔ C) hx)
  have ht : (L ⊔ C).subgroupOf H = ⊤ := hm.2 _ hstrict
  have he := congrArg (Subgroup.map H.subtype) ht
  rw [map_subgroupOf_eq_of_le (sup_le hLH inf_le_left),←MonoidHom.range_eq_map,range_subtype] at he
  intro hCM
  apply c.escaping.escapes
  have hHM : H ≤ D.maximalLocal := by
    rw [←he]
    exact sup_le ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer) hCM
  exact (le_sup_left : I ≤ H).trans hHM

/-- In either binary-five irreducible the literal local point centralizer
is a maximal parabolic outside M, with its intrinsic two-core quotient. -/
theorem Context.local_seed_point_parabolic_of_binary_five
    (c : Context D t v I) (h : FourNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) :
    let H := pointJoin T v I
    let U := (conjugateSpanBy (zpowers u) I).subgroupOf H
    letI := (c.local_seed_orbit_reduced hu).normal
    ∀ (_E : ((I.subgroupOf H).map (actionMk U)) ≃* SL(5,ZMod 2)),
    let C := H ⊓ centralizer ({u} : Set G)
    IsCoatom (C.subgroupOf H) ∧ ¬ C ≤ D.maximalLocal ∧
      (Nonempty ((C ⧸ pCore 2 C) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)) ∨
       Nonempty ((C ⧸ pCore 2 C) ≃* (SL(2,ZMod 2) × SL(3,ZMod 2)))) := by
  let := (c.local_seed_orbit_reduced hu).normal
  let := (c.local_seed_orbit_reduced hu).elementary
  dsimp only
  intro E
  obtain ⟨hm,hq⟩ := c.local_seed_point_structure_of_binary_five h hu hne E
  exact ⟨hm,c.local_seed_point_escapes_of_maximal hu.1 hne hm,hq⟩

/-- Conjugating the actual local fixed line gives a point in the opposite
local natural copy, fixed by the whole half-Sylow and saturated in M. -/
theorem Context.local_seed_opposite_saturated_of_four_natural_cover
    (c : Context D t v I) (h : FourNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) :
    let w := (MulAut.conj t) u
    pointSylow T w = (T : Subgroup G) ⊓ normalizer (L : Set G) ∧
      Chapter1.IsSylowIn 2 (pointSylow T w)
        (D.maximalLocal ⊓ centralizer ({w} : Set G)) := by
  let w := (MulAut.conj t) u
  let S := (T : Subgroup G) ⊓ normalizer (L : Set G)
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) :=
    fun hh => c.escaping.t_not_normalizes (hh c.escaping.t_mem)
  have hi := source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn
  let N := (normalizer (L : Set G)).subgroupOf (T : Subgroup G)
  let : N.Normal := normal_of_index_eq_two hi
  have hfix := c.local_seed_fixed_by_halfSylow_of_four_natural_cover h hu
  have hSC : S ≤ centralizer ({w} : Set G) := by
    intro x hx
    have hx' : t⁻¹ * x * t ∈ S := by
      have hh := (inferInstance : N.Normal).conj_mem ⟨x,hx.1⟩ hx.2
        (⟨t,c.escaping.t_mem⟩ : (T : Subgroup G))⁻¹
      exact ⟨(T : Subgroup G).mul_mem
        ((T : Subgroup G).mul_mem ((T : Subgroup G).inv_mem c.escaping.t_mem) hx.1)
        c.escaping.t_mem,by
          change ((⟨t,c.escaping.t_mem⟩ : (T : Subgroup G))⁻¹ * ⟨x,hx.1⟩ *
            ⟨t,c.escaping.t_mem⟩) ∈ N
          simpa only [inv_inv] using hh⟩
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg (MulAut.conj t) (hfix _ hx')
    have hc : (MulAut.conj t) (t⁻¹ * x * t) = x := by simp [MulAut.conj_apply,mul_assoc]
    simpa only [map_mul,hc] using hh
  have hwW : w ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom :=
    mem_map_of_mem _ ((commutator_mono (le_componentOrbit _ _) le_rfl) hu.1)
  have hwV := partner_le_fullModule D c.escaping.t_mem hwW
  have hwne : w ≠ 1 := fun he => hne ((MulAut.conj t).map_eq_one_iff.mp he)
  have hw0 : w ∉ centralizer (localOrbit T L : Set G) := by
    intro hh
    exact hwne (mem_bot.mp (c.full_fixed_eq_bot ▸
      (show w ∈ D.fullModule ⊓ centralizer (localOrbit T L : Set G) from ⟨hwV,hh⟩)))
  have hCM : D.maximalLocal ⊓ centralizer ({w} : Set G) ≤ normalizer (L : Set G) :=
    source_nonnormal_element_centralizer_stabilizes D hn (c.escaping.crossed hwW) hw0
  have he : pointSylow T w = S := le_antisymm
    (le_inf inf_le_left (by
      intro x hx
      exact hCM ⟨le_normalizer_componentOrbit L T hx.1,hx.2⟩))
    (le_inf inf_le_left hSC)
  refine ⟨he,?_⟩
  rw [he]
  exact (source_nonnormal_stabilizer_sylow D hn).restrict
    (le_inf (inf_le_left.trans (le_normalizer_componentOrbit L T)) hSC)
    (le_inf inf_le_left hCM)

/-- The binary-five branch forces escape at a saturated point in the
opposite local natural copy, without replacing the original full module. -/
theorem Context.local_opposite_escape_of_binary_five
    (c : Context D t v I) (h : FourNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) :
    let H := pointJoin T v I
    let U := (conjugateSpanBy (zpowers u) I).subgroupOf H
    letI := (c.local_seed_orbit_reduced hu).normal
    ∀ (_E : ((I.subgroupOf H).map (actionMk U)) ≃* SL(5,ZMod 2)),
    let w := (MulAut.conj t) u
    ¬ centralizer ({w} : Set G) ≤ D.maximalLocal := by
  let := (c.local_seed_orbit_reduced hu).normal
  dsimp only
  intro E hh
  have hesc := (c.local_seed_point_parabolic_of_binary_five h hu hne E).2.1
  apply hesc
  intro x hx
  have hx' : (MulAut.conj t) x ∈ centralizer ({(MulAut.conj t) u} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul] using congrArg (MulAut.conj t) (mem_centralizer_singleton_iff.mp hx.2)
  exact (mem_normalizer_iff.mp
    (D.maximalLocal.le_normalizer (le_normalizer_componentOrbit L T c.escaping.t_mem)) x).mpr
      (hh hx')

/-- Escaping local point centralizers supply another original constrained
context, now with its point in the opposite local natural three-space. -/
theorem Context.reselect_local_point_of_escaping_centralizer
    (c : Context D t v I) (h : FourNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1)
    (hout : ¬ centralizer ({(MulAut.conj t) u} : Set G) ≤ D.maximalLocal) :
    let w := (MulAut.conj t) u
    ∃ J : Subgroup G, Context D t w J ∧
      w ∈ (⁅D.moduleSubgroup,L⁆).map (MulAut.conj t).toMonoidHom ∧
      pointSylow T w = (T : Subgroup G) ⊓ normalizer (L : Set G) := by
  let w := (MulAut.conj t) u
  have hw : w ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom :=
    mem_map_of_mem _ ((commutator_mono (le_componentOrbit _ _) le_rfl) hu.1)
  have hwne : w ≠ 1 := fun he => hne ((MulAut.conj t).map_eq_one_iff.mp he)
  have hs := c.local_seed_opposite_saturated_of_four_natural_cover h hu hne
  have hp := pointSylowControl_of_thompson_centralizes D c.many
    c.escaping.t_mem c.escaping.t_not_normalizes c.escaping.crossed
    (c.full_thompson_fixed_of_three (c.three_dvd_of_prepared (c.prepared_of_four_natural_cover h)))
  obtain ⟨J,hJ⟩ := escapingComponent_of_local_sylow D c.escaping.t_mem
    c.escaping.t_not_normalizes c.escaping.crossed c.escaping.half_unique hp hw hwne hs.2 hout
  have hnJ : ¬ IsQuasisimple J := by
    intro hq
    let := hq
    obtain ⟨e,⟨s⟩⟩ := h
    apply Quasisimple.Other.not_complementary_of_large_moved D hJ ?_
      (Quasisimple.RankTwo.not_rank_two_of_binary_three D hJ e)
    have hc := s.card_le_central_image J hJ.strict.le
      ((source_full_moved_le_component D).trans hJ.strict.le) le_rfl
    simpa only [Nat.card_fun,Nat.card_fin,Nat.card_zmod,←pow_mul] using hc
  have hwV := partner_le_fullModule D c.escaping.t_mem hw
  have hCW := (Subgroup.centralizer_le_normalizer _).trans hJ.moved_normalizer
  refine ⟨J,⟨c.many,c.minimal,c.nonA5,hJ,hnJ,?_,?_⟩,mem_map_of_mem _ hu.1,hs.1⟩
  · exact source_a5_point_component_characteristicTwo D hwV hwne (c.escaping.crossed hw)
      hCW J hJ.le_centralizer hJ.component hnJ
  · exact source_a5_point_component_reduced_module D hwV hwne (c.escaping.crossed hw)
      hCW J hJ.strict.le hJ.le_centralizer hJ.component hJ.normalizes hnJ hJ.sylow

/-- Escaping local point centralizers supply another original constrained
context, now with its point in the opposite local natural three-space. -/
theorem Context.reselect_local_point_of_binary_five
    (c : Context D t v I) (h : FourNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) :
    let H := pointJoin T v I
    let U := (conjugateSpanBy (zpowers u) I).subgroupOf H
    letI := (c.local_seed_orbit_reduced hu).normal
    ∀ (_E : ((I.subgroupOf H).map (actionMk U)) ≃* SL(5,ZMod 2)),
    let w := (MulAut.conj t) u
    ∃ J : Subgroup G, Context D t w J ∧
      w ∈ (⁅D.moduleSubgroup,L⁆).map (MulAut.conj t).toMonoidHom ∧
      pointSylow T w = (T : Subgroup G) ⊓ normalizer (L : Set G) := by
  let := (c.local_seed_orbit_reduced hu).normal
  dsimp only
  intro E
  exact c.reselect_local_point_of_escaping_centralizer h hu hne
    (c.local_opposite_escape_of_binary_five h hu hne E)

/-- The seven-dimensional augmentation cover cannot be generated by the
local Sylow-fixed involution: its Sylow-fixed vectors are component-fixed constants. -/
theorem Context.no_augmentation_cover_of_local_seed
    (c : Context D t v I) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) :
    let H := pointJoin T v I
    let U := (conjugateSpanBy (zpowers u) I).subgroupOf H
    letI := (c.local_seed_orbit_reduced hu).normal
    letI := (c.local_seed_orbit_reduced hu).elementary
    let A := (I.subgroupOf H).map (actionMk U)
    ∀ (_E : ActionEquiv ((action U).comp A.subtype)
      (BinaryPermutation.alternatingCoreRepresentation (Fin 8))), False := by
  let H := pointJoin T v I
  let R := conjugateSpanBy (zpowers u) I
  let U := R.subgroupOf H
  let K := I.subgroupOf H
  let := (c.local_seed_orbit_reduced hu).normal
  let := (c.local_seed_orbit_reduced hu).elementary
  let A := K.map (actionMk U)
  dsimp only
  intro E
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le I.le_normalizer (inf_le_right.trans c.escaping.normalizes))
  obtain ⟨P,hP⟩ := c.join_sylow
  obtain ⟨S,hS⟩ := P.exists_subgroupOf_eq_of_normal K
  let f := E.groupEquiv.toMonoidHom.comp ((actionMk U).subgroupMap K)
  have hf : Function.Surjective f := E.groupEquiv.surjective.comp
    ((actionMk U).subgroupMap_surjective K)
  let Q := S.mapSurjective hf
  have huR : u ∈ R := le_conjugateSpanBy _ _ (mem_zpowers u)
  have hRVI : R ≤ orbitModule D v I := conjugateSpanBy_mono (zpowers_le.mpr
    ⟨(commutator_mono (le_componentOrbit _ _) le_rfl) hu.1,hu.2⟩) le_rfl
  have hRH : R ≤ H := hRVI.trans c.orbit_le_join
  let w : Additive U := Additive.ofMul ⟨⟨u,hRH huR⟩,huR⟩
  have hconst := BinaryPermutation.alternatingEight_core_sylow_fixed_constant Q (E.linearEquiv w) (by
    rintro a ⟨x,hx,rfl⟩
    have hxP : (x:H) ∈ (P : Subgroup H) := by
      change x ∈ (P : Subgroup H).subgroupOf K
      rw [←hS]
      exact hx
    have hxS : ((x:H):G) ∈ pointSylow T v := hP ▸ mem_map_of_mem H.subtype hxP
    have he : action U (actionMk U (x:H)) w = w := by
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Subtype.ext
      have ha := congrArg H.subtype (action_apply U (x:H) w)
      exact ha.trans (mul_inv_eq_iff_eq_mul.mpr (hu.2 _ hxS))
    exact (E.intertwines (((actionMk U).subgroupMap K) x) w).symm.trans
      (congrArg E.linearEquiv he))
  have hall := (BinaryPermutation.core_fixed_iff_constant
    (by simp : 3 ≤ Nat.card (Fin 8)) (E.linearEquiv w)).mpr hconst
  have huL : u ∈ centralizer (L : Set G) := by
    intro l hl
    let lH : H := ⟨l,(c.escaping.strict.le.trans le_sup_left) hl⟩
    let lK : K := ⟨lH,c.escaping.strict.le hl⟩
    have hh : action U (actionMk U lH) w = w := E.linearEquiv.injective
      ((E.intertwines (((actionMk U).subgroupMap K) lK) w).trans (hall (f lK)))
    have he := congrArg (fun a : Additive U => ((a.toMul:H):G)) hh
    have ha := congrArg H.subtype (action_apply U lH w)
    exact mul_inv_eq_iff_eq_mul.mp (ha.symm.trans he)
  have hz : u ∈ sourceMovedFixed D :=
    ⟨(commutator_mono (le_componentOrbit _ _) le_rfl) hu.1,huL⟩
  rw [c.moved_fixed_eq_bot] at hz
  exact hne (mem_bot.mp hz)

/-- After excluding the augmentation cover, the whole smaller orbit has
only dimensions four, five, six or ten. -/
theorem Context.local_seed_dimension_without_seven_of_four_natural_cover
    (c : Context D t v I) (h : FourNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) :
    let U := (conjugateSpanBy (zpowers u) I).subgroupOf (pointJoin T v I)
    letI := (c.local_seed_orbit_reduced hu).elementary
    Module.finrank (ZMod 2) (Additive U) = 4 ∨
      Module.finrank (ZMod 2) (Additive U) = 5 ∨
      Module.finrank (ZMod 2) (Additive U) = 6 ∨
      Module.finrank (ZMod 2) (Additive U) = 10 := by
  let := (c.local_seed_orbit_reduced hu).normal
  let := (c.local_seed_orbit_reduced hu).elementary
  cases c.local_seed_single_action_of_four_natural_cover h hu hne with
  | natural d hd _ E =>
    have he := E.linearEquiv.finrank_eq.trans (Module.finrank_fin_fun (ZMod 2))
    rcases hd with rfl | rfl
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
  | orthogonal _ model _ =>
    rcases model with h6 | h7
    · obtain ⟨E⟩ := h6
      exact Or.inr (Or.inr (Or.inl (E.linearEquiv.finrank_eq.trans
        (BinaryPermutation.finrank_natural_even (Fin 8) (by decide)))))
    · exact (c.no_augmentation_cover_of_local_seed hu hne h7.some).elim
  | exterior _ _ _ dim => exact Or.inr (Or.inr (Or.inr dim))


end CFSG.Quasithin.Chapter10.PointControl.Constrained

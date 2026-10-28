module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarked
public import Theory.Representation.CentralizerMultiplicity
public import Theory.ElementaryAbelian.GeneratorRank
public import Theory.ElementaryAbelian.Quotient
public import Theory.Representation.BinaryOffender.FaithfulInvariantSection

/-!
# Multiplicity geometry of the nonfaithful marked constituent

The original actor kernel is a nontrivial proper intersection with the
centralizer of the normal component orbit. That centralizer acts faithfully
on the actual H-intertwiner space. Evaluation at the selected nonzero point
detects a moving intertwiner, producing a disjoint equivalent constituent;
at twice the constituent degree this is an actual complementary copy.

The small-actor bound fixes the original binary dimension and gives a
quotient formula retaining the rank lost to the kernel. On an orthogonal
constituent stabilized by a noncentral actor, displacement has rank one.
These are input reductions for small-component recognition, not that
recognition itself. FixedPointAlternative states the separate G.11.1(3)
obligation on the same source vector and action.

Source: Aschbacher--Smith, G.10.14--16 and the paragraphs preceding
G.11.8--9, printed pp.361--364 and 368--369.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
namespace MarkedSource
variable {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : MarkedSource T M Mc F g B v L I)
include s

theorem constituent_ne_top_of_not_actorFaithful
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I)) : I ≠ ⊤ := by
  intro htop
  apply hk
  intro a b hab
  apply Subtype.ext
  apply s.hypothesis.faithful
  ext w
  exact LinearMap.congr_fun hab ⟨w, htop.symm ▸ Submodule.mem_top⟩

theorem constituent_isotropic_of_not_actorFaithful
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I)) :
    ∀ u ∈ I, ∀ w ∈ I, B u w = 0 := by
  have hd := (Recognition.source_terminal_constituent_homogeneous_of_point_mem
    s.simple T s.empty s.maximal s.unique_overgroup s.many_overgroups s.seed_card
    (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
    s.normalizer_not_mem s.nonsolvable s.hypothesis s.component s.moved
    s.selected.isIrrPlus s.point_mem).2.2.2
  exact hd.resolve_right (fun h => s.constituent_ne_top_of_not_actorFaithful hk h.1)

theorem twice_constituent_finrank_le_of_not_actorFaithful
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I)) :
    2 * Module.finrank (ZMod 2) I ≤ Module.finrank (ZMod 2) (Additive F.Uhat) :=
  B.twice_finrank_le_of_isotropic s.hypothesis.nondegenerate I
    (s.constituent_isotropic_of_not_actorFaithful hk)

theorem actor_dimension :
    Module.finrank (ZMod 2) (Additive F.Uhat) =
      2 * (Module.finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) + 1) := by
  have hb := s.hypothesis.dimension_bound.1
  have hr := Group.rank_le_of_surjective
    (QuotientGroup.mk' ((F.terminalDot (conjugate F.ZU g)).subgroupOf
      (F.terminalDot (F.X g)))) (QuotientGroup.mk'_surjective _)
  have hf := IsElementaryAbelian.rank_le_finrank (p := 2) (F.terminalDot (F.X g))
  have hs := s.small_actor
  have hp := s.dimension_gt_two
  have hi := I.finrank_le
  omega

/-- The small-actor inequality forces the original transvection space
E-hat to have exactly half the ambient binary dimension. -/
theorem markedSpace_dimension :
    2 * Module.finrank (ZMod 2) (hatSpace F (F.E g)) =
      Module.finrank (ZMod 2) (Additive F.Uhat) := by
  have hd := s.actor_dimension
  have hw := s.hypothesis.dimension
  have hi := B.twice_finrank_le_of_isotropic s.hypothesis.nondegenerate
    (hatSpace F (F.E g)) s.hypothesis.isotropic
  have hr := Group.rank_le_of_surjective
    (QuotientGroup.mk' ((F.terminalDot (conjugate F.ZU g)).subgroupOf
      (F.terminalDot (F.X g)))) (QuotientGroup.mk'_surjective _)
  have hf := IsElementaryAbelian.rank_le_finrank (p := 2) (F.terminalDot (F.X g))
  omega

/-- The dimension bound after factoring the actual nonfaithful actor kernel.
The lost rank is k, determined by the order of the original intersection. -/
theorem actor_dimension_of_kernel_card {k : ℕ}
    (hc : Nat.card ((centralizer (componentOrbit L ⊤ : Set F.TerminalHdot)).subgroupOf
      (F.terminalDot (F.X g))) = 2 ^ k) :
    Module.finrank (ZMod 2) (Additive F.Uhat) = 2 *
      (Module.finrank (ZMod 2) (Additive ((F.terminalDot (F.X g)) ⧸
        (centralizer (componentOrbit L ⊤ : Set F.TerminalHdot)).subgroupOf
          (F.terminalDot (F.X g)))) + k + 1) := by
  let X := F.terminalDot (F.X g)
  let Y := (centralizer (componentOrbit L ⊤ : Set F.TerminalHdot)).subgroupOf X
  have hX : Nat.card X = 2 ^ Module.finrank (ZMod 2) (Additive X) := by
    rw [Nat.card_congr Additive.ofMul]
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive X))
  have hQ : Nat.card (X ⧸ Y) = 2 ^ Module.finrank (ZMod 2) (Additive (X ⧸ Y)) := by
    rw [Nat.card_congr Additive.ofMul]
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (X ⧸ Y)))
  have hp := Y.index_mul_card
  rw [Subgroup.index_eq_card, hc, hX, hQ, ← pow_add] at hp
  have he := (Nat.pow_right_injective (by decide : 2 ≤ 2)) hp
  rw [s.actor_dimension, ← he]

theorem actor_centralizer_ne_bot
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I)) :
    F.terminalDot (F.X g) ⊓ centralizer (componentOrbit L ⊤ : Set F.TerminalHdot) ≠ ⊥ :=
  fun he => hk (s.actorFaithful_iff.mpr he)

theorem actor_centralizer_lt :
    F.terminalDot (F.X g) ⊓ centralizer (componentOrbit L ⊤ : Set F.TerminalHdot) <
      F.terminalDot (F.X g) := by
  apply lt_of_le_of_ne inf_le_left
  intro he
  have hXC : F.terminalDot (F.X g) ≤ centralizer (componentOrbit L ⊤ : Set F.TerminalHdot) :=
    he ▸ inf_le_right
  apply s.moved
  rw [commutator_comm, commutator_eq_bot_iff_le_centralizer]
  exact hXC.trans (centralizer_le (le_componentOrbit L ⊤))

/-- The original orbit centralizer has trivial intrinsic two-core. -/
theorem centralizer_twoCore_eq_bot :
    pCore 2 (centralizer (componentOrbit L ⊤ : Set F.TerminalHdot)) = ⊥ := by
  let : (componentOrbit L ⊤).Normal := componentOrbit_top_normal L
  rw [pCore_subnormal_eq_comap 2 (Subgroup.Normal.isSubnormal inferInstance),
    s.hypothesis.twoCore_eq_bot]
  exact (MonoidHom.ker_eq_bot_iff _).mpr (Subgroup.subtype_injective _)

/-- The original centralizer acts faithfully on the literal multiplicity space. -/
theorem multiplicity_action_faithful :
    Function.Injective (CentralizerMultiplicity.action F.terminalRepresentation (componentOrbit L ⊤)
      (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I s.selected.invariant)) := by
  apply CentralizerMultiplicity.action_faithful _ _ _ s.hypothesis.faithful
  exact (Recognition.source_terminal_constituent_homogeneous_of_point_mem
    s.simple T s.empty s.maximal s.unique_overgroup s.many_overgroups s.seed_card
    (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
    s.normalizer_not_mem s.nonsolvable s.hypothesis s.component s.moved
    s.selected.isIrrPlus s.point_mem).1

/-- A kernel actor fixes I but moves an actual H-intertwiner into V. -/
theorem kernel_moves_multiplicity
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I)) :
    let H := componentOrbit L ⊤
    let R := invariantSubspace F.terminalRepresentation H I s.selected.invariant
    ∃ c : centralizer (H : Set F.TerminalHdot),
      c.val ∈ F.terminalDot (F.X g) ∧ c ≠ 1 ∧
      (∀ w : I, F.terminalRepresentation c w = w) ∧
      ∃ f : CentralizerMultiplicity.Multiplicity F.terminalRepresentation H R,
        F.terminalRepresentation c (f ⟨v,s.point_mem⟩) ≠ f ⟨v,s.point_mem⟩ := by
  classical
  intro H R
  obtain ⟨a,ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp (s.actor_centralizer_ne_bot hk)
  let c : centralizer (H : Set F.TerminalHdot) := ⟨a.val,a.property.2⟩
  have hc : c ≠ 1 := by
    intro he
    apply ha
    apply Subtype.ext
    exact congrArg (fun z : centralizer (H : Set F.TerminalHdot) => (z : F.TerminalHdot)) he
  refine ⟨c,a.property.1,hc,?_,?_⟩
  · exact (source_marked_constituent_fixes_iff_centralizes s.simple T s.empty s.maximal
      s.unique_overgroup s.many_overgroups s.seed_card (Classical.choice s.centralizer_quotient)
      F s.nonabelian g s.parabolic_mem s.normalizer_not_mem s.nonsolvable s.hypothesis
      s.component s.moved s.selected.isIrrPlus s.point_mem ⟨a.val,a.property.1⟩).mpr a.property.2
  · by_contra! hfix
    apply hc
    apply s.multiplicity_action_faithful
    rw [map_one]
    exact (CentralizerMultiplicity.action_eq_one_iff F.terminalRepresentation H R
      s.irreducible (fun he => s.hypothesis.point_ne_zero (congrArg Subtype.val he)) c).mpr hfix

/-- A nontrivial constituent kernel produces a second, disjoint copy of I
as an actual subrepresentation of the same H-action. -/
theorem exists_disjoint_copy_of_not_actorFaithful
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I)) :
    let R := invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I s.selected.invariant
    ∃ J : Subrepresentation (F.terminalRepresentation.comp (componentOrbit L ⊤).subtype),
      Nonempty (Representation.Equiv R.toRepresentation J.toRepresentation) ∧
      Disjoint I J.toSubmodule := by
  intro R
  obtain ⟨c,_,_,hfix,f,hmove⟩ := s.kernel_moves_multiplicity hk
  let : IsIrreducible R.toRepresentation := s.irreducible
  have hf0 : f ≠ 0 := by
    intro hz
    apply hmove
    rw [hz]
    exact map_zero _
  have hfi := (IsIrreducible.injective_or_eq_zero f).resolve_right hf0
  let e : Representation.Equiv R.toRepresentation f.range.toRepresentation := {
    toLinearEquiv := LinearEquiv.ofInjective f.toLinearMap hfi
    isIntertwining' h := by
      ext w
      exact LinearMap.congr_fun (f.isIntertwining' h) w }
  have hR : IsAtom R := (Subrepresentation.irreducible_iff_isAtom R).mp s.irreducible
  have hJ : IsAtom f.range := (Subrepresentation.irreducible_iff_isAtom f.range).mp
    ((RepEquiv.irreducible_euqiv ⟨e.toLinearEquiv,e.isIntertwining'⟩).mp s.irreducible)
  have hne : R ≠ f.range := by
    intro he
    have hw : f ⟨v,s.point_mem⟩ ∈ R.toSubmodule := by
      exact he.ge (show f ⟨v,s.point_mem⟩ ∈ f.range from ⟨⟨v,s.point_mem⟩,rfl⟩)
    exact hmove (hfix ⟨_,hw⟩)
  refine ⟨f.range,⟨e⟩,?_⟩
  have hd := hR.disjoint_of_ne hJ hne
  rw [Submodule.disjoint_def]
  intro w hwI hwJ
  have hz : w ∈ (R ⊓ f.range).toSubmodule := ⟨hwI,hwJ⟩
  rw [hd.eq_bot] at hz
  exact hz

/-- At multiplicity two the constructed copy is a genuine complementary
H-submodule, with an intertwining equivalence to the original I. -/
theorem exists_complementary_copy_of_double_dimension
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I) :
    let R := invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I s.selected.invariant
    ∃ J : Subrepresentation (F.terminalRepresentation.comp (componentOrbit L ⊤).subtype),
      Nonempty (Representation.Equiv R.toRepresentation J.toRepresentation) ∧
      Disjoint I J.toSubmodule ∧ I ⊔ J.toSubmodule = ⊤ := by
  intro R
  obtain ⟨J,⟨e⟩,hdis⟩ := s.exists_disjoint_copy_of_not_actorFaithful hk
  refine ⟨J,⟨e⟩,hdis,?_⟩
  apply Submodule.eq_top_of_finrank_eq
  have he := e.toLinearEquiv.finrank_eq
  have hs := Submodule.finrank_sup_add_finrank_inf_eq I J.toSubmodule
  rw [hdis.eq_bot,finrank_bot,add_zero] at hs
  change Module.finrank (ZMod 2) I = Module.finrank (ZMod 2) J.toSubmodule at he
  omega

/-- In the two-copy case, every nonidentity kernel actor has fixed space
exactly I. This proves the freeness used to compare the kernel rank with
an original centered-transvection orbit, without projective recognition. -/
theorem kernel_actor_fixedSpace_of_double_dimension
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    (y : F.terminalDot (F.X g)) (hy : y ≠ 1)
    (hyC : (y : F.TerminalHdot) ∈ centralizer (componentOrbit L ⊤ : Set F.TerminalHdot)) :
    LinearMap.ker (F.terminalRepresentation y - 1) = I := by
  let H := componentOrbit L ⊤
  obtain ⟨J,⟨e⟩,_,hsup⟩ := s.exists_complementary_copy_of_double_dimension hk hd
  let : IsIrreducible J.toRepresentation :=
    (RepEquiv.irreducible_euqiv ⟨e.toLinearEquiv,e.isIntertwining'⟩).mp s.irreducible
  have hfix : ∀ w : I, F.terminalRepresentation y w = w :=
    (source_marked_constituent_fixes_iff_centralizes s.simple T s.empty s.maximal
      s.unique_overgroup s.many_overgroups s.seed_card (Classical.choice s.centralizer_quotient)
      F s.nonabelian g s.parabolic_mem s.normalizer_not_mem s.nonsolvable s.hypothesis
      s.component s.moved s.selected.isIrrPlus s.point_mem y).mpr hyC
  have hIK : I ≤ LinearMap.ker (F.terminalRepresentation y - 1) :=
    fun w hw => sub_eq_zero.mpr (hfix ⟨w,hw⟩)
  let f : IntertwiningMap J.toRepresentation (F.terminalRepresentation.comp H.subtype) := {
    toLinearMap := (F.terminalRepresentation y - 1).comp J.toSubmodule.subtype
    isIntertwining' h := by
      ext w
      change F.terminalRepresentation y (F.terminalRepresentation h w) - F.terminalRepresentation h w =
        F.terminalRepresentation h (F.terminalRepresentation y w - w)
      rw [map_sub]
      have hc := (mem_centralizer_iff.mp hyC) h h.property
      have he := congrArg (fun a : F.TerminalHdot => F.terminalRepresentation a w) hc.symm
      simpa only [map_mul,Module.End.mul_apply] using
        congrArg (fun u => u - F.terminalRepresentation h w) he }
  have hf0 : f ≠ 0 := by
    intro hz
    have hJK : J.toSubmodule ≤ LinearMap.ker (F.terminalRepresentation y - 1) := by
      intro w hw
      exact congrArg (fun t : IntertwiningMap J.toRepresentation
        (F.terminalRepresentation.comp H.subtype) => t ⟨w,hw⟩) hz
    have htop : (⊤ : Submodule (ZMod 2) (Additive F.Uhat)) ≤
        LinearMap.ker (F.terminalRepresentation y - 1) := hsup ▸ sup_le hIK hJK
    apply hy
    apply Subtype.ext
    change (y : F.TerminalHdot) = 1
    apply s.hypothesis.faithful
    rw [map_one]
    apply LinearMap.ext
    intro w
    exact sub_eq_zero.mp (htop (show w ∈ (⊤ : Submodule (ZMod 2) (Additive F.Uhat)) from Submodule.mem_top))
  have hfi := (IsIrreducible.injective_or_eq_zero f).resolve_right hf0
  apply le_antisymm ?_ hIK
  intro w hw
  obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp (hsup.symm ▸ (Submodule.mem_top : w ∈ (⊤ : Submodule (ZMod 2) (Additive F.Uhat))))
  have hfb : f ⟨b,hb⟩ = 0 := by
    have he := congrArg (fun z => (F.terminalRepresentation y - (1 : Module.End (ZMod 2) (Additive F.Uhat))) z) hab
    rw [map_add,show (F.terminalRepresentation y - 1) a = 0 from hIK ha,
      zero_add,show (F.terminalRepresentation y - 1) w = 0 from hw] at he
    exact he
  have hb0 : b = 0 := congrArg Subtype.val (hfi (hfb.trans (map_zero f).symm))
  rw [hb0,add_zero] at hab
  exact hab ▸ ha

/-- The transvection bound of G.10.14(1), on the literal second constituent.
Only stability under this one actor is assumed. -/
theorem orthogonal_constituent_displacement_le_one
    {J : Submodule (ZMod 2) (Additive F.Uhat)}
    (hJ : IsIrrPlus F.terminalRepresentation (componentOrbit L ⊤) J)
    (hvJ : v ∉ J) (hJI : J ≤ B.orthogonal I)
    (x : F.terminalDot (F.X g))
    (hxJ : (x : F.TerminalHdot) ∈ subspaceStabilizer F.terminalRepresentation J) :
    Module.finrank (ZMod 2)
      (LinearMap.range ((F.terminalRepresentation x - 1).comp J.subtype)) ≤ 1 := by
  let : (componentOrbit L ⊤).Normal := componentOrbit_top_normal L
  have hle : LinearMap.range ((F.terminalRepresentation x - 1).comp J.subtype) ≤
      J ⊓ hatSpace F (F.E g) := by
    rintro w ⟨u,rfl⟩
    exact ⟨J.sub_mem ((hxJ u).mpr u.property) u.property,
      s.hypothesis.displacement x u (hJI u.property v s.point_mem)⟩
  exact (Submodule.finrank_mono hle).trans
    (s.hypothesis.constituent_inter_W_finrank_le_one
      (s.hypothesis.irreducible_of_not_solvable s.nonsolvable)
      (componentOrbit L ⊤) hJ hvJ)

/-- All actual irreducible H-submodules have the selected simple type. -/
theorem constituents_sameModule
    (J : Subrepresentation (F.terminalRepresentation.comp (componentOrbit L ⊤).subtype))
    (hJ : IsIrreducible J.toRepresentation) :
    Homogeneous.SameModule
      (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I s.selected.invariant) J := by
  let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  obtain ⟨_,hXP,hN⟩ := Recognition.source_terminal_actor_normal_in_point_sylow
    s.simple T s.empty s.maximal s.unique_overgroup s.many_overgroups s.seed_card
    (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
    s.normalizer_not_mem s.hypothesis
  exact s.hypothesis.constituent_sameModule_of_point_mem s.nonsolvable
    s.component s.moved P ((normal_subgroupOf_iff_le_normalizer hXP).mp hN)
    (Recognition.terminal_component_normalizer_index_le_two s.simple F (by decide) L s.component)
    s.selected.isIrrPlus s.point_mem J hJ

/-- Every actual irreducible H-constituent has the selected binary degree. -/
theorem constituent_finrank_eq
    (J : Subrepresentation (F.terminalRepresentation.comp (componentOrbit L ⊤).subtype))
    (hJ : IsIrreducible J.toRepresentation) :
    Module.finrank (ZMod 2) J.toSubmodule = Module.finrank (ZMod 2) I := by
  obtain ⟨e⟩ := (Homogeneous.sameModule_iff_repEquiv _ J).mp (s.constituents_sameModule J hJ)
  exact e.toLinearEquiv.finrank_eq.symm

/-- Faithfulness of H holds on each concrete constituent, with no change
of the acting group by an outer automorphism. -/
theorem constituent_faithful
    (J : Subrepresentation (F.terminalRepresentation.comp (componentOrbit L ⊤).subtype))
    (hJ : IsIrreducible J.toRepresentation) : Function.Injective J.toRepresentation := by
  let R := invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I s.selected.invariant
  have hf : Function.Injective R.toRepresentation :=
    (Recognition.source_terminal_constituent_homogeneous_of_point_mem
      s.simple T s.empty s.maximal s.unique_overgroup s.many_overgroups s.seed_card
      (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
      s.normalizer_not_mem s.nonsolvable s.hypothesis s.component s.moved
      s.selected.isIrrPlus s.point_mem).2.1
  obtain ⟨e⟩ := (Homogeneous.sameModule_iff_repEquiv R J).mp (s.constituents_sameModule J hJ)
  intro a b hab
  apply hf
  apply LinearMap.ext
  intro w
  apply e.injective
  exact (LinearMap.congr_fun (e.isIntertwining' a) w).trans
    ((LinearMap.congr_fun hab (e w)).trans (LinearMap.congr_fun (e.isIntertwining' b) w).symm)

/-- A noncentral actor stabilizing an orthogonal constituent induces an
actual rank-one displacement on it, the transvection step of G.10.14. -/
theorem orthogonal_constituent_displacement_eq_one
    {J : Submodule (ZMod 2) (Additive F.Uhat)}
    (hJ : IsIrrPlus F.terminalRepresentation (componentOrbit L ⊤) J)
    (hvJ : v ∉ J) (hJI : J ≤ B.orthogonal I)
    (x : F.terminalDot (F.X g))
    (hxJ : (x : F.TerminalHdot) ∈ subspaceStabilizer F.terminalRepresentation J)
    (hxC : (x : F.TerminalHdot) ∉ centralizer (componentOrbit L ⊤ : Set F.TerminalHdot)) :
    Module.finrank (ZMod 2)
      (LinearMap.range ((F.terminalRepresentation x - 1).comp J.subtype)) = 1 := by
  have hb := s.orthogonal_constituent_displacement_le_one hJ hvJ hJI x hxJ
  have hp : Module.finrank (ZMod 2)
      (LinearMap.range ((F.terminalRepresentation x - 1).comp J.subtype)) ≠ 0 := by
    intro hz
    let H := componentOrbit L ⊤
    let : H.Normal := componentOrbit_top_normal L
    let R := invariantSubspace F.terminalRepresentation H J hJ.choose
    have hf := s.constituent_faithful R
      (hJ.irreducible_of_normal_restriction F.terminalRepresentation
        (s.hypothesis.irreducible_of_not_solvable s.nonsolvable) H)
    apply hxC
    apply centralizes_of_fixes_faithful_section F.terminalRepresentation H J hJ.choose
    · intro a ha hh
      have he : R.toRepresentation ⟨a,ha⟩ = R.toRepresentation 1 := by
        rw [map_one]
        apply LinearMap.ext
        intro w
        apply Subtype.ext
        exact hh w w.property
      exact congrArg Subtype.val (hf he)
    · exact le_normalizer_of_normal (mem_top _)
    · intro w hw
      have hm : F.terminalRepresentation x w - w ∈
          LinearMap.range ((F.terminalRepresentation x - 1).comp J.subtype) :=
        ⟨⟨w,hw⟩,rfl⟩
      rw [Submodule.finrank_eq_zero.mp hz] at hm
      exact sub_eq_zero.mp hm
  omega

/-- The dimension split used by the two independent recognition branches.
The two-copy side already has actual complementary equivalent H-submodules. -/
theorem constituent_dimension_cases_of_not_actorFaithful
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I)) :
    Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I ∨
      2 * Module.finrank (ZMod 2) I < Module.finrank (ZMod 2) (Additive F.Uhat) := by
  have hle := s.twice_constituent_finrank_le_of_not_actorFaithful hk
  omega

/-- G.11.1(3) for the same marked point and the literal source actor.
This is a remaining source obligation, not a field of MarkedSource. -/
def FixedPointAlternative : Prop :=
  fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
      Submodule.span (ZMod 2) {v} ∨
    ∃ a : F.terminalDot (F.X g), a ≠ 1 ∧
      Module.finrank (ZMod 2) (LinearMap.range (F.terminalRepresentation a - 1)) ≤ 2 ∧
      v ∈ LinearMap.range (F.terminalRepresentation a - 1)

end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable

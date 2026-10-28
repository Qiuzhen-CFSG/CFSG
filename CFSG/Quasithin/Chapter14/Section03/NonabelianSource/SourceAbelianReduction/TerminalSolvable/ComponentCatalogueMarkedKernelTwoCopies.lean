module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedKernelFixedPoint
public import Theory.Representation.NormalConstituentDisplacement
public import CFSG.Quasithin.ChapterG.Section11.Transvection

/-!
# The exact actor kernel in the double-copy marked branch

The half-dimensional transvection space has exactly as many centered
transvections as the original actor, so its action is faithful. This supplies
an actual vector outside the selected constituent. The exact kernel fixed
space then makes its orbit free and binary, proving that C_X(H) has order
two. The literal constituent-action image consequently loses one actor
rank, and dim I equals the quotient actor rank plus two.

A low-rank nonidentity actor restricts to a transvection on each copy.
The same selected-vector alternative and relative Sylow normality also
apply the proved G.6.4 to the actual constituent quotient. Recognition
of its surviving models remains explicit; these results do not assume
that the original data are a counterexample to G.11.2.

Source: Aschbacher--Smith, G.10.16(4), G.11.1(3,4), and the two-copy
argument in G.11.8, printed pp.363--364 and 368--369.
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


/-- In the small-actor branch the action on the entire marked space is faithful. -/
theorem markedSpace_actor_faithful :
    Function.Injective (fun x : F.terminalDot (F.X g) =>
      (F.terminalRepresentation (x : F.TerminalHdot)).comp
        (hatSpace F (F.E g)).subtype) := by
  classical
  let W := hatSpace F (F.E g)
  let p : W := ⟨v,s.hypothesis.point_mem⟩
  let E := (Submodule.span (ZMod 2) {p}).dualAnnihilator
  let f (x : F.terminalDot (F.X g)) : Module.Dual (ZMod 2) W :=
    (s.hypothesis.transvections x).choose
  have hf (x : F.terminalDot (F.X g)) : f x p = 0 ∧
      ∀ w : W, F.terminalRepresentation x w = (w : Additive F.Uhat) + f x w • v :=
    (s.hypothesis.transvections x).choose_spec
  let c : F.terminalDot (F.X g) → E := fun x => ⟨f x, by
    apply (Submodule.mem_dualAnnihilator _).mpr
    change Submodule.span (ZMod 2) {p} ≤ (f x).ker
    exact Submodule.span_le.mpr (by simpa using (hf x).1)⟩
  have hc : Function.Surjective c := by
    intro t
    have htp : t.val p = 0 :=
      (Submodule.mem_dualAnnihilator _).mp t.property p (Submodule.mem_span_singleton_self p)
    obtain ⟨x,hx⟩ := s.hypothesis.full_transvections t.val htp
    refine ⟨x,Subtype.ext (LinearMap.ext fun w => ?_)⟩
    apply smul_left_injective (ZMod 2) s.hypothesis.point_ne_zero
    exact add_left_cancel ((hf x).2 w |>.symm.trans (hx w))
  have hp : p ≠ 0 := fun he => s.hypothesis.point_ne_zero (congrArg Subtype.val he)
  have he := Subspace.finrank_add_finrank_dualAnnihilator_eq
    (Submodule.span (ZMod 2) {p})
  rw [finrank_span_singleton hp] at he
  have hdim : Module.finrank (ZMod 2) E =
      Module.finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) := by
    have hx := s.actor_dimension
    have hw := s.markedSpace_dimension
    change 1 + Module.finrank (ZMod 2) E = Module.finrank (ZMod 2) W at he
    change 2 * Module.finrank (ZMod 2) W = _ at hw
    omega
  have hcard : Nat.card (F.terminalDot (F.X g)) = Nat.card E := by
    rw [Nat.card_congr Additive.ofMul,
      Module.natCard_eq_pow_finrank (K := ZMod 2)
        (V := Additive (F.terminalDot (F.X g))),
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E),hdim]
  have hci := (Nat.bijective_iff_surjective_and_card c).mpr ⟨hc,hcard⟩ |>.1
  intro x y hxy
  apply hci
  apply Subtype.ext
  apply LinearMap.ext
  intro w
  apply smul_left_injective (ZMod 2) s.hypothesis.point_ne_zero
  apply add_left_cancel (a := (w : Additive F.Uhat))
  exact ((hf x).2 w).symm.trans ((LinearMap.congr_fun hxy w).trans ((hf y).2 w))

/-- The literal marked transvection space contains a vector outside I. -/
theorem exists_markedSpace_not_mem_constituent
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I)) :
    ∃ w ∈ hatSpace F (F.E g), w ∉ I := by
  by_contra! h
  apply hk
  intro x y hxy
  apply s.markedSpace_actor_faithful
  ext w
  exact LinearMap.congr_fun hxy ⟨w,h w w.property⟩

/-- The nontrivial constituent kernel has order two in the two-copy case. -/
theorem actor_kernel_card_two_of_double_dimension
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I) :
    Nat.card ((centralizer (componentOrbit L ⊤ : Set F.TerminalHdot)).subgroupOf
      (F.terminalDot (F.X g))) = 2 := by
  classical
  let X := F.terminalDot (F.X g)
  let Y := (centralizer (componentOrbit L ⊤ : Set F.TerminalHdot)).subgroupOf X
  obtain ⟨w,hw,hwI⟩ := s.exists_markedSpace_not_mem_constituent hk
  have hfree (y : Y) (hy : F.terminalRepresentation (y : X) w = w) : y = 1 := by
    by_contra hy1
    have hyX : (y : X) ≠ 1 := fun he => hy1 (Subtype.ext he)
    apply hwI
    rw [← s.kernel_actor_fixedSpace_of_double_dimension hk hd (y : X) hyX y.property]
    exact sub_eq_zero.mpr hy
  have hinj : Function.Injective (fun y : Y => F.terminalRepresentation (y : X) w) := by
    intro a b hab
    dsimp only at hab
    have he : a⁻¹ * b = 1 := by
      apply hfree
      change F.terminalRepresentation ((a : F.TerminalHdot)⁻¹ * b) w = w
      rw [map_mul,Module.End.mul_apply,← hab,← Module.End.mul_apply,← map_mul,
        inv_mul_cancel,map_one,Module.End.one_apply]
    exact inv_mul_eq_one.mp he
  let c (y : Y) : ZMod 2 := (s.hypothesis.transvections (y : X)).choose ⟨w,hw⟩
  have hc (y : Y) : F.terminalRepresentation (y : X) w = w + c y • v :=
    (s.hypothesis.transvections (y : X)).choose_spec.2 ⟨w,hw⟩
  have hci : Function.Injective c := by
    intro a b he
    apply hinj
    change F.terminalRepresentation (a : X) w = F.terminalRepresentation (b : X) w
    rw [hc a,hc b,he]
  have hb : Nat.card Y ≤ 2 := by
    simpa only [Nat.card_zmod] using Nat.card_le_card_of_injective c hci
  have hY : Y ≠ ⊥ := by
    intro he
    have hi : X ⊓ centralizer (componentOrbit L ⊤ : Set F.TerminalHdot) = ⊥ := by
      apply le_bot_iff.mp
      intro z hz
      have hm : (⟨z,hz.1⟩ : X) ∈ Y := hz.2
      rw [he] at hm
      exact congrArg Subtype.val (show (⟨z,hz.1⟩ : X) = 1 from hm)
    exact s.actor_centralizer_ne_bot hk hi
  have hl := (Subgroup.one_lt_card_iff_ne_bot Y).mpr hY
  change 1 < Nat.card Y at hl
  change Nat.card Y = 2
  omega

/-- The quotient loses precisely one binary dimension. -/
theorem actor_quotient_dimension_of_double_dimension
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I) :
    Module.finrank (ZMod 2) I =
      Module.finrank (ZMod 2) (Additive ((F.terminalDot (F.X g)) ⧸
        (centralizer (componentOrbit L ⊤ : Set F.TerminalHdot)).subgroupOf
          (F.terminalDot (F.X g)))) + 2 := by
  have he := s.actor_dimension_of_kernel_card (k := 1)
    (by simpa only [pow_one] using s.actor_kernel_card_two_of_double_dimension hk hd)
  omega


/-- The quotient by C_X(H) is the literal actor image in Aut_HX(I). -/
def actorQuotientEquivImage :
    ((F.terminalDot (F.X g)) ⧸
      (centralizer (componentOrbit L ⊤ : Set F.TerminalHdot)).subgroupOf
        (F.terminalDot (F.X g))) ≃*
      MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
        (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes
        (F.terminalDot (F.X g)) := by
  let H := componentOrbit L ⊤
  let X := F.terminalDot (F.X g)
  let P := H ⊔ X
  let σ := MarkedAction.action F.terminalRepresentation H X I
    s.selected.invariant s.actor_stabilizes
  let q := QuotientGroup.mk' σ.ker
  let eX : X.subgroupOf P ≃* X := subgroupOfEquivOfLe (show X ≤ P from le_sup_right)
  let f := (q.subgroupMap (X.subgroupOf P)).comp eX.symm.toMonoidHom
  have hf : Function.Surjective f := (q.subgroupMap_surjective _).comp eX.symm.surjective
  have hker : f.ker = (centralizer (H : Set F.TerminalHdot)).subgroupOf X := by
    ext a
    change f a = 1 ↔ (a : F.TerminalHdot) ∈ centralizer (H : Set F.TerminalHdot)
    rw [Subtype.ext_iff]
    change (QuotientGroup.mk ⟨a,(show X ≤ P from le_sup_right) a.property⟩ : P ⧸ σ.ker) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    change σ ⟨a,(show X ≤ P from le_sup_right) a.property⟩ = 1 ↔ _
    rw [← source_marked_constituent_fixes_iff_centralizes s.simple T s.empty s.maximal
      s.unique_overgroup s.many_overgroups s.seed_card
      (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
      s.normalizer_not_mem s.nonsolvable s.hypothesis s.component s.moved
      s.selected.isIrrPlus s.point_mem a]
    constructor
    · intro he w
      exact congrArg Subtype.val (LinearMap.congr_fun he w)
    · intro he
      ext w
      exact he w
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)

/-- The actor in the actual action quotient has order 2^(dim I - 2).
This is the cardinal input to G.9 after the lost kernel dimension. -/
theorem actorImage_card_of_double_dimension
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I) :
    Nat.card (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes
      (F.terminalDot (F.X g))) = 2 ^ (Module.finrank (ZMod 2) I - 2) := by
  rw [← Nat.card_congr s.actorQuotientEquivImage.toEquiv, Nat.card_congr Additive.ofMul]
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  congr 1
  have he := s.actor_quotient_dimension_of_double_dimension hk hd
  omega


/-- The original point-normalizer cover, pulled back to HX and then mapped
through its literal constituent-action quotient. -/
def constituentSQTKCover :
    ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple
      (MarkedAction.quotient F.terminalRepresentation (componentOrbit L ⊤)
        (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes) :=
  ((Recognition.terminal_sqtkCover s.simple F (by decide)).subgroup
    (componentOrbit L ⊤ ⊔ F.terminalDot (F.X g))).map
      (MarkedAction.projection F.terminalRepresentation (componentOrbit L ⊤)
        (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes)
      (QuotientGroup.mk'_surjective _)

/-- The numerical G.9 setup on the actual action image uses the reduced
actor rank dim I - 2. Component recognition remains a separate step. -/
theorem actorImage_setup_of_double_dimension
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I) :
    ChapterG.Section09.Setup
      (kerRepresentation (MarkedAction.action F.terminalRepresentation (componentOrbit L ⊤)
        (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes))
      (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
        (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes
        (F.terminalDot (F.X g))) (Module.finrank (ZMod 2) I - 2) := by
  let X := F.terminalDot (F.X g)
  let P := componentOrbit L ⊤ ⊔ X
  let : IsElementaryAbelian 2 (X.subgroupOf P) :=
    IsElementaryAbelian.subgroupOf (show X ≤ P from le_sup_right)
  refine ⟨kerRepresentation_faithful _,IsElementaryAbelian.map _,
    s.actorImage_card_of_double_dimension hk hd,?_⟩
  have hi := s.dimension_gt_two
  omega


/-- A low-rank actor is outside the exact constituent kernel. -/
theorem lowRank_actor_not_centralizer
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    (a : F.terminalDot (F.X g)) (ha : a ≠ 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (F.terminalRepresentation a - 1)) ≤ 2) :
    (a : F.TerminalHdot) ∉ centralizer (componentOrbit L ⊤ : Set F.TerminalHdot) := by
  intro hc
  have he := (F.terminalRepresentation a - 1).finrank_range_add_finrank_ker
  rw [s.kernel_actor_fixedSpace_of_double_dimension hk hd a ha hc] at he
  have hi := s.dimension_gt_two
  omega

/-- G.10.16(2) for every actual simple constituent. -/
theorem lowRank_actor_stabilizes_constituent
    (a : F.terminalDot (F.X g))
    (hr : Module.finrank (ZMod 2) (LinearMap.range (F.terminalRepresentation a - 1)) ≤ 2)
    (J : Subrepresentation (F.terminalRepresentation.comp (componentOrbit L ⊤).subtype))
    (hJ : IsIrreducible J.toRepresentation) :
    (a : F.TerminalHdot) ∈ subspaceStabilizer F.terminalRepresentation J.toSubmodule := by
  let : (componentOrbit L ⊤).Normal := componentOrbit_top_normal L
  apply (subspace_map_eq_iff F.terminalRepresentation J.toSubmodule a).mp
  apply map_constituent_eq_self_of_displacement_lt F.terminalRepresentation
    (componentOrbit L ⊤) a J hJ
  rw [s.constituent_finrank_eq J hJ]
  have hi := s.dimension_gt_two
  exact lt_of_le_of_lt hr hi

private theorem constituent_displacement_pos
    (a : F.terminalDot (F.X g))
    (hc : (a : F.TerminalHdot) ∉ centralizer (componentOrbit L ⊤ : Set F.TerminalHdot))
    (J : Subrepresentation (F.terminalRepresentation.comp (componentOrbit L ⊤).subtype))
    (hJ : IsIrreducible J.toRepresentation) :
    0 < Module.finrank (ZMod 2)
      (LinearMap.range ((F.terminalRepresentation a - 1).comp J.toSubmodule.subtype)) := by
  apply Nat.pos_of_ne_zero
  intro hz
  let H := componentOrbit L ⊤
  let : H.Normal := componentOrbit_top_normal L
  have hf := s.constituent_faithful J hJ
  apply hc
  apply centralizes_of_fixes_faithful_section F.terminalRepresentation H J.toSubmodule
    (le_subspaceStabilizer _ _ (fun b hb w hw => J.apply_mem_toSubmodule ⟨b,hb⟩ hw))
  · intro b hb hfix
    have he : J.toRepresentation ⟨b,hb⟩ = J.toRepresentation 1 := by
      rw [map_one]
      ext w
      exact hfix w w.property
    exact congrArg Subtype.val (hf he)
  · exact le_normalizer_of_normal (mem_top _)
  · intro w hw
    have hm : F.terminalRepresentation a w - w ∈
        LinearMap.range ((F.terminalRepresentation a - 1).comp J.toSubmodule.subtype) :=
      ⟨⟨w,hw⟩,rfl⟩
    rw [Submodule.finrank_eq_zero.mp hz] at hm
    exact sub_eq_zero.mp hm

/-- In the double-degree branch a nonidentity low-rank actor restricts to
an actual transvection on the selected constituent. -/
theorem lowRank_actor_constituent_rank_one
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    (a : F.terminalDot (F.X g)) (ha : a ≠ 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (F.terminalRepresentation a - 1)) ≤ 2) :
    Module.finrank (ZMod 2)
      (LinearMap.range ((F.terminalRepresentation a - 1).comp I.subtype)) = 1 := by
  let R := invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I s.selected.invariant
  obtain ⟨J,⟨e⟩,hdis,_⟩ := s.exists_complementary_copy_of_double_dimension hk hd
  have hJ : IsIrreducible J.toRepresentation :=
    (RepEquiv.irreducible_euqiv ⟨e.toLinearEquiv,e.isIntertwining'⟩).mp s.irreducible
  have hc := s.lowRank_actor_not_centralizer hk hd a ha hr
  have hpI := s.constituent_displacement_pos a hc R s.irreducible
  have hpJ := s.constituent_displacement_pos a hc J hJ
  let P := LinearMap.range ((F.terminalRepresentation a - 1).comp I.subtype)
  let Q := LinearMap.range ((F.terminalRepresentation a - 1).comp J.toSubmodule.subtype)
  have hPI : P ≤ I := by
    rintro _ ⟨w,rfl⟩
    exact I.sub_mem ((s.actor_stabilizes a.property w).mpr w.property) w.property
  have hQJ : Q ≤ J.toSubmodule := by
    rintro _ ⟨w,rfl⟩
    exact J.toSubmodule.sub_mem
      ((s.lowRank_actor_stabilizes_constituent a hr J hJ w).mpr w.property) w.property
  have hdPQ : Disjoint P Q := hdis.mono hPI hQJ
  have hb : P ⊔ Q ≤ LinearMap.range (F.terminalRepresentation a - 1) := by
    apply sup_le
    · rintro _ ⟨w,rfl⟩
      exact ⟨w,rfl⟩
    · rintro _ ⟨w,rfl⟩
      exact ⟨w,rfl⟩
  have hs := Submodule.finrank_sup_add_finrank_inf_eq P Q
  rw [hdPQ.eq_bot,finrank_bot,add_zero] at hs
  have hm := (Submodule.finrank_mono hb).trans hr
  change 0 < Module.finrank (ZMod 2) P at hpI
  change 0 < Module.finrank (ZMod 2) Q at hpJ
  change Module.finrank (ZMod 2) P = 1
  omega

/-- The transvection has rank one for the faithful quotient representation,
with the literal quotient map applied to the original actor. -/
theorem lowRank_actor_image_rank_one
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    (a : F.terminalDot (F.X g)) (ha : a ≠ 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (F.terminalRepresentation a - 1)) ≤ 2) :
    let σ := MarkedAction.action F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes
    let aP : (componentOrbit L ⊤ ⊔ F.terminalDot (F.X g) : Subgroup F.TerminalHdot) :=
      ⟨a,(show F.terminalDot (F.X g) ≤ componentOrbit L ⊤ ⊔ F.terminalDot (F.X g)
        from le_sup_right) a.property⟩
    Module.finrank (ZMod 2)
      (LinearMap.range (kerRepresentation σ ((QuotientGroup.mk' σ.ker) aP) - 1)) = 1 := by
  intro σ aP
  let δ := kerRepresentation σ ((QuotientGroup.mk' σ.ker) aP) - 1
  have he := Submodule.finrank_map_subtype_eq I (LinearMap.range δ)
  rw [← LinearMap.range_comp] at he
  have hm : I.subtype.comp δ = (F.terminalRepresentation a - 1).comp I.subtype := by
    ext w
    rfl
  rw [hm] at he
  exact he.symm.trans (s.lowRank_actor_constituent_rank_one hk hd a ha hr)


/-- The two remaining source branches, now with rank-one displacement on I
in the low-rank branch. Recognition of these alternatives is still required. -/
theorem fixedPoint_or_constituent_transvection
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    :
    fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
        Submodule.span (ZMod 2) {v} ∨
      ∃ a : F.terminalDot (F.X g), a ≠ 1 ∧
        (a : F.TerminalHdot) ∉ centralizer (componentOrbit L ⊤ : Set F.TerminalHdot) ∧
        Module.finrank (ZMod 2)
          (LinearMap.range ((F.terminalRepresentation a - 1).comp I.subtype)) = 1 := by
  rcases s.fixedPointAlternative with hf | ⟨a,ha,hr,_⟩
  · exact Or.inl hf
  · exact Or.inr ⟨a,ha,s.lowRank_actor_not_centralizer hk hd a ha hr,
      s.lowRank_actor_constituent_rank_one hk hd a ha hr⟩


/-- The original source also supplies the relative Sylow normality required
by G.11.1(4), with the same selected vector. -/
theorem actor_normalSylow :
    ChapterG.Section11.NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) := by
  let S : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  exact ⟨S,Recognition.source_terminal_actor_normal_in_point_sylow s.simple T s.empty
    s.maximal s.unique_overgroup s.many_overgroups s.seed_card
    (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
    s.normalizer_not_mem s.hypothesis⟩

/-- In the nonfaithful branch, failure of the fixed-line alternative gives
an actual G.6.4 classification on the selected constituent's kernel quotient.
The marked vector belongs to the displacement of the actual original actor.
No counterexample to the complete G.11.2 catalogue is assumed. -/
theorem constituent_rankOne_classification_of_fixedSpace_ne_point
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hfix : fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) ≠
      Submodule.span (ZMod 2) {v}) :
    let H := componentOrbit L ⊤
    let X := F.terminalDot (F.X g)
    let σ := MarkedAction.action F.terminalRepresentation H X I
      s.selected.invariant s.actor_stabilizes
    ∃ a : X, orderOf (a : F.TerminalHdot) = 2 ∧
      v ∈ RankTwo.movedSpace F.terminalRepresentation a ∧
      Module.finrank (ZMod 2) (RankTwo.movedSpace F.terminalRepresentation a) = 2 ∧
      let aP : (H ⊔ X : Subgroup F.TerminalHdot) :=
        ⟨a,(show X ≤ H ⊔ X from le_sup_right) a.property⟩
      Module.finrank (ZMod 2) (LinearMap.range (σ aP - LinearMap.id)) = 1 ∧
      ChapterG.Section06.Conclusion (kerRepresentation σ) (QuotientGroup.mk' σ.ker aP) := by
  obtain ⟨a,_,hr,hv⟩ := s.fixedPointAlternative.resolve_left hfix
  exact ChapterG.Section11.proper_marked_constituent_rankOne_classification s.hypothesis
    ⟨Recognition.terminal_sqtkCover s.simple F (by decide)⟩
    ⟨a,a.property,hr,hv⟩ s.actor_normalSylow s.nonsolvable s.component s.moved
    s.selected.isIrrPlus s.point_mem (s.constituent_ne_top_of_not_actorFaithful hk)

end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable

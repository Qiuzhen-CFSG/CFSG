module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.GroupTheory.Sylow
public import Theory.PGroupCore
public import Theory.GroupTheory.GeneralizedFitting.Defs

/-!
# Algebraic preparation for the Green Book extension step

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, Lemma
5.3.2, printed pp. 658--659, and Definition F.4.3, printed p. 274.

The source applies Delgado--Goldschmidt--Stellmacher [DGS85, Theorem A] to
recognize compatible local actions on the actual rank-two Lie group. That
recognition theorem is not proved here. In particular, the legacy
`GreenHypothesisA`, `GreenLocalActions` and `MAlphaExtension` below do not
express its full hypotheses or conclusion. Their public interfaces are kept
for compatibility; `greenBookExtension` is only a subgroup construction.

`SourceLocalConditions` instead uses the intrinsic generalized Fitting
subgroup and actual product factorizations. It records the local facts from
5.3.1 used by 5.3.2, not all of DGS Hypothesis A: the rank-one model and Sylow
conditions still have to be supplied by the recognition development.

The compatible-action helpers prove the algebraic part of F.4.3 from explicit
local realization data. The proof uses normality of inner automorphisms to
turn local product decompositions into the global product; the middle
intersection determines the other two intersections. Neither a concrete Lie
model nor trivial action on its Dynkin diagram follows from these helpers.
The source theorem remains dependent on genuine DGS recognition and the
amalgam identifications of Section 5.2.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter5.Section03GreenExtension

open Subgroup

/-! ## Amalgams -/

/-- A generating subgroup diagram. The name is legacy: a concrete Lie model,
Borel identification and exact intersection are additional data. -/
structure LieAmalgam (A : Type*) [Group A] where
  G₁ : Subgroup A
  G₁₂ : Subgroup A
  G₂ : Subgroup A
  middle_left : G₁₂ ≤ G₁
  middle_right : G₁₂ ≤ G₂
  generated : G₁ ⊔ G₂ = ⊤

/-- The local amalgam obtained from the two maximal 2-local subgroups. -/
structure LocalAmalgam (G : Type*) [Group G] where
  M₁ : Subgroup G
  M₁₂ : Subgroup G
  M₂ : Subgroup G
  middle_left : M₁₂ ≤ M₁
  middle_right : M₁₂ ≤ M₂

/-! ## The source's Hypothesis A data -/

/-- Legacy family labels, with no connection to a concrete group model. -/
inductive LieRankTwoKind
  | linear
  | unitary
  | symplectic
  | exceptional
  deriving DecidableEq, Repr

/-- Legacy data: `fstar` is an arbitrary subgroup, not the intrinsic
 generalized Fitting subgroup. This is not the source Fitting condition;
 use `SourceLocalConditions` for that condition. -/
structure FittingTwoCoreWitness {G : Type*} [Group G]
    (M L : Subgroup G) where
  fstar : Subgroup G
  fstar_eq_twoCore_M : fstar = (pCore 2 M).map M.subtype
  twoCore_eq : (pCore 2 M).map M.subtype = (pCore 2 L).map L.subtype

/-- Legacy local data, insufficient for DGS Hypothesis A. In particular,
`kind` is not a model identification and the factorizations are only joins. -/
structure GreenHypothesisA {G : Type*} [Group G]
    (γ : LocalAmalgam G) (q : ℕ) where
  q_even : Even q
  q_gt_two : 2 < q
  L₁ : Subgroup G
  L₂ : Subgroup G
  o2_generated_trivial :
    (pCore 2 (γ.M₁ ⊔ γ.M₂ : Subgroup G)).map
      (Subgroup.subtype (γ.M₁ ⊔ γ.M₂ : Subgroup G)) = ⊥
  fitting_left : FittingTwoCoreWitness γ.M₁ L₁
  fitting_right : FittingTwoCoreWitness γ.M₂ L₂
  factor_left : γ.M₁ = L₁ ⊔ γ.M₁₂
  factor_right : γ.M₂ = L₂ ⊔ γ.M₁₂
  S : Subgroup G
  normalizer_eq_middle : Subgroup.normalizer (S : Set G) = γ.M₁₂
  normalizer_left : γ.M₁ ⊓ Subgroup.normalizer (S : Set G) = γ.M₁₂
  normalizer_right : γ.M₂ ⊓ Subgroup.normalizer (S : Set G) = γ.M₁₂
  kind : LieRankTwoKind

/-! ## Automorphism groups and extensions -/

/-- The canonical inner copy of a group in its automorphism group. -/
def innerSubgroup (A : Type*) [Group A] : Subgroup (MulAut A) :=
  (MulAut.conj : A →* MulAut A).range

/-- Legacy faithful actions with containments, but no overlap agreement. -/
structure GreenLocalActions {A G : Type*} [Group A] [Group G]
    (α : LieAmalgam A) (γ : LocalAmalgam G) where
  left : γ.M₁ →* MulAut A
  right : γ.M₂ →* MulAut A
  middle : γ.M₁₂ →* MulAut A
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  middle_injective : Function.Injective middle
  leftContains : α.G₁.map (MulAut.conj : A →* MulAut A) ≤ left.range
  rightContains : α.G₂.map (MulAut.conj : A →* MulAut A) ≤ right.range
  middle_left_range : middle.range ≤ left.range
  middle_right_range : middle.range ≤ right.range

/-- Legacy faithful local maps into an automorphism subgroup. This omits
compatibility, the intersection and product conditions, and Dynkin action,
so is not Definition F.4.3. -/
structure MAlphaExtension {A G : Type*} [Group A] [Group G]
    (α : LieAmalgam A) (γ : LocalAmalgam G) where
  carrier : Subgroup (MulAut A)
  contains_defining : innerSubgroup A ≤ carrier
  contained_in_automorphisms : carrier ≤ ⊤
  leftAction : γ.M₁ →* carrier
  rightAction : γ.M₂ →* carrier
  middleAction : γ.M₁₂ →* carrier
  leftFaithful : Function.Injective leftAction
  rightFaithful : Function.Injective rightAction
  middleFaithful : Function.Injective middleAction

private theorem inner_le_sup_ranges {A G : Type*} [Group A] [Group G]
    (α : LieAmalgam A) (γ : LocalAmalgam G)
    (a : GreenLocalActions α γ) :
    innerSubgroup A ≤ a.left.range ⊔ a.right.range := by
  intro x hx
  rcases hx with ⟨g, rfl⟩
  -- The two rank-one factors generate the defining group.  We use the
  -- supplied local containments after transporting the equality `generated`.
  have hgen : α.G₁ ⊔ α.G₂ = (⊤ : Subgroup A) := α.generated
  have hg : MulAut.conj g ∈ (α.G₁.map (MulAut.conj : A →* MulAut A)) ⊔
      (α.G₂.map (MulAut.conj : A →* MulAut A)) := by
    rw [← Subgroup.map_sup]
    simp [hgen]
  exact (sup_le_sup a.leftContains a.rightContains) hg

/-- Legacy subgroup construction from supplied faithful local actions.
The unused local hypothesis does not make this a proof of Lemma 5.3.2. -/
theorem greenBookExtension {A G : Type*} [Group A] [Group G]
    (α : LieAmalgam A) (γ : LocalAmalgam G) (q : ℕ)
    (_hA : GreenHypothesisA γ q) (a : GreenLocalActions α γ) :
    Nonempty (MAlphaExtension α γ) := by
  let carrier : Subgroup (MulAut A) := a.left.range ⊔ a.right.range
  have hinner : innerSubgroup A ≤ carrier := inner_le_sup_ranges α γ a
  let leftAction : γ.M₁ →* carrier :=
    a.left.codRestrict carrier (fun x =>
      (show a.left.range ≤ carrier from le_sup_left) ⟨x, rfl⟩)
  let rightAction : γ.M₂ →* carrier :=
    a.right.codRestrict carrier (fun x =>
      (show a.right.range ≤ carrier from le_sup_right) ⟨x, rfl⟩)
  let middleAction : γ.M₁₂ →* carrier :=
    a.middle.codRestrict carrier (fun x => by
      have hm : a.middle x ∈ a.middle.range := ⟨x, rfl⟩
      have hl : a.middle x ∈ a.left.range := a.middle_left_range hm
      exact (show a.left.range ≤ carrier from le_sup_left) hl)
  refine ⟨{
    carrier := carrier
    contains_defining := hinner
    contained_in_automorphisms := le_top
    leftAction := leftAction
    rightAction := rightAction
    middleAction := middleAction
    leftFaithful := ?_
    rightFaithful := ?_
    middleFaithful := ?_ }⟩
  · intro x y hxy
    apply a.left_injective
    exact congrArg Subtype.val hxy
  · intro x y hxy
    apply a.right_injective
    exact congrArg Subtype.val hxy
  · intro x y hxy
    apply a.middle_injective
    exact congrArg Subtype.val hxy

/-- Snake-case public spelling for downstream Chapter 5 modules. -/
theorem green_book_extension {A G : Type*} [Group A] [Group G]
    (α : LieAmalgam A) (γ : LocalAmalgam G) (q : ℕ)
    (_hA : GreenHypothesisA γ q) (a : GreenLocalActions α γ) :
    Nonempty (MAlphaExtension α γ) :=
  greenBookExtension α γ q _hA a

/-! ## Intrinsic local conditions and compatible actions -/

/-- The local equalities from 5.3.1 used in 5.3.2. All cores are computed
inside the indicated local group, then mapped to the ambient group when
necessary. Product decompositions are products, not subgroup joins.

This is only part of Hypothesis A: no rank-one or rank-two identification,
field parameter, or Sylow hypothesis is asserted by this record. -/
structure SourceLocalConditions {G : Type*} [Group G] [Finite G]
    (γ : LocalAmalgam G) (L₁ L₂ S : Subgroup G) : Prop where
  middle_eq : γ.M₁₂ = γ.M₁ ⊓ γ.M₂
  left_le : L₁ ≤ γ.M₁
  right_le : L₂ ≤ γ.M₂
  generated_twoCore : pCore 2 (γ.M₁ ⊔ γ.M₂ : Subgroup G) = ⊥
  fitting_left : Theory.GroupTheory.generalizedFitting γ.M₁ = pCore 2 γ.M₁
  fitting_right : Theory.GroupTheory.generalizedFitting γ.M₂ = pCore 2 γ.M₂
  twoCore_left : (pCore 2 γ.M₁).map γ.M₁.subtype = (pCore 2 L₁).map L₁.subtype
  twoCore_right : (pCore 2 γ.M₂).map γ.M₂.subtype = (pCore 2 L₂).map L₂.subtype
  factor_left : ∀ x ∈ γ.M₁, ∃ l ∈ L₁, ∃ b ∈ γ.M₁₂, x = l * b
  factor_right : ∀ x ∈ γ.M₂, ∃ l ∈ L₂, ∃ b ∈ γ.M₁₂, x = l * b
  normalizer_eq_middle : Subgroup.normalizer (S : Set G) = γ.M₁₂

/-- Faithful local actions agreeing on the specified whole overlap.
Unlike mere range containment, these equations retain the amalgam marking. -/
structure CompatibleLocalActions {A G : Type*} [Group A] [Group G]
    (α : LieAmalgam A) (γ : LocalAmalgam G) extends GreenLocalActions α γ where
  left_agrees : ∀ b : γ.M₁₂, left ⟨b, γ.middle_left b.property⟩ = middle b
  right_agrees : ∀ b : γ.M₁₂, right ⟨b, γ.middle_right b.property⟩ = middle b

/-- Inner automorphisms form a normal subgroup even before centerlessness
is established. Identifying this subgroup with the defining group still
requires injectivity of `MulAut.conj`. -/
theorem innerSubgroup_normal (A : Type*) [Group A] : (innerSubgroup A).Normal := by
  refine ⟨?_⟩
  rintro x ⟨g, rfl⟩ φ
  refine ⟨φ g, ?_⟩
  ext y
  simp [MulAut.conj_apply, MulAut.mul_apply]

namespace CompatibleLocalActions

variable {A G : Type*} [Group A] [Group G]
    {α : LieAmalgam A} {γ : LocalAmalgam G} (a : CompatibleLocalActions α γ)

/-- The candidate completion in the automorphism group. -/
def completion : Subgroup (MulAut A) := a.left.range ⊔ a.right.range

theorem inner_le_completion : innerSubgroup A ≤ a.completion :=
  inner_le_sup_ranges α γ a.toGreenLocalActions

/-- Relative normality of the inner copy in the candidate completion. -/
theorem defining_normal : ((innerSubgroup A).subgroupOf a.completion).Normal := by
  let _ := innerSubgroup_normal A
  infer_instance

/-- The local isomorphisms onto their images agree on every element of the
whole overlap, not only on a Sylow subgroup. -/
theorem agree_on_overlap (b : γ.M₁₂) :
    a.left ⟨b, γ.middle_left b.property⟩ =
      a.right ⟨b, γ.middle_right b.property⟩ :=
  (a.left_agrees b).trans (a.right_agrees b).symm

private theorem product_of_factorization
    {M B L : Subgroup G} (hBM : B ≤ M) (hLM : L ≤ M)
    (f : M →* MulAut A) (b : B →* MulAut A) (P : Subgroup A)
    (hagree : ∀ x : B, f ⟨x, hBM x.property⟩ = b x)
    (hfactor : ∀ x ∈ M, ∃ l ∈ L, ∃ y ∈ B, x = l * y)
    (himage : ∀ l : L, f ⟨l, hLM l.property⟩ ∈
      P.map (MulAut.conj : A →* MulAut A)) :
    ∀ x : M, ∃ g ∈ P, ∃ y : B, f x = MulAut.conj g * b y := by
  intro x
  obtain ⟨l, hl, y, hy, he⟩ := hfactor x x.property
  obtain ⟨g, hg, hfg⟩ := himage ⟨l, hl⟩
  refine ⟨g, hg, ⟨y, hy⟩, ?_⟩
  have hx : x = (⟨l, hLM hl⟩ : M) * ⟨y, hBM hy⟩ := Subtype.ext he
  rw [hx, map_mul, hagree ⟨y, hy⟩, ← hfg]

/-- Transfer the actual products `Mᵢ = Lᵢ M₁₂` from 5.3.1 through
compatible actions. Only the local product fields are used here; the
Fitting conditions do not prove the required images of `Lᵢ`. Those images
must come from the missing recognition theorem. -/
theorem local_products_of_source [Finite G] {L₁ L₂ S : Subgroup G}
    (h : SourceLocalConditions γ L₁ L₂ S)
    (hleft : ∀ l : L₁, a.left ⟨l, h.left_le l.property⟩ ∈
      α.G₁.map (MulAut.conj : A →* MulAut A))
    (hright : ∀ l : L₂, a.right ⟨l, h.right_le l.property⟩ ∈
      α.G₂.map (MulAut.conj : A →* MulAut A)) :
    (∀ x : γ.M₁, ∃ g ∈ α.G₁, ∃ b : γ.M₁₂,
      a.left x = MulAut.conj g * a.middle b) ∧
    (∀ x : γ.M₂, ∃ g ∈ α.G₂, ∃ b : γ.M₁₂,
      a.right x = MulAut.conj g * a.middle b) := by
  exact ⟨product_of_factorization γ.middle_left h.left_le a.left a.middle α.G₁
      a.left_agrees h.factor_left hleft,
    product_of_factorization γ.middle_right h.right_le a.right a.middle α.G₂
      a.right_agrees h.factor_right hright⟩

/-- Local products imply the global product in F.4.3. Normality of the
inner subgroup is what upgrades a generated join to an actual product. -/
theorem completion_product
    (hleft : ∀ x : γ.M₁, ∃ g ∈ α.G₁, ∃ b : γ.M₁₂,
      a.left x = MulAut.conj g * a.middle b)
    (hright : ∀ x : γ.M₂, ∃ g ∈ α.G₂, ∃ b : γ.M₁₂,
      a.right x = MulAut.conj g * a.middle b) :
    ∀ φ, φ ∈ a.completion ↔ ∃ g : A, ∃ b : γ.M₁₂,
      φ = MulAut.conj g * a.middle b := by
  have hle : a.completion ≤ innerSubgroup A ⊔ a.middle.range := by
    apply sup_le
    · rintro _ ⟨x, rfl⟩
      obtain ⟨g, _, b, he⟩ := hleft x
      rw [he]
      exact Subgroup.mul_mem_sup ⟨g, rfl⟩ ⟨b, rfl⟩
    · rintro _ ⟨x, rfl⟩
      obtain ⟨g, _, b, he⟩ := hright x
      rw [he]
      exact Subgroup.mul_mem_sup ⟨g, rfl⟩ ⟨b, rfl⟩
  let _ := innerSubgroup_normal A
  intro φ
  constructor
  · intro hφ
    obtain ⟨_, ⟨g, rfl⟩, _, ⟨b, rfl⟩, he⟩ :=
      Subgroup.mem_sup_of_normal_left.mp (hle hφ)
    exact ⟨g, b, he.symm⟩
  · rintro ⟨g, b, rfl⟩
    exact a.completion.mul_mem (a.inner_le_completion ⟨g, rfl⟩)
      (Subgroup.mem_sup_left (a.middle_left_range ⟨b, rfl⟩))

private theorem local_inner_intersection {L : Type*} [Group L]
    (P : Subgroup A) (f : L →* MulAut A)
    (hcontains : P.map (MulAut.conj : A →* MulAut A) ≤ f.range)
    (hbase : α.G₁₂ ≤ P)
    (hmiddle : a.middle.range ⊓ innerSubgroup A =
      α.G₁₂.map (MulAut.conj : A →* MulAut A))
    (hprod : ∀ x : L, ∃ g ∈ P, ∃ b : γ.M₁₂,
      f x = MulAut.conj g * a.middle b) :
    f.range ⊓ innerSubgroup A = P.map (MulAut.conj : A →* MulAut A) := by
  apply le_antisymm
  · rintro φ ⟨⟨x, rfl⟩, hx⟩
    obtain ⟨g, hg, b, he⟩ := hprod x
    have hb : a.middle b ∈ innerSubgroup A := by
      have ht := (innerSubgroup A).mul_mem
        ((innerSubgroup A).inv_mem (show MulAut.conj g ∈ innerSubgroup A from ⟨g, rfl⟩)) hx
      simpa only [he, inv_mul_cancel_left] using ht
    have hbm : a.middle b ∈ P.map (MulAut.conj : A →* MulAut A) :=
      Subgroup.map_mono hbase (hmiddle ▸ ⟨⟨b, rfl⟩, hb⟩)
    rw [he]
    exact (P.map _).mul_mem ⟨g, hg, rfl⟩ hbm
  · intro φ hφ
    refine ⟨hcontains hφ, ?_⟩
    rcases hφ with ⟨g, _, rfl⟩
    exact ⟨g, rfl⟩

/-- The middle intersection and the two local products force both parabolic
intersections and the exact common overlap of the realized local groups.
Injectivity of inner conjugation prevents central elements from collapsing
the defining amalgam's intersection. These are algebraic consequences of
explicit realization inputs, not a recognition theorem. -/
theorem intersections
    (hconj : Function.Injective (MulAut.conj : A →* MulAut A))
    (hα : α.G₁ ⊓ α.G₂ = α.G₁₂)
    (hmiddle : a.middle.range ⊓ innerSubgroup A =
      α.G₁₂.map (MulAut.conj : A →* MulAut A))
    (hleft : ∀ x : γ.M₁, ∃ g ∈ α.G₁, ∃ b : γ.M₁₂,
      a.left x = MulAut.conj g * a.middle b)
    (hright : ∀ x : γ.M₂, ∃ g ∈ α.G₂, ∃ b : γ.M₁₂,
      a.right x = MulAut.conj g * a.middle b) :
    a.left.range ⊓ innerSubgroup A = α.G₁.map (MulAut.conj : A →* MulAut A) ∧
    a.right.range ⊓ innerSubgroup A = α.G₂.map (MulAut.conj : A →* MulAut A) ∧
    a.left.range ⊓ a.right.range = a.middle.range := by
  have h₁ := a.local_inner_intersection α.G₁ a.left a.leftContains
    α.middle_left hmiddle hleft
  have h₂ := a.local_inner_intersection α.G₂ a.right a.rightContains
    α.middle_right hmiddle hright
  refine ⟨h₁, h₂, le_antisymm ?_ (le_inf a.middle_left_range a.middle_right_range)⟩
  rintro φ ⟨⟨x, rfl⟩, hx⟩
  obtain ⟨g, hg, b, he⟩ := hleft x
  have hgr : MulAut.conj g ∈ a.right.range := by
    have ht := a.right.range.mul_mem hx
      (a.right.range.inv_mem (a.middle_right_range ⟨b, rfl⟩))
    simpa only [he, mul_inv_cancel_right] using ht
  have hg₂ : MulAut.conj g ∈ α.G₂.map (MulAut.conj : A →* MulAut A) :=
    h₂ ▸ ⟨hgr, ⟨g, rfl⟩⟩
  have hg₁₂ : MulAut.conj g ∈ α.G₁₂.map (MulAut.conj : A →* MulAut A) := by
    rw [← hα, Subgroup.map_inf _ _ _ hconj]
    exact ⟨⟨g, hg, rfl⟩, hg₂⟩
  have hgm : MulAut.conj g ∈ a.middle.range := (hmiddle.symm ▸ hg₁₂).1
  rw [he]
  exact a.middle.range.mul_mem hgm ⟨b, rfl⟩

end CompatibleLocalActions

end CFSG.Quasithin.Chapter5.Section03GreenExtension

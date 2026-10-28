module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.ProfileActors
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.EqualLinearApplication
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The equal-linear Fong--Seitz branch from the original DGS actors

The actual Chapter 10 actor is S times the original local factor. Its
published BOneActionData quotient, with the full original parabolic
core as kernel, therefore identifies the full root-generated actor.
The central panel kernel vanishes in binary SL2, so this also identifies
the faithful local permutation group. Both maps retain the original
actor quotient on representatives.

The two original natural actions force equal field orders. Finite-field
uniqueness supplies an actual field isomorphism, and the already proved
original-core and panel-index transports give the two root orders and
both commuting orientations. This proves every clause of I (6A)(a)
from the same earlier inputs used by original_bOne_profile, on its m=4
quotient. The original application supplies C2's literal kernelRoot
commutator and the full original S image. Fields two and four are included.

Original Chapter 6/7 actions and section 2/5 reflection/kernel inputs
remain with their named producers. No geometric completion is assumed
to descend to the ambient original group, and no perfectness is used.
Source: DGS (10.5), pp.156--157; Fong--Seitz I (6A)(a), pp.37--38.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
open DGS85.NoncommutingProfile DGS85.Reduction Subgroup.CosetGeometry.RankTwo
private def mapSubgroupOfEquiv {A B : Type*} [Group A] [Group B]
    (H : Subgroup A) (f : A →* B) (hf : Function.Injective f)
    {J E : Subgroup B} (hmap : H.map f = J) (hJE : J ≤ E) : H ≃* J.subgroupOf E :=
  ((H.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hmap)).trans
    (subgroupOfEquivOfLe hJE).symm

private theorem mapSubgroupOfEquiv_apply {A B : Type*} [Group A] [Group B]
    (H : Subgroup A) (f : A →* B) (hf : Function.Injective f)
    {J E : Subgroup B} (hmap : H.map f = J) (hJE : J ≤ E) (a : H) :
    ((mapSubgroupOfEquiv H f hf hmap hJE a : E) : B) = f a := rfl

variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
  (b : Bool)
  (c : BOneActionData (reducedFamily L S) (base (reducedFamily L S) b)
    (base (reducedFamily L S) (!b)) k W)
  (hactor : c.actor =
    ((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S (if b then 1 else 0)).subgroupOf (G₀ L S))
include Q e h split hactor

/-- The published DGS actor becomes the literal original S-times-local actor. -/
theorem marked_bOne_actor_image :
    c.actor.map (G₀ L S).subtype = S ⊔ L (if b then 1 else 0) := by
  let i : Fin 2 := if b then 1 else 0
  have hPG' (t : Fin 2) : P₀ L S t ≤ G₀ L S := by
    fin_cases t
    · exact le_sup_left
    · exact le_sup_right
  have hPG := hPG' i
  have hAG : (B₀ L S).pCoreIn 2 ⊔ starredParabolic L S i ≤ G₀ L S :=
    (sup_le ((pCoreIn_le 2 _).trans le_sup_right) le_sup_left).trans hPG
  rw [hactor,map_subgroupOf_eq_of_le hAG,B₀_core h,marked_original_borel_core Q e h split]
  change S ⊔ ((parabolic L S i).pCoreIn 2 ⊔ L i) = S ⊔ L i
  rw [←sup_assoc,sup_eq_left.mpr (show (parabolic L S i).pCoreIn 2 ≤ S from h.parabolic_core_le_S i)]

/-- Restrict the literal reduced-completion inclusion to the full original actor. -/
def markedBOneActorEquiv : c.actor ≃* (S ⊔ L (if b then 1 else 0)).subgroupOf
    (parabolic L S (if b then 1 else 0)) :=
  mapSubgroupOfEquiv c.actor (G₀ L S).subtype (G₀ L S).subtype_injective
    (marked_bOne_actor_image Q e h split b c hactor)
    (sup_le (show S ≤ parabolic L S (if b then 1 else 0) from le_sup_right.trans le_sup_left)
      (show L (if b then 1 else 0) ≤ parabolic L S (if b then 1 else 0) from
        le_sup_left.trans le_sup_left))

@[simp] theorem markedBOneActorEquiv_apply (a : c.actor) :
    ((markedBOneActorEquiv Q e h split b c hactor a :
      parabolic L S (if b then 1 else 0)) : G) = (a : G₀ L S) :=
  mapSubgroupOfEquiv_apply _ _ _ _ _ _

/-- The original quotient map retains the full original parabolic two-core kernel. -/
theorem markedBOneActorEquiv_kernel :
    (c.quotient.comp (markedBOneActorEquiv Q e h split b c hactor).symm.toMonoidHom).ker =
      (pCore 2 (parabolic L S (if b then 1 else 0))).subgroupOf
        ((S ⊔ L (if b then 1 else 0)).subgroupOf (parabolic L S (if b then 1 else 0))) := by
  let i : Fin 2 := if b then 1 else 0
  let j := markedBOneActorEquiv Q e h split b c hactor
  ext a
  obtain ⟨z,rfl⟩ := j.surjective a
  change c.quotient (j.symm (j z)) = 1 ↔ (j z).val ∈ pCore 2 (parabolic L S i)
  rw [MulEquiv.symm_apply_apply]
  change z ∈ c.quotient.ker ↔ _
  rw [c.kernel]
  have hcore := reduced_base_Q_map h b
  have hm : ((z : G₀ L S) : G) ∈ (parabolic L S i).pCoreIn 2 ↔
      (z : G₀ L S) ∈ DGS85.Q (reducedFamily L S) (base (reducedFamily L S) b) := by
    rw [←hcore]
    exact mem_map_iff_mem (G₀ L S).subtype_injective
  change (z : G₀ L S) ∈ DGS85.Q (reducedFamily L S) (base (reducedFamily L S) b) ↔ _
  rw [←hm,←markedBOneActorEquiv_apply Q e h split b c hactor z]
  exact mem_map_iff_mem (K := pCore 2 (parabolic L S i)) (x := (j z).val)
    (parabolic L S i).subtype_injective

/-- Both the full root actor and its faithful image follow the actual DGS quotient map. -/
theorem marked_bOne_actors
    (s : RootReflection Q split (if b then 1 else 0))
    (hV : simpleRemainder Q split (if b then 1 else 0) ≤ localKernel Q (if b then 1 else 0)) :
    ∃ μ : rankOne Q split (if b then 1 else 0) ≃* SL(2,k),
      ∃ ν : localGroup Q split (if b then 1 else 0) ≃* PSL(2,k),
        (∀ r, ν (RootLocalCover.projection Q split (if b then 1 else 0) r) =
          Atlas.RankOneFieldAutomorphisms.slEquivPSL (μ r)) ∧
        ∀ r : rankOne Q split (if b then 1 else 0), ∃ a : c.actor,
          ∃ ha : ((a : G₀ L S) : G) ∈ parabolic L S (if b then 1 else 0),
            MarkedLocal.endpointMap Q e (if b then 1 else 0) ⟨a,ha⟩ = r ∧ μ r = c.quotient a := by
  let i : Fin 2 := if b then 1 else 0
  let A := (S ⊔ L i).subgroupOf (parabolic L S i)
  let j := markedBOneActorEquiv Q e h split b c hactor
  have hj := markedBOneActorEquiv_apply Q e h split b c hactor
  let f : A →* SL(2,k) := c.quotient.comp j.symm.toMonoidHom
  have hf : Function.Surjective f := c.onto.comp j.symm.surjective
  have hk := markedBOneActorEquiv_kernel Q e h split b c hactor
  let : A.Normal := marked_sylow_factor_normal Q e h split i
  have hSA : S.subgroupOf (parabolic L S i) ≤ A := subgroupOf_mono _ le_sup_left
  obtain ⟨μ,ν,hν,hμ⟩ := marked_linear_localGroup Q e h split i s hV A hSA f hf hk
  refine ⟨μ,ν,hν,?_⟩
  intro r
  obtain ⟨a,ha,he⟩ := hμ r
  let z := j.symm a
  have hz : ((z : G₀ L S) : G) = ((a : parabolic L S i) : G) := by
    rw [←hj z]
    exact congrArg (fun v : A => ((v : parabolic L S i) : G)) (j.apply_symm_apply a)
  refine ⟨z,hz ▸ a.val.property,?_,he⟩
  convert ha using 1
  congr 1
  exact Subtype.ext hz

omit b c hactor in
/-- All clauses of I (6A)(a), with both original endpoint orientations.
The common field is realized by an actual finite-field isomorphism. -/
theorem marked_bOne_sixA
    {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
    [Field k₁] [Finite k₁] [CharP k₁ 2]
    [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
    (c₀ : BOneActionData (reducedFamily L S) (base (reducedFamily L S) false)
      (base (reducedFamily L S) true) k₀ W₀)
    (c₁ : BOneActionData (reducedFamily L S) (base (reducedFamily L S) true)
      (base (reducedFamily L S) false) k₁ W₁)
    (hactor₀ : c₀.actor = ((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S 0).subgroupOf (G₀ L S))
    (hactor₁ : c₁.actor = ((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S 1).subgroupOf (G₀ L S))
    (E₀ : letI : Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2
      W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀))
    (hm : rotationOrder Q = 4) (s : ∀ i, RootReflection Q split i)
    (hV : ∀ i, simpleRemainder Q split i ≤ localKernel Q i) :
    ∃ n : ℕ, 0 < n ∧ Nat.card k₀ = 2^n ∧
      Nonempty (localGroup Q split 0 ≃* PSL(2,k₀)) ∧
      Nonempty (localGroup Q split 1 ≃* PSL(2,k₀)) ∧
      (∀ i, Nat.card (simpleRoot Q split i) = 2^n) ∧
      (∀ i j, i ≠ j → ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ = ⊥) ∧
      Nat.card split.U = (2^n)^4 := by
  let : Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2
  let : Fintype k₀ := Fintype.ofFinite k₀
  let : Fintype k₁ := Fintype.ofFinite k₁
  have heq := paired_field_orders_eq (reduced_triple h) c₀ c₁ E₀
  let θ : k₁ ≃+* k₀ := FiniteField.ringEquivOfCardEq
    (by simpa only [Nat.card_eq_fintype_card] using heq.symm)
  obtain ⟨μ₀,ν₀,_,_⟩ := marked_bOne_actors Q e h split false c₀ hactor₀ (s 0) (hV 0)
  obtain ⟨μ₁,ν₁,_,_⟩ := marked_bOne_actors Q e h split true c₁ hactor₁ (s 1) (hV 1)
  obtain ⟨n,_,hn⟩ := FiniteField.card k₀ 2
  have hn' : Nat.card k₀ = 2^(n : ℕ) := by simpa only [Nat.card_eq_fintype_card] using hn
  refine ⟨n,n.pos,hn',⟨ν₀⟩,⟨ν₁.trans (Atlas.fieldEquivPSL 2 θ)⟩,?_,?_,?_⟩
  · intro i
    exact (marked_bOne_simpleRoot_card Q e h c₀ c₁ hactor₀ hactor₁ E₀ split i).trans hn'
  · intro i j hij
    exact marked_bOne_root_commutator Q e h c₀ c₁ split i j hij (hV j)
  · rw [←hn']
    exact marked_bOne_unipotent_card Q e h c₀ c₁ hactor₀ hactor₁ E₀ split hm

omit Q e split b c hactor in
/-- The completed equal-linear branch on the original quotient supplies the
actual C2 kernelRoot premise and the full original S image, including q=2. -/
theorem original_bOne_sixA
    {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
    [Field k₁] [Finite k₁] [CharP k₁ 2]
    [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
    (c₀ : BOneActionData (reducedFamily L S) (base (reducedFamily L S) false)
      (base (reducedFamily L S) true) k₀ W₀)
    (c₁ : BOneActionData (reducedFamily L S) (base (reducedFamily L S) true)
      (base (reducedFamily L S) false) k₁ W₁)
    (hactor₀ : c₀.actor = ((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S 0).subgroupOf (G₀ L S))
    (hactor₁ : c₁.actor = ((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S 1).subgroupOf (G₀ L S))
    (E₀ : letI : Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2
      W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀))
    (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
    (hm : rotationOrder Q₀ = 4) (s : ∀ i, RootReflection Q₀ split₀ i)
    (hV : ∀ i, simpleRemainder Q₀ split₀ i ≤ localKernel Q₀ i) :
    Nonempty (localGroup Q₀ split₀ 0 ≃* PSL(2,k₀)) ∧
      Nonempty (localGroup Q₀ split₀ 1 ≃* PSL(2,k₀)) ∧
      (∀ i, Nat.card (simpleRoot Q₀ split₀ i) = Nat.card k₀) ∧
      ⁅simpleRoot Q₀ split₀ 1,C2RankThree.kernelRoot Q₀ split₀⁆ = ⊥ ∧
      Nat.card ((S.subgroupOf (generated L S)).map Q₀.q) = Nat.card k₀ ^ 4 := by
  obtain ⟨n,_,hn,h₀,h₁,_,_,_⟩ := marked_bOne_sixA Q₀ (originalMarkedIso Q₀) h split₀
    c₀ c₁ hactor₀ hactor₁ E₀ hm s hV
  exact ⟨h₀,h₁,original_bOne_c2_data h c₀ c₁ hactor₀ hactor₁ E₀ Q₀ split₀ hm (hV 0)⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure

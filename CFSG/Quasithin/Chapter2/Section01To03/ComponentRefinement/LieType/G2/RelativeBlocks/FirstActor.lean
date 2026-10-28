module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.RelativeBlocks.FirstActor.NormalForm
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.RelativeBlocks.Sections
public import Mathlib.GroupTheory.IsSubnormal


/-!
# No nontrivial square-trivial two-perfect actor in the first derived G₂ parabolic

Four root elements B(1), E(1), C(1)D(1), and B(1)E(1) lie in both the
five-root radical and the actual derived G₂ model. Their derived membership
follows from root commutators and Weyl conjugation, uniformly including the
binary field. Normality of the radical in the full parabolic puts its
intersection with the derived model in the intrinsic two-core of `firstModel`.

The four square tests and the proved two-cell normal form force any element
acting with square-one commutators on this core into the radical. Hence a
two-perfect subgroup with that action is a two-group and is trivial. This
proves the stronger statement for every two-perfect subgroup, together with
the requested subnormal formulation.

The sole conditional input is `local₁.pCoreIn 2 = radical₁`, discharged by
the outer short-local assembly. No quotient, order, simplicity, or local
perfectness input is needed. This is the first-coordinate prerequisite for
Aschbacher–Smith 2.3.9(7), printed p.526; the relative-block assembly remains
in its owning module.

The root model and its identities are from the licensed ATLAS port; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

open Atlas.G2 Atlas.G2.LieParabolicSetup Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2.RelativeBlocks
namespace FirstActor
variable {F : Type*} [Field F] [CharP F 2]

omit [CharP F 2] in
private theorem rootA_mem_derived : rootA (1 : F) ∈ commutator (Model F) := by
  have he : ⁅rootB (1:F),rootE (1 : F)⁆ = rootA (1 : F) := by
    simpa [unipotentProduct] using
      fiveRoot_commutator (F := F) ![0,1,0,0,0,0] ![0,0,0,0,1,0] rfl rfl
  rw [← he]
  exact commutator_mem_commutator (mem_top _) (mem_top _)

omit [CharP F 2] in
private theorem rootB_mem_derived : rootB (1 : F) ∈ commutator (Model F) := by
  rw [← weylR_rootA]
  exact (inferInstance : (commutator (Model F)).Normal).conj_mem _ rootA_mem_derived _

omit [CharP F 2] in
private theorem rootE_mem_derived : rootE (1 : F) ∈ commutator (Model F) := by
  rw [← weylS_rootB]
  exact (inferInstance : (commutator (Model F)).Normal).conj_mem _ rootB_mem_derived _

private theorem rootCD_mem_derived : rootC (1 : F) * rootD (1 : F) ∈ commutator (Model F) := by
  have he : ⁅rootF (1:F),rootE (1 : F)⁆ = rootA (1 : F) * rootB (1 : F) * (rootC (1 : F) * rootD (1 : F)) := by
    rw [commutatorElement_def,← rootF_neg,rootF_conjugate_rootE]
    simp [CharTwo.neg_eq,mul_assoc]
  have hm : ⁅rootF (1:F),rootE (1 : F)⁆ ∈ commutator (Model F) :=
    commutator_mem_commutator (mem_top _) (mem_top _)
  rw [he] at hm
  exact ((commutator (Model F)).mul_mem_cancel_left
    ((commutator (Model F)).mul_mem rootA_mem_derived rootB_mem_derived)).mp hm

/-- The actual embedding of the derived first parabolic into the octonion model. -/
def ambient : firstModel F →* Model F :=
  (commutator (Model F)).subtype.comp (firstModel F).subtype

omit [CharP F 2] in
theorem ambient_injective : Function.Injective (ambient (F := F)) := by
  intro x y h
  exact Subtype.ext (Subtype.ext h)

omit [CharP F 2] in
private theorem local_le_parabolic : local₁ (F := F) ≤ parabolic₁ :=
  sup_le_sup_right (show unipotent (K := F) ≤ borel from le_sup_left) _

private theorem radical_core [Finite F]
    (hc : (local₁ (F := F)).pCoreIn 2 = radical₁) :
    radical₁.comap (ambient (F := F)) ≤ pCore 2 (firstModel F) := by
  have hn : (radical₁.comap (ambient (F := F))).Normal := by
    constructor
    intro a ha b
    change ambient (b*a*b⁻¹) ∈ radical₁
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp
      (parabolic_normalizes_radical hc (show ambient b ∈ parabolic₁ from b.property))
      (ambient a)).mp ha
  exact le_sSup ⟨hn,radical₁_isTwoGroup.comap_of_injective ambient ambient_injective⟩

private theorem core_witness [Finite F]
    (hc : (local₁ (F := F)).pCoreIn 2 = radical₁)
    {q : Model F} (hr : q ∈ radical₁) (hd : q ∈ commutator (Model F)) :
    q ∈ (pCore 2 (firstModel F)).map ambient := by
  let x : firstModel F := ⟨⟨q,hd⟩,local_le_parabolic (radical₁_le_local₁ hr)⟩
  exact ⟨x,radical_core hc hr,rfl⟩

/-- The four derived-core witnesses force each square-trivial actor into the radical. -/
theorem mem_radical_of_core_squares [Finite F]
    (hc : (local₁ (F := F)).pCoreIn 2 = radical₁)
    (x : firstModel F)
    (hs : ∀ q ∈ pCore 2 (firstModel F), (⁅q,x⁆ : firstModel F)^2=1) :
    ambient x ∈ radical₁ := by
  have ht {q : Model F} (hq : q ∈ (pCore 2 (firstModel F)).map ambient) :
      ⁅q,ambient x⁆^2=1 := by
    obtain ⟨r,hr,rfl⟩ := hq
    simpa only [map_pow,map_commutatorElement,map_one] using congrArg ambient (hs r hr)
  apply mem_radical_of_normalForm (parabolic_normalForm hc x.property)
  · exact ht (core_witness hc ⟨![0,1,0,0,0,0],rfl,by simp [unipotentProduct]⟩ rootB_mem_derived)
  · exact ht (core_witness hc ⟨![0,0,0,0,1,0],rfl,by simp [unipotentProduct]⟩ rootE_mem_derived)
  · exact ht (core_witness hc ⟨![0,0,1,1,0,0],rfl,by simp [unipotentProduct]⟩ rootCD_mem_derived)
  · exact ht (core_witness hc ⟨![0,1,0,0,1,0],rfl,by simp [unipotentProduct]⟩
      ((commutator (Model F)).mul_mem rootB_mem_derived rootE_mem_derived))

end FirstActor

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Every two-perfect square-trivial actor in the derived first parabolic is trivial. -/
theorem first_actor_eq_bot_of_twoPerfect
    (hc : (local₁ (F := F)).pCoreIn 2 = radical₁)
    (X : Subgroup (firstModel F)) (hp : IsPPerfect 2 X)
    (hs : ∀ q ∈ pCore 2 (firstModel F), ∀ x ∈ X, (⁅q,x⁆ : firstModel F)^2=1) : X=⊥ := by
  have hX : X.map FirstActor.ambient ≤ radical₁ := by
    rintro _ ⟨x,hx,rfl⟩
    exact FirstActor.mem_radical_of_core_squares hc x (fun q hq => hs q hq x hx)
  have hpX : IsPGroup 2 X :=
    (radical₁_isTwoGroup.to_le hX).of_equiv
      (X.equivMapOfInjective FirstActor.ambient FirstActor.ambient_injective).symm
  have he := hp.hom_eq_one_of_isPGroup hpX (MonoidHom.id X)
  apply eq_bot_iff.mpr
  intro x hx
  exact congrArg Subtype.val (DFunLike.congr_fun he ⟨x,hx⟩)

/-- The subnormal actor exclusion required by the relative-block assembly. -/
theorem first_actor_eq_bot
    (hc : (local₁ (F := F)).pCoreIn 2 = radical₁)
    (X : Subgroup (firstModel F)) (_hsub : X.IsSubnormal) (hp : IsPPerfect 2 X)
    (hs : ∀ q ∈ pCore 2 (firstModel F), ∀ x ∈ X, (⁅q,x⁆ : firstModel F)^2=1) : X=⊥ :=
  first_actor_eq_bot_of_twoPerfect hc X hp hs

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2.RelativeBlocks

end

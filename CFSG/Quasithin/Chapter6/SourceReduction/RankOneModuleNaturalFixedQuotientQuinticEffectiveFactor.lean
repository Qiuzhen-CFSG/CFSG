module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticEffectiveProduct
public import Theory.GroupTheory.CoreCentralNormalizerAction.Socle
public import Theory.GroupTheory.PermutingSupCard

/-!
# The literal simple factor and quintic Sylow product

The original component action contains the inner automorphism group of its
core-central quotient. This normal subgroup is isomorphic to that quotient
and has trivial centralizer. The original faithful quintic image and actual
Sylow image give a subgroup of order a power of two times five inside the
same effective ambient group.

Source: Aschbacher--Smith 6.1.4 and A.3.15, printed pp.665 and 50--51.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- The actual effective action supplies the faithful order-five actor,
full Sylow subgroup and original simple factor needed by the model-specific
Sylow product exclusions. -/
theorem original_hermitian_quintic_effective_factor
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) :
    let A := coreCentralActorImage K M₁
    let N := (MulAut.innerSubgroup (coreCentralQuotient K)).subgroupOf A
    ∃ (E : Subgroup A) (S : Sylow 2 A) (a : ℕ),
      N.Normal ∧ Nonempty (N ≃* coreCentralQuotient K) ∧ Nat.card E = 5 ∧
      centralizer (N : Set A) = ⊥ ∧
      Nat.card (E ⊔ (S : Subgroup A) : Subgroup A) ∣ 2^a * 5 := by
  let A := coreCentralActorImage K M₁
  let C := coreCentralQuotient K
  let I := MulAut.innerSubgroup C
  let N := I.subgroupOf A
  let := hq
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective
    (QuotientGroup.mk'_surjective (center (K ⧸ pCore 2 K)))
  have hz : center C = ⊥ := Group.IsPerfect.center_quotient_center_eq_bot (K ⧸ pCore 2 K)
  have hIA : I ≤ A := by
    change MulAut.innerSubgroup (coreCentralQuotient K) ≤ coreCentralActorImage K M₁
    rw [←coreCentralActorImage_self K]
    exact map_mono (subgroupOf_mono _ hK.1)
  let eI : C ≃* I := MonoidHom.ofInjective
    (f := (MulAut.conj : C →* MulAut C)) (MulAut.conj_injective_of_center_eq_bot hz)
  let eN : N ≃* C := (subgroupOfEquivOfLe hIA).trans eI.symm
  have hcent : centralizer (N : Set A) = ⊥ := by
    apply bot_unique
    intro a ha
    apply Subtype.ext
    apply (centralizer_inner_eq_bot_of_perfect (H := C)).le
    intro i hi
    exact congrArg Subtype.val (ha ⟨i,hIA hi⟩ hi)
  obtain ⟨hS,D,_,_,hD,hDA,hperm⟩ :=
    original_hermitian_quintic_effective_product h hout hm hM₁ hCM₁ hK hnot hq
  obtain ⟨S,hS⟩ := hS
  let B := coreCentralActorImage K D
  let E := B.subgroupOf A
  have hE : Nat.card E = 5 :=
    (Nat.card_congr (subgroupOfEquivOfLe hDA).toEquiv).trans hD
  have hEmap : E.map A.subtype = B := map_subgroupOf_eq_of_le hDA
  have hp : (E : Set A) * (S : Set A) = (S : Set A) * (E : Set A) := by
    apply Set.image_injective.mpr A.subtype_injective
    change A.subtype '' ((E : Set A) * ((S : Subgroup A) : Set A)) =
      A.subtype '' (((S : Subgroup A) : Set A) * (E : Set A))
    rw [Set.image_mul,Set.image_mul,←coe_map,←coe_map,hEmap,hS]
    exact hperm
  obtain ⟨a,ha⟩ := S.isPGroup'.exists_card_eq
  have hd : Disjoint E (S : Subgroup A) := disjoint_of_coprime_natCard (by
    rw [hE,ha]
    exact (by decide : Nat.Coprime 5 2).pow_right a)
  refine ⟨E,S,a,inferInstance,⟨eN⟩,hE,hcent,?_⟩
  rw [card_sup_eq_mul_of_permutes_of_disjoint E S hp hd,hE,ha,mul_comm]

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

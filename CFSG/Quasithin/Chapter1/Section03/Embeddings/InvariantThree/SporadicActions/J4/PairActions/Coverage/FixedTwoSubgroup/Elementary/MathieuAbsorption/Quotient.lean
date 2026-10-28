module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.Reduction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# Transport of elementary J₄ pairs through the concrete Mathieu quotient

Restrict an ambient Sylow two-subgroup to the literal max1 subgroup and
map it through the certified M₂₄ quotient. The elementary-nine subgroup
maps injectively because the kernel is a two-group. Setwise permutability
passes to the quotient without any assertion that either factor is normal.
The kernel lies in the restricted Sylow subgroup, so the entire original
product is the full inverse image of its quotient product.

Sylow conjugacy in M₂₄, together with a lift of the conjugator into max1,
reduces the remaining max4 containment calculation to one specified Sylow.
Its inverse image is exactly `OddIndex.twoSubgroup`, whose fifteen matrix
generators are already certified. Every quotient product to be considered
has order 9,216. `FixedSylowPreimagePlacement` states the remaining concrete
containment obligation; this module does not assert it.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`), citing Aschbacher, *Overgroups of
Sylow subgroups in sporadic groups* (1986). The quotient and literal local
carriers are documented in `Janko4.Model.LocalStructure.Mathieu` and
`Janko4.Model.LocalStructure.SymmetricLinear.Model`.
-/

@[expose] public section

set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true

open Subgroup
open scoped Pointwise

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.MathieuAbsorption

/-- The literal ATLAS max1 subgroup in the existing binary matrix carrier. -/
abbrev Local : Subgroup Janko4.Model :=
  Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four

attribute [local irreducible] Janko4.modelGroup Janko4.Cardinality.max1Subgroup

/-- The actual max1 quotient homomorphism, followed by its M₂₄ isomorphism. -/
noncomputable def projection : Local →* Sporadic.Mathieu.M24 :=
  (Janko4.LocalStructure.localQuotientEquivM24
    Janko4.matrixA_mul_self Janko4.matrixB_pow_four).toMonoidHom.comp
      (QuotientGroup.mk' (Janko4.Cardinality.localKernel
        Janko4.matrixA_mul_self Janko4.matrixB_pow_four))

/-- Every Mathieu element has a lift in max1. -/
theorem projection_surjective : Function.Surjective projection :=
  (Janko4.LocalStructure.localQuotientEquivM24
    Janko4.matrixA_mul_self Janko4.matrixB_pow_four).surjective.comp
      (QuotientGroup.mk'_surjective _)

/-- The quotient kernel is exactly the certified binary normal closure. -/
theorem projection_ker : projection.ker = Janko4.Cardinality.localKernel
    Janko4.matrixA_mul_self Janko4.matrixB_pow_four := by
  ext x
  change Janko4.LocalStructure.localQuotientEquivM24 _ _
    (QuotientGroup.mk' _ x) = 1 ↔ _
  rw [map_eq_one_iff _ (Janko4.LocalStructure.localQuotientEquivM24 _ _).injective]
  exact QuotientGroup.eq_one_iff x

/-- The order-2048 kernel is a two-group. -/
theorem projection_ker_isPGroup : IsPGroup 2 projection.ker := by
  rw [projection_ker]
  exact IsPGroup.of_card (n := 11) (Janko4.Cardinality.localKernel_card
    Janko4.matrixA_mul_self Janko4.matrixB_pow_four)

/-- Restrict an ambient subgroup to max1 and take its Mathieu image. -/
noncomputable def image (K : Subgroup Janko4.Model) : Subgroup Sporadic.Mathieu.M24 :=
  (K.subgroupOf Local).map projection

/-- The full inverse image in max1, embedded in the original J₄ carrier. -/
noncomputable def preimage (H : Subgroup Sporadic.Mathieu.M24) : Subgroup Janko4.Model :=
  (H.comap projection).map Local.subtype

/-- Restriction and surjective transport preserve the supplied Sylow witness. -/
noncomputable def sylowImage (S : Sylow 2 Janko4.Model) (hS : S.toSubgroup ≤ Local) :
    Sylow 2 Sporadic.Mathieu.M24 :=
  (S.subtype hS).mapSurjective projection_surjective

@[simp] theorem sylowImage_coe (S : Sylow 2 Janko4.Model) (hS : S.toSubgroup ≤ Local) :
    (sylowImage S hS).toSubgroup = image S.toSubgroup := rfl

/-- A normal two-subgroup lies in the restricted Sylow subgroup. -/
theorem ker_le_sylow (S : Sylow 2 Janko4.Model) (hS : S.toSubgroup ≤ Local) :
    projection.ker ≤ S.toSubgroup.subgroupOf Local :=
  projection_ker_isPGroup.le_sylow_of_normal (S.subtype hS)

/-- The odd subgroup loses no elements through the binary quotient kernel. -/
noncomputable def complementEquiv [Finite Janko4.Model]
    {R : Subgroup Janko4.Model} (hR : R ≤ Local) (hE : IsElementaryAbelian 3 R) :
    R ≃* image R := by
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ := hE
  have hc : Nat.Coprime 3 (Nat.card projection.ker) := by
    rw [projection_ker, Janko4.Cardinality.localKernel_card]
    decide
  have hi : Function.Injective (projection.comp (R.subgroupOf Local).subtype) :=
    injective_comp_subtype_of_coprime_ker projection hc _
      ((IsElementaryAbelian.isPGroup 3 R).comap_subtype)
  exact (subgroupOfEquivOfLe hR).symm.trans
    (MulEquiv.ofBijective (projection.subgroupMap (R.subgroupOf Local))
      ⟨fun _ _ he => hi (congrArg Subtype.val he),
        projection.subgroupMap_surjective _⟩)

/-- The quotient image remains elementary abelian. -/
theorem image_elementary [Finite Janko4.Model]
    {R : Subgroup Janko4.Model} (hR : R ≤ Local) (hE : IsElementaryAbelian 3 R) :
    IsElementaryAbelian 3 (image R) := by
  let _ := hE
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ := IsElementaryAbelian.subgroupOf (p := 3) hR
  exact IsElementaryAbelian.map projection

/-- The coprime quotient preserves the odd subgroup’s exact order. -/
theorem image_card [Finite Janko4.Model]
    {R : Subgroup Janko4.Model} (hR : R ≤ Local) (hE : IsElementaryAbelian 3 R) :
    Nat.card (image R) = Nat.card R :=
  (Nat.card_congr (complementEquiv hR hE).toEquiv).symm

/-- Transport setwise permutability through restriction and the quotient. -/
theorem image_permutes {S : Sylow 2 Janko4.Model} {R : Subgroup Janko4.Model}
    (h : PairInput S R) (hS : S.toSubgroup ≤ Local) (hR : R ≤ Local) :
    (image R : Set Sporadic.Mathieu.M24) * (image S.toSubgroup : Set Sporadic.Mathieu.M24) =
      (image S.toSubgroup : Set Sporadic.Mathieu.M24) * (image R : Set Sporadic.Mathieu.M24) := by
  have hl : (R.subgroupOf Local : Set Local) * (S.toSubgroup.subgroupOf Local : Set Local) =
      (S.toSubgroup.subgroupOf Local : Set Local) * (R.subgroupOf Local : Set Local) := by
    apply Set.image_injective.mpr Local.subtype_injective
    simpa only [Set.image_mul, ← coe_map, map_subgroupOf_eq_of_le hR,
      map_subgroupOf_eq_of_le hS, Sylow.coe_coe] using h.permutes
  simpa only [image, coe_map, Set.image_mul] using congrArg (Set.image projection) hl

/-- The original join is the full inverse image, since it contains the kernel. -/
theorem preimage_join (S : Sylow 2 Janko4.Model) {R : Subgroup Janko4.Model}
    (hS : S.toSubgroup ≤ Local) (hR : R ≤ Local) :
    preimage (image R ⊔ image S.toSubgroup) = R ⊔ S.toSubgroup := by
  unfold preimage image
  rw [← Subgroup.map_sup, comap_map_eq_self ((ker_le_sylow S hS).trans le_sup_right),
    Subgroup.map_sup, map_subgroupOf_eq_of_le hR, map_subgroupOf_eq_of_le hS]

/-- The image of the already certified local Sylow subgroup. -/
noncomputable def standardSylow : Sylow 2 Sporadic.Mathieu.M24 :=
  Janko4.OuterReduction.OddIndex.localSylow.mapSurjective projection_surjective

/-- The fixed quotient Sylow lifts to the specified fifteen-generator subgroup. -/
theorem preimage_standardSylow :
    preimage standardSylow.toSubgroup = Janko4.OuterReduction.OddIndex.twoSubgroup := by
  change ((Janko4.OuterReduction.OddIndex.localSylow.toSubgroup.map projection).comap
    projection).map Local.subtype = _
  rw [comap_map_eq_self (projection_ker_isPGroup.le_sylow_of_normal
    Janko4.OuterReduction.OddIndex.localSylow)]
  rfl

/-- An actual local lift transports quotient conjugation to ambient conjugation. -/
theorem preimage_map_conj (H : Subgroup Sporadic.Mathieu.M24) (l : Local) :
    preimage (H.map (MulAut.conj (projection l)).toMonoidHom) =
      (preimage H).map (MulAut.conj (l : Janko4.Model)).toMonoidHom := by
  apply le_antisymm
  · rintro _ ⟨x, ⟨y, hy, he⟩, rfl⟩
    change projection l * y * (projection l)⁻¹ = projection x at he
    refine ⟨((l⁻¹ * x * l : Local) : Janko4.Model), ⟨l⁻¹ * x * l, ?_, rfl⟩, ?_⟩
    · change projection (l⁻¹ * x * l) ∈ H
      have hx : projection (l⁻¹ * x * l) = y := by
        rw [map_mul, map_mul, map_inv, ← he]
        group
      rwa [hx]
    · change (l : Janko4.Model) * ((l⁻¹ * x * l : Local) : Janko4.Model) *
        (l : Janko4.Model)⁻¹ = (x : Janko4.Model)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
  · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨l * y * l⁻¹, ?_, rfl⟩
    exact ⟨projection y, hy, by simp⟩

/-- The certified M₂₄ order gives Sylow two-order 1024. -/
theorem sylow_card (T : Sylow 2 Sporadic.Mathieu.M24) : Nat.card T = 1024 := by
  have hfac : Nat.factorization 244823040 2 = 10 := by
    have hzero : padicValNat 2 239085 = 0 :=
      padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr (by norm_num)))
    rw [Nat.factorization_def 244823040 Nat.prime_two,
      show (244823040 : ℕ) = 2 ^ 10 * 239085 by norm_num,
      padicValNat_base_pow_mul (by norm_num) (by norm_num) 10, hzero]
  rw [T.card_eq_multiplicity, Sporadic.Mathieu.m24_order, hfac]
  norm_num

/-- Every permuting elementary-nine/Sylow pair has product order 9,216. -/
theorem quotient_product_card (T : Sylow 2 Sporadic.Mathieu.M24)
    (U : Subgroup Sporadic.Mathieu.M24) (hE : IsElementaryAbelian 3 U)
    (hU : Nat.card U = 3 ^ 2)
    (hp : (U : Set Sporadic.Mathieu.M24) * (T : Set Sporadic.Mathieu.M24) =
      (T : Set Sporadic.Mathieu.M24) * (U : Set Sporadic.Mathieu.M24)) :
    Nat.card (U ⊔ T.toSubgroup : Subgroup Sporadic.Mathieu.M24) = 9216 := by
  let _ := hE
  have hd : Disjoint U T.toSubgroup :=
    (IsElementaryAbelian.isPGroup 3 U).disjoint_of_coprime T.isPGroup' (by decide)
  have hc := card_set_mul_mul_card_inf U T.toSubgroup
  rw [hd.eq_bot, card_bot, mul_one, ← coe_sup_of_set_mul_comm U T.toSubgroup hp,
    hU, sylow_card T] at hc
  exact hc

open Janko4.LocalStructure.SymmetricLinear

attribute [local irreducible] max4Subgroup

/-- Remaining incidence calculation for one fixed Sylow in the concrete M₂₄
quotient. The conclusion concerns the full preimage and the literal max4
carrier. No quotient tag or assumed overlap replaces this containment. -/
def FixedSylowPreimagePlacement : Prop :=
  ∀ [Finite Janko4.Model] [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model]
    (_hthin : IsStronglyQuasithin Janko4.Model)
    (_hrank : primeRank 3 Janko4.Model = 2)
    (U : Subgroup Sporadic.Mathieu.M24), IsElementaryAbelian 3 U → Nat.card U = 3 ^ 2 →
      (U : Set Sporadic.Mathieu.M24) * (standardSylow : Set Sporadic.Mathieu.M24) =
        (standardSylow : Set Sporadic.Mathieu.M24) * (U : Set Sporadic.Mathieu.M24) →
      ∃ g : Janko4.Model,
        preimage (U ⊔ standardSylow.toSubgroup) ≤
          max4Subgroup.map (MulAut.conj g).toMonoidHom

/-- Lift a Sylow conjugator to max1 and compose actual ambient conjugations. -/
theorem preimagePlacement_of_fixed (hfixed : FixedSylowPreimagePlacement)
    [Finite Janko4.Model] [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model]
    (hthin : IsStronglyQuasithin Janko4.Model) (hrank : primeRank 3 Janko4.Model = 2)
    (T : Sylow 2 Sporadic.Mathieu.M24) (U : Subgroup Sporadic.Mathieu.M24)
    (hE : IsElementaryAbelian 3 U) (hU : Nat.card U = 3 ^ 2)
    (hp : (U : Set Sporadic.Mathieu.M24) * (T : Set Sporadic.Mathieu.M24) =
      (T : Set Sporadic.Mathieu.M24) * (U : Set Sporadic.Mathieu.M24)) :
    ∃ g : Janko4.Model, preimage (U ⊔ T.toSubgroup) ≤
      max4Subgroup.map (MulAut.conj g).toMonoidHom := by
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ := hE
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq Sporadic.Mathieu.M24 T standardSylow
  have hTa : T.toSubgroup.map (MulAut.conj a).toMonoidHom = standardSylow.toSubgroup :=
    congrArg Sylow.toSubgroup ha
  have hTset : (MulAut.conj a).toMonoidHom '' (T : Set Sporadic.Mathieu.M24) =
      (standardSylow : Set Sporadic.Mathieu.M24) :=
    congrArg (fun K : Subgroup Sporadic.Mathieu.M24 => (K : Set Sporadic.Mathieu.M24)) hTa
  let U' := U.map (MulAut.conj a).toMonoidHom
  have hE' : IsElementaryAbelian 3 U' := IsElementaryAbelian.map _
  have hU' : Nat.card U' = 3 ^ 2 :=
    (card_map_of_injective (MulAut.conj a).injective).trans hU
  have hp' : (U' : Set Sporadic.Mathieu.M24) * (standardSylow : Set Sporadic.Mathieu.M24) =
      (standardSylow : Set Sporadic.Mathieu.M24) * (U' : Set Sporadic.Mathieu.M24) := by
    have hh := congrArg (Set.image (MulAut.conj a).toMonoidHom) hp
    simpa only [Set.image_mul, hTset, U', coe_map] using hh
  obtain ⟨g, hg⟩ := hfixed hthin hrank U' hE' hU' hp'
  have hjoin : U' ⊔ standardSylow.toSubgroup =
      (U ⊔ T.toSubgroup).map (MulAut.conj a).toMonoidHom := by
    rw [Subgroup.map_sup, hTa]
  obtain ⟨l, hl⟩ := projection_surjective a
  rw [hjoin, ← hl, preimage_map_conj] at hg
  refine ⟨(l : Janko4.Model)⁻¹ * g, ?_⟩
  intro x hx
  obtain ⟨y, hy, he⟩ := hg (mem_map_of_mem (MulAut.conj (l : Janko4.Model)).toMonoidHom hx)
  refine ⟨y, hy, ?_⟩
  change g * y * g⁻¹ = (l : Janko4.Model) * x * (l : Janko4.Model)⁻¹ at he
  change ((l : Janko4.Model)⁻¹ * g) * y * ((l : Janko4.Model)⁻¹ * g)⁻¹ = x
  calc
    _ = (l : Janko4.Model)⁻¹ * (g * y * g⁻¹) * (l : Janko4.Model) := by group
    _ = x := by rw [he]; group

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.MathieuAbsorption

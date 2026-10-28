module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.MathieuAbsorption.Quotient
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.MathieuAbsorption.FixedSylowPlacement.PairGeneration
public import Theory.GroupTheory.SylowOvergroupIncidence
public import Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.Automorphisms
public import Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.Order
public import Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.Reduction

/-!
# An obstruction to universal fixed-Sylow max4 placement

Two certified elementary-nine/Sylow products in the concrete Mathieu quotient
together generate the full quotient. Since the Mathieu Sylow subgroup is self-normalizing,
no single proper subgroup conjugacy class can contain both products.
Their inverse images therefore generate the literal max1 subgroup. If the fixed two-subgroup's ambient normalizer
lies in max1, the proved Mathieu normalizer calculation makes it
self-normalizing and Sylow in J₄. Sylow conjugacy then makes any two max4
conjugates containing it equal. Universal placement would consequently put
all of max1 into one max4 conjugate and force eleven to divide its order.

The proposed max4 two-core quotient has order 20,160, so its full extension
by the two-core has order prime to eleven. Thus the universal placement
contract is incompatible with these two additional model contracts. In fact,
one of the two specified quotient pairs then has no such placement, without
any simplicity, perfectness, quasithinness or three-rank assumption. Neither
model contract is discharged here, and this is not an unconditional negation
of placement. In particular, no `fixedSylowPreimagePlacement` is asserted.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`). The source retains a final irreducibility
sieve; a universal absorption assertion is an additional claim.
-/

public section

open Subgroup
open Janko4.OuterReduction.OddIndex
open Janko4.LocalStructure.SymmetricLinear

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.MathieuAbsorption

attribute [local irreducible] Janko4.modelGroup Janko4.Cardinality.max1Subgroup max4Subgroup

/-- No single proper conjugacy type can cover the two fixed-Sylow products. -/
theorem quotientNine_not_le_conjugates (M : Subgroup Sporadic.Mathieu.M24) (hM : M ≠ ⊤) :
    ∃ k : Fin 2, ¬ ∃ g : Sporadic.Mathieu.M24,
      FixedSylowObstruction.quotientNine k ⊔ standardSylow.toSubgroup ≤
        M.map (MulAut.conj g).toMonoidHom := by
  by_contra! hp
  obtain ⟨g, hg⟩ := hp 0
  obtain ⟨h, hh⟩ := hp 1
  let K := M.map (MulAut.conj g).toMonoidHom
  have hTK : standardSylow.toSubgroup ≤ K := le_sup_right.trans hg
  have hn : normalizer (standardSylow : Set Sporadic.Mathieu.M24) ≤
      standardSylow.toSubgroup :=
    Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer.sylow_normalizer_le
      Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer.candidate_card
      (Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer.candidate_automorphisms_isPGroup
        Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer.candidate_card) standardSylow
  have hc : K.map (MulAut.conj (h * g⁻¹)).toMonoidHom =
      M.map (MulAut.conj h).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext x : 1
    change (h * g⁻¹) * (g * x * g⁻¹) * (h * g⁻¹)⁻¹ = h * x * h⁻¹
    group
  have he : M.map (MulAut.conj h).toMonoidHom = K := by
    rw [← hc]
    exact standardSylow.conjugate_overgroup_eq_of_normalizer_le K hTK
      (hn.trans (hTK.trans K.le_normalizer)) _
      (hc.symm ▸ (le_sup_right.trans hh))
  have ht : K = ⊤ := by
    apply top_unique
    rw [← FixedSylowObstruction.quotient_products_generate]
    exact sup_le hg (hh.trans he.le)
  apply hM
  apply Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  rw [Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective]
  exact ht


private theorem preimage_injective : Function.Injective preimage := by
  intro H K h
  exact Subgroup.comap_injective projection_surjective
    (Subgroup.map_injective Local.subtype_injective h)

/-- Ambient normalizer containment, if established, makes the specified
two-subgroup self-normalizing. The quotient normalizer theorem is proved. -/
theorem fixedTwo_self_normalizing_of_normalizer_le_local
    (hN : normalizer (twoSubgroup : Set Janko4.Model) ≤ Local) :
    normalizer (twoSubgroup : Set Janko4.Model) ≤ twoSubgroup := by
  intro g hg
  let l : Local := ⟨g, hN hg⟩
  have he : preimage (standardSylow.toSubgroup.map
      (MulAut.conj (projection l)).toMonoidHom) = preimage standardSylow.toSubgroup := by
    rw [preimage_map_conj, preimage_standardSylow]
    exact mem_normalizer_iff_map_conj_eq.mp hg
  have hn : projection l ∈ normalizer (standardSylow.toSubgroup : Set Sporadic.Mathieu.M24) :=
    mem_normalizer_iff_map_conj_eq.mpr (preimage_injective he)
  have hm := Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer.sylow_normalizer_le
    Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer.candidate_card
    (Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer.candidate_automorphisms_isPGroup
      Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer.candidate_card) standardSylow hn
  rw [← preimage_standardSylow]
  exact ⟨l, hm, rfl⟩

/-- Self-normalization promotes the already certified two-group to an
ambient Sylow subgroup, using the normalizer-index congruence. -/
noncomputable def fixedTwoSylow_of_self_normalizing
    (hN : normalizer (twoSubgroup : Set Janko4.Model) ≤ twoSubgroup) : Sylow 2 Janko4.Model :=
  twoSubgroup_isPGroup.toSylow (by
    have he := le_antisymm hN twoSubgroup.le_normalizer
    have hc := Sylow.card_quotient_normalizer_modEq_card_quotient twoSubgroup_card
    intro hd
    have hn := (hc.dvd_iff dvd_rfl).mpr hd
    change 2 ∣ twoSubgroup.relIndex (normalizer (twoSubgroup : Set Janko4.Model)) at hn
    rw [he, relIndex_self] at hn
    norm_num at hn)

private theorem local_le_max4_conjugate_of_two_placements
    [Finite Janko4.Model]
    (hN : normalizer (twoSubgroup : Set Janko4.Model) ≤ Local)
    (hplace : ∀ k : Fin 2, ∃ g : Janko4.Model,
      preimage (FixedSylowObstruction.quotientNine k ⊔ standardSylow.toSubgroup) ≤
        max4Subgroup.map (MulAut.conj g).toMonoidHom) :
    ∃ g : Janko4.Model, Local ≤ max4Subgroup.map (MulAut.conj g).toMonoidHom := by
  have hn := fixedTwo_self_normalizing_of_normalizer_le_local hN
  let S := fixedTwoSylow_of_self_normalizing hn
  have hS : S.toSubgroup = twoSubgroup := rfl
  have hpair (k : Fin 2) : S.toSubgroup ≤
      preimage (FixedSylowObstruction.quotientNine k ⊔ standardSylow.toSubgroup) := by
    rw [hS, ← preimage_standardSylow]
    exact Subgroup.map_mono (Subgroup.comap_mono le_sup_right)
  obtain ⟨g, hg⟩ := hplace 0
  obtain ⟨h, hh⟩ := hplace 1
  let M := max4Subgroup.map (MulAut.conj g).toMonoidHom
  have hSM : S.toSubgroup ≤ M := (hpair 0).trans hg
  have hc : M.map (MulAut.conj (h * g⁻¹)).toMonoidHom =
      max4Subgroup.map (MulAut.conj h).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext x
    change (h * g⁻¹) * (g * x * g⁻¹) * (h * g⁻¹)⁻¹ = h * x * h⁻¹
    group
  have hNM : normalizer (S : Set Janko4.Model) ≤ normalizer (M : Set Janko4.Model) :=
    hn.trans (hSM.trans M.le_normalizer)
  have he : max4Subgroup.map (MulAut.conj h).toMonoidHom = M := by
    rw [← hc]
    exact S.conjugate_overgroup_eq_of_normalizer_le M hSM hNM _
      (hc.symm ▸ (hpair 1).trans hh)
  refine ⟨g, ?_⟩
  rw [← FixedSylowObstruction.preimage_products_generate]
  exact sup_le hg (hh.trans he.le)

/-- Universal placement and ambient normalizer containment would absorb the
whole max1 subgroup, not merely the two elementary pairs. -/
theorem local_le_max4_conjugate_of_fixedSylowPreimagePlacement
    [Finite Janko4.Model] [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model]
    (hthin : IsStronglyQuasithin Janko4.Model) (hrank : primeRank 3 Janko4.Model = 2)
    (hfixed : FixedSylowPreimagePlacement)
    (hN : normalizer (twoSubgroup : Set Janko4.Model) ≤ Local) :
    ∃ g : Janko4.Model, Local ≤ max4Subgroup.map (MulAut.conj g).toMonoidHom := by
  apply local_le_max4_conjugate_of_two_placements hN
  intro k
  exact hfixed hthin hrank _
    (FixedSylowObstruction.quotientNine_properties k).1
    (FixedSylowObstruction.quotientNine_properties k).2
    (FixedSylowObstruction.quotientNine_permutes k)

/-- The elementary-pair placement contract would force an eleven-element
factor in the literal max4 subgroup if ambient normalizer control holds. -/
theorem eleven_dvd_max4_of_fixedSylowPreimagePlacement
    [Finite Janko4.Model] [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model]
    (hthin : IsStronglyQuasithin Janko4.Model) (hrank : primeRank 3 Janko4.Model = 2)
    (hfixed : FixedSylowPreimagePlacement)
    (hN : normalizer (twoSubgroup : Set Janko4.Model) ≤ Local) :
    11 ∣ Nat.card max4Subgroup := by
  obtain ⟨g, hg⟩ := local_le_max4_conjugate_of_fixedSylowPreimagePlacement hthin hrank hfixed hN
  have hc := card_dvd_of_le hg
  rw [card_map_of_injective (MulAut.conj g).injective] at hc
  have hl : 11 ∣ Nat.card Local := by
    rw [Janko4.Cardinality.max1Subgroup_card]
    norm_num
  exact hl.trans hc

/-- The specified two-core quotient makes max4 eleven-free, independently
of the size of its binary kernel. -/
theorem max4_eleven_free_of_quotient [Finite Janko4.Model]
    (hQ : Nonempty ((max4Subgroup ⧸ pCore 2 max4Subgroup) ≃* QuotientModel)) :
    ¬ 11 ∣ Nat.card max4Subgroup := by
  obtain ⟨e⟩ := hQ
  have hcard : Nat.card QuotientModel = 20160 := by
    rw [Nat.card_prod, Nat.card_perm, Nat.card_fin, Atlas.Comparisons.Exceptional.sl3Two_card]
    norm_num
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := max4Subgroup)).exists_card_eq
  have hc := card_eq_card_quotient_mul_card_subgroup (pCore 2 max4Subgroup)
  rw [Nat.card_congr e.toEquiv, hcard, hn] at hc
  rw [hc]
  apply (by decide : Nat.Prime 11).not_dvd_mul (by decide)
  intro h
  have hd := (by decide : Nat.Prime 11).dvd_of_dvd_pow h
  norm_num at hd

/-- Under the two concrete model contracts, one of the two specified
elementary-nine pairs has no max4 placement. All of its quotient-pair
hypotheses are certified independently in `PairGeneration`. -/
theorem quotientNine_not_placeable_of_normalizer_and_quotient
    [Finite Janko4.Model]
    (hN : normalizer (twoSubgroup : Set Janko4.Model) ≤ Local)
    (hQ : Nonempty ((max4Subgroup ⧸ pCore 2 max4Subgroup) ≃* QuotientModel)) :
    ∃ k : Fin 2, ¬ ∃ g : Janko4.Model,
      preimage (FixedSylowObstruction.quotientNine k ⊔ standardSylow.toSubgroup) ≤
        max4Subgroup.map (MulAut.conj g).toMonoidHom := by
  by_contra! hplace
  obtain ⟨g, hg⟩ := local_le_max4_conjugate_of_two_placements hN hplace
  have hc := card_dvd_of_le hg
  rw [card_map_of_injective (MulAut.conj g).injective] at hc
  have hl : 11 ∣ Nat.card Local := by
    rw [Janko4.Cardinality.max1Subgroup_card]
    norm_num
  exact max4_eleven_free_of_quotient hQ (hl.trans hc)

/-- These two outstanding concrete model contracts are incompatible with
the proposed universal fixed-Sylow placement. This is a conditional
obstruction; neither model premise is asserted by this theorem. -/
theorem not_fixedSylowPreimagePlacement_of_normalizer_and_quotient
    [Finite Janko4.Model] [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model]
    (hthin : IsStronglyQuasithin Janko4.Model) (hrank : primeRank 3 Janko4.Model = 2)
    (hN : normalizer (twoSubgroup : Set Janko4.Model) ≤ Local)
    (hQ : Nonempty ((max4Subgroup ⧸ pCore 2 max4Subgroup) ≃* QuotientModel)) :
    ¬ FixedSylowPreimagePlacement := by
  intro hfixed
  exact max4_eleven_free_of_quotient hQ
    (eleven_dvd_max4_of_fixedSylowPreimagePlacement hthin hrank hfixed hN)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.MathieuAbsorption

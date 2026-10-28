module
public import Theory.Character.ModularBlock.SubgroupBrauerHom
public import Mathlib.GroupTheory.Sylow

/-!
# Augmentation and maximal Sylow support

A central group-algebra element with nonzero augmentation in characteristic
two has nonzero coefficient restriction at every two-subgroup. Its Sylow
two-subgroups are therefore maximal coefficient supports, and conversely
every maximal coefficient support is Sylow.

Augmentation is preserved by the subgroup Brauer map, so a zero restriction
would contradict nonzero augmentation. Sylow containment and cardinality
then characterize maximal support. The central-factor lemma transfers
maximal support using multiplicativity: a nonzero restriction of a factor
forces the parent restriction to be nonzero. For a central idempotent,
maximal support consequently gives a nonzero central idempotent restriction.
All conclusions retain the finite group and characteristic-two hypotheses.

Ported from revision c3503435 of public/lean-eval/glauberman_zStar,
Submission/ZStar/SubgroupBrauerMap.lean. These generic support results feed
the specialization to the reduced principal block selector.
-/

public section
noncomputable section
open scoped BigOperators
namespace ModularBlock.SubgroupBrauerMap
universe u v
attribute [local instance] Fintype.ofFinite

theorem hasTwoCoefficientSupport_of_augmentation_ne_zero
    {R : Type u} [CommRing R] [CharP R 2]
    {G : Type v} [Group G] [Finite G]
    (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (e : MonoidAlgebra R G)
    (he : e ∈ Set.center (MonoidAlgebra R G))
    (haug : groupAlgebraAugmentation R G e ≠ 0) :
    DefectSupport.HasTwoCoefficientSupport e Q := by
  rw [DefectSupport.hasTwoCoefficientSupport_iff_restriction_ne_zero]
  refine ⟨hQ, ?_⟩
  intro hzero
  have hrestrictAug := congrArg
    (groupAlgebraAugmentation R
      (Subgroup.centralizer (Q : Set G))) hzero
  rw [map_zero,
    augmentation_subgroupCentralizerRestriction Q hQ e he] at hrestrictAug
  exact haug hrestrictAug

/-- Every Sylow `2`-subgroup is a maximal Brauer-support subgroup of a
central element with nonzero augmentation.  In particular this recovers the
standard fact that defect groups of the principal block are Sylow. -/
theorem sylow_isMaximalTwoCoefficientSupport_of_augmentation_ne_zero
    [Fact (Nat.Prime 2)]
    {R : Type u} [CommRing R] [CharP R 2]
    {G : Type v} [Group G] [Finite G]
    (P : Sylow 2 G)
    (e : MonoidAlgebra R G)
    (he : e ∈ Set.center (MonoidAlgebra R G))
    (haug : groupAlgebraAugmentation R G e ≠ 0) :
    DefectSupport.IsMaximalTwoCoefficientSupport e (P : Subgroup G) := by
  refine ⟨hasTwoCoefficientSupport_of_augmentation_ne_zero
      (P : Subgroup G) P.isPGroup' e he haug, ?_⟩
  intro Q hQ
  obtain ⟨P', hQP'⟩ := hQ.1.exists_le_sylow
  calc
    Nat.card Q ≤ Nat.card (P' : Subgroup G) :=
      Subgroup.card_le_of_le hQP'
    _ = 2 ^ (Nat.card G).factorization 2 :=
      Sylow.card_eq_multiplicity P'
    _ = Nat.card (P : Subgroup G) :=
      (Sylow.card_eq_multiplicity P).symm

/-- Conversely, every maximal support subgroup of an augmentation-nonzero
central element is a Sylow `2`-subgroup. -/
theorem exists_sylow_eq_of_isMaximalTwoCoefficientSupport_of_augmentation_ne_zero
    [Fact (Nat.Prime 2)]
    {R : Type u} [CommRing R] [CharP R 2]
    {G : Type v} [Group G] [Finite G]
    (e : MonoidAlgebra R G)
    (he : e ∈ Set.center (MonoidAlgebra R G))
    (haug : groupAlgebraAugmentation R G e ≠ 0)
    (Q : Subgroup G)
    (hQ : DefectSupport.IsMaximalTwoCoefficientSupport e Q) :
    ∃ P : Sylow 2 G, (P : Subgroup G) = Q := by
  let P : Sylow 2 G := Classical.choice (inferInstance : Nonempty (Sylow 2 G))
  have hPSupport : DefectSupport.HasTwoCoefficientSupport e (P : Subgroup G) :=
    hasTwoCoefficientSupport_of_augmentation_ne_zero
      (P : Subgroup G) P.isPGroup' e he haug
  have hlower : Nat.card (P : Subgroup G) ≤ Nat.card Q :=
    hQ.2 (P : Subgroup G) hPSupport
  obtain ⟨P', hQP'⟩ := hQ.1.1.exists_le_sylow
  have hupper : Nat.card Q ≤ Nat.card (P : Subgroup G) := by
    calc
      Nat.card Q ≤ Nat.card (P' : Subgroup G) :=
        Subgroup.card_le_of_le hQP'
      _ = 2 ^ (Nat.card G).factorization 2 :=
        Sylow.card_eq_multiplicity P'
      _ = Nat.card (P : Subgroup G) :=
        (Sylow.card_eq_multiplicity P).symm
  have hcardQ : Nat.card Q = 2 ^ (Nat.card G).factorization 2 := by
    calc
      Nat.card Q = Nat.card (P : Subgroup G) :=
        Nat.le_antisymm hupper hlower
      _ = 2 ^ (Nat.card G).factorization 2 :=
        Sylow.card_eq_multiplicity P
  exact ⟨Sylow.ofCard Q hcardQ, rfl⟩

/-- A central factor which is still visible at a maximal support subgroup has
the same maximal support.  Any larger support of the factor would, by
multiplicativity of the subgroup Brauer map, also be a support of the parent
central element. -/
theorem isMaximalTwoCoefficientSupport_of_central_factor
    [Fact (Nat.Prime 2)]
    {R : Type u} [CommRing R] [CharP R 2]
    {G : Type v} [Group G] [Finite G]
    (f b : MonoidAlgebra R G)
    (hfcenter : f ∈ Set.center (MonoidAlgebra R G))
    (hbcenter : b ∈ Set.center (MonoidAlgebra R G))
    (hfb : f * b = f)
    (Q : Subgroup G)
    (hbMax : DefectSupport.IsMaximalTwoCoefficientSupport b Q)
    (hfQ : DefectSupport.HasTwoCoefficientSupport f Q) :
    DefectSupport.IsMaximalTwoCoefficientSupport f Q := by
  refine ⟨hfQ, ?_⟩
  intro Rsub hfR
  have hfRestrNe :
      DefectSupport.subgroupCentralizerRestriction R Rsub f ≠ 0 :=
    (DefectSupport.hasTwoCoefficientSupport_iff_restriction_ne_zero f Rsub).mp
      hfR |>.2
  have hbRestrNe :
      DefectSupport.subgroupCentralizerRestriction R Rsub b ≠ 0 := by
    intro hzero
    apply hfRestrNe
    have hmul := subgroupCentralizerRestriction_mul_of_mem_center
      Rsub hfR.1 f b hfcenter hbcenter
    rw [hfb, hzero, mul_zero] at hmul
    exact hmul
  apply hbMax.2 Rsub
  rw [DefectSupport.hasTwoCoefficientSupport_iff_restriction_ne_zero]
  exact ⟨hfR.1, hbRestrNe⟩

/-- At a maximal support subgroup, the Brauer image of a central idempotent
is a nonzero central idempotent.  This is the precise algebraic bridge from
coefficient support to a block-defect witness. -/
theorem maximalSupport_restriction_isNonzeroCentralIdempotent
    [Fact (Nat.Prime 2)]
    {R : Type u} [CommRing R] [CharP R 2]
    {G : Type v} [Group G] [Finite G]
    (e : MonoidAlgebra R G)
    (hecenter : e ∈ Set.center (MonoidAlgebra R G))
    (heidem : IsIdempotentElem e)
    (Q : Subgroup G)
    (hQ : DefectSupport.IsMaximalTwoCoefficientSupport e Q) :
    (DefectSupport.subgroupCentralizerRestriction R Q e ∈
        Set.center
          (MonoidAlgebra R (Subgroup.centralizer (Q : Set G)))) ∧
      IsIdempotentElem (DefectSupport.subgroupCentralizerRestriction R Q e) ∧
      DefectSupport.subgroupCentralizerRestriction R Q e ≠ 0 := by
  refine ⟨subgroupCentralizerRestriction_mem_center Q e hecenter, ?_, ?_⟩
  · exact subgroupCentralizerRestriction_isIdempotent_of_mem_center
      Q hQ.1.1 e hecenter heidem
  · exact
      (DefectSupport.hasTwoCoefficientSupport_iff_restriction_ne_zero e Q).mp
        hQ.1 |>.2

end ModularBlock.SubgroupBrauerMap


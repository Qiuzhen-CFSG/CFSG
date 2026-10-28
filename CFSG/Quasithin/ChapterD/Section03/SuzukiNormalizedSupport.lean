module
public import CFSG.Quasithin.ChapterD.Section03.SuzukiSeedCost
public import CFSG.Quasithin.ChapterD.Section03.EvenConstituent
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.SourceTransport
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionSuzuki
public import Theory.Representation.SL2.NaturalSectionBudget
public import Theory.Representation.CliffordSubquotient
public import Theory.Representation.BinaryOffender.SemisimpleIrrPlus
public import Theory.SpecificGroups.PSL2.FieldDegreeOuterOrder

/-!
# Normalized odd-degree binary support for a Suzuki kernel actor

An elementary actor on odd-degree binary SL2 induces inner automorphisms,
so it preserves a homogeneous Irr+ seed. Clifford semisimplicity makes the
seed irreducible, and the inherited cubic bound recognizes it as natural:
the Hermitian alternative requires even field degree. The natural linear
normalizer has no strong offender, contradicting the Suzuki seed-cost bound.

Restriction to the full normalizer of the actual component handles relative
normality and retains all ambient outer actors. The Chapter 10 application
supplies semisimplicity from its original irreducible moved representation.
Source: Aschbacher--Smith A.1.42, D.3.9 and K.3.1,
printed pp.32,200--201,453--454; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped MatrixGroups MonoidAlgebra
namespace CFSG.Quasithin.ChapterD
variable {G V F : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] [Field F] [Finite F] [CharP F 2]
local instance suzukiNormalizedBinaryAlgebra : Algebra (ZMod 2) F := ZMod.algebra _ 2

/-- A natural constituent cannot be an invariant seed for an actor that
centralizes a fixed-free Suzuki component. -/
theorem suzuki_no_invariant_natural_seed
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G)
    (hfix : fixedSpace ρ K = ⊥)
    (m : ℕ) (hm : 0 < m) (e : K ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (J A : Subgroup G) [J.Normal] (eJ : J ≃* SL(2,F)) (hF : 2 < Nat.card F)
    (hA : A ∈ QhatStar ρ) (hKJ : K ≤ centralizer (J : Set G))
    (hKA : K ≤ centralizer (A : Set G))
    (R : Submodule (ZMod 2) V) (hJR : J ≤ subspaceStabilizer ρ R)
    (hAR : A ≤ subspaceStabilizer ρ R)
    (hi : IsIrreducible (invariantSubspace ρ J R hJR).toRepresentation)
    (hmove : ¬ R ≤ fixedSpace ρ A)
    (hnat : SL2.BinarySmall.IsNatural
      ((invariantSubspace ρ J R hJR).toRepresentation.comp eJ.symm.toMonoidHom)) : False := by
  let X := J ⊔ A
  have hXR : X ≤ subspaceStabilizer ρ R := sup_le hJR hAR
  let σ := (invariantSubspace ρ X R hXR).toRepresentation
  let J' := J.subgroupOf X
  let e' : J' ≃* J := subgroupOfEquivOfLe (show J ≤ X from le_sup_left)
  have hir : IsIrreducible (σ.comp J'.subtype) :=
    (irreducible_comp_surjective_iff e'.toMonoidHom e'.surjective _).mpr hi
  have hiX : σ.IsIrreducible := irreducible_of_subgroup_restriction σ J' hir
  have hc : K ≤ centralizer (X : Set G) :=
    le_centralizer_iff.mp (sup_le (le_centralizer_iff.mp hKJ) (le_centralizer_iff.mp hKA))
  have hs := suzuki_commuting_seed_strong ρ K hfix m hm e X A hA hc le_sup_right
    R hXR hiX hmove
  let f := subgroupActionHom ρ R J hJR
  let N := restrictedSubgroup ρ R J
  have he : f.range = N := subgroupActionHom_range ρ R J hJR
  let : N.Normal := Normal.map inferInstance (subspaceActionHom ρ R)
    (stabilizerRepresentation ρ R).asGroupHom.rangeRestrict_surjective
  let : f.range.Normal := he.symm ▸ (inferInstance : N.Normal)
  obtain ⟨b⟩ := hnat
  let b' : Representation.Equiv ((subspaceImageRepresentation ρ R).comp f)
      ((SL2NaturalOffenders.NoStrong.natural (F := F)).comp eJ.toMonoidHom) := {
    __ := b.toLinearEquiv
    isIntertwining' j := by
      apply LinearMap.ext
      intro v
      have hh := LinearMap.congr_fun (b.isIntertwining' (eJ j)) v
      change b ((invariantSubspace ρ J R hJR).toRepresentation (eJ.symm (eJ j)) v) =
        SL2.BinarySmall.natural (eJ j) (b v) at hh
      rw [eJ.symm_apply_apply,SL2.BinarySmall.natural_apply] at hh
      change b ((subspaceImageRepresentation ρ R) (f j) v) = (eJ j).val.mulVec (b v)
      have heq : (subspaceImageRepresentation ρ R) (f j) v =
          (invariantSubspace ρ J R hJR).toRepresentation j v := Subtype.ext rfl
      rw [heq]
      exact hh }
  have hn := not_strong_of_marked_normal_range (subspaceImageRepresentation ρ R)
    (subspaceImageRepresentation_injective ρ R) f
    (SL2NaturalOffenders.NoStrong.natural (F := F)) eJ.toMonoidHom eJ.surjective b'
    (SL2NaturalOffenders.normalizer_not_strong (F := F) hF)
  exact hn ⟨restrictedSubgroup ρ R A,hA.1.2.1.restrictedSubgroup ρ R hAR hmove,hs⟩

/-- In odd binary degree, every normalized simple support has an invariant
natural seed, which the commuting Suzuki multiplicity bound excludes. -/
theorem suzuki_no_normal_odd_binary_support
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (K : Subgroup G) (hfix : fixedSpace ρ K = ⊥)
    (m : ℕ) (hm : 0 < m) (e : K ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (J A : Subgroup G) [J.Normal] [IsSimpleGroup J] [IsQuasisimple J]
    [IsSemisimpleModule (ZMod 2)[J] (Representation.asModule (ρ.comp J.subtype))]
    (hJ : IsSQTK KnownSimple.IsKnownSimple J)
    (hA : A ∈ QhatStar ρ) (hKJ : K ≤ centralizer (J : Set G))
    (hKA : K ≤ centralizer (A : Set G)) (hJA : ⁅J,A⁆ = J)
    (eJ : J ≃* SL(2,F)) (n : ℕ) (hn : 2 ≤ n) (hF : Nat.card F = 2^n)
    (hodd : Odd n) : False := by
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  have hJn : J ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot J).mp inferInstance
  have hAJ : A ≤ normalizer (J : Set G) := by rw [normalizer_eq_top]; exact le_top
  obtain ⟨R,hR⟩ := exists_isIrrPlusWith_of_faithful ρ hf J A hJn hAJ
    (IsElementaryAbelian.isPGroup 2 A)
  have ho : Odd (Nat.card (MulAut.Outer J)) := by
    rw [Nat.card_congr (MulAut.outerCongr (eJ.trans (Theory.PSL2.sl2QuotientEquiv F))).toEquiv,
      Theory.PSL2.outer_card_eq_field_degree F hF]
    exact hodd
  have hAR := Chapter3.Section02.ChosenSource325.homogeneous_invariant_of_odd_outer
    ρ hR (inferInstance : IsElementaryAbelian 2 A) ho
  let : IsSemisimpleRepresentation (ρ.comp J.subtype) :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mpr inferInstance
  have hi := hR.isIrrPlus.irreducible_of_semisimple ρ
  let U := invariantSubspace ρ J R hR.invariant
  have hfaith : Function.Injective U.toRepresentation := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rcases U.toRepresentation.normal_ker.eq_bot_or_eq_top with hb | ht
    · exact hb
    · apply False.elim
      apply hR.isIrrPlus.not_le_fixedSpace ρ
      intro v hv j
      have hj : j ∈ U.toRepresentation.ker := ht.symm ▸ mem_top j
      exact congrArg Subtype.val (LinearMap.congr_fun hj (⟨v,hv⟩ : R))
  have hmove : ¬ R ≤ fixedSpace ρ A := by
    intro hh
    apply hR.isIrrPlus.not_le_fixedSpace ρ
    rw [←hJA]
    exact le_fixedSpace_commutator_of_invariant ρ hR.invariant hh
  have hb := RPlusBound.restricted ρ
    (show A ∈ RPlusBound ρ 2 from
      ⟨⟨hA.1.2.1,hA.1.2.2.2.le.trans hA.1.1⟩,QhatStar.mem_RPlus ρ hA⟩)
    R hAR hmove
  have hC : restrictedSubgroup ρ R A ∈ Qhat (subspaceImageRepresentation ρ R) :=
    ⟨hb.1,isCubic_restrictedSubgroup ρ R hA.1.2.2.1,hb.2⟩
  obtain ⟨_,hnat | hherm⟩ := even_subspace_actor_recognition ρ J hJ eJ n hn hF U hi hfaith _ hC
  · exact suzuki_no_invariant_natural_seed ρ K hfix m hm e J A eJ
      (by rw [hF]; exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) hn))
      hA hKJ hKA R hR.invariant hAR hi hmove hnat
  · obtain ⟨s,hs,_⟩ := hherm
    exact Nat.not_even_iff_odd.mpr hodd ⟨s,by omega⟩



/-- The normal-support exclusion applies inside the full normalizer of an
actual component, retaining ambient outer actors and the original kernel. -/
theorem suzuki_no_normalized_odd_binary_support
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ) (hi : ρ.IsIrreducible)
    (K : Subgroup G) (hfix : fixedSpace ρ K = ⊥)
    (m : ℕ) (hm : 0 < m) (e : K ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (J A : Subgroup G) [IsSimpleGroup J]
    (hJ : IsComponent G J) (hSQ : IsSQTK KnownSimple.IsKnownSimple J)
    (hA : A ∈ QhatStar ρ) (hKJ : K ≤ centralizer (J : Set G))
    (hKA : K ≤ centralizer (A : Set G)) (hAJ : A ≤ normalizer (J : Set G))
    (hJA : ⁅J,A⁆ = J)
    (eJ : J ≃* SL(2,F)) (n : ℕ) (hn : 2 ≤ n) (hF : Nat.card F = 2^n)
    (hodd : Odd n) : False := by
  let N := normalizer (J : Set G)
  have hJN : J ≤ N := J.le_normalizer
  have hKN : K ≤ N := hKJ.trans (Subgroup.centralizer_le_normalizer _)
  let J' := J.subgroupOf N
  let K' := K.subgroupOf N
  let A' := A.subgroupOf N
  let σ := ρ.comp N.subtype
  let eJ' : J' ≃* J := subgroupOfEquivOfLe hJN
  let eK' : K' ≃* K := subgroupOfEquivOfLe hKN
  let : J'.Normal := (normal_subgroupOf_iff_le_normalizer hJN).mpr le_rfl
  let : IsSimpleGroup J' := eJ'.isSimpleGroup
  let : IsQuasisimple J := hJ.2
  let : IsQuasisimple J' := IsQuasisimple.of_mulEquiv eJ'.symm
  let : ρ.IsIrreducible := hi
  let := subnormal_restriction_semisimple ρ J hJ.1
  let : IsSemisimpleModule (ZMod 2)[J'] (Representation.asModule (σ.comp J'.subtype)) :=
    comp_semisimple_of_surjective (ρ.comp J.subtype) eJ'.toMonoidHom eJ'.surjective
  have hfix' : fixedSpace σ K' = ⊥ := by
    rw [fixedSpace_comp_map, map_subgroupOf_eq_of_le hKN]
    exact hfix
  have hJ'A' : ⁅J',A'⁆ = J' := by
    apply map_injective N.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hJN,map_subgroupOf_eq_of_le hAJ,hJA]
  have hcJ : K' ≤ centralizer (J' : Set N) := by
    intro k hk j hj
    exact Subtype.ext (hKJ hk j.val hj)
  have hcA : K' ≤ centralizer (A' : Set N) := by
    intro k hk a ha
    exact Subtype.ext (hKA hk a.val ha)
  exact suzuki_no_normal_odd_binary_support σ (hf.comp N.subtype_injective) K' hfix'
    m hm (eK'.trans e) J' A' ((IsSQTK.equiv eJ').mpr hSQ)
    (SourceReduction.starred_subgroupOf ρ hA hAJ) hcJ hcA hJ'A'
    (eJ'.trans eJ) n hn hF hodd

end CFSG.Quasithin.ChapterD

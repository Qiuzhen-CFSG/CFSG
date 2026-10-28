module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.LinearChiefSection
public import Theory.GroupTheory.SimpleNormalFaithfulness

/-!
# Faithfulness on the original linear chief section

The normal PSL₃(4) image has index three in the actual PGL₃(4) quotient.
Its center is trivial and its three-rank is two, so quasithinness makes its
centralizer order prime to three. A homomorphism moving this simple normal
subgroup therefore has trivial kernel: a disjoint kernel would centralize
it and embed in the quotient of order three.

Apply this to the chief section already selected inside the original U.
The binary representation of KX/O₂(KX) is faithful, and the kernel of the
original KX-action is exactly its two-core. All section endpoints, inclusions
and quotient maps are retained. No extension-recognition premise is added.

This discharges faithfulness for the module comparison in 11.1.2, but does
not identify the adjoint extension or prove either centralizer exclusion.
Common-normal existence and the final triangle assembly remain separate.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.2, printed pp.763--764, the KX-chief-factor argument.
-/

open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
open Theory.GroupAction.ComponentRankAction
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
public noncomputable section
variable {H M : Type*} [Group H] [Finite H] [Monoid M]

/-- Under the original rank bound, movement of the normal PSL₃ image
forces faithfulness of a homomorphism on the actual PGL₃ quotient. -/
theorem projective_component_quotient_hom_injective
    (K : Subgroup H) [K.Normal] (hK : K.IsCComponent)
    (hr : primeRank 3 H ≤ 2)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour (H ⧸ pCore 2 H))
    (τ : (H ⧸ pCore 2 H) →* M)
    (hmove : ∃ k : K, τ (QuotientGroup.mk' (pCore 2 H) k) ≠ 1) :
    Function.Injective τ := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let B := K.map q
  let : B.Normal := (inferInstance : K.Normal).map q (QuotientGroup.mk'_surjective _)
  obtain ⟨F,_,_,hF,⟨eK⟩⟩ := hm
  let eB : B ≃* PSL(3,F) := (cComponentTwoCoreQuotientEquiv hK).symm.trans eK
  let : IsSimpleGroup PSL(3,F) := Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup B := eB.isSimpleGroup
  let : Fintype F := Fintype.ofFinite F
  let : Fintype Matrix.PSL3Four.F := Fintype.ofFinite _
  let ef : F ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Matrix.PSL3Four.card_F] using hF)
  let e : B ≃* Matrix.PSL3Four.PSL := eB.trans (Atlas.fieldEquivPSL 3 ef)
  have hBcard : Nat.card B = 20160 :=
    (Nat.card_congr e.toEquiv).trans Matrix.PSL3Four.card_PSL
  have hB : ClassicalGroup.IsPSL B 3 4 := ⟨F,inferInstance,inferInstance,hF,⟨eB⟩⟩
  have hc : Nat.card (H ⧸ pCore 2 H) = 60480 := by
    rw [CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.card_pgl_sign_eq_three_mul_psl_sign
      false 4 hB hp (by norm_num [CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.SignedCongruence]),hBcard]
  have hi : B.index = 3 := by
    have hh := B.card_mul_index
    rw [hc,hBcard] at hh
    omega
  have hz : center B = ⊥ := by
    apply bot_unique
    intro x hx
    apply eB.map_eq_one_iff.mp
    exact (Group.IsPerfect.center_quotient_center_eq_bot SL(3,F)).le
      ((centerCongr eB) ⟨x,hx⟩).property
  have hcop : Nat.Coprime 3 (Nat.card (centralizer (B : Set (H ⧸ pCore 2 H)))) := by
    apply centralizer_coprime B
    · rw [hz,card_bot]; decide
    · rw [primeRank_congr 3 eB]
      exact Theory.SpecificGroups.SignedThreeCubicRank.linear_projective
        (show Nat.card F = 2^2 by simpa using hF) (by decide)
    · exact (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans hr
  apply MonoidHom.injective_of_simple_normal_moved τ B ?_ (by rw [hi]; exact hcop.symm)
  obtain ⟨k,hk⟩ := hmove
  exact ⟨⟨q k,mem_map_of_mem q k.property⟩,hk⟩

open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

open NoncentralChiefRefinement in
/-- The original selected chief section has faithful irreducible quotient action
and its literal KX-action has kernel exactly O₂(KX). -/
theorem linear_point_chief_faithful_representation
    (f : InvariantFlag (.sl3 m)) (hd : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 ≤ K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 0) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 0) ≤ centralizer (f.Vi 0 : Set G)) :
    let U := conjugateSpanBy V (centralizer (f.Vi 0 : Set G))
    let J := (K ⊔ X) ⊔ U
    U ≤ (K ⊔ (T : Subgroup G)).pCoreIn 2 ∧
    ∃ B A : NormalNode J,
      (f.Vi 0).subgroupOf J ≤ B.val ∧ B ⋖ A ∧ A.val ≤ U.subgroupOf J ∧
      ∃ he : IsElementaryAbelian 2 (Section B A),
      let _ := he
      ∃ ρ : Representation (ZMod 2)
        ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)) (Additive (Section B A)),
        Representation.IsIrreducible ρ ∧ Function.Injective ρ ∧
        ρ.comp (QuotientGroup.mk' (pCore 2 (K ⊔ X : Subgroup G))) =
          (binarySectionRepresentation B A).comp
            (inclusion (show K ⊔ X ≤ J from le_sup_left)) ∧
        ((binarySectionRepresentation B A).comp
          (inclusion (show K ⊔ X ≤ J from le_sup_left))).ker =
            pCore 2 (K ⊔ X : Subgroup G) ∧
        ∃ k : K, ρ (QuotientGroup.mk' (pCore 2 (K ⊔ X : Subgroup G))
          (inclusion (show K ≤ K ⊔ X from le_sup_left) k)) ≠ 1 := by
  intro U J
  obtain ⟨hU,B,A,hZB,hBA,hAU,he,ρ,hirr,hρ,k,hkρ⟩ :=
    linear_point_chief_quotient_representation D S m f hd hfix hX hK hLK hk hp hcard hmove
  let _ := he
  let H := K ⊔ X
  let C := K.subgroupOf H
  have hKH : K ≤ H := le_sup_left
  have hXN : X ≤ normalizer (f.Vi 0 : Set G) := by
    apply f.cartan_normalizes _ hX 0
    intro i W hW hT
    exact (SL3.flag_inner_unique D S m i W hW hT).trans
      (SL3.flag_inner_unique D S m i (f.space i) (f.dimension i)
        (inf_le_left.trans (f.invariant i))).symm
  have hHN : H ≤ normalizer (f.Vi 0 : Set G) := sup_le hK.1.1 hXN
  let : C.Normal := normal_subgroupOf_of_le_normalizer
    (hHN.trans ((normal_subgroupOf_iff_le_normalizer hK.1.1).mp hK.2))
  have hC : C.IsCComponent := hK.1.2.subgroupOf_of_le hKH hHN
  have hr : primeRank 3 H ≤ 2 :=
    (_root_.primeRank_le_of_injective 3 (inclusion hHN) (inclusion_injective hHN)).trans
      ((S.source.simpleQTKE.twoLocal_sqtk (f.normalizer_twoLocal 0)).stronglyQuasithin
        3 Nat.prime_three (by decide))
  let e : C ≃* K := subgroupOfEquivOfLe hKH
  have hm : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 4 := by
    obtain ⟨F,_,_,hF,⟨ek⟩⟩ := hk
    exact ⟨F,inferInstance,inferInstance,hF,
      ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans ek⟩⟩
  have hfaith : Function.Injective ρ := projective_component_quotient_hom_injective
    C hC hr hm hp ρ ⟨⟨⟨k,hKH k.property⟩,k.property⟩,hkρ⟩
  refine ⟨hU,B,A,hZB,hBA,hAU,he,ρ,hirr,hfaith,hρ,?_,k,hkρ⟩
  rw [←hρ,MonoidHom.ker_comp_of_injective _ _ hfaith,QuotientGroup.ker_mk']

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle

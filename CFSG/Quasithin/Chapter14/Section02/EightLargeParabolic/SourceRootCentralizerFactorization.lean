module

public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceRootCartanComplement
public import Theory.Representation.SL2.EightTorusRootLines
public import Theory.Representation.BinaryConjugationSection.CoprimeTwoRootFactorization
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.SpecificGroups.SL2.FaithfulRootMovement

/-!
# The original Cartan-fixed core factors through both root centralizers

Two distinct full root images have binary fixed lines spanning the entire
Cartan-fixed plane in the original core section. Coprime lifting retains
the actual Cartan, and full root movement eliminates the central twist.
The resulting ordered product takes place inside the full original core.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceRootCentralizerFactorization
variable {G : Type*} [Group G] [Finite G]

private theorem card_map_of_disjoint {E D : Type*} [Group E] [Group D]
    (q : E →* D) (R : Subgroup E) (hk : Disjoint R q.ker) :
    Nat.card (R.map q)=Nat.card R := by
  have hi : Function.Injective (q.subgroupMap R) := by
    apply (q.subgroupMap R).ker_eq_bot_iff.mp
    apply bot_unique
    intro x hx
    exact Subtype.ext (hk.le_bot ⟨x.property,congrArg Subtype.val hx⟩)
  exact (Nat.card_congr (MulEquiv.ofBijective (q.subgroupMap R)
    ⟨hi,q.subgroupMap_surjective R⟩).toEquiv).symm

private theorem factorization_of_triple_core (P : Subgroup G)
    (ε : (P ⧸ pCore 2 P) ≃* Theory.PSL2.BinaryGroup 3)
    (hs : SourceTripleModule.HasTripleExtraspecialCore P ε)
    (A R S : Subgroup G) (hAP : A≤P) (hRP : R≤P) (hSP : S≤P)
    (hA7 : Nat.card A=7) (hR : IsPGroup 2 R) (hS : IsPGroup 2 S)
    (hR8 : Nat.card R=8) (hS8 : Nat.card S=8)
    (hkR : Disjoint R (P.pCoreIn 2)) (hkS : Disjoint S (P.pCoreIn 2))
    (hAR : A≤normalizer (R:Set G)) (hAS : A≤normalizer (S:Set G))
    (hne : (R.subgroupOf P).map (QuotientGroup.mk' (pCore 2 P))≠
      (S.subgroupOf P).map (QuotientGroup.mk' (pCore 2 P))) :
    ∀ v∈P.pCoreIn 2⊓centralizer (A:Set G),
      ∃ a∈P.pCoreIn 2⊓centralizer (A:Set G)⊓centralizer (R:Set G),
      ∃ b∈P.pCoreIn 2⊓centralizer (A:Set G)⊓centralizer (S:Set G), v=a*b := by
  classical
  obtain ⟨hex,Z,hZ,hN,hel,ρ,d,_,hirr,hcard,_⟩ := hs
  let _ := hex
  let _ := hN
  let _ := hel
  let Q := P.pCoreIn 2
  let V := Additive (Q ⧸ Z.subgroupOf Q)
  let : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  let eSL := ε.trans (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 3)).symm
  let π := QuotientGroup.mk' (pCore 2 P)
  let q : P →* SL(2,GaloisField 2 3) := eSL.toMonoidHom.comp π
  let σ : Representation (ZMod 2) SL(2,GaloisField 2 3) V := ρ.comp eSL.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff eSL.symm.toMonoidHom eSL.symm.surjective ρ).mpr hirr
  have hd : Module.finrank (ZMod 2) V=8 := by
    have hc := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=V)
    rw [Nat.card_zmod] at hc
    exact Nat.pow_right_injective (by decide : 1<2) (hc.symm.trans hcard : 2^Module.finrank (ZMod 2) V=2^8)
  have hker : q.ker=pCore 2 P := by
    rw [MonoidHom.ker_comp_of_injective _ _ eSL.injective,QuotientGroup.ker_mk']
  let A₀ := A.subgroupOf P
  have hA₀7 : Nat.card A₀=7 := (Nat.card_congr (subgroupOfEquivOfLe hAP).toEquiv).trans hA7
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hA₀ : IsPGroup 7 A₀ := IsPGroup.of_card (n:=1) (by simpa only [pow_one] using hA₀7)
  have hAm7 : Nat.card (A₀.map q)=7 := by
    apply (card_map_of_disjoint q A₀ ?_).trans hA₀7
    rw [hker]
    exact hA₀.disjoint_of_coprime pCore_isPGroup (by decide)
  have hroot (B : Subgroup G) (hBP : B≤P) (hB : IsPGroup 2 B)
      (hcB : Nat.card B=8) (hkB : Disjoint B Q) (hAB : A≤normalizer (B:Set G)) :
      IsPGroup 2 ((B.subgroupOf P).map q) ∧ Nat.card ((B.subgroupOf P).map q)=8 ∧
      A₀.map q≤normalizer (((B.subgroupOf P).map q):Set SL(2,GaloisField 2 3)) ∧ ⁅B,A⁆=B := by
    let B₀ := B.subgroupOf P
    have hB₀ : IsPGroup 2 B₀ := hB.of_equiv (subgroupOfEquivOfLe hBP).symm
    have hc : Nat.card B₀=8 := (Nat.card_congr (subgroupOfEquivOfLe hBP).toEquiv).trans hcB
    have hk : Disjoint B₀ q.ker := by
      rw [hker]
      apply disjoint_def.mpr
      intro b hb hq
      exact Subtype.ext (hkB.le_bot ⟨hb,mem_map_of_mem P.subtype hq⟩)
    have hn : A₀≤normalizer (B₀:Set P) := fun a ha => B.le_normalizer_comap P.subtype (hAB ha)
    refine ⟨hB₀.map q,(card_map_of_disjoint q B₀ hk).trans hc,
      (map_mono hn).trans (B₀.le_normalizer_map q),?_⟩
    have hm := Matrix.SpecialLinearGroup.faithful_root_commutator_eq q B₀ A₀ hB₀
      (by rw [hc,GaloisField.card 2 3 (by decide)]; rfl) hk hn
      (by rw [hAm7]; decide) (by
        intro hz
        have hh := congrArg (fun K : Subgroup SL(2,GaloisField 2 3) => Nat.card K) hz
        rw [hAm7,card_bot] at hh
        omega)
    have hh := congrArg (Subgroup.map P.subtype) hm
    rw [map_commutator,map_subgroupOf_eq_of_le hBP,map_subgroupOf_eq_of_le hAP] at hh
    exact hh
  obtain ⟨hRm,hRmc,hnR,hmR⟩ := hroot R hRP hR hR8 hkR hAR
  obtain ⟨hSm,hSmc,hnS,hmS⟩ := hroot S hSP hS hS8 hkS hAS
  have hneq : (R.subgroupOf P).map q≠(S.subgroupOf P).map q := by
    intro hh
    apply hne
    have hh' : ((R.subgroupOf P).map π).map eSL.toMonoidHom=
        ((S.subgroupOf P).map π).map eSL.toMonoidHom := by
      simpa only [Subgroup.map_map] using hh
    exact (Subgroup.map_injective eSL.injective) hh'
  have hsum := (SL2.BinarySmall.eight_irreducible_torus_root_lines σ hd
    ((R.subgroupOf P).map q) ((S.subgroupOf P).map q) (A₀.map q)
    hRm hSm hRmc hSmc hneq hAm7 hnR hnS).2.2.2
  have hspace (B : Subgroup G) :
      fixedSpace (ρ.comp π) (B.subgroupOf P)=fixedSpace σ ((B.subgroupOf P).map q) := by
    rw [←fixedSpace_comp_map]
    congr 1
    ext h v
    change ρ (π h) v=ρ (eSL.symm (eSL (π h))) v
    rw [eSL.symm_apply_apply]
  have hZH : Z≤centralizer (P:Set G) := by
    rw [hZ]
    apply centerIn_centralizes_of_card_two _ d.normalized
    rw [centerIn_eq_map_center,card_map_of_injective Q.subtype_injective]
    exact IsExtraspecial.center_order_p 2 Q
  have hAp : IsPGroup 7 A := IsPGroup.of_card (n:=1) (by simpa only [pow_one] using hA7)
  let : Group.IsNilpotent Q := (isPGroup_pCoreIn 2 P).isNilpotent
  apply d.fixed_core_two_root_factorization A R S hAP hRP hSP inferInstance
    (IsPGroup.coprime_card_of_ne 7 2 (by decide) A Q hAp (isPGroup_pCoreIn 2 P)) hmR hmS hZH
  rw [hspace R,hspace S,hspace A]
  exact hsum

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eR : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)
include hG hempty hM hu hmany hcard e hH eR

/-- The original full-core centralizer of any common seven-normalizer is
an ordered product of the centralizers of the two actual opposite roots. -/
theorem source_two_root_core_factorization
    (A R S : Subgroup G) (hAH : A≤H) (hRH : R≤H) (hSH : S≤H)
    (hA7 : Nat.card A=7) (hR : IsPGroup 2 R) (hS : IsPGroup 2 S)
    (hR8 : Nat.card R=8) (hS8 : Nat.card S=8)
    (hkR : Disjoint R (H.pCoreIn 2)) (hkS : Disjoint S (H.pCoreIn 2))
    (hAR : A≤normalizer (R:Set G)) (hAS : A≤normalizer (S:Set G))
    (hne : (R.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))≠
      (S.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) :
    ∀ v∈H.pCoreIn 2⊓centralizer (A:Set G),
      ∃ a∈H.pCoreIn 2⊓centralizer (A:Set G)⊓centralizer (R:Set G),
      ∃ b∈H.pCoreIn 2⊓centralizer (A:Set G)⊓centralizer (S:Set G), v=a*b :=
  factorization_of_triple_core H _
    (SourceTripleModule.source_core_triple hG T hempty hM hu hmany hcard e H hH eR)
    A R S hAH hRH hSH hA7 hR hS hR8 hS8 hkR hkS hAR hAS hne

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceRootCentralizerFactorization

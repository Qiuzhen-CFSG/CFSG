module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedCoreEquality
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedResidualCore

/-!
# The literal paired residual cores exclude the source branch

Apply the irreducible-section argument inside the actual subgroup Mc.
The resulting equality of its two-core with the restricted join of the
two point-residual cores maps through Mc.subtype to the literal equality
required by the original paired-core contradiction. The original local
hypotheses supply Mc's Sylow-overgroup membership and centralizer identity.

The paired geometric inputs remain explicit here: they are the two
irreducible sections and the ordinary/modulo centralizer identities used
in 14.6.9(k)--(n). Their carriers are subgroups of Mc, and the residual-core
join is fixed to the actual C.5 blocks rather than an abstract model.

Source: Aschbacher--Smith, proof of 14.6.9(k)--(n), printed p.1027.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
attribute [local instance] omegaCore_normal

theorem source_paired_core_exclusion_of_sections
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (I : Subgroup G)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (Λ : Subgroup G)
    (c : OriginalHypotheses I Λ ((pResidual 2 I).map I.subtype)
      ((T : Subgroup G) ⊓ I) ((T : Subgroup G) ⊓ I))
    (b : OrbitDecomposition (c.sylow : Subgroup I)
      (((T : Subgroup G) ⊓ I).subgroupOf I) (pResidual 2 I))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (hi : IsAlternatingBlock ((b.block i).map I.subtype) 5)
    (S B A C K E Z₀ : Subgroup Mc)
    (hST : S ≤ (T : Subgroup G).subgroupOf Mc)
    (hSnormal : (S.subgroupOf ((T : Subgroup G).subgroupOf Mc)).Normal)
    (hCS : C ≤ S) (hQC : pCore 2 Mc ≤ C) (hEA : E ≤ A)
    (hZ₀Z : Z₀ ≤ omegaOneCenterAmbient (pCore 2 Mc))
    [(Z₀.subgroupOf S).Normal]
    (hBE : B ≤ normalizer (E : Set Mc))
    (hirrE : IsIrreducibleSection B Z₀ E)
    (hcenter : ((center (S ⧸ Z₀.subgroupOf S)).comap
      (QuotientGroup.mk' (Z₀.subgroupOf S))).map S.subtype ≤ E)
    (hBA : B ≤ normalizer (A : Set Mc))
    (hBC : B ≤ normalizer (C : Set Mc))
    (hirrC : IsIrreducibleSection B A C)
    (hsmall : ⁅A,K⁆ ≤ E)
    (hcomm : ⁅C,K⁆ = (((((pResidual 2 ((b.block i).map I.subtype ⊓ Mc : Subgroup G)).map
        ((b.block i).map I.subtype ⊓ Mc).subtype).pCoreIn 2) ⊔
      (((pResidual 2 ((b.block j).map I.subtype ⊓ Mc : Subgroup G)).map
        ((b.block j).map I.subtype ⊓ Mc).subtype).pCoreIn 2)).subgroupOf Mc))
    (a : Mc)
    (hlarge : Nat.card (A ⊓ A.map (MulAut.conj a).toMonoidHom : Subgroup Mc) < Nat.card E)
    (hcent : C ⊓ centralizer ((((((pResidual 2 ((b.block i).map I.subtype ⊓ Mc : Subgroup G)).map
        ((b.block i).map I.subtype ⊓ Mc).subtype).pCoreIn 2) ⊔
      (((pResidual 2 ((b.block j).map I.subtype ⊓ Mc : Subgroup G)).map
        ((b.block j).map I.subtype ⊓ Mc).subtype).pCoreIn 2)).subgroupOf Mc) : Set Mc) ≤ Z₀)
    (hmod : ∀ c ∈ C, (∀ n ∈ (((((pResidual 2 ((b.block i).map I.subtype ⊓ Mc : Subgroup G)).map
        ((b.block i).map I.subtype ⊓ Mc).subtype).pCoreIn 2) ⊔
      (((pResidual 2 ((b.block j).map I.subtype ⊓ Mc : Subgroup G)).map
        ((b.block j).map I.subtype ⊓ Mc).subtype).pCoreIn 2)).subgroupOf Mc), ⁅n,c⁆ ∈ Z₀) → c ∈ (((((pResidual 2 ((b.block i).map I.subtype ⊓ Mc : Subgroup G)).map
        ((b.block i).map I.subtype ⊓ Mc).subtype).pCoreIn 2) ⊔
      (((pResidual 2 ((b.block j).map I.subtype ⊓ Mc : Subgroup G)).map
        ((b.block j).map I.subtype ⊓ Mc).subtype).pCoreIn 2)).subgroupOf Mc)) :
    False := by
  let K₁ := (b.block i).map I.subtype
  let K₂ := (b.block j).map I.subtype
  let B₁ := K₁ ⊓ Mc
  let B₂ := K₂ ⊓ Mc
  let X₁ := (pResidual 2 B₁).map B₁.subtype
  let X₂ := (pResidual 2 B₂).map B₂.subtype
  let R₁ := X₁.pCoreIn 2
  let R₂ := X₂.pCoreIn 2
  let N := (R₁ ⊔ R₂).subgroupOf Mc
  have hZ : Nat.card (centralInvolutions T) = 2 :=
    plane_centralInvolutions_card T M hM.1.2 hcard e
  have hMc := (plane_ordering_and_overgroups hG T hempty hM hunique hmany hcard hZ).2.2.1
  have hTMc : (T : Subgroup G) ≤ Mc := by
    rw [hMc]
    exact le_centralizer_iff.mp (centralInvolutions_le_centralizer_sylow T)
  have hMcMax : IsMaximalTwoLocal Mc :=
    (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      hunique ▸ Set.mem_singleton Mc).1
  have hMcOver : Mc ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal hMcMax.1,hTMc⟩
  have hcore : pCore 2 Mc = N :=
    source_omegaCore_eq_of_paired_sections hG T hempty hMcOver hMc.le
      S B A C K E N Z₀ hST hSnormal hCS hQC hEA hZ₀Z
      hBE hirrE hcenter hBA hBC hirrC hsmall hcomm a hlarge hcent hmod
  have hR₁ : R₁ ≤ Mc := (pCoreIn_le 2 X₁).trans
    ((map_subtype_le (pResidual 2 B₁)).trans inf_le_right)
  have hR₂ : R₂ ≤ Mc := (pCoreIn_le 2 X₂).trans
    ((map_subtype_le (pResidual 2 B₂)).trans inf_le_right)
  have hQ : Mc.pCoreIn 2 = R₁ ⊔ R₂ := by
    change (pCore 2 Mc).map Mc.subtype = R₁ ⊔ R₂
    rw [hcore]
    exact map_subgroupOf_eq_of_le (sup_le hR₁ hR₂)
  exact source_paired_residual_core_exclusion hG T hempty hM hunique hmany hcard e hab
    H hH u hu I hI Λ c b i j hij hs hi hQ
end CFSG.Quasithin.Chapter14.Section06

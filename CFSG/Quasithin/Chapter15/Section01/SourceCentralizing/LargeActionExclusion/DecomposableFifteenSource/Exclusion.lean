module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableFifteenSource.KernelProfile
public import Theory.GroupTheory.RankTwoNoncyclicCubicQuotient

/-!
# Exclusion of the original quintic residual of order fifteen

The faithful partner section maps onto its actual action on the fixed module.
Pulling back the elementary cubic group of order nine preserves the original
rank-two cover. The noncyclic abelian cubic quotient theorem gives a normal
three-complement in this preimage, hence in its subgroup given by the original
section kernel. This contradicts the source kernel profile.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker

private theorem false_of_cubic_preimage
    {B A D : Type*} [Group B] [Finite B] [Group A] [Finite A] [Group D]
    (cover : B →* A) (hcover : Function.Surjective cover) (hrank : primeRank 3 B ≤ 2)
    (f : A →* D) (hf : Function.Surjective f)
    (hnot : ¬HasNormalPComplement 3 f.ker)
    (R : Subgroup D) [IsElementaryAbelian 3 R] (hR : Nat.card R = 9) : False := by
  let : Finite D := Finite.of_surjective f hf
  let P := R.comap f
  let B₀ := P.comap cover
  let g : B₀ →* P := (cover.comp B₀.subtype).codRestrict P (fun x => x.property)
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨b,hb⟩ := hcover x.val
    exact ⟨⟨b,show cover b ∈ P from hb ▸ x.property⟩,Subtype.ext hb⟩
  let q : P →* R := (f.comp P.subtype).codRestrict R (fun x => x.property)
  have hq : Function.Surjective q := by
    intro r
    obtain ⟨a,ha⟩ := hf r.val
    exact ⟨⟨a,show f a ∈ R from ha ▸ r.property⟩,Subtype.ext ha⟩
  have hkP : f.ker ≤ P := by
    intro x hx
    change f x ∈ R
    rw [show f x = 1 from hx]
    exact R.one_mem
  have hPnot : ¬HasNormalPComplement 3 P :=
    fun hc => hnot (hasNormalPComplement_of_le 3 hkP hc)
  have hnc : ¬IsCyclic R :=
    IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq (p := 3) (by simpa using hR)
  have hcompP : HasNormalPComplement 3 P :=
    hasNormalThreeComplement_of_noncyclic_abelian_three_quotient
      g hg ((primeRank_subgroup_le 3 B₀).trans hrank) q hq
      (IsElementaryAbelian.isPGroup 3 R) hnc
  exact hPnot hcompP

variable {G : Type*} [Group G] [Finite G]

/-- The literal original prime-five residual-order-fifteen source is impossible. -/
theorem PreparedChosenModule.false_of_full_decomposable_fifteen
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
      let C := M ⊓ centralizer (Z₁ : Set G)
      letI := caseI_module_centralizer_normal (Z1 := Z₁) h.normalized
      Nat.card (pResidual 2 (C ⧸ (M ⊓ centralizer (V : Set G)).subgroupOf C)) = 15 →
      False := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive Z₁ C h15
  let E := thompsonFixed T V
  let H := conjugateSpanBy V (centralizer (E : Set G))
  let K := (commutatorPreimage Mc H E).subgroupOf Mc
  obtain ⟨hn,hK,_,f,hf,hnot,R,hR,hRcard⟩ :=
    h.decomposable_fifteen_section_kernel_profile hG T hempty hM hmany hJ hu hne hfull
      c d hd s π hp hs hdec hq hfive h15
  let : K.Normal := hK
  let : IsElementaryAbelian 3 R := hR
  have hMc : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  have hrank : primeRank 3 Mc ≤ 2 :=
    (hG.twoLocal_sqtk hMc.1.1).stronglyQuasithin 3 Nat.prime_three (by decide)
  exact false_of_cubic_preimage
    (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K) hrank f hf hnot R hRcard

end CFSG.Quasithin.Chapter15.Section01

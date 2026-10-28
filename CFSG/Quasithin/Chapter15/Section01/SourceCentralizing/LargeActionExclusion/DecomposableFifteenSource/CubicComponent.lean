module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableFifteenSource.KernelProfile
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableFifteenSource.PartnerThreeCore
public import Theory.GroupTheory.PCoreFreePreimage
public import Theory.GroupTheory.RankTwoCubicComponentAlternative

/-!
# A component forced by the original residual-fifteen source

Restrict the actual faithful section quotient to the preimage of its
original elementary cubic group of order nine. Its two-core remains
trivial, and its kernel still has no normal three-complement. Rank stays
on the corresponding subgroup of the original partner. The cubic
quotient theorem therefore produces an ordinary component of order
divisible by three after quotienting the literal three-prime core.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker

private theorem component_in_cubic_preimage
    {B A D : Type*} [Group B] [Finite B] [Group A] [Finite A] [Group D]
    (cover : B →* A) (hcover : Function.Surjective cover) (hrank : primeRank 3 B ≤ 2)
    (f : A →* D) (hf : Function.Surjective f)
    (hnot : ¬HasNormalPComplement 3 f.ker)
    (R : Subgroup D) [IsElementaryAbelian 3 R] (hR : Nat.card R = 9) :
    ∃ L : Subgroup ((R.comap f) ⧸ pPrimeCore 3 (R.comap f)),
      IsComponent ((R.comap f) ⧸ pPrimeCore 3 (R.comap f)) L ∧ 3 ∣ Nat.card L := by
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
  exact exists_component_of_not_normalThreeComplement_of_noncyclic_abelian_quotient
    g hg ((primeRank_subgroup_le 3 B₀).trans hrank) q hq
      (IsElementaryAbelian.isPGroup 3 R) hnc hPnot

variable {G : Type*} [Group G] [Finite G]

/-- The original cubic preimage has trivial two-core and an actual ordinary
component of three-divisible order modulo its three-prime core. -/
theorem PreparedChosenModule.decomposable_fifteen_cubic_preimage_component
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
      let E := thompsonFixed T V
      let H := conjugateSpanBy V (centralizer (E : Set G))
      let K := (commutatorPreimage Mc H E).subgroupOf Mc
      ∃ hn : Mc ≤ normalizer (E : Set G),
        ∃ hK : K.Normal, letI := hK
          ∃ f : (Mc ⧸ K) →* internalActionImage Mc E hn,
            Function.Surjective f ∧ ¬HasNormalPComplement 3 f.ker ∧
            let R := pCore 3 (internalActionImage Mc E hn);
              IsElementaryAbelian 3 R ∧ Nat.card R = 9 ∧
              pCore 2 (R.comap f) = ⊥ ∧
              ∃ L : Subgroup ((R.comap f) ⧸ pPrimeCore 3 (R.comap f)),
                IsComponent ((R.comap f) ⧸ pPrimeCore 3 (R.comap f)) L ∧
                  3 ∣ Nat.card L := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive Z₁ C h15
  let E := thompsonFixed T V
  let H := conjugateSpanBy V (centralizer (E : Set G))
  let K := (commutatorPreimage Mc H E).subgroupOf Mc
  obtain ⟨hn,hK,hcore,f,hf,hnot,_,_,_⟩ :=
    h.decomposable_fifteen_section_kernel_profile hG T hempty hM hmany hJ hu hne hfull
      c d hd s π hp hs hdec hq hfive h15
  let : K.Normal := hK
  obtain ⟨hn',hR,hRcard,_⟩ := h.decomposable_fifteen_partner_three_core
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive h15
  let R := pCore 3 (internalActionImage Mc E hn)
  let : IsElementaryAbelian 3 R := hR
  have hMc : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  have hrank : primeRank 3 Mc ≤ 2 :=
    (hG.twoLocal_sqtk hMc.1.1).stronglyQuasithin 3 Nat.prime_three (by decide)
  have hpc : pCore 2 (R.comap f) = ⊥ :=
    pCore_comap_eq_bot_of_coprime 2 f R hcore (by rw [hRcard]; decide)
  obtain ⟨L,hL,hLthree⟩ := component_in_cubic_preimage
    (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K) hrank f hf hnot R hRcard
  exact ⟨hn,hK,f,hf,hnot,hR,hRcard,hpc,L,hL,hLthree⟩

end CFSG.Quasithin.Chapter15.Section01

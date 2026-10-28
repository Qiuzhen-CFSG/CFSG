module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableFifteenSource.CubicImage
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableFifteenSource.ReducedPartner
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableFifteenSource.SectionThreeComplement
public import Theory.GroupTheory.CommutatorPreimageTransport

/-!
# The actual faithful section kernel in the residual-fifteen case

The original partner acts faithfully on H/E after quotienting by its
literal commutator preimage. This quotient has trivial two-core and maps
onto the original action on E. The latter action contains an elementary
abelian group of order nine, while the kernel has no normal three-complement.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker

private theorem reduced_section_core_free
    {B : Type*} [Group B] (H E K : Subgroup B) [E.Normal] [K.Normal]
    (hred : IsPReduced 2 (H.map (QuotientGroup.mk' E)))
    (hK : K = commutatorPreimage ⊤ H E) : pCore 2 (B ⧸ K) = ⊥ := by
  let q := QuotientGroup.mk' E
  let W := H.map q
  let : W.Normal := hred.normal
  let g := (QuotientGroup.mk' (centralizer (W : Set (B ⧸ E)))).comp q
  have hg : Function.Surjective g :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hk : K = g.ker := by
    rw [hK,commutatorPreimage_eq_inf_comap_centralizer,top_inf_eq]
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
  let e := (QuotientGroup.quotientMulEquivOfEq hk).trans
    (QuotientGroup.quotientKerEquivOfSurjective g hg)
  apply (map_eq_bot_iff_of_injective (f := e.toMonoidHom) _ e.injective).mp
  exact (pCore_map_iso 2 e).trans hred.quotient_pCore_eq_bot

variable {G : Type*} [Group G] [Finite G]

/-- The original order-fifteen source produces its actual core-free section
action, its quotient action on E, and the incompatible kernel profile. -/
theorem PreparedChosenModule.decomposable_fifteen_section_kernel_profile
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
          pCore 2 (Mc ⧸ K) = ⊥ ∧
          ∃ f : (Mc ⧸ K) →* internalActionImage Mc E hn,
            Function.Surjective f ∧ ¬ HasNormalPComplement 3 f.ker ∧
            ∃ R : Subgroup (internalActionImage Mc E hn),
              IsElementaryAbelian 3 R ∧ Nat.card R = 9 := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive Z₁ C h15
  let E := thompsonFixed T V
  let H := conjugateSpanBy V (centralizer (E : Set G))
  let K := (commutatorPreimage Mc H E).subgroupOf Mc
  have hpartner := h.decomposable_fifteen_partner_and_normalization
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive h15
  have hUcEq : localModule T Mc = E := hpartner.1
  obtain ⟨hn,R,hR,hRcard⟩ := h.decomposable_fifteen_partner_cubic_nine
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive h15
  obtain ⟨hK,hnot⟩ := h.decomposable_five_full_partner_section_not_three_complement
    hG T hempty hM hmany hJ hu hne hfull c d hd s π hp hs hdec hq hfive hUcEq
  let : K.Normal := hK
  let : (E.subgroupOf Mc).Normal := normal_subgroupOf_of_le_normalizer hn
  have hred := h.decomposable_five_full_partner_section_reduced
    hG T hempty hM hmany hJ hu hne hfull c d hd s π hp hs hdec hq hfive hUcEq
  have hCMc : centralizer (E : Set G) ≤ Mc := by
    rw [←hUcEq]
    exact localModule_centralizer_le_partner T Mc hu
  have hHMc : H ≤ Mc :=
    (conjugateSpanBy_le_self
      (V.le_centralizer.trans (centralizer_le (show E ≤ V from inf_le_left)))).trans hCMc
  have hcore : pCore 2 (Mc ⧸ K) = ⊥ := by
    apply reduced_section_core_free (H.subgroupOf Mc) (E.subgroupOf Mc) K hred
    dsimp only [K]
    rw [commutatorPreimage_subgroupOf Mc H E Mc le_rfl hHMc hn]
    simp only [subgroupOf_self]
  have hKC := h.decomposable_five_section_kernel_centralizes
    hG T hempty hM hmany hJ hu hne hfull c d hd s π hp hs hdec hq hfive
    H (le_conjugateSpanBy V (centralizer (E : Set G))) hn
  let f₀ := (actionHom Mc E hn).rangeRestrict
  have hf₀ : f₀.ker = (centralizer (E : Set G)).subgroupOf Mc := by
    rw [MonoidHom.ker_rangeRestrict,actionHom_ker]
  have hKf : K ≤ f₀.ker := by
    rw [hf₀]
    exact fun _ hx => hKC hx
  let f := QuotientGroup.lift K f₀ hKf
  have hf : f.ker =
      ((centralizer (E : Set G)).subgroupOf Mc).map (QuotientGroup.mk' K) := by
    rw [QuotientGroup.ker_lift,hf₀]
  have hfnot : ¬ HasNormalPComplement 3 f.ker := by
    rw [hf]
    exact hnot
  exact ⟨hn,hK,hcore,f,QuotientGroup.lift_surjective_of_surjective K f₀
    (actionHom Mc E hn).rangeRestrict_surjective hKf,hfnot,R,hR,hRcard⟩

end CFSG.Quasithin.Chapter15.Section01

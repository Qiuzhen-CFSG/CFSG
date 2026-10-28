module
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.PushingUpModels
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.MatchingParabolics
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SourcePlacement

/-!
# Ordinary components of the normalized rank-one pushing-up pair

The unchanged module embeds in the ordinary component's central quotient:
a central element would be fixed by the original residual. Its rank twelve
then reduces the SQTK list to Ree. Three-divisibility excludes the unitary
marking, while the Suzuki marking retains the literal residual map into a
full Suzuki-side Ree parabolic.

These results do not assume residual uniqueness. The remaining constrained
components and the Suzuki ordinary-component contradiction are separate.
Source: Aschbacher--Smith C.3.2--5 and 4.2.12--13, pp.149--150,610--612.
-/
public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
variable {G S : Type*} [Group G] [Finite G] [Group S] [Finite S] [IsSimpleGroup S]

/-- A module with no fixed points embeds in a containing central quotient. -/
theorem rank_le_central_quotient_of_fixed_eq_bot
    {F K U : Subgroup G} (hFK : F ≤ K) (hUF : U ≤ F)
    (hfix : U ⊓ centralizer (F : Set G) = ⊥) :
    primeRank 2 U ≤ primeRank 2 (K ⧸ center K) := by
  let i := inclusion (hUF.trans hFK)
  let f := (QuotientGroup.mk' (center K)).comp i
  have hf : f.ker = ⊥ := by
    apply bot_unique
    intro x hx
    have hz : i x ∈ center K := (QuotientGroup.eq_one_iff _).mp hx
    have hc : (x : G) ∈ centralizer (F : Set G) := by
      intro y hy
      exact congrArg K.subtype (mem_center_iff.mp hz ⟨y,hFK hy⟩)
    have he : (x : G) = 1 := mem_bot.mp (hfix ▸ (show (x : G) ∈ U ⊓ centralizer (F : Set G) from ⟨x.property,hc⟩))
    exact Subtype.ext he
  exact Theory.GroupTheory.primeRank_le_of_injective 2 f ((MonoidHom.ker_eq_bot_iff f).mp hf)

/-- The full Theorem C catalogue applies to the actual ordinary quotient. -/
private theorem ordinary_theoremC_model
    {H M F R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (K : Subgroup H) (hK : IsComponent H K) :
    ChapterA.Section02.IsTheoremCModel (K ⧸ center K) := by
  let := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Group.IsPerfect (K ⧸ center K) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hz : center K = pCore 2 K :=
    IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot h.oddCore_eq_bot K)
  have hsq : IsStronglyQuasithin (K ⧸ center K) := by
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ (hz.symm ▸ pCore_isPGroup)).trans
      ((h.sqtk.subgroup K).stronglyQuasithin p hp ho)
  exact ChapterA.Section02.theoremC_knownSimple inferInstance
    (Group.IsPerfect.not_isMulCommutative _) hsq ((h.sqtk.isKGroup.subgroup K).quotient _)

/-- The actual ordinary C.2.8 component is Ree after the marked residual exclusions. -/
theorem ordinary_ree_of_large_rankOne
    {H M F R W U : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (hn : M ≤ normalizer (F : Set G))
    (hUF : U ≤ F.pCoreIn 2) (hne : U ≠ ⊥) (hcomm : U = ⁅U,F⁆)
    (hfix : U ⊓ centralizer (F : Set G) = ⊥) (hr : 12 ≤ primeRank 2 U)
    (hS : ¬ Group.IsSolvable S)
    (hexp : ¬ ∀ P : Subgroup S, IsPGroup 2 P → ∀ x : P, x ^ 2 = 1)
    (π : F →* S) (hπ : Function.Surjective π)
    (K : Subgroup H) (hK : IsComponent H K) :
    ∃ _hFK : F ≤ K.map H.subtype, ∃ m : ℕ, 1 ≤ m ∧
      Nonempty ((K.map H.subtype ⧸ center (K.map H.subtype)) ≃* ReeF4.Model m) := by
  let J := K.map H.subtype
  have hFJ : F ≤ J := by
    intro f hf
    exact ⟨⟨f,h.component_le.trans h.local_le hf⟩,
      h.ordinary_component_contains_original K hK hf,rfl⟩
  let e := (K.equivMapOfInjective H.subtype H.subtype_injective).symm
  let z := QuotientGroup.congr (center J) (center K) e (Theory.GroupTheory.FixedElementary.map_center e)
  have hspan := h.normalized_span_eq hn
  let : Group.IsPerfect F := hspan ▸ h.span_perfect
  have hrJ := hr.trans (rank_le_central_quotient_of_fixed_eq_bot hFJ
    (hUF.trans (pCoreIn_le 2 F)) hfix)
  have hm := (ordinary_theoremC_model h K hK).of_mulEquiv z
  rcases bender_or_CrankTwo_of_rank_twelve hm hrJ with hb | ⟨n,hm⟩
  · exact (no_bender_of_residual_module J F U hFJ hUF hne hcomm hb).elim
  · exact ⟨hFJ,ree_of_CrankTwo_residual_module F J U hFJ hUF hne hcomm
      hS hexp π hπ hrJ hm⟩

/-- A unitary marked residual excludes every ordinary component of this C.2.8 pair. -/
theorem no_ordinary_unitary
    {H M F R W U : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (hn : M ≤ normalizer (F : Set G))
    (hUF : U ≤ F.pCoreIn 2) (hne : U ≠ ⊥) (hcomm : U = ⁅U,F⁆)
    (hfix : U ⊓ centralizer (F : Set G) = ⊥) (hr : 12 ≤ primeRank 2 U)
    (hS : ¬ Group.IsSolvable S) (π : F →* S) (hπ : Function.Surjective π)
    {s : ℕ} (hs : 2 ≤ s) (hu : ClassicalGroup.IsPSU S 3 (2 ^ s))
    (K : Subgroup H) (hK : IsComponent H K) : False := by
  obtain ⟨hFK,m,hm,⟨e⟩⟩ := ordinary_ree_of_large_rankOne h hn hUF hne hcomm hfix hr
    hS (unitary_not_two_exponent hs hu) π hπ K hK
  let r := residualQuotientMap hFK e
  let := residualQuotientMap_kernel_solvable hFK e
  obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hUF hne hcomm e
  exact no_ree_local_of_three_dvd hS (unitary_not_two_exponent hs hu)
    (unitary_three_dvd_card hs hu) π hπ hm _ hp hpne r hnorm

/-- The Suzuki marking retains the literal residual in a full Ree parabolic. -/
theorem ordinary_suzuki_ree_parabolic
    {H M F R W U : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (hn : M ≤ normalizer (F : Set G))
    (hUF : U ≤ F.pCoreIn 2) (hne : U ≠ ⊥) (hcomm : U = ⁅U,F⁆)
    (hfix : U ⊓ centralizer (F : Set G) = ⊥) (hr : 12 ≤ primeRank 2 U)
    (hS : ¬ Group.IsSolvable S) (π : F →* S) (hπ : Function.Surjective π)
    {a : ℕ} (ha : 1 ≤ a) (es : S ≃* SuzukiMatrixGroup a)
    (K : Subgroup H) (hK : IsComponent H K) :
    ∃ hFK : F ≤ K.map H.subtype,
      ∃ m : ℕ, 1 ≤ m ∧ ∃ e : (K.map H.subtype ⧸ center (K.map H.subtype)) ≃* ReeF4.Model m,
        ∃ g : ReeF4.Model m,
          (residualQuotientMap hFK e).range.map (MulAut.conj g).toMonoidHom ≤
            ReeF4.ConverseParabolics.parabolic m .suzuki := by
  obtain ⟨hFK,m,hm,⟨e⟩⟩ := ordinary_ree_of_large_rankOne h hn hUF hne hcomm hfix hr
    hS (suzuki_not_two_exponent ha es) π hπ K hK
  exact ⟨hFK,ree_suzuki_parabolic_of_suzuki_residual F (K.map H.subtype) U hFK
    hUF hne hcomm hS π hπ ha es (Or.inr ⟨m,hm,⟨e⟩⟩)⟩
end CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl


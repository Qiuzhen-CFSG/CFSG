module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryMathieuLarge
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups.ThreeFree

/-!
# The original quintic source excludes both binary linear ordinary rows

The actual quotient has a full-Sylow overgroup with five dividing its order
and no odd prime except five. The native binary flag theorem forces any
three-free full-Sylow overgroup to be the Sylow itself, a contradiction.
The same original component's PSL₄(2) and PSL₅(2) model predicates are then
transported through their actual field and projective equivalences.
No whole-M generation, parabolic placement, or global residual is used.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
open Theory.SpecificGroups.BinaryComponentResidual
variable {G : Type*} [Group G] [Finite G]

private theorem binary_no_two_five_sylow_overgroup
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (P : Sylow 2 SL(n,ZMod 2)) (H : Subgroup SL(n,ZMod 2)) (a b : ℕ)
    (hPH : (P : Subgroup _) ≤ H) (h5 : 5 ∣ Nat.card H)
    (hc : Nat.card H ∣ 2^a * 5^b) : False := by
  have h3 : ¬3 ∣ Nat.card H := Nat.prime_three.coprime_iff_not_dvd.mp
    ((((by decide : Nat.Coprime 3 2).pow_right a).mul_right
      ((by decide : Nat.Coprime 3 5).pow_right b)).of_dvd_right hc)
  let f := BinaryLinear.OuterCyclic.slEquivLinear n
  let : Finite (BinaryLinear.OuterCyclic.LinearGroup n) :=
    Finite.of_equiv SL(n,ZMod 2) f.toEquiv
  let Q := P.mapSurjective (f := f.toMonoidHom) f.surjective
  let K := H.map f.toMonoidHom
  have hQK : (Q : Subgroup (BinaryLinear.OuterCyclic.LinearGroup n)) ≤ K := map_mono hPH
  have hK3 : ¬3 ∣ Nat.card K := by rwa [card_map_of_injective f.injective]
  have he : K = (Q : Subgroup (BinaryLinear.OuterCyclic.LinearGroup n)) := by
    rcases hn with rfl | rfl <;>
      exact BinaryLinear.SylowFlagOvergroups.eq_sylow_of_not_three_dvd Q K hQK hK3
  have hK5 : 5 ∣ Nat.card K := by rwa [card_map_of_injective f.injective]
  obtain ⟨r,hr⟩ := Q.isPGroup'.exists_card_eq
  rw [he,hr] at hK5
  exact (by decide : ¬5 ∣ 2) ((by decide : Nat.Prime 5).dvd_of_dvd_pow hK5)

/-- The actual raw ordinary two-core quotient is neither binary SL₄ nor
binary SL₅, including any proposed nontrivial central two-cover. -/
theorem PreparedChosenModule.decomposable_five_raw_not_binary_linear_quotient
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
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
      let Z1 := thompsonPlane T V (c.ambientFactor d s.first).space
      let G1 := centralizer (Z1 : Set G)
      let C := M ⊓ G1
      let R := (pResidual 2 C).map C.subtype
      let S := (T : Subgroup G) ⊓ G1
      ∀ {L : Subgroup G}, L ≤ G1 → IsComponent G1 (L.subgroupOf G1) →
        center L = pCore 2 L → IsQuasisimple (L ⧸ pCore 2 L) → Chapter1.IsSylowIn 2 (S ⊓ L) L →
        R ⊔ ⁅V,R⁆ ≤ normalizer (L : Set G) → ⁅L,⁅V,R⁆⁆ ≠ ⊥ →
        ∀ n : ℕ, (n = 4 ∨ n = 5) →
          ¬ Nonempty ((L ⧸ pCore 2 L) ≃* SL(n,ZMod 2)) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive Z1 G1 C R S L hLG hLc hcenter hquasi hSyl hnL hmove n hn
  rintro ⟨e⟩
  obtain ⟨P,H,a,b,hPH,h5,hc⟩ := h.decomposable_five_raw_two_five_sylow_overgroup
    hG T hempty hM hmany hJ hfull c d hd s π hp hs hdec hq hfive
    hLG hLc hcenter hquasi hSyl hnL hmove e (linear hn)
  exact binary_no_two_five_sylow_overgroup hn P H a b hPH h5 hc

/-- The two original binary projective model rows of ModelAction115 are
impossible on the same raw component, with the actual field transported. -/
theorem PreparedChosenModule.decomposable_five_raw_not_binary_psl
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
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
      let Z1 := thompsonPlane T V (c.ambientFactor d s.first).space
      let G1 := centralizer (Z1 : Set G)
      let C := M ⊓ G1
      let R := (pResidual 2 C).map C.subtype
      let S := (T : Subgroup G) ⊓ G1
      ∀ {L : Subgroup G}, L ≤ G1 → IsComponent G1 (L.subgroupOf G1) →
        center L = pCore 2 L → IsQuasisimple (L ⧸ pCore 2 L) → Chapter1.IsSylowIn 2 (S ⊓ L) L →
        R ⊔ ⁅V,R⁆ ≤ normalizer (L : Set G) → ⁅L,⁅V,R⁆⁆ ≠ ⊥ →
        ∀ n : ℕ, (n = 4 ∨ n = 5) → ¬ ClassicalGroup.IsPSL L n 2 := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive Z1 G1 C R S L hLG hLc hcenter hquasi hSyl hnL hmove n hn hm
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let k : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  let f : L ≃* SL(n,ZMod 2) := (e.trans (Atlas.fieldEquivPSL n k)).trans
    (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega))
  have hz : center L = ⊥ := by
    apply (center L).eq_bot_iff_card.mpr
    rw [Nat.card_congr (centerCongr f).toEquiv,(linear hn).1,card_bot]
  let q : (L ⧸ pCore 2 L) ≃* SL(n,ZMod 2) :=
    ((QuotientGroup.quotientMulEquivOfEq (hcenter.symm.trans hz)).trans
      QuotientGroup.quotientBot).trans f
  exact h.decomposable_five_raw_not_binary_linear_quotient
    hG T hempty hM hmany hJ hfull c d hd s π hp hs hdec hq hfive
    hLG hLc hcenter hquasi hSyl hnL hmove n hn ⟨q⟩

end CFSG.Quasithin.Chapter15.Section01

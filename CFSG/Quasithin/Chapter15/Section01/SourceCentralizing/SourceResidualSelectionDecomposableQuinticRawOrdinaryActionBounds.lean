module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryAction
public import Theory.GroupTheory.PerfectCentralCoverAutomorphisms
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.ElementaryRank
public import Theory.SpecificGroups.PSL3Three.EightGeometry.CentralProduct
public import Theory.SpecificGroups.PSL2.PrimeFieldTwoRank
public import Theory.Representation.AlternatingSevenConjugatePair.ElementaryGeometry
public import Theory.Alternating.Aut

/-!
# Small ordinary quotients excluded by the original faithful sixteen

Automorphisms of a perfect group descend faithfully modulo its whole
center. The original elementary sixteen therefore embeds in the full
automorphism group of every proposed ordinary quotient. The intrinsic
elementary bounds exclude A₆, A₇, PSL₃(3), and prime-field PSL₂(p), p > 3.
All central two-covers and the same selected raw component are retained.

This does not exclude larger binary or higher-field models. No
generation-dependent component record or marked generation is used.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

private theorem no_small_automorphism_quotient
    {H X : Type*} [Group H] [Finite H] [Group.IsPerfect H] [Group X]
    (hcenter : center H = pCore 2 H)
    (A : Subgroup (MulAut H)) [IsElementaryAbelian 2 A] (hcard : Nat.card A = 16)
    (hsmall : ∀ B : Subgroup (MulAut X), IsElementaryAbelian 2 B → Nat.card B ≤ 8)
    (e : (H ⧸ pCore 2 H) ≃* X) : False := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = center H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk',←hcenter]
  let c : PerfectCentralCovering.Cover H X := ⟨q,hq,inferInstance,hk.le⟩
  have hh := hsmall (A.map (c.autMap hk)) (IsElementaryAbelian.map _)
  rw [card_map_of_injective (c.autMap_injective hk),hcard] at hh
  omega

private theorem alternating_seven_automorphism_elementary_bound
    (A : Subgroup (MulAut (alternatingGroup (Fin 7))))
    (hA : IsElementaryAbelian 2 A) : Nat.card A ≤ 8 := by
  let e : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
    MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 7)))
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by decide) (by decide))
  let := hA
  have hh := Representation.AlternatingSevenConjugatePair.ElementaryGeometry.elementary_card_le
    (A := A.map e.symm.toMonoidHom) (IsElementaryAbelian.map _)
  rwa [card_map_of_injective e.symm.injective] at hh

/-- A faithful elementary sixteen in the automorphism group of the actual
perfect central cover excludes the four small ordinary quotient families. -/
theorem raw_ordinary_sixteen_small_quotient_exclusions
    {H : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    (hcenter : center H = pCore 2 H)
    (A : Subgroup (MulAut H)) [IsElementaryAbelian 2 A] (hcard : Nat.card A = 16) :
    ¬ Nonempty ((H ⧸ pCore 2 H) ≃* alternatingGroup (Fin 6)) ∧
    ¬ Nonempty ((H ⧸ pCore 2 H) ≃* alternatingGroup (Fin 7)) ∧
    ¬ Nonempty ((H ⧸ pCore 2 H) ≃* Matrix.PSL3Three.PSL) ∧
    ∀ p : ℕ, p.Prime → 3 < p →
      ¬ Nonempty ((H ⧸ pCore 2 H) ≃* PSL(2,ZMod p)) := by
  refine ⟨?_,?_,?_,?_⟩
  · rintro ⟨e⟩
    exact no_small_automorphism_quotient hcenter A hcard
      (fun B hB => by let := hB; exact AlternatingSix.ShadowLocal.elementary_card_le_eight B) e
  · rintro ⟨e⟩
    exact no_small_automorphism_quotient hcenter A hcard
      alternating_seven_automorphism_elementary_bound e
  · rintro ⟨e⟩
    exact no_small_automorphism_quotient hcenter A hcard
      Matrix.PSL3Three.EightGeometry.elementary_card_le_eight e
  · intro p hp hlarge he
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨e⟩ := he
    apply no_small_automorphism_quotient hcenter A hcard ?_ e
    intro B hB
    have hh := (primeRank_le_iff_elementary_card_le (MulAut PSL(2,ZMod p))).mp
      (Theory.PSL2.primeField_automorphism_two_rank hlarge) B hB
    norm_num at hh
    omega

/-- The same original raw ordinary component excludes the small quotient
families by its actual faithful moving-support action, without M-generation. -/
theorem PreparedChosenModule.decomposable_five_raw_ordinary_small_quotients
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
      ∀ {L : Subgroup G}, L ≤ G1 → IsComponent G1 (L.subgroupOf G1) →
        center L = pCore 2 L →
        R ⊔ ⁅V,R⁆ ≤ normalizer (L : Set G) → ⁅L,⁅V,R⁆⁆ ≠ ⊥ →
        ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
        ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7)) ∧
        ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.PSL3Three.PSL) ∧
        ∀ p : ℕ, p.Prime → 3 < p →
          ¬ Nonempty ((L ⧸ pCore 2 L) ≃* PSL(2,ZMod p)) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive Z1 G1 C R L hLG hLc hcenter hnL hmove
  obtain ⟨hBL,_,hcard⟩ := h.decomposable_five_raw_moving_support_action
    hG T hempty hM hmany hJ hfull c d hd s π hp hs hdec hq hfive hnL hmove
  let B := plane V (c.ambientFactor d s.second).space
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le (plane_le _)
  let : IsElementaryAbelian 2 (internalActionImage B L hBL) :=
    IsElementaryAbelian.of_surjective (actionHom B L hBL).rangeRestrict
      (actionHom B L hBL).rangeRestrict_surjective
  let : IsQuasisimple (L.subgroupOf G1) := hLc.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLG)
  exact raw_ordinary_sixteen_small_quotient_exclusions hcenter
    (internalActionImage B L hBL) hcard

end CFSG.Quasithin.Chapter15.Section01

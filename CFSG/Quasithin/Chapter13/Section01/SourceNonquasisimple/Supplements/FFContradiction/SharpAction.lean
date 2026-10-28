module
public import Theory.Representation.BinaryOffender.SectionSaturation
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction.SharpSection

/-!
# Quadratic action and saturation in the literal candidate

Faithfulness on the simple K-image makes every nonidentity actor element
move the common chief section. Perfect-factor displacement and the sharp
upper bound give a common fixed space for all these elements, hence a
quadratic action. Equality of section and ambient displacement also fixes
the denominator and the quotient above the section. Faithfulness on the
simple K-image promotes both fixedness conclusions to that factor.

The candidate application uses the same Y, Thompson actor, quotient maps,
and chief section. It supplies representation consequences needed for the
remaining tensor recognition and generation steps of Aschbacher--Smith
13.1.9, printed p.871. The controlled normalizer premise still requires the
original Thompson factorization; this is not the final contradiction.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin ChapterB Stellmacher
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
open Chapter1 Chapter1.Section02 Chapter1.Section02.Adequate Chapter12.Section02 ChapterA.Section04 Escape
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

/-- Every nonidentity actor element has the same three-dimensional displacement. -/
theorem common_chief_sharp_quadratic (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L H C Y A : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) (w : RefinedWitness T L H C Y)
    (hTH : (T : Subgroup G) ≤ H) (hAH : canonicalSupplement (T : Subgroup G) L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) {j : ℕ}
    [(commonModule (T : Subgroup G) L Y j).Normal]
    [IsElementaryAbelian 2 (commonModule (T : Subgroup G) L Y j)]
    [IsSimpleGroup (hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j))]
    (ha : CommonActionProperties (T : Subgroup G) L Y j)
    (hA : A ∈ thompsonFamily (radicalSylowCentralizer (T : Subgroup G) L) j)
    (hAn : hatImage (T : Subgroup G) L Y j A ≠ ⊥)
    (c : CommonHatChief (T : Subgroup G) L Y A j)
    (hsharp : fixedCodim (hatRepresentation (T : Subgroup G) L Y j)
      (hatImage (T : Subgroup G) L Y j A) = 3) :
    IsQuadratic (hatRepresentation (T : Subgroup G) L Y j) (hatImage (T : Subgroup G) L Y j A) ∧
      ∀ a ∈ hatImage (T : Subgroup G) L Y j A, a ≠ 1 →
        fixedCodim (hatRepresentation (T : Subgroup G) L Y j) (zpowers a) = 3 ∧
        fixedSpace (hatRepresentation (T : Subgroup G) L Y j) (hatImage (T : Subgroup G) L Y j A) =
          fixedSpace (hatRepresentation (T : Subgroup G) L Y j) (zpowers a) := by
  let := common_canonical_perfect h hmany hL hn (Y := Y) (j := j)
  let := hat_commutator_normal w hTH hAH hTL j
  let := (ha.actor_bound A hA hAn).1.2
  have hcomm : ⁅hatImage (T : Subgroup G) L Y j (canonicalSupplement (T : Subgroup G) L),
      hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j) ⊔
        hatImage (T : Subgroup G) L Y j A⁆ = ⊥ := by
    apply bot_unique
    exact (commutator_mono le_rfl (sup_le
      (map_mono (subgroupOf_mono _ le_sup_left))
      (map_mono (subgroupOf_mono _ (hA.1.trans le_sup_right))))).trans ha.commute.le
  exact c.sharp_quadratic hcomm (common_actor_faithful ha hA) hsharp

/-- The sharp section exhausts displacement on the original binary module. -/
theorem common_chief_fixed_outside {T L Y A : Subgroup G} {j : ℕ}
    [(commonModule T L Y j).Normal] [IsElementaryAbelian 2 (commonModule T L Y j)]
    (c : CommonHatChief T L Y A j)
    (hsection : fixedCodim (sectionRepresentation
      ((hatRepresentation T L Y j).comp
        (CommonChief.actorGroup (hatImage T L Y j (canonicalSupplement T L))
          (hatImage T L Y j (thompsonCommutator T L Y j)) (hatImage T L Y j A)).subtype)
      c.lower c.upper)
      ((hatImage T L Y j A).subgroupOf
        (CommonChief.actorGroup (hatImage T L Y j (canonicalSupplement T L))
          (hatImage T L Y j (thompsonCommutator T L Y j)) (hatImage T L Y j A))) =
      fixedCodim (hatRepresentation T L Y j) (hatImage T L Y j A)) :
    c.lower.toSubmodule ≤ fixedSpace (hatRepresentation T L Y j) (hatImage T L Y j A) ∧
      ∀ a ∈ (hatImage T L Y j A).subgroupOf
        (CommonChief.actorGroup (hatImage T L Y j (canonicalSupplement T L))
          (hatImage T L Y j (thompsonCommutator T L Y j)) (hatImage T L Y j A)),
        ∀ v, c.upper.quotientRepresentation a v = v := by
  have hle : hatImage T L Y j A ≤
      CommonChief.actorGroup (hatImage T L Y j (canonicalSupplement T L))
        (hatImage T L Y j (thompsonCommutator T L Y j)) (hatImage T L Y j A) :=
    le_sup_right.trans le_sup_right
  let F := CommonChief.actorGroup
    (hatImage T L Y j (canonicalSupplement T L))
    (hatImage T L Y j (thompsonCommutator T L Y j)) (hatImage T L Y j A)
  have hfixed := fixedSpace_comp_map (hatRepresentation T L Y j) F.subtype
    ((hatImage T L Y j A).subgroupOf F)
  rw [map_subgroupOf_eq_of_le hle] at hfixed
  have hcod : fixedCodim ((hatRepresentation T L Y j).comp F.subtype)
      ((hatImage T L Y j A).subgroupOf F) =
      fixedCodim (hatRepresentation T L Y j) (hatImage T L Y j A) := by
    unfold fixedCodim
    rw [fixedSpace_comp_map,map_subgroupOf_eq_of_le hle]
  have hsection' : fixedCodim (sectionRepresentation
      ((hatRepresentation T L Y j).comp F.subtype) c.lower c.upper)
      ((hatImage T L Y j A).subgroupOf F) =
      fixedCodim ((hatRepresentation T L Y j).comp F.subtype)
        ((hatImage T L Y j A).subgroupOf F) := hsection.trans hcod.symm
  have h := fixed_outside_section_of_fixedCodim_eq _ c.lower c.upper c.lower_le_upper _ hsection'
  exact ⟨h.1.trans_eq hfixed,h.2⟩

/-- The original candidate now has a quadratic four-group image, uniform
three-dimensional displacement, and actor and K fixedness outside its chief section. -/
theorem candidate_common_chief_quadratic (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : CanonicalStars T) (hrig : QuasisimpleRigidity T)
    (hclass : QuasisimpleClassification T) {L H C : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hH : IsMaximalTwoLocal H) (hTH : (T : Subgroup G) ≤ H)
    (hne : H ≠ normalizer (L : Set G))
    (hC : C ∈ cComponentsIn H) (hAC : canonicalSupplement (T : Subgroup G) L ≤ C)
    {j : ℕ} (hj : j ≤ 1)
    (hN : normalizer (thompsonJ (radicalSylowCentralizer (T : Subgroup G) L) j : Set G) ≤
      normalizer (L : Set G)) :
    j = 1 ∧ ∃ Y : Subgroup G, RefinedWitness T L H C Y ∧
      ∃ n : (commonModule (T : Subgroup G) L Y j).Normal,
        let := n
        ∃ e : IsElementaryAbelian 2 (commonModule (T : Subgroup G) L Y j),
          let := e
          CommonActionProperties (T : Subgroup G) L Y j ∧
          thompsonCommutator (T : Subgroup G) L Y j = Y ∧
          (Nonempty (XiQuotient Y ≃* alternatingGroup (Fin 5)) ∨
            ClassicalGroup.IsPSL (XiQuotient Y) 3 2) ∧
          ∃ A ∈ thompsonFamily (radicalSylowCentralizer (T : Subgroup G) L) j,
            hatImage (T : Subgroup G) L Y j A ≠ ⊥ ∧
            rank (hatImage (T : Subgroup G) L Y j A) = 2 ∧
            fixedCodim (hatRepresentation (T : Subgroup G) L Y j)
              (hatImage (T : Subgroup G) L Y j A) = 3 ∧
            IsQuadratic (hatRepresentation (T : Subgroup G) L Y j)
              (hatImage (T : Subgroup G) L Y j A) ∧
            (∀ a ∈ hatImage (T : Subgroup G) L Y j A, a ≠ 1 →
              fixedCodim (hatRepresentation (T : Subgroup G) L Y j) (zpowers a) = 3 ∧
              fixedSpace (hatRepresentation (T : Subgroup G) L Y j)
                (hatImage (T : Subgroup G) L Y j A) =
                fixedSpace (hatRepresentation (T : Subgroup G) L Y j) (zpowers a)) ∧
            ∃ c : CommonHatChief (T : Subgroup G) L Y A j,
              c.movedSection.rankLoss = 0 ∧
              c.lower.toSubmodule ≤ fixedSpace (hatRepresentation (T : Subgroup G) L Y j)
                (hatImage (T : Subgroup G) L Y j A) ∧
              (∀ a ∈ (hatImage (T : Subgroup G) L Y j A).subgroupOf
                (CommonChief.actorGroup
                  (hatImage (T : Subgroup G) L Y j (canonicalSupplement (T : Subgroup G) L))
                  (hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j))
                  (hatImage (T : Subgroup G) L Y j A)),
                ∀ v, c.upper.quotientRepresentation a v = v) ∧
              c.lower.toSubmodule ≤ fixedSpace (hatRepresentation (T : Subgroup G) L Y j)
                (hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j)) ∧
              ∀ k ∈ (hatImage (T : Subgroup G) L Y j
                  (thompsonCommutator (T : Subgroup G) L Y j)).subgroupOf
                (CommonChief.actorGroup
                  (hatImage (T : Subgroup G) L Y j (canonicalSupplement (T : Subgroup G) L))
                  (hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j))
                  (hatImage (T : Subgroup G) L Y j A)),
                ∀ v, c.upper.quotientRepresentation k v = v := by
  obtain ⟨hj1,Y,w,n,e,ha,hKY,_,hmodel,_,hsimple,A,hA,hAn,_,hr,hcod,c,hε,hsection⟩ :=
    candidate_common_chief_sharp h hmany hs hrig hclass hL hn hH hTH hne hC hAC hj hN
  let := n
  let := e
  let := hsimple
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  obtain ⟨hq,helements⟩ := common_chief_sharp_quadratic h hmany hL hn w hTH
    (hAC.trans hC.1) hTL ha hA hAn c hcod
  have hout := common_chief_fixed_outside c (hsection.trans hcod.symm)
  let := hat_commutator_normal w hTH (hAC.trans hC.1) hTL j
  have hKout := c.factor_fixed_outside (common_actor_faithful ha hA) hAn
    (hsection.trans hcod.symm)
  exact ⟨hj1,Y,w,n,e,ha,hKY,hmodel,A,hA,hAn,hr,hcod,hq,helements,c,hε,hout.1,hout.2,hKout⟩
end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction

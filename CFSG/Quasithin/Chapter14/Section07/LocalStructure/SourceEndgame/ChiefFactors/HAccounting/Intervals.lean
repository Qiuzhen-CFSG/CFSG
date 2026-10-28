module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.HAccounting.DualSection
public import Theory.GroupTheory.NoncentralChiefRefinement.ResidualRestriction.Sections

/-!
# The two marked H-chief intervals and their actual refinements

The literal relative quotient Q_K/C_H(U) inherits one-copy equivariant
coordinates from the constructed dual section. Transitivity of the marked
SL₂(4) on its dual natural module proves chiefness and noncentrality.
Together with U/U₀ this gives the two marked chief intervals in the original
normal filtration 1 ≤ U₀ ≤ U ≤ C_H(U) ≤ Q_K ≤ O₂(H) ≤ H.

Actual complete chief refinements retain every term. Intersecting with the
original L₁ subgroup of H gives another complete chief refinement, allowing
repeated coarse terms. No zero contribution from the other intervals is
assumed here, and this module does not yet assert the total chief count.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 14.7.71, printed p.1075 (PDF p.1092).
-/

public section
noncomputable section
open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.HAccounting
open Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

/-- The source centralizer as an actual normal subgroup of H. -/
@[expose] def cNode : NoncentralChiefRefinement.NormalNode F.H :=
  ⟨(C F).subgroupOf F.H, C_normal d⟩

/-- The original Q_K as an actual normal subgroup of H. -/
@[expose] def qKNode (b : QKDualCoordinates d) : NoncentralChiefRefinement.NormalNode F.H :=
  ⟨(QK F).subgroupOf F.H,
    normal_subgroupOf_of_le_normalizer b.qSection.normalized⟩

/-- The endpoint is the kernel of the original H → S₅ map. -/
@[expose] def coreNode : NoncentralChiefRefinement.NormalNode F.H := ⟨d.qH.ker, inferInstanceAs d.qH.ker.Normal⟩

theorem coreNode_val : (coreNode d).val = (F.H.pCoreIn 2).subgroupOf F.H := d.qH_ker

theorem uNode_le_cNode : uNode d ≤ cNode d := subgroupOf_mono F.H (U_le_C d)

theorem cNode_le_qKNode (b : QKDualCoordinates d) : cNode d ≤ qKNode d b :=
  subgroupOf_mono F.H le_sup_right

theorem qKNode_le_coreNode (hc : d.SectionCentralizer) (b : QKDualCoordinates d) :
    qKNode d b ≤ coreNode d := by
  change (QK F).subgroupOf F.H ≤ d.qH.ker
  rw [d.qH_ker]
  exact subgroupOf_mono F.H (QK_le_QH d hc)

private def dualIntrinsicMap (b : QKDualCoordinates d) :
    (qKNode d b).val →* Multiplicative (Module.Dual (ZMod 2) SL2FourNatural.V) :=
  b.qSection.coordinates.comp (subgroupOfEquivOfLe b.qSection.section_le).toMonoidHom

private theorem dualIntrinsicMap_surjective (b : QKDualCoordinates d) :
    Function.Surjective (dualIntrinsicMap d b) :=
  b.qSection.onto.comp (subgroupOfEquivOfLe b.qSection.section_le).surjective

private theorem dualIntrinsicMap_ker (b : QKDualCoordinates d) :
    (dualIntrinsicMap d b).ker = (cNode d).val.subgroupOf (qKNode d b).val := by
  ext a
  exact b.qSection.coordinates_eq_one_iff ((subgroupOfEquivOfLe b.qSection.section_le) a)

private def oneDualCopy : Multiplicative (Module.Dual (ZMod 2) SL2FourNatural.V) ≃*
    Multiplicative (Fin 1 → Module.Dual (ZMod 2) SL2FourNatural.V) where
  toFun v := Multiplicative.ofAdd (fun _ => v.toAdd)
  invFun v := Multiplicative.ofAdd (v.toAdd 0)
  left_inv _ := rfl
  right_inv v := by
    apply Multiplicative.toAdd.injective
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    rw [hi]
    rfl
  map_mul' _ _ := rfl

/-- Equivariant coordinates on the literal H-normal chief interval Q_K/C. -/
def dualChiefCoordinates (b : QKDualCoordinates d) :
    NoncentralChiefRefinement.SectionCoordinates (cNode d) (qKNode d b) (naturalAction d).dual 1 where
  equiv := ((QuotientGroup.quotientMulEquivOfEq (dualIntrinsicMap_ker d b).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (dualIntrinsicMap d b)
      (dualIntrinsicMap_surjective d b))).trans oneDualCopy
  equivariant h x i := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ x
    exact b.qSection.equivariant h ((subgroupOfEquivOfLe b.qSection.section_le) a)

theorem dualChiefCoordinates_mk (b : QKDualCoordinates d) (a : (qKNode d b).val) (i : Fin 1) :
    ((dualChiefCoordinates d b).equiv
      (QuotientGroup.mk' ((cNode d).val.subgroupOf (qKNode d b).val) a)).toAdd i =
    (b.qSection.coordinates ((subgroupOfEquivOfLe b.qSection.section_le) a)).toAdd := by rfl

theorem dualAction_transitive (a b : Module.Dual (ZMod 2) SL2FourNatural.V)
    (ha : a ≠ 0) (hb : b ≠ 0) : ∃ h : F.H, (naturalAction d).dual h a = b := by
  obtain ⟨v, rfl⟩ := SL2FourNatural.selfDual.surjective a
  obtain ⟨w, rfl⟩ := SL2FourNatural.selfDual.surjective b
  have hv : v ≠ 0 := fun he => ha (he ▸ SL2FourNatural.selfDual.map_zero)
  have hw : w ≠ 0 := fun he => hb (he ▸ SL2FourNatural.selfDual.map_zero)
  obtain ⟨g, hg⟩ := SL2FourNatural.transitive_nonzero v w hv hw
  obtain ⟨k, hk⟩ := d.alternatingActor_lift g
  refine ⟨k.val, ?_⟩
  rw [natural_dual_on_lift d k.val g hk]
  exact (SL2FourNatural.selfDual_equivariant g v).symm.trans
    (congrArg SL2FourNatural.selfDual hg)

theorem dualAction_irreducible : IsIrreducible (naturalAction d).dual := by
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun A => ?_⟩
  by_cases hA : A = ⊥
  · exact Or.inl hA
  right
  have hn : ¬ A ≤ ⊥ := fun h => hA (le_antisymm h bot_le)
  obtain ⟨v, hv, hv0⟩ := SetLike.not_le_iff_exists.mp hn
  apply le_antisymm le_top
  intro w _
  by_cases hw : w = 0
  · rw [hw]
    exact A.toSubmodule.zero_mem
  obtain ⟨h, hh⟩ := dualAction_transitive d v w hv0 hw
  rw [← hh]
  exact A.apply_mem_toSubmodule h hv

theorem dualAction_nontrivial : ∃ h a, (naturalAction d).dual h a ≠ a := by
  obtain ⟨k, hk⟩ := d.alternatingActor_lift (SL2FourNatural.upper 1)
  let v : SL2FourNatural.V := ![0, 1]
  refine ⟨k.val, SL2FourNatural.selfDual v, ?_⟩
  rw [natural_dual_on_lift d k.val _ hk]
  intro he
  have he' : SL2FourNatural.action (SL2FourNatural.upper 1) v = v :=
    SL2FourNatural.selfDual.injective ((SL2FourNatural.selfDual_equivariant _ _).trans he)
  rw [SL2FourNatural.upper_action] at he'
  have hh0 := congrFun he' 0
  change (0 : SL2FourNatural.F) + 1 * 1 = 0 at hh0
  simp at hh0

/-- The actual dual interval is chief; it is not an assumed factor-count tag. -/
theorem dual_chief (b : QKDualCoordinates d) :
    ChiefFactor.IsChief ((QK F).subgroupOf F.H) ((C F).subgroupOf F.H) := by
  let := dualAction_irreducible d
  exact (NoncentralChiefRefinement.covBy_iff_isChief _ _).mp
    ((dualChiefCoordinates d b).covBy (cNode_le_qKNode d b) (dualAction_nontrivial d))

theorem dual_noncentral_two (b : QKDualCoordinates d) :
    NoncentralChiefRefinement.IsNoncentralTwo (cNode d) (qKNode d b) :=
  ⟨(dualChiefCoordinates d b).isPGroup,
    (dualChiefCoordinates d b).not_isCentral (by decide) (dualAction_nontrivial d)⟩

open NoncentralChiefRefinement

/-- The genuine source filtration. Its zero-count intervals have not been
replaced by central or elementary hypotheses. -/
@[expose] def sourceFiltration (hc : d.SectionCentralizer) (b : QKDualCoordinates d) :
    Filtration F.H 6 where
  term := ![⊥, fixedNode d, uNode d, cNode d, qKNode d b, coreNode d, ⊤]
  monotone := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    fin_cases i
    · exact bot_le
    · exact fixedNode_le_uNode d
    · exact uNode_le_cNode d
    · exact cNode_le_qKNode d b
    · exact qKNode_le_coreNode d hc b
    · exact le_top

/-- An actual complete H-chief refinement retaining both literal marked
intervals, their denominators, and the original two-core. -/
theorem exists_complete_source_refinement (hc : d.SectionCentralizer)
    (b : QKDualCoordinates d) :
    ∃ (s : ChiefSeries F.H) (ι : Fin 7 →o Fin (s.length + 1)),
      (∀ i, s (ι i) = (sourceFiltration d hc b).term i) ∧
      ι 0 = 0 ∧ ι (Fin.last 6) = Fin.last s.length ∧
      s.head = ⊥ ∧ s.last = ⊤ := by
  obtain ⟨s, ι, hi, hi0, hi1⟩ := exists_refinement (sourceFiltration d hc b)
  refine ⟨s, ι, hi, hi0, hi1, ?_, ?_⟩
  · have h := hi 0
    rw [hi0] at h
    exact h
  · have h := hi (Fin.last 6)
    rw [hi1] at h
    exact h

/-- Restriction uses the original relative subgroup L₁ ≤ H and intersects
all seven source terms with it. Repeated terms are allowed after restriction. -/
theorem exists_complete_L₁_refinement (hc : d.SectionCentralizer)
    (b : QKDualCoordinates d) :
    ∃ (s : ChiefSeries ((F.Li L 1).subgroupOf F.H))
      (ι : Fin 7 →o Fin (s.length + 1)),
      (∀ i, s (ι i) = restrictNormalNode ((F.Li L 1).subgroupOf F.H)
        ((sourceFiltration d hc b).term i)) ∧
      ι 0 = 0 ∧ ι (Fin.last 6) = Fin.last s.length ∧
      s.head = ⊥ ∧ s.last = ⊤ := by
  obtain ⟨s, ι, hi, hi0, hi1, hs0, hs1⟩ := exists_complete_source_refinement d hc b
  obtain ⟨t, κ, hk, hk0, hk1, ht0, ht1⟩ :=
    s.exists_complete_restriction_refinement ((F.Li L 1).subgroupOf F.H) hs0 hs1
  refine ⟨t, κ.comp ι, ?_, ?_, ?_, ht0, ht1⟩
  · intro i
    exact (hk (ι i)).trans (congrArg (restrictNormalNode _) (hi i))
  · change κ (ι 0) = 0
    rw [hi0, hk0]
  · change κ (ι (Fin.last 6)) = Fin.last t.length
    rw [hi1, hk1]

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.HAccounting

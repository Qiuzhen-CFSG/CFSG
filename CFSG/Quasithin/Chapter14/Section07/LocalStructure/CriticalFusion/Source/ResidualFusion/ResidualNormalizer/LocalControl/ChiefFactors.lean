module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.LocalControl.Preparation
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.LeftChiefFactors.SourceFiltration
public import Theory.GroupTheory.NoncentralChiefRefinement.ResidualRestriction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.LeftChiefFactors.BorelRefinements.SourceChief
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.LeftChiefFactors.SourceBorel
public import Theory.GroupTheory.NoncentralChiefRefinement.ResidualRestriction.Comparison


/-!
# Four noncentral binary chief factors on the original L₁

The natural map is the original projection on U/V₁, composed with its
literal conjugation coordinates. Its kernel is U₀. Restrict the actor to
L₁T without changing that map. The genuine 14.5.21 duality supplies a dual
natural submodule of Q_H/C_{Q_H}(U); its functional formula uses the same
projection. The imported central-cover argument proves C_U(Q_H) ≤ U₀,
which justifies passage through U/C_U(Q_H) without identifying it with U/V₁.

The marked Borel flag and its annihilator give two noncentral binary chief
factors on each of the original natural and dual sections. Since
U ≤ C_{Q_H}(U), their chief refinements concatenate across an actual normal
interval and extend to a complete chief series of L₁T with count at least
four. Intersecting with O²(L₁T) and refining preserves this lower bound:
noncentral binary chief sections survive a normal restriction with two-group
quotient, and two-perfectness forces a noncentral chief factor in each
surviving interval. The ambient inclusion identifies O²(L₁T) with the
literal F.Li L 1. A complete series retaining all original intersected
strata has the same count by equivariant Jordan–Hölder.

The final application supplies SectionCentralizer and Borel compatibility
from the proved local-kernel and marking adapters. It retains the genuine
Structural1222 and Uniqueness127 inputs (qt-12-02 and
qt-1-02-adequate-assembly), the original UpperMarking from the earlier
14.3/14.7 source setup, and SourceDuality with [U,Q_H]=V₁ from
qt-14-05-terminal-duality. No chief count or Baumann-normalizer conclusion
is an input. The parent qt-14-07-residual-local-control retains the earlier
source-input discharge and the application of universal 14.7.10 from
qt-14-07-solvable; this module proves its four-factor branch.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.5.21, printed pp.1019–1020; proof of 14.7.67(4), printed p.1070
(PDF p.1087), applying the alternative of 14.7.10.
-/

@[expose] public section

open Subgroup Representation NoncentralChiefRefinement
open scoped commutatorElement
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualNormalizer.ChiefFactors
open Chapter12.Section08
open Rechoice.Goldschmidt
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

local notation "B" => (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G)

omit [Finite G] in
theorem actor_le_H : B ≤ F.H :=
  sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)

omit [Finite G] in
theorem core_le_actor : F.H.pCoreIn 2 ≤ B :=
  ((pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))).trans_eq
    (map_subgroupOf_eq_of_le (F.invariant 1))).trans le_sup_right

variable (d : Data T L V F W)

/-- The source star marking restricted along the literal inclusion L₁T ≤ H. -/
def actorMap : B →* ChapterJ.S5 := d.qH.comp (inclusion actor_le_H)

theorem actorMap_ker : (actorMap d).ker = (F.H.pCoreIn 2).subgroupOf B := by
  ext b
  change inclusion actor_le_H b ∈ d.qH.ker ↔ (b : G) ∈ F.H.pCoreIn 2
  rw [d.qH_ker]
  rfl

def naturalAction : Representation (ZMod 2) B Representation.SL2FourNatural.V :=
  (d.naturalQuotient.action.comp d.qH).comp (inclusion actor_le_H)

def naturalCoordinates : F.U →* Multiplicative Representation.SL2FourNatural.V :=
  d.projection.toLinearMap.toAddMonoidHom.toMultiplicative.comp
    d.conjugationSection.coordinates

theorem naturalCoordinates_surjective : Function.Surjective (naturalCoordinates d) := by
  intro w
  obtain ⟨v, hv⟩ := d.projection_onto w.toAdd
  obtain ⟨x, hx⟩ := d.conjugationSection.onto (Multiplicative.ofAdd v)
  refine ⟨x, Multiplicative.toAdd.injective ?_⟩
  change d.projection (d.conjugationSection.coordinates x).toAdd = w.toAdd
  rw [hx]
  exact hv

theorem naturalCoordinates_ker : (naturalCoordinates d).ker = d.U₀.subgroupOf F.U := by
  ext x
  exact (d.mem_U₀ x).symm

/-- The original natural quotient, with actor restricted to the actual L₁T. -/
def naturalSection (hc : d.SectionCentralizer) :
    BinaryConjugationSection B F.U d.U₀ (naturalAction d) where
  section_le := (LeftChiefFactors.source_filtration_containments d hc).2.1.trans
    ((LeftChiefFactors.source_filtration_containments d hc).2.2.1.trans core_le_actor)
  kernel_le := d.U₀_le_U
  normalized := actor_le_H.trans d.conjugationSection.normalized
  coordinates := naturalCoordinates d
  onto := naturalCoordinates_surjective d
  kernel_eq := naturalCoordinates_ker d
  equivariant b v := by
    exact (congrArg d.projection
      (d.conjugationSection.equivariant (inclusion actor_le_H b) v)).trans
        (LinearMap.congr_fun (d.projection.isIntertwining' (inclusion actor_le_H b)) _)

theorem naturalSection_coordinates (hc : d.SectionCentralizer) (v : F.U) :
    ((naturalSection d hc).coordinates v).toAdd =
      d.projection (d.conjugationSection.coordinates v).toAdd := rfl

variable {X Y : Type u} [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]
  (s : CriticalIntersections.SourceDuality F X Y)

def dualSection : BinaryConjugationSection B (F.H.pCoreIn 2)
    (F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G))
    (s.qAction.comp (inclusion actor_le_H)) where
  section_le := core_le_actor
  kernel_le := s.qSection.kernel_le
  normalized := actor_le_H.trans s.qSection.normalized
  coordinates := s.qSection.coordinates
  onto := s.qSection.onto
  kernel_eq := s.qSection.kernel_eq
  equivariant b v := s.qSection.equivariant (inclusion actor_le_H b) v

/-- The dual embedding uses the same natural projection and the source pairing. -/
theorem exists_dual_embedding (hc : d.SectionCentralizer)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    ∃ j : Representation.IntertwiningMap (naturalAction d).dual
        (s.qAction.comp (inclusion actor_le_H)),
      Function.Injective j ∧
      ∀ (a : Module.Dual (ZMod 2) Representation.SL2FourNatural.V) (v : F.U),
        s.duality (j a) (s.uSection.coordinates v).toAdd =
          a (d.projection (d.conjugationSection.coordinates v).toAdd) := by
  obtain ⟨j, hj, he⟩ := LeftChiefFactors.exists_dual_natural_embedding d hc s hcomm
  let j' : Representation.IntertwiningMap (naturalAction d).dual
      (s.qAction.comp (inclusion actor_le_H)) :=
    j.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _ (by
      intro b a
      exact LinearMap.congr_fun (j.isIntertwining' (inclusion actor_le_H b)) a)
  exact ⟨j', hj, he⟩

/-- The two source sections occupy disjoint ordered intervals. -/
theorem U_le_dual_kernel (hc : d.SectionCentralizer) :
    F.U ≤ F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G) := by
  rw [LeftChiefFactors.q_centralizer_eq_h_centralizer d hc]
  exact (LeftChiefFactors.source_filtration_containments d hc).2.1

/-- The embedded two-residual of the actual actor is L₁. -/
theorem residual_actor (hTM : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (pResidual 2 B).map (B).subtype = F.Li L 1 :=
  embedded_pResidual_join_pGroup _ _ Li_twoPerfect T.isPGroup' (T_normalizes_Li hTM)

/-- The isomorphism to L₁ is induced by the original ambient inclusion. -/
def residualEquiv (hTM : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    pResidual 2 B ≃* F.Li L 1 :=
  (equivMapOfInjective (pResidual 2 B) (B).subtype (B).subtype_injective).trans
    (MulEquiv.subgroupCongr (residual_actor hTM))

@[simp] theorem residualEquiv_apply
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G)) (x : pResidual 2 B) :
    (residualEquiv hTM x : G) = (x.val : G) := rfl

/-- The transported restricted node is the literal intersection with L₁.
The formula fixes both subtype inclusions, not just an abstract actor model. -/
theorem mem_transported_restriction
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (A : NormalNode B) (x : F.Li L 1) :
    x ∈ (actorNormalEquiv (residualEquiv hTM)
      (restrictNormalNode (pResidual 2 B) A)).val ↔
      (x : G) ∈ A.val.map (B).subtype := by
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r.val, hr, (residualEquiv_apply hTM r).symm⟩
  · rintro ⟨b, hb, he⟩
    let r := (residualEquiv hTM).symm x
    have hrx : ((r.val : B) : G) = (x : G) :=
      (residualEquiv_apply hTM r).symm.trans
        (congrArg Subtype.val ((residualEquiv hTM).apply_symm_apply x))
    have hrb : r.val = b := Subtype.ext (hrx.trans he.symm)
    refine ⟨r, ?_, (residualEquiv hTM).apply_symm_apply x⟩
    change r.val ∈ A.val
    rw [hrb]
    exact hb

/-- All original terms are retained when refining in the actual residual. -/
theorem exists_original_refinement (hc : d.SectionCentralizer)
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ∃ (t : ChiefSeries (F.Li L 1)) (ι : Fin 6 →o Fin (t.length + 1)),
      (∀ i, t (ι i) = actorNormalEquiv (residualEquiv hTM)
        (restrictNormalNode (pResidual 2 B) ((LeftChiefFactors.sourceFiltration d hc).term i))) ∧
      ι 0 = 0 ∧ ι (Fin.last 5) = Fin.last t.length ∧
      t.head = ⊥ ∧ t.last = ⊤ := by
  let f : Filtration (pResidual 2 B) 5 := {
    term i := restrictNormalNode (pResidual 2 B) ((LeftChiefFactors.sourceFiltration d hc).term i)
    monotone := (restrictNormalNode_monotone _).comp (LeftChiefFactors.sourceFiltration d hc).monotone }
  obtain ⟨t, ι, hi, hi0, hi1⟩ := exists_refinement f
  have ht0 : t.head = ⊥ := by
    have h := hi 0
    rw [hi0] at h
    exact h.trans (restrictNormalNode_bot _)
  have ht1 : t.last = ⊤ := by
    have h := hi (Fin.last 5)
    rw [hi1] at h
    exact h.trans (restrictNormalNode_top _)
  refine ⟨t.mapActor (residualEquiv hTM), ι, ?_, hi0, hi1,
    (t.mapActor_complete _ ht0 ht1).1, (t.mapActor_complete _ ht0 ht1).2⟩
  intro i
  exact congrArg (actorNormalEquiv (residualEquiv hTM)) (hi i)

/-- Local action survival and refinement suffice to transfer the complete
series and its lower count to the literal L₁, without a critical-path choice. -/
theorem count_transfer_of_local_survival
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (s₀ : ChiefSeries B) (h0 : s₀.head = ⊥) (h1 : s₀.last = ⊤)
    (hsection : ∀ A C : NormalNode B, A ⋖ C → IsNoncentralTwo A C →
      IsNoncentralTwo (restrictNormalNode (pResidual 2 B) A)
        (restrictNormalNode (pResidual 2 B) C))
    (hrefine : ∀ t : ChiefSeries (pResidual 2 B), IsNoncentralTwo t.head t.last →
      ∃ i : Fin t.length, IsNoncentralTwo (t i.castSucc) (t i.succ)) :
    ∃ t : ChiefSeries (F.Li L 1), t.head = ⊥ ∧ t.last = ⊤ ∧
      s₀.noncentralTwoCount ≤ t.noncentralTwoCount := by
  obtain ⟨t, _, _, _, _, ht0, ht1, hc⟩ :=
    s₀.exists_comparison_of_restriction_survival (pResidual 2 B) h0 h1
      (fun i => hsection _ _ (s₀.step i)) hrefine
  refine ⟨t.mapActor (residualEquiv hTM), (t.mapActor_complete _ ht0 ht1).1,
    (t.mapActor_complete _ ht0 ht1).2, ?_⟩
  rw [t.mapActor_noncentralTwoCount]
  exact hc

/-- Restriction to the actual two-residual cannot decrease the noncentral
binary count. Both local survival premises are now discharged. -/
theorem count_transfer
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (s₀ : ChiefSeries B) (h0 : s₀.head = ⊥) (h1 : s₀.last = ⊤) :
    ∃ t : ChiefSeries (F.Li L 1), t.head = ⊥ ∧ t.last = ⊤ ∧
      s₀.noncentralTwoCount ≤ t.noncentralTwoCount :=
  count_transfer_of_local_survival hTM s₀ h0 h1
    isNoncentralTwo_restrict_pResidual
    (fun t => t.exists_noncentralTwo_pResidual)

open LeftChiefFactors LeftChiefFactors.BorelRefinements

include s

/-- Concatenate the natural and dual chief refinements across the literal
interval U ≤ C_H(U), then extend to a complete series of L₁T. These are the
two distinct contributions in the Baumann paragraph of 14.7.67(4). -/
theorem exists_actor_four_chief_factors
    (h : CompatibleBorel d) (hc : d.SectionCentralizer)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    ∃ t : ChiefSeries B, t.head = ⊥ ∧ t.last = ⊤ ∧
      4 ≤ t.noncentralTwoCount := by
  obtain ⟨a, ha0, hal, ha⟩ := exists_sourceNaturalChief d h hc
  obtain ⟨b, hb0, hbl, hb⟩ := exists_sourceDualChief d h hc s hcomm
  obtain ⟨m, hm0, hml⟩ := exists_chiefSeries (sourceUNode d)
    (sourceCentralizerNode d)
    (fun _ hx => (source_filtration_containments d hc).2.1 hx)
  have ham : a.last = m.head := hal.trans hm0.symm
  have hamb : (a.smash m ham).last = b.head :=
    (RelSeries.last_smash ham).trans (hml.trans hb0.symm)
  let c : ChiefSeries B := (a.smash m ham).smash b hamb
  have hc0 : c.head = sourcePointNode (F := F) (L := L) := by
    simpa only [c, RelSeries.head_smash] using ha0
  have hcl : c.last = sourceQNode (F := F) (L := L) := by
    simpa only [c, RelSeries.last_smash] using hbl
  have hcount : 4 ≤ c.noncentralTwoCount := by
    dsimp only [c]
    rw [ChiefSeries.noncentralTwoCount_smash, ChiefSeries.noncentralTwoCount_smash]
    omega
  obtain ⟨t, ht0, htl, ht⟩ := BinaryFlag.extend_count bot_le le_top c hc0 hcl
  exact ⟨t, ht0, htl, hcount.trans ht⟩

/-- Four noncentral binary factors occur in an actual complete L₁-chief
series retaining every intersected original source stratum. The equivalence
and membership formula above identify these nodes by ambient inclusion. -/
theorem exists_original_four_refinement
    (h : CompatibleBorel d) (hc : d.SectionCentralizer)
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    ∃ (t : ChiefSeries (F.Li L 1)) (ι : Fin 6 →o Fin (t.length + 1)),
      (∀ i, t (ι i) = actorNormalEquiv (residualEquiv hTM)
        (restrictNormalNode (pResidual 2 B) ((sourceFiltration d hc).term i))) ∧
      ι 0 = 0 ∧ ι (Fin.last 5) = Fin.last t.length ∧
      t.head = ⊥ ∧ t.last = ⊤ ∧ 4 ≤ t.noncentralTwoCount := by
  obtain ⟨a, ha0, hal, ha⟩ := exists_actor_four_chief_factors d s h hc hcomm
  obtain ⟨b, hb0, hbl, hb⟩ := count_transfer hTM a ha0 hal
  obtain ⟨t, ι, hi, hi0, hil, ht0, htl⟩ := exists_original_refinement d hc hTM
  refine ⟨t, ι, hi, hi0, hil, ht0, htl, ?_⟩
  rw [t.noncentralTwoCount_eq b (ht0.trans hb0.symm) (htl.trans hbl.symm)]
  exact ha.trans hb

/-- The precise chief-series input to 14.7.10 on the original L₁. The source
upper-root marking supplies Borel compatibility; the proved earlier local
kernel supplies SectionCentralizer. The only remaining source inputs are
12.2.2, 1.2.7, the original 14.7.65 marking, and 14.5.21(1–2). -/
theorem exists_four_chief_factors_of_earlier_setup
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Chapter12.Section08.Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (mark : Rechoice.LocalGeometry.Preparation.UpperMarking d)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    ∃ t : ChiefSeries (F.Li L 1), t.head = ⊥ ∧ t.last = ⊤ ∧
      4 ≤ t.noncentralTwoCount := by
  obtain ⟨t, _, _, _, _, ht0, htl, ht⟩ := exists_original_four_refinement d s
    (compatibleBorel_of_upperMarking d structural mark)
    (d.sectionCentralizer_of_earlier_setup structural uniqueness)
    (d.natural.sylow_normalizes structural) hcomm
  exact ⟨t, ht0, htl, ht⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualNormalizer.ChiefFactors

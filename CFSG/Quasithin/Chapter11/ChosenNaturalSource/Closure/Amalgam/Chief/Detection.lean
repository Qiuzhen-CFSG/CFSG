module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief.Action
public import Theory.Representation.BinaryOffender.MarkedChiefDetection

/-!
# Detecting the conjugated generalized-Fitting lift on a chief section

The common kernel of a chief flag maps to a normal two-subgroup of the
faithful action image. Thus a marked subgroup not absorbed by that two-core
survives on an actual section A covered by B. This argument does not require
the whole action image to have trivial two-core.

The source marker is the conjugate of the actual preimage of F*(K/O2(K)),
embedded in (KT)^g. The joint selector applies the same argument to the commutator with the seed.
The separate joint-detection extension proves that this commutator survives
outside the two-core, using the kernel bound and the seed outside O₂.
Neither statement is assumed to follow merely from OddPair.axis.
Source: Aschbacher--Smith, last paragraph of 11.5.8, printed p.784.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief
open Chapter12.Section02

private theorem exists_chief_not_killed
    {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] [Nontrivial W] (ρ : Representation (ZMod 2) H W) (F : Subgroup H)
    (hF : ¬ F ≤ (pCore 2 (actionImage ρ)).comap (actionHom ρ)) :
    ∃ A B : Subrepresentation ρ, A ⋖ B ∧ ¬ F ≤ (sectionRepresentation ρ A B).ker := by
  classical
  obtain ⟨c,n,hmono,hzero,hlast,hchief⟩ := exists_chief_flag ρ
  by_contra hbad
  have hall : ∀ i, i < n → F ≤ (sectionRepresentation ρ (c i) (c (i+1))).ker := by
    intro i hi
    by_contra hnot
    exact hbad ⟨c i,c (i+1),hchief i hi,hnot⟩
  let K : Subgroup H := ⨅ i : Fin n, (sectionRepresentation ρ (c i) (c (i+1))).ker
  let : K.Normal := normal_iInf_normal fun i => inferInstance
  let J := K.map (actionHom ρ)
  let : J.Normal := Normal.map inferInstance _ ρ.asGroupHom.rangeRestrict_surjective
  let W' : Fin (n+1) → Submodule (ZMod 2) W := fun i => (c i).toSubmodule
  have hJF : J ≤ BinaryRadical.flagKernel (imageRepresentation ρ) W' := by
    rintro _ ⟨g,hg,rfl⟩
    have hg' : ∀ i : Fin n, g ∈ (sectionRepresentation ρ (c i) (c (i+1))).ker :=
      mem_iInf.mp hg
    refine ⟨(BinaryRadical.mem_flagStabilizer _ W').mpr (fun i v => ?_),?_⟩
    · constructor
      · intro hv
        have hh := (c i).apply_mem_toSubmodule g⁻¹ hv
        simpa only [imageRepresentation_actionHom, ←Module.End.mul_apply, ←map_mul,
          inv_mul_cancel, map_one, Module.End.one_apply] using hh
      · intro hv
        exact (c i).apply_mem_toSubmodule g hv
    · intro i v hv
      exact (sectionRepresentation_trivial_iff ρ (c i) (c (i+1)) g).mp
        (fun w => LinearMap.congr_fun (hg' i) w) v hv
  have hJp := (BinaryRadical.flagKernel_isPGroup (imageRepresentation ρ)
    (imageRepresentation_injective ρ) W'
    (by change (c 0).toSubmodule = ⊥; rw [hzero]; rfl)
    (by change (c n).toSubmodule = ⊤; rw [hlast]; rfl)).to_le hJF
  have hJcore : J ≤ pCore 2 (actionImage ρ) := le_sSup ⟨inferInstance,hJp⟩
  apply hF
  intro f hf
  exact hJcore (mem_map_of_mem (actionHom ρ) (mem_iInf.mpr fun i => hall i i.isLt hf))

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Closure.Geometry D) (g : G)

/-- The literal O₂,F*(K) embedded in the original ambient group. -/
def fittingLift : Subgroup G :=
  ((generalizedFitting (E.K ⧸ pCore 2 E.K)).comap
    (QuotientGroup.mk' (pCore 2 E.K))).map E.K.subtype

/-- The conjugated lift, as a subgroup of the actual chief-section actor. -/
def markedFitting : Subgroup (actor E g) :=
  ((fittingLift E).map (MulAut.conj g).toMonoidHom).subgroupOf (actor E g)

theorem fittingLift_le : fittingLift E ≤ E.K := map_subtype_le _

theorem markedFitting_map : (markedFitting E g).map (actor E g).subtype =
    (fittingLift E).map (MulAut.conj g).toMonoidHom :=
  map_subgroupOf_eq_of_le (map_mono ((fittingLift_le E).trans le_sup_left))

variable [IsElementaryAbelian 2 (localClosure E)]

/-- A subgroup whose faithful image is not absorbed by O₂ survives on a
literal chief section. No trivial-two-core premise is imposed on the whole action. -/
theorem exists_fitting_chief_section
    (hF : ¬ markedFitting E g ≤
      (pCore 2 (actionImage (action E g))).comap (actionHom (action E g))) :
    ∃ A B : Subrepresentation (action E g), A ⋖ B ∧
      ¬ markedFitting E g ≤ (sectionRepresentation (action E g) A B).ker := by
  have hU : closure E g ≠ ⊥ := by
    intro he
    have hu : localClosure E = ⊥ :=
      ((localClosure E).map_eq_bot_iff_of_injective (MulAut.conj g).injective).mp he
    exact D.ne_bot (bot_unique ((le_conjugateSpanBy V (KT E)).trans hu.le))
  let : Nontrivial (closure E g) := (Subgroup.nontrivial_iff_ne_bot _).mpr hU
  exact exists_chief_not_killed (action E g) (markedFitting E g) hF

/-- Detect the fitting lift and a seed on the same chief section by detecting
 their commutator. The whole-action core remains in the precise premise. -/
theorem exists_joint_fitting_chief_section (p : OddPair E g)
    (hc : ¬ ⁅markedFitting E g, (seed E g p).range⁆ ≤
      (pCore 2 (actionImage (action E g))).comap (actionHom (action E g))) :
    ∃ A B : Subrepresentation (action E g), A ⋖ B ∧
      ¬ markedFitting E g ≤ (sectionRepresentation (action E g) A B).ker ∧
      ∃ v : V, seed E g p v ∉ (sectionRepresentation (action E g) A B).ker := by
  have hU : closure E g ≠ ⊥ := by
    intro he
    have hu : localClosure E = ⊥ :=
      ((localClosure E).map_eq_bot_iff_of_injective (MulAut.conj g).injective).mp he
    exact D.ne_bot (bot_unique ((le_conjugateSpanBy V (KT E)).trans hu.le))
  let : Nontrivial (closure E g) := (Subgroup.nontrivial_iff_ne_bot _).mpr hU
  obtain ⟨A,B,hAB,hmove⟩ := exists_chief_not_killed (action E g)
    ⁅markedFitting E g, (seed E g p).range⁆ hc
  refine ⟨A,B,hAB,?_,?_⟩
  · intro hF
    exact hmove ((commutator_mono hF le_rfl).trans (commutator_le_left _ _))
  · by_contra hv
    have hS : (seed E g p).range ≤ (sectionRepresentation (action E g) A B).ker := by
      rintro _ ⟨v,rfl⟩
      exact not_not.mp (fun hn => hv ⟨v,hn⟩)
    exact hmove ((commutator_mono le_rfl hS).trans (commutator_le_right _ _))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief

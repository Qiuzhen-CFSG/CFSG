module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentNonsplit
public import CFSG.Quasithin.Chapter3.Section02.SourceComponentThompson
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# Thompson generation of the nonsolvable fixed-core component

The original 13.3.2 quotient list makes K/O₂(K) quasisimple, including
its literal three-cover row. The two distinct maximal local normalizers,
and C_G(Ω₁Z(T)) ≤ C_G(z) ≤ N_G(K), then supply all hypotheses of the
proved Chapter 3 Thompson-generation theorem. Thus K=[K,J(T)] follows
for the same selected component, without an additional generation premise.

The nonsplit application constructs its whole augmentation-core marking,
fixed line and full order-four central seed using these deductions. Only
the genuine earlier 12.2/13.3 clauses and the nonzero-fixed-space branch
remain explicit. Their source producers are qt-d-1222-source and
qt-d-1332-source, with final discharge by qt-d-1341-fixed-core-source.
The fixed-free exclusions and 13.4.10–17 assembly remain with
qt-d-1341-nonsolvable-source. Nonsolvability at both original weights is
still required in that assembly.

Source: Aschbacher–Smith 13.3.2(1), 13.4.6(3), 13.4.10(4–5),
printed pp.885,899,907–909; the Chapter 3 application uses 3.1.8 and 3.2.3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L K V : Subgroup G}

private theorem quasisimple_of_simple_perfect (Q : Type*) [Group Q]
    [Group.IsPerfect Q] [IsSimpleGroup Q] : IsQuasisimple Q where
  simple := ((QuotientGroup.quotientMulEquivOfEq
    (center_eq_bot_of_simple_perfect (G := Q))).trans QuotientGroup.quotientBot).isSimpleGroup

omit [Finite G] in
/-- The actual five quotient models of 13.3.2 are quasisimple. -/
theorem component_quotient_quasisimple
    (h1332 : Source1332OneTwo T)
    (hfK : K ∈ MainForward.faithfulLocalComponents T) :
    IsQuasisimple (K ⧸ pCore 2 K) := by
  let : Group.IsPerfect (K.subgroupOf (K ⊔ (T : Subgroup G))) := hfK.1.1.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show K ≤ K ⊔ (T : Subgroup G) from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show K ≤ K ⊔ (T : Subgroup G) from le_sup_left)).surjective
  let Q := K ⧸ pCore 2 K
  let : Group.IsPerfect Q := inferInstance
  rcases (h1332 K hfK).2 with ⟨⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩ | ⟨⟨e⟩⟩ | hc |
    ⟨F,_,_,J,hF,hJ,⟨e⟩⟩
  · let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    let : IsSimpleGroup Q := e.isSimpleGroup
    exact quasisimple_of_simple_perfect Q
  · let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :=
      Atlas.psl_simple_high_rank 3 (by decide)
    let : IsSimpleGroup Q := e.isSimpleGroup
    exact quasisimple_of_simple_perfect Q
  · let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    let : IsSimpleGroup Q := e.isSimpleGroup
    exact quasisimple_of_simple_perfect Q
  · exact hc.1
  · let : IsSimpleGroup (commutator (Atlas.G2.Model (ZMod 2))) :=
      Atlas.G2.isSimple_commutator_binary
    let : IsSimpleGroup Q := (e.trans (J.projectiveEquivBinaryG2Derived hF hJ)).isSimpleGroup
    exact quasisimple_of_simple_perfect Q

/-- The original two maximal normalizers supply the genuine Chapter 3 generation
premises for the same component selected in C_G(z). -/
theorem component_thompson_generation
    {D : ChosenModule T L V}
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (h1332 : Source1332OneTwo T) {z : G}
    (hzT : z ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hHN : centralizer ({z} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T) :
    ⁅K,elementaryAbelianMaxJ (T : Subgroup G)⁆ = K := by
  have hTK := (h1332 K hfK).1
  have hstar := Section03.Noncentrality.source1332_faithful_maximal h₀.qtke T h1332 hfK
  have hqK := component_quotient_quasisimple h1332 hfK
  have huni := Chapter1.Section02.nonsolvable_uniqueness_knownSimple h₀.qtke T hstar
  have horb : componentOrbit K (T : Subgroup G) = K :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer K _ K le_rfl hTK)
      (le_componentOrbit K _)
  have hN : IsMaximalTwoLocal (normalizer (K : Set G)) := horb ▸ huni.normalizer_maximal
  have hM := h.source_normalizer_maximal_unique structural
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have hout : Chapter3.HasMaximalOutside T (normalizer (K : Set G)) :=
    Chapter3.hasMaximalOutside_of_two_distinct hN hM.1 hTK D.sylow_normalizes_component
      (by intro he; exact hKM (he.symm ▸ K.le_normalizer))
  have hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤
      normalizer (K : Set G) :=
    (centralizer_le (Set.singleton_subset_iff.mpr hzT)).trans hHN
  exact Chapter3.Section02.source_component_thompson_generation h₀.qtke T K hstar
    ((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T K).mp hfK).2
    hqK hTK hout hC

/-- The original selected-component geometry discharges both quasisimplicity and
Thompson generation in the nonsplit whole-module marking and full-seed application.
Only the genuine earlier source clauses and the nonzero-fixed-space branch remain. -/
theorem component_core_marking_of_source_fixed
    {D : ChosenModule T L V}
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    {z : G} (hzV : z ∈ V)
    (hzT : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hKz : K ≤ centralizer ({z} : Set G))
    (hHN : centralizer ({z} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (hfixed : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ :
      Subgroup G) ⊓ centralizer (K : Set G) ≠ ⊥) :
    let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
    ∃ DK : ChosenModule T K U, Nonempty (CoreMarking DK) ∧
      U ⊓ centralizer (K : Set G) = zpowers z ∧
      U = ⁅(ReducedModule (K ⊔ (T : Subgroup G))).map
        (K ⊔ (T : Subgroup G)).subtype,K⁆ ∧
      Nonempty (ComponentModuleAt DK z) ∧
      omegaOneCenterAmbient (T : Subgroup G) =
        V ⊓ omegaOneCenterAmbient (T : Subgroup G) ∧
      Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4 := by
  have hqK := component_quotient_quasisimple h1332 hfK
  have hgen := component_thompson_generation (D := D) h₀ h structural h1332 hzT hHN hKM hfK
  exact component_core_marking_of_moved_fixed h₀ h structural m fixed hindex hzV hzT hz1
    hKz (h1332 K hfK).1 hKM hfK hqK hgen hfixed

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable

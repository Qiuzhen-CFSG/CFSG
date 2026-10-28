module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityHigherIntrinsicQuotients
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Definitions
public import Theory.GroupTheory.SylowOvergroupSolvability
public import Theory.SpecificGroups.G2Even.BinaryDerivedSolvableOvergroups

/-!
# Applying the seven-module source theorem to the actual containing chain

Use the original full Sylow to restrict Y≤Y_R≤Y₀ to Y₀T. If proper Sylow
overgroups of Y₀ are solvable, the smaller local component is all of Y₀.
The actual SL₃(2), G₂(2)′ and hexacode quotients have this property; so do
the A₅ and A₆ action quotients. For the latter, the kernel in the quasisimple
two-core quotient is central, rather than being identified with O₂(Y₀).

Applying the authorized universal seven-module theorem to a quasisimple
maximal Y₀ leaves only the larger binary and alternating rows, with all
original action equivalences, dimensions and irreducibility assertions.
The source dispatcher either supplies the complete higher rigidity and
parabolic splitting or returns the actual proper containing chain and these
marked rows, allowing also the original nonquasisimple maximal quotient.
Classifying those remaining inclusions and final assembly stay with
qt-d-12213-local-rigidity. This is not a proof of the full 12.2.25 catalogue.
Source: Aschbacher–Smith, 12.2.2(3), A.3.12 and 12.2.25, pp.795,47–48,805.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G} {d : ℕ}

/-- A small maximal-component row forces equality of the actual original
subgroups, using their original common full Sylow. -/
theorem residual_eq_of_containing_solvable_sylow_overgroups
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hd : 3 < d) {K₀ : Subgroup G}
    (hK₀ : K₀ ∈ Chapter1.L G (T : Subgroup G))
    (hYK₀ : rigidityHyperplaneResidual L U V ≤ K₀)
    (hproper : SolvableSylowOvergroups K₀) : rigidityHyperplaneResidual L U V = K₀ := by
  let J := K₀ ⊔ (T : Subgroup G)
  let S := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  have hYJ : rigidityHyperplaneResidual L U V ≤ J := hYK₀.trans le_sup_left
  have hlocal := (Chapter1.mem_LIn_iff_subgroupOf
    (show (T : Subgroup G) ≤ J from le_sup_right) hYJ).mp
    ⟨hYJ,residual_mem_local_family D A C hd (((structural G T L h).2.2 V D).1)⟩
  have he := ChapterA.Section03.SourceEmbeddings.eq_of_solvable_sylow_overgroups S
    hlocal.1 hK₀.1 (comap_mono hYK₀)
    (SolvableSylowOvergroups.of_equiv (subgroupOfEquivOfLe
      (show K₀ ≤ J from le_sup_left)) hproper)
  have hm := congrArg (Subgroup.map J.subtype) he
  change ((rigidityHyperplaneResidual L U V).subgroupOf J).map J.subtype =
    (K₀.subgroupOf J).map J.subtype at hm
  simpa only [map_subgroupOf_eq_of_le hYJ,
    map_subgroupOf_eq_of_le (show K₀ ≤ J from le_sup_left)] using hm

private theorem small_linear_properSylow :
    SolvableSylowOvergroups (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
  SolvableSylowOvergroups.of_equiv Matrix.PSL3Two.equiv
    (Matrix.PSL3Two.solvableSylowOvergroups_projective_of_card_two (by simp))

private theorem hexacode_properSylow : SolvableSylowOvergroups Atlas.Codes.HexEvenAutomorphisms := by
  let := Representation.Hexacode.even_isPerfect
  exact SolvableSylowOvergroups.of_central_quotient Atlas.Codes.hexEvenCoordinate
    Atlas.Codes.hexEvenCoordinate_surjective Representation.Hexacode.even_kernel_eq_center.le
    AlternatingSix.ProperSylowOvergroups.isSolvable

private theorem small_alternating_properSylow {n : ℕ} (hn : n = 5 ∨ n = 6) :
    SolvableSylowOvergroups (alternatingGroup (Fin n)) := by
  rcases hn with rfl | rfl
  · exact fun _ P _ hP => alternatingGroup.isSolvable_subgroup_five_of_ne_top P hP
  · exact AlternatingSix.ProperSylowOvergroups.isSolvable

private theorem chosen_alternating_properSylow {K₀ W : Subgroup G}
    (E : ChosenModule T K₀ W) (hq : IsQuasisimple (K₀ ⧸ pCore 2 K₀))
    {n : ℕ} (hn : n = 5 ∨ n = 6)
    (e : letI := E.actionCentralizer_normal
      (K₀ ⧸ (centralizer (W : Set G)).subgroupOf K₀) ≃* alternatingGroup (Fin n)) :
    SolvableSylowOvergroups K₀ := by
  let := E.actionCentralizer_normal
  let := hq
  let f := e.toMonoidHom.comp E.coreToFaithful
  have hf : Function.Surjective f := e.surjective.comp E.coreToFaithful_surjective
  have hk : f.ker ≤ center (K₀ ⧸ pCore 2 K₀) := by
    apply (IsQuasisimple.normal_le_center_or_eq_top f.ker).resolve_right
    intro ht
    have hz : f = 1 := f.ker_eq_top_iff.mp ht
    have hone (x : alternatingGroup (Fin n)) : x = 1 := by
      obtain ⟨y,rfl⟩ := hf x
      exact DFunLike.congr_fun hz y
    rcases hn with rfl | rfl
    · obtain ⟨x,hx⟩ := exists_ne (1 : alternatingGroup (Fin 5))
      exact hx (hone x)
    · obtain ⟨x,hx⟩ := exists_ne (1 : alternatingGroup (Fin 6))
      exact hx (hone x)
  exact isSolvable_proper_sylow_overgroup_of_twoCore_quotient
    (SolvableSylowOvergroups.of_central_quotient f hf hk (small_alternating_properSylow hn))

/-- The still possible seven-module rows for a proper maximal containing
component. These retain the literal chosen module and all original markings. -/
inductive ProperContainingModuleRows {K₀ W : Subgroup G} (E : ChosenModule T K₀ W) : Prop
  | linear (n : ℕ) (degree : n = 4 ∨ n = 5)
      (action : ActionEquiv E.quotientAction (specialLinearNatural (k := ZMod 2) n))
  | linearFiveExterior
      (groupEquiv : (K₀ ⧸ pCore 2 K₀) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
      (dimension : Module.finrank (ZMod 2) E.space = 10)
      (irreducible : IsIrreducible E.quotientAction)
  | alternating (n : ℕ) (degree : n = 7 ∨ n = 8)
      (action : letI := E.actionCentralizer_normal
        ActionEquiv E.faithfulCentralAction (alternatingNatural n))
  | alternatingSevenFour
      (groupEquiv : letI := E.actionCentralizer_normal
        (K₀ ⧸ (centralizer (W : Set G)).subgroupOf K₀) ≃* alternatingGroup (Fin 7))
      (dimension : Module.finrank (ZMod 2) E.space = 4)

/-- Apply original 12.2.2 to the actual proper containing component. The
SL₃, G₂(2)′, triple-six and small alternating rows are discharged here. -/
theorem proper_containing_module_rows
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hd : 3 < d) {K₀ W : Subgroup G}
    (hK₀ : K₀ ∈ Chapter1.L G (T : Subgroup G))
    (hYK₀ : rigidityHyperplaneResidual L U V < K₀)
    (E : ChosenModule T K₀ W) (hq : IsQuasisimple (K₀ ⧸ pCore 2 K₀))
    (rows : ModuleAlternatives1222 E) : ProperContainingModuleRows E := by
  let := E.actionCentralizer_normal
  have hnot : ¬ SolvableSylowOvergroups K₀ := fun hp => hYK₀.ne
    (residual_eq_of_containing_solvable_sylow_overgroups h D structural A C hd hK₀ hYK₀.le hp)
  have hsmall {X : Type} [Group X] (e : (K₀ ⧸ pCore 2 K₀) ≃* X)
      (hp : SolvableSylowOvergroups X) : False :=
    hnot (isSolvable_proper_sylow_overgroup_of_twoCore_quotient
      (SolvableSylowOvergroups.of_equiv e hp))
  cases rows with
  | linear n hn e =>
    rcases hn with rfl | hn
    · exact (hsmall e.groupEquiv small_linear_properSylow).elim
    · exact .linear n hn e
  | linearThreeExtension e _ _ => exact (hsmall e small_linear_properSylow).elim
  | linearFiveExterior e hd hi => exact .linearFiveExterior e hd hi
  | alternating n hlo hhi e =>
    have hn : n = 7 ∨ n = 8 := by
      by_contra hh
      exact hnot (chosen_alternating_properSylow E hq (by omega) e.groupEquiv)
    exact .alternating n hn e
  | alternatingSevenFour e hd => exact .alternatingSevenFour e hd
  | g2 e => exact (hsmall e.groupEquiv Atlas.G2.binaryDerived_solvableSylowOvergroups).elim
  | tripleSix e _ _ _ => exact (hsmall e hexacode_properSylow).elim

/-- In the original source chain a proper normal containing component has
only these larger marked module rows whenever its maximal overcomponent has
quasisimple two-core quotient. No extra classification input is introduced. -/
theorem source_proper_containing_module_rows
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222Modules.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hd : 3 < d) {K K₀ : Subgroup G}
    (hYK : rigidityHyperplaneResidual L U V < K) (hKK₀ : K ≤ K₀)
    (hK₀ : FaithfulMaximalLocal T K₀)
    (hq : IsQuasisimple (K₀ ⧸ pCore 2 K₀)) :
    ∃ W : Subgroup G, ∃ E : ChosenModule T K₀ W, ProperContainingModuleRows E := by
  have h₀ : Hypothesis1223 KnownSimple.IsKnownSimple T K₀ :=
    { h with maximal_faithful := hK₀, quasisimple := hq }
  obtain ⟨⟨W,⟨E⟩⟩⟩ := (structural G T K₀ h₀).2.1
  exact ⟨W,E,proper_containing_module_rows h D structural A C hd hK₀.1.1
    (lt_of_lt_of_le hYK hKK₀) E hq (modules G T K₀ W h₀ E)⟩

/-- An exhaustive source reduction: equality closes the full higher rigidity
branch; a proper chain retains only the larger marked 12.2.2 rows or the
nonquasisimple maximal quotient. The final catalogue construction remains here. -/
theorem source_rigidity_or_remaining_containing_rows
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222Modules.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d) :
    (normalizer (sectionRadical T U : Set G) ≤ normalizer (rigidityHyperplaneResidual L U V : Set G) ∧
      (d = 3 ∨ d = 4) ∧ normalizer (L : Set G) = L ∧ L.pCoreIn 2 = V ∧
        ParabolicSplitting T L V U) ∨
    ∃ K K₀ : Subgroup G,
      K ≤ normalizer (sectionRadical T U : Set G) ∧
      (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent ∧
      rigidityHyperplaneResidual L U V < K ∧
      normalizer (sectionRadical T U : Set G) ≤ normalizer (K : Set G) ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧ K ≤ K₀ ∧ FaithfulMaximalLocal T K₀ ∧
      pCore 2 (ThreeRigidity.image T U K) ≤ center (ThreeRigidity.image T U K) ∧
      ¬ Chapter1.Section02.LocalModels.IsAlternating (ThreeRigidity.image T U K) 7 ∧
      ((¬ IsQuasisimple (K₀ ⧸ pCore 2 K₀)) ∨
        ∃ W : Subgroup G, ∃ E : ChosenModule T K₀ W, ProperContainingModuleRows E) := by
  obtain ⟨K,K₀,hKN,hK,hYK,hn,hlocal,hKK₀,hK₀,hseven⟩ :=
    source_containing_component_without_seven h D structural A C hnone hd
  by_cases he : rigidityHyperplaneResidual L U V = K
  · have hnormal : normalizer (sectionRadical T U : Set G) ≤
        normalizer (rigidityHyperplaneResidual L U V : Set G) := by simpa only [he] using hn
    exact Or.inl ⟨hnormal,source_rigidity_step_of_residual_normal h D structural A C hnone hd hnormal⟩
  · have hlt := lt_of_le_of_ne hYK he
    refine Or.inr ⟨K,K₀,hKN,hK,hlt,hn,hlocal,hKK₀,hK₀,
      containing_image_twoCore_central h D structural A C
        (RigidityKernel.source_centralizers h D structural A C hnone) hd hK hYK,hseven,?_⟩
    by_cases hq : IsQuasisimple (K₀ ⧸ pCore 2 K₀)
    · exact Or.inr (source_proper_containing_module_rows h D structural modules A C hd hlt hKK₀ hK₀ hq)
    · exact Or.inl hq

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity

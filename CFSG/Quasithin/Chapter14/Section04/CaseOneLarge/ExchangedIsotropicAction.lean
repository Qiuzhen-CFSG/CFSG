module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ExchangedIsotropicModels
public import Theory.Representation.BinaryAlternatingSevenControl.Normalizer
public import Theory.SpecificGroups.AlternatingSeven.ConjugatePairs
public import Theory.Representation.AlternatingSevenConjugatePair
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.SymmetricSeven

/-!
# The original isotropic exchanged action is the S7 conjugate pair

The faithful four-dimensional A7 image is self-normalizing. Homogeneous
selection therefore makes the ambient component centralizer trivial, and
the original exchanging actor supplies an odd element. Conjugation gives
actual S7 coordinates extending the original component coordinates.

The original complementary summands give the faithful S7 representation,
the two inequivalent irreducible four-spaces and both odd swapping clauses.
Transport through the literal terminal quotient then discharges the marked
S7 premise in the existing 14.4.11 contradiction. The large-case remainder
is nondegenerate, with every earlier source premise and MixedSizeInput
retained. Recognition of that remaining branch and guarded assembly are
separate outstanding parts of the same source task.

Source: Aschbacher--Smith G.11.6, printed p.366, and 14.4.11, p.1011;
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ExchangedIsotropicModels
variable {D U : Type*} [Group D] [Finite D] [AddCommGroup U]
  [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  {ρ : Representation (ZMod 2) D U} {B : LinearMap.BilinForm (ZMod 2) U}
  {v : U} {W : Submodule (ZMod 2) U} {X : Subgroup D}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}

private theorem seven_linear_centralizer
    {J : Type*} [Group J] (σ : Representation (ZMod 2) J U)
    (hf : Function.Injective σ) (hd : finrank (ZMod 2) U = 4)
    (e : J ≃* alternatingGroup (Fin 7))
    (z : LinearMap.GeneralLinearGroup (ZMod 2) U)
    (hz : ∀ a, Commute z (σ.asGroupHom a)) : z = 1 := by
  let τ : Representation (ZMod 2) (alternatingGroup (Fin 7)) U := σ.comp e.symm.toMonoidHom
  have hτ (a) : τ.asGroupHom a = σ.asGroupHom (e.symm a) := by
    apply Units.ext
    rfl
  have hc : z ∈ centralizer (actionImage τ : Set _) := by
    rintro _ ⟨a,rfl⟩
    rw [hτ]
    exact (hz (e.symm a)).eq.symm
  have hn := Subgroup.centralizer_le_normalizer _ hc
  rw [BinaryAlternatingSevenControl.actionImage_self_normalizing τ
    (hf.comp e.symm.injective) hd] at hn
  obtain ⟨a,ha⟩ := hn
  have hcenter : a ∈ center (alternatingGroup (Fin 7)) := by
    rw [mem_center_iff]
    intro b
    apply e.symm.injective
    apply hf
    have hh := hz (e.symm b)
    rw [← ha,hτ] at hh
    simpa only [map_mul,Units.val_mul,Representation.asGroupHom_apply] using
      congrArg Units.val hh.eq.symm
  rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at hcenter
  simpa [hcenter] using ha.symm

private theorem seven_component_centralizer
    (h : ChapterG.Section10.Hypothesis ρ B v W X X₀)
    (hn : ¬ Group.IsSolvable D) {C : Subgroup D} (hC : IsComponent D C)
    {I : Submodule (ZMod 2) U}
    (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit C ⊤) X I)
    (hc : ExchangedGeometry.CompletedData ρ B C X I hI)
    (hf : Function.Injective (invariantSubspace ρ (componentOrbit C ⊤) I hI.invariant).toRepresentation)
    (hd : finrank (ZMod 2) I = 4)
    (e : componentOrbit C ⊤ ≃* alternatingGroup (Fin 7)) :
    centralizer (componentOrbit C ⊤ : Set D) = ⊥ := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  have hir := h.irreducible_of_not_solvable hn
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ h.faithful hir
    H hC.componentOrbit_top_ne_bot
  let Z := centralizer (H : Set D)
  have hZI := FullLinearFourLift.centralizer_stabilizes_homogeneous ρ H X I hI hfix hc.2.1
  have hfixed : I ≤ fixedSpace ρ Z := by
    intro u hu g
    let y : subspaceStabilizer ρ I := ⟨g,hZI g.property⟩
    have hz : (stabilizerRepresentation ρ I).asGroupHom y = 1 := by
      apply seven_linear_centralizer
        (invariantSubspace ρ H I hI.invariant).toRepresentation hf hd e
      intro a
      apply Units.ext
      apply LinearMap.ext
      intro w
      apply Subtype.ext
      change ρ (g : D) (ρ (a : D) w) = ρ (a : D) (ρ (g : D) w)
      rw [← Module.End.mul_apply,← map_mul,← Module.End.mul_apply,← map_mul,
        g.property a a.property]
    exact congrArg (fun f : LinearMap.GeneralLinearGroup (ZMod 2) I => (f.val ⟨u,hu⟩ : U)) hz
  by_contra hne
  have hzero := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ h.faithful hir Z hne
  exact hI.isIrrPlus.ne_bot ρ (bot_unique (hzero ▸ hfixed))

/-- The whole terminal group has actual seven-point coordinates extending
those of its normal component. The outer element comes from the original
exchanged actor, rather than from an unmarked group-order argument. -/
theorem whole_symmetric_seven
    (h : ChapterG.Section10.Hypothesis ρ B v W X X₀)
    (hn : ¬ Group.IsSolvable D) {C : Subgroup D} (hC : IsComponent D C)
    {I : Submodule (ZMod 2) U}
    (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit C ⊤) X I)
    (hc : ExchangedGeometry.CompletedData ρ B C X I hI)
    (hf : Function.Injective (invariantSubspace ρ (componentOrbit C ⊤) I hI.invariant).toRepresentation)
    (hd : finrank (ZMod 2) I = 4)
    (e : componentOrbit C ⊤ ≃* alternatingGroup (Fin 7)) :
    ∃ f : D ≃* Equiv.Perm (Fin 7), ∀ a : componentOrbit C ⊤,
      f a = (e a : Equiv.Perm (Fin 7)) := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  have hz := seven_component_centralizer h hn hC hI hc hf hd e
  let f := AlternatingSeven.ConjugatePairs.action H e
  have hfinj := AlternatingSeven.ConjugatePairs.action_injective H e hz
  have heven (a : Equiv.Perm (Fin 7)) (ha : a ∈ alternatingGroup (Fin 7)) :
      ∃ z : D, f z = a := by
    obtain ⟨z,hz⟩ := e.surjective ⟨a,ha⟩
    exact ⟨z,(AlternatingSeven.ConjugatePairs.action_on_subgroup H e z).trans
      (congrArg Subtype.val hz)⟩
  obtain ⟨x,hx,_,_⟩ := hc.2.2.1
  have hxi : (x : D)⁻¹ = x := inv_eq_iff_mul_eq_one.mpr (by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2)
      (x : D) x.property)
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ h.faithful
    (h.irreducible_of_not_solvable hn) H hC.componentOrbit_top_ne_bot
  have ho := hI.conjugation_not_inner ρ hfix x (by rwa [hxi])
  have hout : f x ∉ alternatingGroup (Fin 7) := by
    intro he
    obtain ⟨a,ha⟩ := e.surjective ⟨f x,he⟩
    have hax : (a : D) = x := hfinj
      ((AlternatingSeven.ConjugatePairs.action_on_subgroup H e a).trans
        (congrArg Subtype.val ha))
    apply ho
    rw [← hax,MulAut.conjNormal_val]
    exact ⟨a,rfl⟩
  have hfsurj : Function.Surjective f := by
    intro a
    by_cases ha : a ∈ alternatingGroup (Fin 7)
    · exact heven a ha
    · have hh : a * (f x)⁻¹ ∈ alternatingGroup (Fin 7) := by
        rw [mul_mem_iff_of_index_two alternatingGroup.index_eq_two,inv_mem_iff]
        exact iff_of_false ha hout
      obtain ⟨z,hz⟩ := heven _ hh
      exact ⟨z * x,by rw [map_mul,hz,inv_mul_cancel_right]⟩
  exact ⟨MulEquiv.ofBijective f ⟨hfinj,hfsurj⟩,
    AlternatingSeven.ConjugatePairs.action_on_subgroup H e⟩

/-- Recognize the original representation as the actual pair of inequivalent
four-dimensional A7 constituents, with every odd permutation interchanging
the two original summands. -/
theorem marked_symmetric_seven_pair
    (h : ChapterG.Section10.Hypothesis ρ B v W X X₀)
    (hn : ¬ Group.IsSolvable D) {C : Subgroup D} (hC : IsComponent D C)
    {I : Submodule (ZMod 2) U}
    (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit C ⊤) X I)
    (hc : ExchangedGeometry.CompletedData ρ B C X I hI)
    (hf : Function.Injective (invariantSubspace ρ (componentOrbit C ⊤) I hI.invariant).toRepresentation)
    (hd : finrank (ZMod 2) I = 4)
    (e : componentOrbit C ⊤ ≃* alternatingGroup (Fin 7)) :
    ∃ f : D ≃* Equiv.Perm (Fin 7),
    ∃ P : Representation.AlternatingSevenConjugatePair.Pair U,
      (∀ a w, P.representation (f a) w = ρ a w) ∧ P.first.toSubmodule = I := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  obtain ⟨f,hfH⟩ := whole_symmetric_seven h hn hC hI hc hf hd e
  let A := alternatingGroup (Fin 7)
  let σ : Representation (ZMod 2) (Equiv.Perm (Fin 7)) U := ρ.comp f.symm.toMonoidHom
  have hfa (a : A) : f.symm (a : Equiv.Perm (Fin 7)) = (e.symm a : D) := by
    apply f.injective
    rw [f.apply_symm_apply,hfH,e.apply_symm_apply]
  have hmem (z : D) : f z ∈ A ↔ z ∈ H := by
    constructor
    · intro hz
      have heq := hfa ⟨f z,hz⟩
      rw [f.symm_apply_apply] at heq
      exact heq.symm ▸ (e.symm ⟨f z,hz⟩).property
    · intro hz
      rw [hfH ⟨z,hz⟩]
      exact (e ⟨z,hz⟩).property
  obtain ⟨x,hx,hcompl,_⟩ := hc.2.2.1
  have hxi : (x : D)⁻¹ = x := inv_eq_iff_mul_eq_one.mpr (by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2)
      (x : D) x.property)
  have hxx : (x : D) * x = 1 := inv_eq_iff_mul_eq_one.mp hxi
  have hxout : f x ∉ A := by
    intro ha
    exact hx ((subspace_map_eq_iff ρ I x).mpr (hI.invariant ((hmem x).mp ha)))
  let R := invariantSubspace ρ H I hI.invariant
  let S := conjugateSubrepresentation ρ H R (x : D)
  let first : Subrepresentation (σ.comp A.subtype) := {
    toSubmodule := I
    apply_mem_toSubmodule := by
      intro a w hw
      change ρ (f.symm (a : Equiv.Perm (Fin 7))) w ∈ I
      rw [hfa]
      exact R.apply_mem_toSubmodule (e.symm a) hw }
  let second : Subrepresentation (σ.comp A.subtype) := {
    toSubmodule := S.toSubmodule
    apply_mem_toSubmodule := by
      intro a w hw
      change ρ (f.symm (a : Equiv.Perm (Fin 7))) w ∈ S.toSubmodule
      rw [hfa]
      exact S.apply_mem_toSubmodule (e.symm a) hw }
  have hfirst : first.toRepresentation = R.toRepresentation.comp e.symm.toMonoidHom := by
    ext a w
    change ρ (f.symm (a : Equiv.Perm (Fin 7))) w = ρ (e.symm a : D) w
    rw [hfa]
  have hsecond : second.toRepresentation = S.toRepresentation.comp e.symm.toMonoidHom := by
    ext a w
    change ρ (f.symm (a : Equiv.Perm (Fin 7))) w = ρ (e.symm a : D) w
    rw [hfa]
  have hir : IsIrreducible R.toRepresentation :=
    hI.isIrrPlus.irreducible_of_normal_restriction ρ (h.irreducible_of_not_solvable hn) H
  have hsr : IsIrreducible S.toRepresentation := by
    apply (Subrepresentation.irreducible_iff_isAtom _).mpr
    simpa [S] using ((conjugateSubrepresentationOrderIso ρ H (x : D)⁻¹).isAtom_iff R).mpr
      ((Subrepresentation.irreducible_iff_isAtom R).mp hir)
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ h.faithful
    (h.irreducible_of_not_solvable hn) H hC.componentOrbit_top_ne_bot
  have hinequiv : ¬ Nonempty (Representation.Equiv first.toRepresentation second.toRepresentation) := by
    rintro ⟨q⟩
    let l : R.toSubmodule ≃ₗ[ZMod 2] S.toSubmodule := q.toLinearEquiv
    apply hI.not_equiv_moved ρ hfix x (by rwa [hxi])
    refine ⟨.mk l ?_⟩
    intro a
    apply LinearMap.ext
    intro w
    have hh := LinearMap.congr_fun (q.isIntertwining' (e a)) w
    change l (first.toRepresentation (e a) w) = second.toRepresentation (e a) (l w) at hh
    rw [hfirst,hsecond] at hh
    change l (R.toRepresentation (e.symm (e a)) w) =
      S.toRepresentation (e.symm (e a)) (l w) at hh
    rw [e.symm_apply_apply] at hh
    exact hh
  have heven (g : Equiv.Perm (Fin 7)) (hg : g ∉ A) :
      f.symm g * (x : D) ∈ H ∧ (x : D) * f.symm g ∈ H := by
    constructor <;> apply (hmem _).mp <;> rw [map_mul,f.apply_symm_apply]
    · rw [mul_mem_iff_of_index_two alternatingGroup.index_eq_two]
      exact iff_of_false hg hxout
    · rw [mul_mem_iff_of_index_two alternatingGroup.index_eq_two]
      exact iff_of_false hxout hg
  let P : Representation.AlternatingSevenConjugatePair.Pair U := {
    representation := σ
    faithful := h.faithful.comp f.symm.injective
    first := first
    second := second
    complementary := by
      change IsCompl I (I.map (ρ (x : D)⁻¹))
      rwa [hxi]
    first_dim := hd
    second_dim := (finrank_map_action ρ I (x : D)⁻¹).trans hd
    first_irreducible := by
      rw [hfirst]
      exact (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr hir
    second_irreducible := by
      rw [hsecond]
      exact (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr hsr
    inequivalent := hinequiv
    swap_first := by
      intro g hg w hw
      change ρ (f.symm g) w ∈ I.map (ρ (x : D)⁻¹)
      rw [hxi]
      refine Submodule.mem_map.mpr ⟨ρ ((x : D) * f.symm g) w,
        R.apply_mem_toSubmodule ⟨_,(heven g hg).2⟩ hw,?_⟩
      rw [← Module.End.mul_apply,← map_mul,← mul_assoc,hxx,one_mul]
    swap_second := by
      intro g hg w hw
      change w ∈ I.map (ρ (x : D)⁻¹) at hw
      obtain ⟨z,hz,rfl⟩ := Submodule.mem_map.mp hw
      change ρ (f.symm g) (ρ (x : D)⁻¹ z) ∈ I
      rw [hxi,← Module.End.mul_apply,← map_mul]
      exact R.apply_mem_toSubmodule ⟨_,(heven g hg).1⟩ hz }
  exact ⟨f,P,by intro a w; change ρ (f.symm (f a)) w = ρ a w; rw [f.symm_apply_apply],rfl⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ExchangedIsotropicModels

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.Tensor CoreGeometry
open LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The A7 carrier and whole S7 conjugate-pair marking are both derived from
the original isotropic constituent. The previously conditional 14.4.11
consumer therefore excludes this branch without any recognition input. -/
theorem source_exchanged_isotropic_contradiction (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)))
    {C : Subgroup F.TerminalHdot} (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation (componentOrbit C ⊤)
      (F.terminalDot (F.X g)) I) (hv : v ∉ I)
    (hiso : ∀ a ∈ I, ∀ b ∈ I, B a b = 0) : False := by
  have hnotnd : ¬ (B.restrict I).Nondegenerate := by
    intro hnd
    apply hI.isIrrPlus.ne_bot F.terminalRepresentation
    apply le_bot_iff.mp
    intro a ha
    exact congrArg Subtype.val (hnd.1 ⟨a,ha⟩ (fun b => hiso a ha b b.property))
  obtain ⟨hc,hmodel⟩ := source_exchanged_recognized_component_input d earlier hq chosen
    structural alternatives F hne hZ hlarge g hgP hgH hyp hline hn hC hm hI hv
  obtain ⟨_,hi,⟨e⟩,hd,_⟩ := hmodel.resolve_left hnotnd
  have hf : Function.Injective (invariantSubspace F.terminalRepresentation
      (componentOrbit C ⊤) I hI.invariant).toRepresentation := by
    obtain ⟨_,hf,_,_⟩ := hc.2.2.2.2.2.2.resolve_left hnotnd
    exact fun a b hab => hf (Units.ext hab)
  have hnonsolv := source_large_terminal_not_solvable d earlier hq chosen structural alternatives
    F hne hZ hlarge
  obtain ⟨f,P,hP,_⟩ := ExchangedIsotropicModels.marked_symmetric_seven_pair hyp hnonsolv hC
    hI hc hf hd ((MulEquiv.subgroupCongr hi.1).trans e)
  let q : coreQuotient F.H ≃* F.TerminalHdot :=
    QuotientGroup.quotientMulEquivOfEq
      (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ).symm
  apply source_symmetric_seven_contradiction d earlier hq chosen structural alternatives
    classification F hne hZ hlarge g hg hgP hgH (q.trans f) P
  intro a w
  exact hP (QuotientGroup.mk' F.terminalHatAction.ker a) w

namespace FixedLineReduction
/-- The original large-case remainder is now nondegenerate. The full
isotropic carrier sieve and the marked S7 action are discharged above;
all original markings, fixed-point clauses and the independent mixed-size
premise are retained. -/
theorem source_large_nondegenerate_remainder_of_mixed_size (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (size : Chapter10.MixedZeroCore.MixedSizeInput G)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ heU : IsElementaryAbelian 2 F.Uhat, letI := heU
    ∃ heX : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := heX
    ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2) ∧
      ChapterG.Section11.NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      FixedLineModuleData F.terminalRepresentation B v (F.terminalDot (F.X g)) ∧
      ∃ C : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot C ∧
        ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
        ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B C ∧
        ∃ I : Submodule (ZMod 2) (Additive F.Uhat),
        ∃ hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation
            (componentOrbit C ⊤) (F.terminalDot (F.X g)) I,
          v ∉ I ∧ ChapterG.Section10.ExchangedConstituentGeometry F.terminalRepresentation B v
            (hatSpace F (F.E g)) (F.terminalDot (F.X g)) I ∧
          ExchangedGeometry.CompletedData F.terminalRepresentation B C
            (F.terminalDot (F.X g)) I hI ∧ (B.restrict I).Nondegenerate := by
  obtain ⟨heU,heX,B,v,hyp,hline,hS,hn,hmodule,C,hC,hm,horth,I,hI,hv,hgeo,hc,hmodel⟩ :=
    source_large_recognized_isotropic_remainder_of_mixed_size d earlier hq chosen structural
      alternatives classification size F hne hZ hlarge g hgP hgH
  let := heU
  let := heX
  refine ⟨heU,heX,B,v,hyp,hline,hS,hn,hmodule,C,hC,hm,horth,I,hI,hv,hgeo,hc,?_⟩
  rcases hmodel with hnd | ⟨hiso,_⟩
  · exact hnd
  · exact (source_exchanged_isotropic_contradiction d earlier hq chosen structural alternatives
      classification F hne hZ hlarge g hg hgP hgH hyp hline hn hC hm hI hv hiso).elim
end FixedLineReduction
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

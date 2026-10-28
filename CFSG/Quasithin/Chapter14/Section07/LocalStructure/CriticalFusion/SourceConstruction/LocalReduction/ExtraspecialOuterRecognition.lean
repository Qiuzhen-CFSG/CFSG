module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialOuterSpan
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialSpanRecognition

/-!
# The five marked module possibilities for the original S/R

Descend the original LT-action through the actual L/O₂(L) map. The
Sylow-fixed cyclic vector and its point-parabolic plane satisfy the proved
H.6.5 recognition theorem. Thus S/R has one of the five actual module
structures, with the original quotient, parabolic and dual orientation
retained. Their exact L₁-chief counts are one through five.

This is the five-model reduction used in Aschbacher–Smith 14.7.24(1),
printed p.1051, refs/quasithin.pdf. Selecting the Core alternative still
requires the central branch's two-factor count. The earlier source inputs
retain their existing producers and final discharge at qt-d-14775-source.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem outerRecognition_descent
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W)
    (hk : (Q T L).subgroupOf (L ⊔ (T : Subgroup G)) ≤ ρ.ker) :
    ∃ σ : Representation (ZMod 2) BinaryLinearThree.Group W,
      σ.comp (SpanMarking.qL h) = ρ.comp (inclusion le_sup_left) := by
  let τ : Representation (ZMod 2) L W :=
    ρ.comp (inclusion (le_sup_left : L ≤ L ⊔ (T : Subgroup G)))
  have hcore : L.pCoreIn 2 ≤ Q T L :=
    pCoreIn_mono_of_normalizes le_sup_left (sup_le L.le_normalizer (h.sylow_normalizes structural))
  have hkill : (SpanMarking.qL h).ker ≤ τ.ker := by
    rw [SpanMarking.qL_ker]
    intro l hl
    exact hk (hcore hl)
  have hkillU : (SpanMarking.qL h).ker ≤ τ.asGroupHom.ker := by
    intro l hl
    apply Units.ext
    exact hkill hl
  let β := (SpanMarking.qL h).liftOfSurjective (SpanMarking.qL_surjective h) ⟨τ.asGroupHom,hkillU⟩
  let σ : Representation (ZMod 2) BinaryLinearThree.Group W := (Units.coeHom _).comp β
  refine ⟨σ,?_⟩
  apply MonoidHom.ext
  intro l
  exact congrArg Units.val ((SpanMarking.qL h).liftOfRightInverse_comp_apply
    (Function.surjInv (SpanMarking.qL_surjective h))
    (Function.rightInverse_surjInv (SpanMarking.qL_surjective h)) ⟨τ.asGroupHom,hkillU⟩ l)

private theorem outerRecognition_orbit_map
    {A B W : Type*} [Group A] [Group B] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) B W) (q : A →* B) (P : Subgroup A) (w : W) :
    BinaryLinearThree.ParabolicCyclic.orbitSpan σ (P.map q) w =
      BinaryLinearThree.ParabolicCyclic.orbitSpan (σ.comp q) P w := by
  unfold BinaryLinearThree.ParabolicCyclic.orbitSpan
  congr 1
  ext v
  constructor
  · rintro ⟨b,⟨a,ha,rfl⟩,he⟩
    exact ⟨a,ha,he⟩
  · rintro ⟨a,ha,he⟩
    exact ⟨q a,mem_map_of_mem q ha,he⟩


open BinaryLinearThree.ParabolicCyclic in
/-- The original S/R has one of the five actual H.6.5 module structures.
The quotient map, parabolic orientation, natural-to-dual equivalence and
literal conjugation section are retained in the same witness. -/
theorem extraspecial_outer_module_alternatives
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    let S := conjugateSpanBy F.U L
    let R := conjugateSpanBy ⁅F.U,Q T L⁆ L
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W)
      (ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W)
      (_s : BinaryConjugationSection (L ⊔ (T : Subgroup G)) S R ρ)
      (e : MulAut BinaryLinearThree.Group)
      (σ : Representation (ZMod 2) BinaryLinearThree.Group W),
      (Q T L).subgroupOf (L ⊔ (T : Subgroup G)) ≤ ρ.ker ∧
      σ.comp (e.symm.toMonoidHom.comp (SpanMarking.qL h)) = ρ.comp (inclusion le_sup_left) ∧
      ((T : Subgroup G).subgroupOf L).map (e.symm.toMonoidHom.comp (SpanMarking.qL h)) =
        Matrix.PSL3Two.borelSL ∧
      (F.H.subgroupOf L).map (e.symm.toMonoidHom.comp (SpanMarking.qL h)) =
        Matrix.PSL3Two.lineParabolicSL ∧
      Nonempty (Representation.Equiv (BinaryLinearThree.W.comp e.symm.toMonoidHom) BinaryLinearThree.W.dual) ∧
      Alternatives σ ∧
      ∃ n : ℕ, 1 ≤ n ∧ n ≤ 5 ∧ BinaryLinearThree.ParabolicCyclic.ChiefCounts.HasCount
        (ρ.comp (inclusion (((F.Li_le L 1).trans inf_le_left).trans
          (le_sup_left : L ≤ L ⊔ (T : Subgroup G))))) n := by
  obtain ⟨W,ha,hm,ρ,s,hker,_⟩ :=
    extraspecial_outer_span_binary_section h hab structural previous faithful he
  obtain ⟨τ,hτ⟩ := outerRecognition_descent h structural ρ hker
  obtain ⟨e,hS,hP,hdual⟩ := SpanMarking.exists_marking h F (h.sylow_normalizes structural)
  let q := e.symm.toMonoidHom.comp (SpanMarking.qL h)
  let σ := τ.comp e.toMonoidHom
  have hσ : σ.comp q = ρ.comp (inclusion le_sup_left) := by
    calc _ = τ.comp (SpanMarking.qL h) := by
           ext l w
           change τ (e (e.symm (SpanMarking.qL h l))) w = _
           rw [e.apply_symm_apply]
           rfl
         _ = _ := hτ
  have hq : Function.Surjective q := e.symm.surjective.comp (SpanMarking.qL_surjective h)
  obtain ⟨w,_,_,hfix,hgen,hplane,hd⟩ :=
    extraspecial_outer_cyclic_seed h hab structural previous faithful he s
  have hfixed : ∀ a ∈ Matrix.PSL3Two.borelSL, σ a w = w := by
    intro a ha
    rw [←hS] at ha
    obtain ⟨l,hl,rfl⟩ := ha
    have hh := congrArg (fun ψ : Representation (ZMod 2) L W => ψ l w) hσ
    exact hh.trans (hfix l hl)
  have hfull : orbitSpan σ ⊤ w = ⊤ := by
    rw [←map_top_of_surjective q hq,outerRecognition_orbit_map,hσ]
    exact hgen
  have hdim : Module.finrank (ZMod 2) (orbitSpan σ Matrix.PSL3Two.lineParabolicSL w) = 2 := by
    rw [←hP,outerRecognition_orbit_map,hσ]
    exact hd
  have hclass := parabolic_seed_alternatives σ w hfixed hfull hdim
  refine ⟨W,ha,hm,ρ,s,e,σ,hker,hσ,hS,hP,hdual,hclass,?_⟩
  rcases extraspecial_span_counted_alternatives q hP σ hσ hclass with hh | hh | hh | hh | hh
  · exact ⟨1,by omega,by omega,hh.2⟩
  · exact ⟨2,by omega,by omega,hh.2⟩
  · exact ⟨3,by omega,by omega,hh.2⟩
  · exact ⟨4,by omega,by omega,hh.2⟩
  · exact ⟨5,by omega,by omega,hh.2⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction

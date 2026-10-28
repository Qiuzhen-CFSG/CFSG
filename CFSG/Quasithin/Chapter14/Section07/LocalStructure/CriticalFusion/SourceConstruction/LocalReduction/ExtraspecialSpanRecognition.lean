module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialSpanModule
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SpanMarking
public import Theory.Representation.PSL3Two.ParabolicCyclic
public import Theory.Representation.PSL3Two.ParabolicCyclic.ChiefCounts

/-!
# Recognition and chief counts for the original R/V

Descend the original L-action on R/V through its marked quotient, using
unit-valued linear automorphisms to retain the full action kernel. The
compatible Sylow and parabolic marking carries the constructed cyclic plane
to the hypotheses of the proved H.6.5 classification. This gives actual
equivariant isomorphisms with the natural, core, Steinberg, and the two
indicated direct-sum models. The marking retains the dual-natural orientation
relative to the original natural action.

Transport each concrete chief count along the image of the literal L₁.
Finite residual-image compatibility identifies that image with the intrinsic
two-residual of the line parabolic. The five alternatives therefore have
respectively one, two, three, four and five noncentral L₁-chief factors.
The final application constructs the original LT conjugation section, kills Q,
and supplies the classification with no module-recognition premise.

Source: Aschbacher–Smith 14.7.22 and H.6.5, printed pp.1050,388,
refs/quasithin.pdf. The earlier source inputs retain their existing producers;
final discharge remains with qt-d-14775-source.
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

private theorem spanRecognition_descent
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

private theorem spanRecognition_orbit_map
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


private theorem spanRecognition_relative_first_actor : (F.Li L 1).subgroupOf L =
    (pResidual 2 (F.H.subgroupOf L)).map (F.H.subgroupOf L).subtype := by
  apply map_injective L.subtype_injective
  rw [map_subgroupOf_eq_of_le ((F.Li_le L 1).trans inf_le_left),
    map_embedded_pResidual,subgroupOf_map_subtype]
  simp only [InvariantFlag.Li,show ¬ (3 = 5 ∧ (1 = 2 ∨ 1 = 3)) by decide,↓reduceIte]
  change (pResidual 2 (L ⊓ F.H : Subgroup G)).map (L ⊓ F.H).subtype = _
  rw [inf_comm]

open BinaryLinearThree.ParabolicCyclic.ChiefCounts in
/-- Model chief counts pull back along the literal original L₁-action.
Relative residuals and the full quotient map are retained. -/
theorem extraspecial_span_model_count
    (q : L →* BinaryLinearThree.Group)
    (hP : (F.H.subgroupOf L).map q = Matrix.PSL3Two.lineParabolicSL)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W}
    (σ : Representation (ZMod 2) BinaryLinearThree.Group W)
    (hσ : σ.comp q = ρ.comp (inclusion le_sup_left))
    {n : ℕ} (hc : HasCount (σ.comp actor.subtype) n) :
    HasCount (ρ.comp (inclusion
      (((F.Li_le L 1).trans inf_le_left).trans (le_sup_left : L ≤ L ⊔ (T : Subgroup G))))) n := by
  have hmap : ((F.Li L 1).subgroupOf L).map q = actor := by
    rw [spanRecognition_relative_first_actor,map_embedded_pResidual,hP]
    rfl
  let j : F.Li L 1 →* L := inclusion ((F.Li_le L 1).trans inf_le_left)
  let f : F.Li L 1 →* actor := (q.comp j).codRestrict actor (by
    intro a
    rw [←hmap]
    exact ⟨j a,a.property,rfl⟩)
  have hf : Function.Surjective f := by
    intro a
    have ha : (a : BinaryLinearThree.Group) ∈ ((F.Li L 1).subgroupOf L).map q := by
      rw [hmap]
      exact a.property
    obtain ⟨l,hl,he⟩ := ha
    exact ⟨⟨l,hl⟩,Subtype.ext he⟩
  have hh := hc.reindex f hf
  have heq : (σ.comp actor.subtype).comp f = ρ.comp (inclusion
      (((F.Li_le L 1).trans inf_le_left).trans (le_sup_left : L ≤ L ⊔ (T : Subgroup G)))) := by
    ext a w
    exact congrArg (fun ψ : Representation (ZMod 2) L W => ψ (j a) w) hσ
  rwa [heq] at hh

set_option backward.isDefEq.respectTransparency false in
open BinaryLinearThree BinaryLinearThree.ParabolicCyclic BinaryLinearThree.ParabolicCyclic.ChiefCounts in
/-- Each source alternative carries its exact number of noncentral L₁-chief
factors. Thus the one- and two-factor cases identify the dual natural and
core alternatives under the already oriented marking. -/
theorem extraspecial_span_counted_alternatives
    (q : L →* BinaryLinearThree.Group)
    (hP : (F.H.subgroupOf L).map q = Matrix.PSL3Two.lineParabolicSL)
    {X : Type u} [AddCommGroup X] [Module (ZMod 2) X]
    {ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) X}
    (σ : Representation (ZMod 2) BinaryLinearThree.Group X)
    (hσ : σ.comp q = ρ.comp (inclusion le_sup_left))
    (hc : Alternatives σ) :
    let τ := ρ.comp (inclusion
      (((F.Li_le L 1).trans inf_le_left).trans (le_sup_left : L ≤ L ⊔ (T : Subgroup G))))
    (Nonempty (σ.Equiv BinaryLinearThree.W) ∧ HasCount τ 1) ∨
    (Nonempty (σ.Equiv U₂) ∧ HasCount τ 2) ∨
    (Nonempty (σ.Equiv S) ∧ HasCount τ 3) ∨
    (Nonempty (σ.Equiv (BinaryLinearThree.W.prod S)) ∧ HasCount τ 4) ∨
    (Nonempty (σ.Equiv (U₂.prod S)) ∧ HasCount τ 5) := by
  dsimp only
  change Nonempty (σ.Equiv BinaryLinearThree.W) ∨ Nonempty (σ.Equiv U₂) ∨
    Nonempty (σ.Equiv S) ∨ Nonempty (σ.Equiv (BinaryLinearThree.W.prod S)) ∨
    Nonempty (σ.Equiv (U₂.prod S)) at hc
  rcases hc with hh | hh | hh | hh | hh
  · obtain ⟨e⟩ := hh
    exact Or.inl ⟨⟨e⟩,extraspecial_span_model_count q hP σ hσ
      (natural_count.mapEquiv (restrictEquiv e.symm actor.subtype))⟩
  · obtain ⟨e⟩ := hh
    exact Or.inr (Or.inl ⟨⟨e⟩,extraspecial_span_model_count q hP σ hσ
      (core_count.mapEquiv (restrictEquiv e.symm actor.subtype))⟩)
  · obtain ⟨e⟩ := hh
    exact Or.inr (Or.inr (Or.inl ⟨⟨e⟩,extraspecial_span_model_count q hP σ hσ
      (steinberg_count.mapEquiv (restrictEquiv e.symm actor.subtype))⟩))
  · obtain ⟨e⟩ := hh
    have ee : Representation.Equiv ((BinaryLinearThree.W.prod S).comp actor.subtype)
        (σ.comp actor.subtype) := .mk e.symm.toLinearEquiv
          (fun a => e.symm.toIntertwiningMap.isIntertwining' a.val)
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨e⟩,extraspecial_span_model_count q hP σ hσ
      (natural_prod_steinberg_count.mapEquiv ee)⟩)))
  · obtain ⟨e⟩ := hh
    have ee : Representation.Equiv ((U₂.prod S).comp actor.subtype)
        (σ.comp actor.subtype) := .mk e.symm.toLinearEquiv
          (fun a => e.symm.toIntertwiningMap.isIntertwining' a.val)
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨e⟩,extraspecial_span_model_count q hP σ hσ
      (core_prod_steinberg_count.mapEquiv ee)⟩)))

open BinaryLinearThree.ParabolicCyclic in
/-- The original R/V has one of the five actual H.6.5 module structures.
The quotient map, parabolic orientation, natural-to-dual equivalence and
literal conjugation section are retained in the same witness. -/
theorem extraspecial_span_module_alternatives
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    let R := conjugateSpanBy ⁅F.U,Q T L⁆ L
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W)
      (ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W)
      (_s : BinaryConjugationSection (L ⊔ (T : Subgroup G)) R V ρ)
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
  obtain ⟨W,ha,hm,ρ,s,hker,_,_⟩ :=
    extraspecial_span_binary_section h hab structural previous faithful he
  obtain ⟨τ,hτ⟩ := spanRecognition_descent h structural ρ hker
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
    extraspecial_span_cyclic_seed h hab structural previous faithful he s
  have hfixed : ∀ a ∈ Matrix.PSL3Two.borelSL, σ a w = w := by
    intro a ha
    rw [←hS] at ha
    obtain ⟨l,hl,rfl⟩ := ha
    have hh := congrArg (fun ψ : Representation (ZMod 2) L W => ψ l w) hσ
    exact hh.trans (hfix l hl)
  have hfull : orbitSpan σ ⊤ w = ⊤ := by
    rw [←map_top_of_surjective q hq,spanRecognition_orbit_map,hσ]
    exact hgen
  have hdim : Module.finrank (ZMod 2) (orbitSpan σ Matrix.PSL3Two.lineParabolicSL w) = 2 := by
    rw [←hP,spanRecognition_orbit_map,hσ]
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

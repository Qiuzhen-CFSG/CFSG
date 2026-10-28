module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialSpanCentral
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialSpanFaithfulPlane
public import Theory.Representation.BinaryConjugationSection.IntersectedChiefFactor

/-!
# The two original module alternatives for R/V

The faithful chief interval meets R in a noncentral point-residual plane.
Compare its literal coordinates with R/V: its kernel is the image of the
original lower endpoint. Together with E/V, these give two noncentral
chief intervals. The original centralizer bounds make both intervening
gaps central. Refining the gaps proves an exact count of two.

The five marked H.6.5 alternatives have counts one through five, so only
the six-dimensional core survives in the faithful branch. The original
central branch has count one and is dual-natural. The final original-group
application discharges the chief-interval premises and retains the actual
L quotient map, dual marking, exact H-kernel and both central flanks.

Source: Aschbacher–Smith 14.7.23, printed pp.1050–1051,
refs/quasithin.pdf. The retained earlier source implications have their
existing producers; their final discharge remains with qt-d-14775-source.
Maximal-normalizer control and the later local residual reductions through
14.7.52 remain open.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}




open NoncentralChiefRefinement BinaryLinearThree.ParabolicCyclic.ChiefCounts in
/-- The faithful interval contributes precisely one further noncentral factor
to R/V, in addition to E/V. Both gaps are the original central flanks. -/
theorem extraspecial_span_count_two_of_faithful_interval
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (N B : NormalNode F.H) (hNB : N ⋖ B)
    (hUN : F.U ≤ N.val.map F.H.subtype)
    (hBC : B.val.map F.H.subtype ≤ centralizer (F.U : Set G))
    (hm : ¬ ⁅F.Li L 1,B.val.map F.H.subtype⁆ ≤ N.val.map F.H.subtype)
    (hupper : ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype)
    (hlower : ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U)
    {X : Type u} [AddCommGroup X] [Module (ZMod 2) X]
    {τ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) X}
    (s : BinaryConjugationSection (L ⊔ (T : Subgroup G))
      (conjugateSpanBy ⁅F.U,Q T L⁆ L) V τ) :
    HasCount (τ.comp (inclusion (((F.Li_le L 1).trans inf_le_left).trans
      (le_sup_left : L ≤ L ⊔ (T : Subgroup G))))) 2 := by
  let : Finite X := Finite.of_surjective (fun r => (s.coordinates r).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  let R := conjugateSpanBy ⁅F.U,Q T L⁆ L
  let E := ⁅F.U,Q T L⁆
  let j : F.Li L 1 →* (L ⊔ (T : Subgroup G) : Subgroup G) :=
    inclusion (((F.Li_le L 1).trans inf_le_left).trans le_sup_left)
  have hnorm (D : NormalNode F.H) : F.H ≤ normalizer (D.val.map F.H.subtype : Set G) := by
    have hh := (map_mono (f := F.H.subtype)
      (show (⊤ : Subgroup F.H) ≤ normalizer (D.val : Set F.H) from le_normalizer_of_normal)).trans
        (D.val.le_normalizer_map F.H.subtype)
    simpa only [←MonoidHom.range_eq_map,range_subtype] using hh
  let I (D : NormalNode F.H) : Subrepresentation (τ.comp j) := {
    toSubmodule := s.imageSpace (D.val.map F.H.subtype)
    apply_mem_toSubmodule a x hx := s.imageSpace_apply_mem _ (j a)
      (hnorm D (F.Li_le L 1 a.property).2) x hx }
  obtain ⟨c,hs,_,_,_,_,_,_,_,_,_,_,hRC,_,hinter,_⟩ :=
    extraspecial_span_source_reduction h hab structural previous faithful he
  obtain ⟨D,hD,hirr⟩ := extraspecial_span_plane_irreducible h hab structural previous faithful he s
  have hatom : IsAtom D := (Subrepresentation.irreducible_iff_isAtom D).mp hirr
  have hDN : D ≤ I N := by
    change D.toSubmodule ≤ s.imageSpace (N.val.map F.H.subtype)
    rw [hD]
    exact s.imageSpace_mono ((hinter.symm.le.trans inf_le_left).trans hUN)
  have hIB : I N ≤ I B := s.imageSpace_mono (map_mono hNB.le)
  have hcentral₀ : Central D (I N) := by
    have hcomm : ⁅F.Li L 1,R ⊓ N.val.map F.H.subtype⁆ ≤ E := by
      change ⁅F.Li L 1,R ⊓ N.val.map F.H.subtype⁆ ≤ ⁅F.U,Q T L⁆
      rw [←hinter]
      apply le_inf
      · rw [commutator_comm]
        exact (commutator_mono inf_le_right (pointResidual_le F)).trans hlower
      · exact (commutator_mono le_rfl inf_le_left).trans
          (le_normalizer_iff_commutator_le_right.mp
            ((((F.Li_le L 1).trans inf_le_left).trans le_sup_left).trans s.normalized))
    intro a x hx
    change τ (j a) x-x ∈ D.toSubmodule
    rw [hD]
    apply s.imageSpace_mono hcomm
    rw [s.imageSpace_commutator _ _
      (((F.Li_le L 1).trans inf_le_left).trans le_sup_left) inf_le_left]
    apply Submodule.subset_span
    refine ⟨j a,a.property,x,?_,rfl⟩
    obtain ⟨r,hr,heq⟩ := (s.mem_imageSpace_iff _ x).mp hx
    exact (s.mem_imageSpace_iff _ x).mpr ⟨r,⟨r.property,hr⟩,heq⟩
  have hcentral₁ : Central (I B) ⊤ := by
    have hcomm : ⁅F.Li L 1,R⁆ ≤ B.val.map F.H.subtype := by
      rw [commutator_comm]
      exact (commutator_mono (hRC.trans inf_le_right) (pointResidual_le F)).trans hupper
    intro a x _
    change τ (j a) x-x ∈ s.imageSpace (B.val.map F.H.subtype)
    apply s.imageSpace_mono hcomm
    rw [s.imageSpace_commutator _ _
      (((F.Li_le L 1).trans inf_le_left).trans le_sup_left) le_rfl,s.imageSpace_self]
    exact Submodule.subset_span ⟨j a,a.property,x,Submodule.mem_top,rfl⟩
  have hnoncentral : ¬ Central ⊥ D := by
    intro htriv
    obtain ⟨a,ha,hn⟩ := extraspecial_span_plane_cubic_norm h hab structural previous he s
    apply hatom.ne_bot
    apply bot_unique
    intro x hx
    have hfix : τ a x=x := sub_eq_zero.mp (htriv ⟨a,ha⟩ x hx)
    have hh := hn x (hD ▸ hx)
    rw [hfix,hfix] at hh
    have hxx : x+x=0 := by
      calc x+x = (2 : ZMod 2) • x := (two_smul (ZMod 2) x).symm
           _ = 0 := by simp
    change x = 0
    simpa only [hxx,zero_add] using hh
  obtain ⟨Y,ha,hmY,ρ,t,J,hJ,_,hJirr,hJnc,_,_⟩ :=
    extraspecial_span_faithful_interval h hab structural previous faithful he N B hNB hUN hBC hm
  let : J.toRepresentation.IsIrreducible := hJirr
  obtain ⟨f,hf,hk⟩ := BinaryConjugationSection.exists_intersection_intertwiner
    (((F.Li_le L 1).trans inf_le_left).trans le_sup_left)
    ((F.Li_le L 1).trans inf_le_right) s t ((le_conjugateSpanBy V F.H).trans hUN)
    (I N) (I B) J rfl rfl hJ
  have hJmove : ¬ ∀ a y, J.toRepresentation a y = y := by
    intro htriv
    apply hJnc
    intro a y hy
    exact sub_eq_zero.mpr (congrArg Subtype.val (htriv a ⟨y,hy⟩))
  obtain ⟨hcover,hnc⟩ := BinaryConjugationSection.chief_interval_of_surjective_intertwiner (ν := J.toRepresentation) (I N) (I B) hIB f hf hk hJmove
  have h01 := exists_series_count_join
    (exists_noncentral_chief_series ⊥ D (bot_covBy_iff.mpr hatom) hnoncentral)
    (exists_central_series D (I N) hDN hcentral₀)
  have h012 := exists_series_count_join h01
    (exists_noncentral_chief_series (I N) (I B) hcover hnc)
  simpa only [HasCount,Nat.add_zero,Nat.reduceAdd] using exists_series_count_join h012
    (exists_central_series (I B) ⊤ le_top hcentral₁)

open NoncentralChiefRefinement BinaryLinearThree.ParabolicCyclic
  BinaryLinearThree.ParabolicCyclic.ChiefCounts in
/-- Source 14.7.23's two module alternatives for the original R/V. The
central case is the dual-natural action; the faithful case is the six-dimensional
permutation core under the same dual marking. The original quotient map,
point-parabolic marking, chief kernels, and both central flanks are retained. -/
theorem extraspecial_span_two_module_alternatives
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
      ((⁅centralizer (F.U : Set G),K F⁆ ≤ F.U ∧
        Nonempty (σ.Equiv BinaryLinearThree.W) ∧
        Nonempty (Representation.Equiv (ρ.comp (inclusion le_sup_left))
          (BinaryLinearThree.W.dual.comp (SpanMarking.qL h))) ∧
        HasCount (ρ.comp (inclusion (((F.Li_le L 1).trans inf_le_left).trans
          (le_sup_left : L ≤ L ⊔ (T : Subgroup G))))) 1) ∨
       (Nonempty (σ.Equiv BinaryLinearThree.U₂) ∧
        Nonempty (Representation.Equiv (ρ.comp (inclusion le_sup_left))
          (BinaryLinearThree.U₂.comp (e.symm.toMonoidHom.comp (SpanMarking.qL h)))) ∧
        HasCount (ρ.comp (inclusion (((F.Li_le L 1).trans inf_le_left).trans
          (le_sup_left : L ≤ L ⊔ (T : Subgroup G))))) 2 ∧
        ∃ N B : NormalNode F.H, N ⋖ B ∧
          F.U ≤ N.val.map F.H.subtype ∧ B.val.map F.H.subtype ≤ centralizer (F.U : Set G) ∧
          ¬ ⁅F.Li L 1,B.val.map F.H.subtype⁆ ≤ N.val.map F.H.subtype ∧
          Nat.card (Section N B) = 64 ∧ (sectionAction N B).ker = pCore 2 F.H ∧
          ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype ∧
          ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U)) := by
  obtain ⟨W,ha,hm,ρ,s,e,σ,hker,hσ,hS,hP,hdual,hclass,_⟩ :=
    extraspecial_span_module_alternatives h hab structural previous faithful he
  let q := e.symm.toMonoidHom.comp (SpanMarking.qL h)
  refine ⟨W,ha,hm,ρ,s,e,σ,hker,hσ,hS,hP,hdual,?_⟩
  obtain ⟨_,hc | ⟨N,B,hNB,hUN,hBC,hmove,hsize,hkernel,hupper,hlower⟩⟩ :=
    extraspecial_centralizer_core_reduction_no_small_intervals h hab structural previous faithful he
  · have hcount := extraspecial_span_count_one_of_central h hab structural previous faithful he hc s
    have hnat : Nonempty (σ.Equiv BinaryLinearThree.W) := by
      rcases extraspecial_span_counted_alternatives q hP σ hσ hclass with hh | hh | hh | hh | hh
      · exact hh.1
      all_goals have := hcount.unique hh.2; omega
    obtain ⟨en⟩ := hnat
    obtain ⟨ed⟩ := hdual
    refine Or.inl ⟨hc,⟨en⟩,?_,hcount⟩
    rw [←hσ]
    exact ⟨(restrictEquiv en q).trans (restrictEquiv ed (SpanMarking.qL h))⟩
  · have hcount := extraspecial_span_count_two_of_faithful_interval h hab structural previous faithful he
      N B hNB hUN hBC hmove hupper hlower s
    have hcore : Nonempty (σ.Equiv BinaryLinearThree.U₂) := by
      rcases extraspecial_span_counted_alternatives q hP σ hσ hclass with hh | hh | hh | hh | hh
      · have := hcount.unique hh.2; omega
      · exact hh.1
      all_goals have := hcount.unique hh.2; omega
    obtain ⟨ec⟩ := hcore
    refine Or.inr ⟨⟨ec⟩,?_,hcount,N,B,hNB,hUN,hBC,hmove,hsize,hkernel,hupper,hlower⟩
    rw [←hσ]
    exact ⟨restrictEquiv ec q⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction

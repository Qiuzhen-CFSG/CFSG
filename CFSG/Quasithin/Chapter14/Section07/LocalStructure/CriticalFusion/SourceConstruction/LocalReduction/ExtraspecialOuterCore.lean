module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialOuterRecognition
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialOuterFixedPlane
public import Theory.Representation.BinaryConjugationSection.RelativeIntersectedChiefFactor
public import Theory.Representation.PSL3Two.ParabolicCyclic.ChiefCounts.Refinement

/-!
# Core recognition in the original central branch

Under [C_H(U),K] ≤ U, compare S/R with P/C_P(U). Their relative
intersection R ∩ P lies in C_P(U); R itself need not lie in P. The
comparison therefore retains precisely this relative kernel. It gives
one noncentral chief plane above the image of C_P(U). The original U/E
is another such plane. The two remaining gaps are central for L₁.

Refining these gaps proves an exact count of two noncentral factors.
The five marked H.6.5 possibilities have distinct counts, so S/R is
actually equivariantly isomorphic to the six-dimensional permutation core,
with the original quotient map and dual parabolic marking retained.

Source: Aschbacher–Smith 14.7.24(1), printed p.1051, refs/quasithin.pdf.
All local recognition premises are proved here; the genuine earlier source
inputs retain their producers and final discharge at qt-d-14775-source.
The central-subgroup deduction is in ExtraspecialCentralCompletion.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Point normality places the original [S,L₁] inside P = O₂(K). -/
theorem extraspecial_outer_commutator_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ⁅conjugateSpanBy F.U L,F.Li L 1⁆ ≤ (K F).pCoreIn 2 := by
  have hn := (extraspecial_source_reduction h hab structural previous he).1
  have hHnA := (normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn
  have hSQ := (original_span_le_core h hab structural).2
  have hAL := (F.Li_le L 1).trans inf_le_left
  have hAQ : F.Li L 1 ≤ normalizer (Q T L : Set G) :=
    (hAL.trans le_sup_left).trans
      ((L ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hc : ⁅conjugateSpanBy F.U L,F.Li L 1⁆ ≤ F.Li L 1 ⊓ Q T L := le_inf
    (le_normalizer_iff_commutator_le_right.mp ((hSQ.trans (Q_le_H F)).trans hHnA))
    ((commutator_mono hSQ le_rfl).trans (le_normalizer_iff_commutator_le_left.mp hAQ))
  exact (hc.trans (inf_pCoreIn_le_of_le 2 (hAL.trans le_sup_left))).trans_eq
    (extraspecial_centralizer_core_reduction_no_small_intervals h hab structural previous faithful he).1

private theorem outerCount_irreducible_plane
    {A X : Type*} [Group A] [AddCommGroup X] [Module (ZMod 2) X]
    [FiniteDimensional (ZMod 2) X]
    (τ : Representation (ZMod 2) A X) (hd : Module.finrank (ZMod 2) X = 2)
    (hf : ∀ x, (∀ a, τ a x = x) → x = 0) : τ.IsIrreducible := by
  let : Nontrivial X := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank (ZMod 2) X)
  rw [Representation.IsIrreducible,isSimpleOrder_iff]
  refine ⟨inferInstance,fun N => ?_⟩
  by_cases hb : N = ⊥
  · exact Or.inl hb
  by_cases ht : N = ⊤
  · exact Or.inr ht
  exfalso
  have hNb : N.toSubmodule ≠ ⊥ := fun hh => hb (Subrepresentation.toSubmodule_injective hh)
  have hNt : N.toSubmodule ≠ ⊤ := fun hh => ht (Subrepresentation.toSubmodule_injective hh)
  have hpos : 0 < Module.finrank (ZMod 2) N.toSubmodule :=
    Nat.pos_of_ne_zero (fun hh => hNb (Submodule.finrank_eq_zero.mp hh))
  have hlt := Submodule.finrank_lt hNt
  have hdim : Module.finrank (ZMod 2) N.toSubmodule = 1 := by omega
  apply hNb
  apply bot_unique
  intro x hx
  exact hf x (fun a => by
    have hh := BinaryParabolicNatural.linear_one_trivial hdim
      (LinearMap.GeneralLinearGroup.toLinearEquiv (N.toRepresentation.asGroupHom a))
    exact congrArg (fun f : N.toSubmodule ≃ₗ[ZMod 2] N.toSubmodule => (f ⟨x,hx⟩ : X)) hh)

open BinaryLinearThree.ParabolicCyclic.ChiefCounts in
/-- The central case has exactly two noncentral L₁-chief factors on the
literal S/R, using both original quotient maps. -/
theorem extraspecial_outer_count_two_of_central
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (hc : ⁅centralizer (F.U : Set G),K F⁆ ≤ F.U)
    {X : Type u} [AddCommGroup X] [Module (ZMod 2) X]
    {τ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) X}
    (s : BinaryConjugationSection (L ⊔ (T : Subgroup G))
      (conjugateSpanBy F.U L) (conjugateSpanBy ⁅F.U,Q T L⁆ L) τ) :
    HasCount (τ.comp (inclusion (((F.Li_le L 1).trans inf_le_left).trans
      (le_sup_left : L ≤ L ⊔ (T : Subgroup G))))) 2 := by
  let : Finite X := Finite.of_surjective (fun x => (s.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  let P := (K F).pCoreIn 2
  let PC := P ⊓ centralizer (F.U : Set G)
  let S := conjugateSpanBy F.U L
  let R := conjugateSpanBy ⁅F.U,Q T L⁆ L
  let j : F.Li L 1 →* (L ⊔ (T : Subgroup G) : Subgroup G) :=
    inclusion (((F.Li_le L 1).trans inf_le_left).trans le_sup_left)
  have hnP : F.H ≤ normalizer (P : Set G) :=
    (H_normalizes_K F).trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 (K F)))
  have hnPC : F.H ≤ normalizer (PC : Set G) :=
    (le_inf hnP ((le_normalizer_conjugateSpanBy V F.H).trans
      (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  let I (B : Subgroup G) (hnB : F.H ≤ normalizer (B : Set G)) : Subrepresentation (τ.comp j) := {
    toSubmodule := s.imageSpace B
    apply_mem_toSubmodule a x hx := s.imageSpace_apply_mem _ (j a)
      (hnB (F.Li_le L 1 a.property).2) x hx }
  let N := I PC hnPC
  let B := I P hnP
  obtain ⟨D,hD,hirr⟩ := extraspecial_outer_plane_irreducible h hab structural previous faithful he s
  have hatom : IsAtom D := (Subrepresentation.irreducible_iff_isAtom D).mp hirr
  have hUPC : F.U ≤ PC := le_inf (span_le_residual_core h hab)
    (le_centralizer_iff_isMulCommutative.mpr hab)
  have hDN : D ≤ N := by
    change D.toSubmodule ≤ s.imageSpace PC
    rw [hD]
    exact s.imageSpace_mono hUPC
  have hNB : N ≤ B := s.imageSpace_mono inf_le_left
  have hcentral₀ : Central D N := by
    have hcomm : ⁅F.Li L 1,S ⊓ PC⁆ ≤ F.U := by
      rw [commutator_comm]
      exact (commutator_mono (inf_le_right.trans inf_le_right) (pointResidual_le F)).trans hc
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
  have hcentral₁ : Central B ⊤ := by
    have hcomm : ⁅F.Li L 1,S⁆ ≤ P := by
      rw [commutator_comm]
      exact extraspecial_outer_commutator_core h hab structural previous faithful he
    intro a x _
    change τ (j a) x-x ∈ s.imageSpace P
    apply s.imageSpace_mono hcomm
    rw [s.imageSpace_commutator _ _
      (((F.Li_le L 1).trans inf_le_left).trans le_sup_left) le_rfl,s.imageSpace_self]
    exact Submodule.subset_span ⟨j a,a.property,x,Submodule.mem_top,rfl⟩
  have hnoncentral : ¬ Central ⊥ D := by
    intro htriv
    obtain ⟨a,ha,hn⟩ := extraspecial_outer_plane_cubic_norm h hab structural previous faithful he s
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
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  obtain ⟨Y,ha,hm,ρ,sU,sP,_,_,_⟩ := extraspecial_core_duality
    h hab structural previous hex hcard hexp P (Or.inr rfl)
  let : Finite Y := Finite.of_surjective (fun u => (sU.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp sU.onto)
  let k : F.Li L 1 →* F.H := inclusion ((F.Li_le L 1).trans inf_le_right)
  let J : Subrepresentation (ρ.dual.comp k) := {
    toSubmodule := sP.imageSpace S
    apply_mem_toSubmodule a y hy := sP.imageSpace_apply_mem S (k a)
      ((original_outer_span_normalized h structural)
        ((le_sup_left : L ≤ L ⊔ (T : Subgroup G)) (F.Li_le L 1 a.property).1)) y hy }
  obtain ⟨_,hd,hfree⟩ := extraspecial_core_outer_fixed_plane h hab structural previous faithful ⟨e⟩ sU sP
  let : J.toRepresentation.IsIrreducible := outerCount_irreducible_plane _ hd (by
    intro w hw
    apply Subtype.ext
    exact hfree w (fun a => congrArg Subtype.val (hw a)))
  have hJmove : ¬ ∀ a y, J.toRepresentation a y = y := by
    intro htriv
    have hz : J.toSubmodule = ⊥ := by
      apply bot_unique
      intro y hy
      exact hfree y (fun a => congrArg Subtype.val (htriv a ⟨y,hy⟩))
    change Module.finrank (ZMod 2) J.toSubmodule = 2 at hd
    rw [hz,finrank_bot] at hd
    contradiction
  obtain ⟨c,hs,_,_,_,_,_,_,_,_,_,_,hRC,_⟩ :=
    extraspecial_span_source_reduction h hab structural previous faithful ⟨e⟩
  have hRP : R ⊓ P ≤ PC := le_inf inf_le_right ((inf_le_left.trans hRC).trans inf_le_right)
  obtain ⟨f,hf,hk⟩ := BinaryConjugationSection.exists_relative_intersection_intertwiner
    (((F.Li_le L 1).trans inf_le_left).trans le_sup_left)
    ((F.Li_le L 1).trans inf_le_right) s sP inf_le_left hRP
    N B J rfl rfl rfl
  obtain ⟨hcover,hnc⟩ := BinaryConjugationSection.chief_interval_of_surjective_intertwiner
    (X := X) (Y := J.toSubmodule) (τ := τ.comp j) (ν := J.toRepresentation) N B hNB f hf hk hJmove
  have h01 := exists_series_count_join
    (exists_noncentral_chief_series ⊥ D (bot_covBy_iff.mpr hatom) hnoncentral)
    (exists_central_series D N hDN hcentral₀)
  have h012 := exists_series_count_join h01 (exists_noncentral_chief_series N B hcover hnc)
  simpa only [HasCount,Nat.add_zero,Nat.reduceAdd] using exists_series_count_join h012
    (exists_central_series B ⊤ le_top hcentral₁)
open BinaryLinearThree.ParabolicCyclic.ChiefCounts in
/-- Source 14.7.24(1): the actual outer quotient is the marked permutation core. -/
theorem extraspecial_outer_core_of_central
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (hc : ⁅centralizer (F.U : Set G),K F⁆ ≤ F.U)
 :
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
      Nonempty (σ.Equiv BinaryLinearThree.U₂) ∧
      Nonempty (Representation.Equiv (ρ.comp (inclusion le_sup_left))
        (BinaryLinearThree.U₂.comp (e.symm.toMonoidHom.comp (SpanMarking.qL h)))) ∧
      HasCount (ρ.comp (inclusion (((F.Li_le L 1).trans inf_le_left).trans
        (le_sup_left : L ≤ L ⊔ (T : Subgroup G))))) 2 := by
  obtain ⟨W,ha,hm,ρ,s,e,σ,hker,hσ,hS,hP,hdual,hclass,_⟩ :=
    extraspecial_outer_module_alternatives h hab structural previous faithful he
  have hcount := extraspecial_outer_count_two_of_central h hab structural previous faithful he hc s
  let q := e.symm.toMonoidHom.comp (SpanMarking.qL h)
  have hcore : Nonempty (σ.Equiv BinaryLinearThree.U₂) := by
    rcases extraspecial_span_counted_alternatives q hP σ hσ hclass with hh | hh | hh | hh | hh
    · have := hcount.unique hh.2; omega
    · exact hh.1
    all_goals have := hcount.unique hh.2; omega
  obtain ⟨ec⟩ := hcore
  refine ⟨W,ha,hm,ρ,s,e,σ,hker,hσ,hS,hP,hdual,⟨ec⟩,?_,hcount⟩
  rw [←hσ]
  exact ⟨restrictEquiv ec q⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction

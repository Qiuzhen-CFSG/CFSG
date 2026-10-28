module

public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Mathieu.Partner
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.CoreGeometry
public import CFSG.Quasithin.ChapterH.Section10To12.TripleRecognition.Restriction
public import Theory.Representation.Mathieu.M22James.NoFF.GroupBounds

/-!
# Identifying the original Mathieu action

James's intertwiner identifies the faithful irreducible twelve-dimensional
module on the triple-cover component. Conjugating the whole action through
that intertwiner gives a faithful matrix representation with the literal
native component as its image. The native matrix normalizer then identifies
the whole group, provided that the component is proper.

For the original flag, G.10's dimension inequality forces the elementary
actor to have rank at least five. The triple cover itself has two-rank at
most four, so the component is proper. This supplies both compatible group
and module coordinates to the completed Mathieu partner construction and
its large-case contradiction. The catalogue row remains explicit; this
module does not classify all possible source actions.

Source: Aschbacher--Smith, 14.4.2(6), 14.4.12--14, printed pp.1006,1011--1012;
H.12.1(1,3), pp.393--394, using James (1973), Lemma 8.3.
-/

public noncomputable section

open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative Matrix
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.Mathieu
open LargerDimension.LocalAction.Components
open ChapterH.Section10To12
open Sporadic.Mathieu
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel

private theorem mathieu_coordinates_of_component
    {Q W : Type*} [Group Q] [Finite Q] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) Q W) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) (hd : finrank (ZMod 2) W = 12)
    (K : Subgroup Q) (hK : IsTripleM22 K) (hF : generalizedFitting Q = K)
    (hproper : K ≠ ⊤) :
    ∃ e : Q ≃* ActorCatalogue.Native.Model,
    ∃ c : W ≃ₗ[ZMod 2] ActorCatalogue.Native.Space,
      ∀ a w, c (ρ a w) = ActorCatalogue.Native.action (e a) (c w) := by
  let : K.Normal := hF ▸ inferInstance
  obtain ⟨c⟩ := TripleRecognition.restriction_equiv_of_generalizedFitting
    K hK hF ρ hf hd
  let e := hK.groupEquiv
  let f : Q →* Matrix12ˣ :=
    (Units.mapEquiv Matrix.toLinAlgEquiv'.symm.toMulEquiv).toMonoidHom.comp
      ((LinearMap.GeneralLinearGroup.congrLinearEquiv c.toLinearEquiv).toMonoidHom.comp
        ρ.asGroupHom)
  have hact (a : Q) (w : W) :
      (f a : Matrix12) *ᵥ (c w) = c (ρ a w) := by
    change (Matrix.toLinAlgEquiv' (Matrix.toLinAlgEquiv'.symm
      (c.toLinearEquiv.conjRingEquiv (ρ a)))) (c w) = _
    rw [Matrix.toLinAlgEquiv'.apply_symm_apply]
    change c (ρ a (c.toLinearEquiv.symm (c w))) = c (ρ a w)
    exact congrArg (fun x => c (ρ a x)) (c.toLinearEquiv.symm_apply_apply w)
  have hfi : Function.Injective f := by
    intro a b hab
    apply hf
    apply LinearMap.ext
    intro w
    apply c.injective
    change c (ρ a w) = c (ρ b w)
    rw [← hact,← hact,hab]
  have hcomp (k : K) : f k = (e k).val := by
    apply Units.ext
    apply Matrix.toLinAlgEquiv'.injective
    apply LinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := c.toLinearEquiv.surjective w
    change (f k : Matrix12) *ᵥ (c v) = M22TripleCover.binaryRepresentation (e k) (c v)
    rw [hact]
    exact Representation.IntertwiningMap.isIntertwining _ _ c.toIntertwiningMap k v
  have hm : K.map f = derivedGroup := by
    ext a
    constructor
    · rintro ⟨k,hk,rfl⟩
      rw [hcomp ⟨k,hk⟩]
      exact (e ⟨k,hk⟩).property
    · intro ha
      obtain ⟨k,hk⟩ := e.surjective ⟨a,ha⟩
      exact ⟨k,k.property,(hcomp k).trans (congrArg Subtype.val hk)⟩
  refine ⟨ActorCatalogue.Native.equivOfMatrixComponent K f hfi hm hproper,
    c.toLinearEquiv,?_⟩
  intro a w
  rw [ActorCatalogue.Native.equivOfMatrixComponent_action]
  exact (hact a w).symm

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The source dimension and the actual elementary actor force the triple
component to have a proper outer extension. -/
theorem source_mathieu_component_proper (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (hK : IsTripleM22 (generalizedFitting (coreQuotient F.H)))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 12) :
    generalizedFitting (coreQuotient F.H) ≠ ⊤ := by
  intro ht
  obtain ⟨g,_,hgP,hgH⟩ := exists_source_conjugator d earlier hq chosen structural F
  obtain ⟨_,hx,B,v,hyp⟩ := source_terminal_hypothesis F d earlier hq chosen
    structural alternatives hne g hgP hgH
  let := hx
  let e : F.TerminalHdot ≃* M22TripleCover :=
    (QuotientGroup.quotientMulEquivOfEq
      (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ)).trans
      (Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr ht).symm.trans hK.groupEquiv))
  have hr : Group.rank (F.terminalDot (F.X g)) ≤ 4 := by
    have h := Subgroup.rank_le_primeRank 2 (F.terminalDot (F.X g))
      (IsElementaryAbelian.isPGroup 2 (F.terminalDot (F.X g)))
    exact h.trans ((primeRank_congr 2 e).trans_le M22TripleCover.NoFF.twoRank_le_four)
  have hqrank := Group.rank_le_of_surjective
    (QuotientGroup.mk' ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (QuotientGroup.mk'_surjective _)
  have hb := hyp.dimension_bound.1
  rw [hd] at hb
  omega


/-- The triple-cover action row gives compatible coordinates on the whole
source quotient and its module; the outer-extension premise is derived. -/
theorem source_mathieu_coordinates (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (hK : IsTripleM22 (generalizedFitting (coreQuotient F.H)))
    (hirr : letI := chosen.elementary
      letI := F.U_normal
      (CoreGeometry.sourceAction F
        (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ)).representation.IsIrreducible)
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 12) :
    ∃ e : coreQuotient F.H ≃* ActorCatalogue.Native.Model,
    ∃ c : Additive F.Uhat ≃ₗ[ZMod 2] ActorCatalogue.Native.Space,
      ∀ (a : F.H) w,
        ActorCatalogue.Native.action (ActorCatalogue.starProjection F.H e a) (c w) =
          c (F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) w) := by
  let := chosen.elementary
  let := F.U_normal
  let s := CoreGeometry.sourceAction F
    (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ)
  let : s.representation.IsIrreducible := hirr
  obtain ⟨e,c,hc⟩ := mathieu_coordinates_of_component s.representation s.faithful hd
    _ hK rfl (source_mathieu_component_proper d earlier hq chosen structural alternatives F hne hZ hK hd)
  refine ⟨e,c,?_⟩
  intro a w
  exact (hc (QuotientGroup.mk' (pCore 2 F.H) a) w).symm

/-- The completed Mathieu exclusion now consumes only its action-catalogue
row, without an assumed native marking or proper-extension witness. -/
theorem source_mathieu_exclusion (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (hlarge : 64 < Nat.card F.U)
    (hK : IsTripleM22 (generalizedFitting (coreQuotient F.H)))
    (hirr : letI := chosen.elementary
      letI := F.U_normal
      (CoreGeometry.sourceAction F
        (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ)).representation.IsIrreducible)
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 12) : False := by
  obtain ⟨e,c,hc⟩ := source_mathieu_coordinates d earlier hq chosen structural alternatives
    F hne hZ hK hirr hd
  obtain ⟨g,hg,hgP,hgH⟩ := exists_source_conjugator d earlier hq chosen structural F
  exact source_mathieu_contradiction d earlier hq chosen structural alternatives classification
    F hne hZ hlarge g hg hgP hgH e c hc

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

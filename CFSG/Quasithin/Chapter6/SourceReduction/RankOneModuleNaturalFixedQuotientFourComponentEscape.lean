module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientFourComponentModule
public import Theory.Representation.BinaryOffender.NormalizerNonFF

/-!
# The two-generalized-Fitting preimage escapes the original maximal local

The actual C.2.7 radical supplies a best offender on the full original R₂(LT).
Its faithful action in LR/C(R₂) has a normal Hermitian component. Coordinates
embed that action in the full linear normalizer, which is non-FF when s > 1.
Consequently the two-generalized-Fitting preimage of a maximal two-local
containing C_G(Ω₁Z(T)) cannot be contained in M.

Source: Aschbacher--Smith 6.1.4, printed p.666, using C.2.7 and D.3.3.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open ChapterA.Section04 RankOneGeneric OrthogonalFourMinus.FiniteModel
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ : Subgroup G} {n s : ℕ} [NeZero s]
local instance componentEscapeFixedAlgebra : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance componentEscapeBinaryModule : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))

/-- The actual preimage O_{2,F*}(M₁) escapes M. All radical placement and FF
inputs are derived from the original hypotheses and the full Hermitian model. -/
theorem full_reduced_hermitian_component_escape
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian s)) (hs : 1 < s)
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁) :
    ¬ twoGeneralizedFittingPreimage M₁ ≤ M := by
  intro hF
  let R := M₁.pCoreIn 2
  let B := reducedSubgroup (L ⊔ (T : Subgroup G))
  let J := L ⊔ R
  let U := B.subgroupOf J
  have hi := full_reduced_hermitian_component_input h hout hm hs hM₁ hCM₁ hF
  obtain ⟨hBQ,hQR,hred⟩ := full_reduced_hermitian_component_module h hout hm hs hM₁ hCM₁ hF
  let := hred.normal
  let := hred.elementary
  have hBR : B ≤ R := hBQ.trans hQR
  have hBJ : B ≤ J := hBR.trans le_sup_right
  have hmove : ⁅U,L.subgroupOf J⁆ ≠ ⊥ := by
    intro hz
    have hh := congrArg (map J.subtype) hz
    rw [map_commutator, map_subgroupOf_eq_of_le hBJ,
      map_subgroupOf_eq_of_le (show L ≤ J from le_sup_left), Subgroup.map_bot] at hh
    exact h.reduced_enlargement_nontrivial hh
  let C := centralizer (U : Set J)
  let q := QuotientGroup.mk' C
  let hq := QuotientGroup.mk'_surjective C
  let hk := QuotientGroup.ker_mk' C
  let ρ := NormalElementaryQuotient.representation U q hq hk
  obtain ⟨A,_,hA⟩ := ChapterC.C27Source.best_offender_on_reduced_submodule hi U hred
    (subgroupOf_mono _ hBR) hmove
  have hff : IsFFModule ρ := (isFFModule_iff_exists_bestOffender ρ).mpr ⟨A.map q,hA⟩
  obtain ⟨e0,f0,hf0⟩ := hm
  let K := L.subgroupOf J
  let : K.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hi.normalizes)
  let i : L →* J ⧸ C := q.comp (inclusion (show L ≤ J from le_sup_left))
  have hir : i.range = K.map q := by
    ext a
    constructor
    · rintro ⟨l,rfl⟩
      exact ⟨inclusion le_sup_left l,l.property,rfl⟩
    · rintro ⟨l,hl,rfl⟩
      exact ⟨⟨l,hl⟩,rfl⟩
  let : i.range.Normal := hir ▸ Normal.map inferInstance q hq
  let f : L →* Matrix.SpecialLinearGroup (Fin 2) (Field s) :=
    e0.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let uB := subgroupOfEquivOfLe hBJ
  let c : Additive U ≃ₗ[ZMod 2] Space s :=
    LinearEquiv.ofBijective ((uB.trans f0).toMonoidHom.toAdditiveLeft.toZModLinearMap 2)
      (uB.trans f0).bijective
  let b : Representation.Equiv (ρ.comp i) ((SL2.BinarySmall.hermitian s).comp f) :=
    { __ := c
      isIntertwining' l := by
        apply LinearMap.ext
        intro x
        let v : B := uB x.toMul
        have hact := hf0 l v
        have hcoords := congrArg f0
          (show f0.symm (Multiplicative.ofAdd
            (SL2.BinarySmall.hermitian s (f l) (f0 v).toAdd)) =
            B.normalizerMonoidHom
              ⟨l,(le_sup_left.trans (reduced_normalizes
                (reducedSubgroup_mem (L ⊔ (T : Subgroup G))))) l.property⟩ v from
            Subtype.ext hact)
        rw [f0.apply_symm_apply] at hcoords
        change c (ρ (q (inclusion le_sup_left l)) x) = _
        apply Eq.trans ?_ (congrArg Multiplicative.toAdd hcoords.symm)
        apply congrArg (fun w : B => (f0 w).toAdd)
        apply Subtype.ext
        change (((NormalElementaryQuotient.representation U q hq hk
          (q (inclusion le_sup_left l)) x).toMul : J) : G) = _
        rw [NormalElementaryQuotient.representation_apply]
        rfl }
  have hL : IsSQTK KnownSimple.IsKnownSimple L :=
    ((h.simpleQTKE.twoLocal_sqtk h.maximal.1).subgroup (L.subgroupOf M)).knownSimple_of_equiv
      (subgroupOfEquivOfLe h.L_le)
  let := hi.quasisimple
  let : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) (Field s)) :=
    IsQuasisimple.of_mulEquiv e0
  have hmodel : IsSQTK KnownSimple.IsKnownSimple (Matrix.SpecialLinearGroup (Fin 2) (Field s)) :=
    (ChapterE.Structure.sqtk_two_quotient hL (pCore 2 L) pCore_isPGroup).knownSimple_of_equiv e0
  exact not_isFFModule_of_marked_normal_range ρ
    (NormalElementaryQuotient.representation_injective U q hq hk) i
    (SL2.BinarySmall.hermitian s) f (e0.surjective.comp (QuotientGroup.mk'_surjective _)) b
    (ChapterD.hermitian_normalizer_not_ff s hmodel hs) hff

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

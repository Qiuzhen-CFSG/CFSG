module

public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.PreparedChosen
public import Theory.Representation.BinaryOffender.InvolutionRatio

/-!
# The literal chosen-module inputs to Section 15.2

This structure collects the original ambient hypotheses and the two remaining
small-action cases. The chosen subgroup is either the original local module or
the mapped support in the original proper case. It contains no conclusions of
Section 15.2. In particular, its small-action alternatives do not assert any
parabolic recognition or centralizer uniqueness theorem.

The quadratic ratio of the prepared module excludes the two-dimensional
dihedral marking: an involution in binary dimension two is an offender.
Consequently the chosen module has dimension four, as asserted in 15.2.1.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.1.3 and
15.2.1, printed pp.1086--1087 and 1104.
-/

public section

open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section02

open Section01 Section03 Section03.InitialSource ChapterA.Section05To06
open ChapterD ChapterD.UniqueFactor

variable {G : Type*} [Group G] [Finite G]

/-- Original source inputs, retaining both the full and the proper chosen module. -/
structure ChosenSmallSource (T : Sylow 2 G) (M Mc V : Subgroup G) : Prop where
  ambient : IsSimpleQTKE KnownSimple.IsKnownSimple G
  empty : MainForward.faithfulLocalComponents T = ∅
  maximal : IsOrderingMaximal T M
  many : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard
  centralizing : elementaryAbelianMaxJ (T : Subgroup G) ≤
    centralizer (localModule T M : Set G)
  partner : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc}
  different : M ≠ Mc
  prepared : PreparedChosenModule T M V
  chosen :
    letI := localModule_elementary_from_source ambient T
      ⟨Chapter1.mem_H_of_isTwoLocal maximal.1.1.1, maximal.1.2⟩
    V = localModule T M ∨ ∃ U : Submodule (ZMod 2) (Additive (localModule T M)),
      SourceCases.Proper T M Mc (localModule T M)
        (imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)) U ∧
      V = (Subgroup.toAddSubgroup.symm U.toAddSubgroup).map (localModule T M).subtype
  small :
    letI := prepared.elementary
    SourceCases.Dihedral (imageRepresentation M V prepared.normalized) ∨
      SourceCases.Omega (imageRepresentation M V prepared.normalized)

/-- The non-FF input used by the critical-distance parity theorem. -/
theorem ChosenSmallSource.not_ff
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V) :
    letI := h.prepared.elementary
    ¬ IsFFModule (imageRepresentation M V h.prepared.normalized) := by
  let := h.prepared.elementary
  intro hff
  have hq := (isFFModule_iff_quadraticRatio_le_one _).mp hff
  rw [h.prepared.quadratic_ratio] at hq
  norm_num at hq

/-- The numerical assertion of original 15.2.1, on the literal chosen module. -/
theorem ChosenSmallSource.finrank_eq_four
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V) :
    letI := h.prepared.elementary
    Module.finrank (ZMod 2) (Additive V) = 4 := by
  let := h.prepared.elementary
  let ρ := imageRepresentation M V h.prepared.normalized
  rcases h.small with ⟨l, p, m, hpm, hd⟩ | ho
  · have hm : m = 2 := by
      rw [ChapterD.CyclicSource.primeDimensionOptions_iff] at hpm
      rcases hpm with ⟨_, hm | hm⟩ | ⟨_, hm⟩
      · have hdim : Module.finrank (ZMod 2) (Additive V) = 2 := by
          simpa only [hm, Nat.mul_one] using hd.dimension
        have ht : orderOf (l.involution : internalActionImage M V h.prepared.normalized) = 2 :=
          (Subgroup.orderOf_coe l.involution).trans l.order_two
        obtain ⟨hA, hr, hquad, hbound⟩ :=
          involution_actor_rank_and_fixedCodim ρ l.involution ht
        have hq := (quadraticRatio_le_one_iff ρ).mpr
          ⟨zpowers (l.involution : internalActionImage M V h.prepared.normalized),
            ⟨hA, by omega⟩, hquad⟩
        rw [h.prepared.quadratic_ratio] at hq
        norm_num at hq
      · exact hm
      · exact hm
    simpa only [hm] using hd.dimension
  · exact ho.2.2.1

/-- The chosen four-space has sixteen elements, independently of full/proper choice. -/
theorem ChosenSmallSource.card_eq_sixteen
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V) :
    Nat.card V = 16 := by
  let := h.prepared.elementary
  change Nat.card (Additive V) = 16
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), h.finrank_eq_four, Nat.card_zmod]
  norm_num

/-- A shared target for the distinguished-plane construction, original
15.2.9--14. The construction, the later uniqueness theorem and the weak-closure
conclusions are separate mathematical obligations. Here `S` is always the
literal centralizer of the plane in `T`. -/
structure ChosenPlaneGeometry {T : Sylow 2 G} {M Mc V : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (H ZS : Subgroup G) : Prop where
  outside : H ∈ Chapter3.HStar (T : Subgroup G) M
  in_partner : H ≤ Mc
  quotient : Nonempty ((H ⧸ pCore 2 H) ≃*
    RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2)))
  full : V = localModule T M
  plane_le : ZS ≤ V
  plane_card : Nat.card ZS = 4
  normalized : H ≤ normalizer (ZS : Set G)
  plane_normalizer : normalizer (ZS : Set G) ≤ Mc
  baumann_le : ChapterB.baumann (T : Subgroup G) ≤
    (T : Subgroup G) ⊓ centralizer (ZS : Set G)

end CFSG.Quasithin.Chapter15.Section02

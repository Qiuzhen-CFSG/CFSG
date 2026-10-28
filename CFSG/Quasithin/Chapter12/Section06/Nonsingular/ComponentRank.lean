module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.ResidualEscape
public import Theory.Mathieu.M23.Properties.TwoRank
public import Theory.Mathieu.SchurMultipliers.M23Kernel
public import CFSG.Quasithin.Chapter12.Section06.CentralLine.LocalContradiction.Displacement
public import Theory.Representation.BinaryOffender.QuadraticQuotient
public import Theory.Representation.BinaryPermutation.EightNonsingularStabilizer.FixedCodimension

/-!
# Rank restrictions on the original nonsingular residual

The actual subgroup V_v has order 32 and embeds in K_v. A quasisimple
K_v with central quotient M₂₃ is centerless by the proved multiplier
calculation, so the intrinsic two-rank bound for M₂₃ contradicts that
subgroup. Self-duality of the natural permutation section computes fixed
codimension five for the original A₆ action. The actual projection of V
onto V/C_V(L), followed by L_v≤K_v, therefore gives corank at least five
for C_V(K_v). This needs no K_v-invariance of V. The source's other
quasisimple model exclusions and C-component recognition remain open.

Source: Aschbacher--Smith, Lemma 12.6.12, printed pp.825--826.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original rank-five moved subgroup excludes the quasisimple M23 row. -/
theorem SourceHypothesis.nonsingular_not_M23_centralQuotient
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G))) :
    ¬ Nonempty (((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.Mathieu.M23) := by
  let := hK
  rintro ⟨e⟩
  have hz := Sporadic.Mathieu.SchurMultipliers.m23_center_eq_bot_of_centralQuotientEquiv e
  let eK : Kv (v : G) ≃* Sporadic.Mathieu.M23 :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.trans e
  have hr := (H.nonsingular_component_rank D v hv).2
  rw [primeRank_equiv 2 eK] at hr
  have := Sporadic.Mathieu.m23_twoRank_le_four
  omega
end CFSG.Quasithin.Chapter12.Section06


public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open BinaryPermutation.EightNonsingular
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original V has at least five dimensions outside C_V(L_v). -/
theorem OrthogonalMarking.nonsingular_local_centralizer_corank
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes) (v : V) (hv : D.Nonsingular v) :
    5 ≤ Nat.log 2 ((centralizer (Lv L (v : G) : Set G)).relIndex V) := by
  obtain ⟨i,j,hij,hp⟩ := nonsingular_pair _ hv
  let ρ := seedRepresentation L V chosen.normalizes
  let σ := (alternatingNaturalRepresentation (Fin 8)).comp D.actorMap
  let f := D.coordinates.toLinearMap.comp (fixedSeed L V chosen.normalizes).toSubmodule.mkQ
  let B := (Lv L (v : G)).subgroupOf L
  have hf : Function.Surjective f := D.coordinates.surjective.comp (Submodule.mkQ_surjective _)
  have he : ∀ g w, f (ρ g w) = σ g (f w) :=
    fun g w => D.equivariant g (Submodule.Quotient.mk w)
  have hle := fixedCodim_le_of_equivariant_surjection ρ σ f hf he B
  have hd : fixedCodim σ B = 5 := by
    unfold fixedCodim
    rw [fixedSpace_comp_map, D.Lv_image_pair v i j hij hp]
    exact pointFixer_fixedCodim i j hij
  rw [hd] at hle
  have hfix : fixedSpace ρ B =
      (fixedSeed (Lv L (v : G)) V ((Lv_le_L L _).trans chosen.normalizes)).toSubmodule := by
    ext w
    constructor
    · intro h l
      exact h ⟨⟨l,(Lv_le_L L _) l.property⟩,l.property⟩
    · intro h l
      exact h ⟨l.val.val,l.property⟩
  rw [fixedCodim,hfix] at hle
  rw [CentralLine.LocalContradiction.fixed_quotient_finrank] at hle
  exact hle

/-- The corank estimate is inherited by the literal residual K_v. -/
theorem SourceHypothesis.nonsingular_component_centralizer_corank
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v) :
    5 ≤ Nat.log 2 ((centralizer (Kv (v : G) : Set G)).relIndex V) := by
  have hLK := Lv_le_Kv_of_A6 L (v : G)
    (Classical.choice (D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv))
  exact (D.nonsingular_local_centralizer_corank H.chosen v hv).trans
    (Nat.log_mono_right (relIndex_le_of_le_left (centralizer_le hLK) index_ne_zero_of_finite))
end CFSG.Quasithin.Chapter12.Section06

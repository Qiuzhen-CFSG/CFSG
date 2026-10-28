module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Swapped.Commuting
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Swapped.Ordinary
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Swapped.Containment.Local
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Swapped.Endpoint
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent

/-!
# The literal normalizer action for commuting exchanged components

The characteristic-two structure of the canonical radical makes its center
a two-group and its center quotient centerless. The residual-factor theorem
then proves that the actual N_L(P) permutes P ∩ K and its exchange conjugate.
Ordinary components commute by the relative component calculus, including
central covers, so this closes that entire branch without a model comparison.

Source: Aschbacher--Smith, 13.1.12(3), printed p.875.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.Section02 Chapter1.XiEmbedding Chapter1.RadicalExclusions
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L K : Subgroup G} {p : ℕ} [Fact p.Prime] {u : G}

/-- Commutation alone supplies the pair permutation; no irreducibility of T_u
or normality of K in its involution centralizer is required. -/
theorem Context.swapped_normalizer_permutation_of_commuting (h : Context T L p)
    (e : Escape T L p u K) (P : Sylow p (XiP p L))
    (d : SwappedData T L p u K ((P : Subgroup (XiP p L)).map (XiP p L).subtype))
    (hc : ⁅K,K.conjBy (Classical.choose d.factors.2)⁆ = ⊥) :
    let P₀ := (P : Subgroup (XiP p L)).map (XiP p L).subtype
    ∀ g ∈ L ⊓ normalizer (P₀ : Set G),
      (P₀ ⊓ K).conjBy g = P₀ ⊓ K ∨
      (P₀ ⊓ K).conjBy g = (P₀ ⊓ K).conjBy (Classical.choose d.factors.2) := by
  let X := XiP p L
  let P₀ := (P : Subgroup X).map X.subtype
  let t := Classical.choose d.factors.2
  have ht := Classical.choose_spec d.factors.2
  have hx := (XiP_mem_XiPlus_source h.hypothesis.simpleQTKE T h.maximal.1.1
    h.nonquasisimple h.odd h.divides).1
  have h114 := lemma_1_1_4_6 T (h.hypothesis.simpleQTKE.evenCharacteristic T)
  have hq := (XiP_oddQuotient_of_A36
    (ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
    h.maximal.1.1 (uniqueness_local_quotient_sqtk h.hypothesis.simpleQTKE h.maximal.1.1.2.2)
    h.nonquasisimple h.odd h.divides).2
  have hperm := normalizer_permutates_commuting_odd_axes h.odd hx.perfect
    (map_subtype_le (P : Subgroup X)) (h.swapped_complement_shape P).isPGroup
    (hx.sylow_sup hq P) (hx.sylow_disjoint h.odd P)
    ((Nat.card_congr d.plane.some.toEquiv).trans (plane_card p))
    (ModelReduction.swapped_intersection_card d.plane d.factors) e.normalized
    (hx.invariant ht.1.1.1) ht.1.2 ht.2.2.1 hc
    (xi_center_isPGroup_of_global_He h114 hx)
    (xi_center_quotient_center_eq_bot h114 hx)
  dsimp only
  intro g hg
  exact hperm g ⟨XiP_invariant p L.le_normalizer hg.1,hg.2⟩

/-- The commuting branch constructs the two literal order-p lines. -/
theorem Context.swapped_line_pair_of_commuting (h : Context T L p)
    (e : Escape T L p u K) (P : Sylow p (XiP p L))
    (d : SwappedData T L p u K ((P : Subgroup (XiP p L)).map (XiP p L).subtype))
    (hc : ⁅K,K.conjBy (Classical.choose d.factors.2)⁆ = ⊥) :
    Nonempty (NormalizerLinePair L ((P : Subgroup (XiP p L)).map (XiP p L).subtype) p) :=
  Context.ordinary_line_pair_of_permutation P d
    (h.swapped_normalizer_permutation_of_commuting e P d hc)

/-- The common endpoint of the ordinary and characteristic-two geometries. -/
theorem Context.swapped_false_of_commuting (h : Context T L p)
    (e : Escape T L p u K) (P : Sylow p (XiP p L))
    (d : SwappedData T L p u K ((P : Subgroup (XiP p L)).map (XiP p L).subtype))
    (hc : ⁅K,K.conjBy (Classical.choose d.factors.2)⁆ = ⊥) : False :=
  h.false_of_swapped_line_pair P d (h.swapped_line_pair_of_commuting e P d hc).some

omit [Finite G] [Fact p.Prime] in
/-- Distinct ordinary components commute inside the literal C_G(u). -/
theorem Escape.ordinary_exchange_commutes (e : Escape T L p u K)
    (hq : IsQuasisimple K) {t : G}
    (ht : t ∈ centralizer ({u} : Set G)) (hm : t ∉ normalizer (K : Set G)) :
    ⁅K,K.conjBy t⁆ = ⊥ := by
  let H := centralizer ({u} : Set G)
  have hK : IsComponentIn K H := ⟨e.component.1,e.component.2.subnormal,
    hq.of_mulEquiv (subgroupOfEquivOfLe e.component.1).symm⟩
  have hKt : IsComponentIn (K.conjBy t) H := by
    have hh := hK.map (MulAut.conj t)
    have he : H.map (MulAut.conj t).toMonoidHom = H :=
      mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer ht)
    rwa [he] at hh
  exact hK.commutator_eq_bot_of_ne hKt
    (fun he => hm (mem_normalizer_iff_map_conj_eq.mpr he.symm))

/-- Every element of the actual N_L(P) fixes or exchanges the ordinary axes. -/
theorem Context.ordinary_normalizer_permutation (h : Context T L p)
    (e : Escape T L p u K) (P : Sylow p (XiP p L))
    (d : SwappedData T L p u K ((P : Subgroup (XiP p L)).map (XiP p L).subtype))
    (hf : generalizedFitting K ≠ pCore 2 K) :
    let P₀ := (P : Subgroup (XiP p L)).map (XiP p L).subtype
    ∀ g ∈ L ⊓ normalizer (P₀ : Set G),
      (P₀ ⊓ K).conjBy g = P₀ ⊓ K ∨
      (P₀ ⊓ K).conjBy g = (P₀ ⊓ K).conjBy (Classical.choose d.factors.2) := by
  have ht := Classical.choose_spec d.factors.2
  exact h.swapped_normalizer_permutation_of_commuting e P d
    (e.ordinary_exchange_commutes (e.quasisimple_of_generalizedFitting_ne hf) ht.1.1.2 ht.2.1)

/-- The complete ordinary-component invariant-pair construction. -/
theorem Context.ordinary_line_pair (h : Context T L p)
    (e : Escape T L p u K) (P : Sylow p (XiP p L))
    (d : SwappedData T L p u K ((P : Subgroup (XiP p L)).map (XiP p L).subtype))
    (hf : generalizedFitting K ≠ pCore 2 K) :
    Nonempty (NormalizerLinePair L ((P : Subgroup (XiP p L)).map (XiP p L).subtype) p) :=
  Context.ordinary_line_pair_of_permutation P d (h.ordinary_normalizer_permutation e P d hf)

/-- The ordinary exchanged-component branch contradicts the canonical action. -/
theorem Context.swapped_ordinary_false (h : Context T L p)
    (e : Escape T L p u K) (P : Sylow p (XiP p L))
    (d : SwappedData T L p u K ((P : Subgroup (XiP p L)).map (XiP p L).subtype))
    (hf : generalizedFitting K ≠ pCore 2 K) : False :=
  h.false_of_swapped_line_pair P d (h.ordinary_line_pair e P d hf).some

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination

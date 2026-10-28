module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Swapped.Containment.Local
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.LocalCore
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.LocalClauses
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.Factors

/-!
# The literal point core normalizes the exchanged component

The two nontrivial disjoint odd factors detect which component is fixed:
an element of C_G(u) centralizing P cannot exchange them. Frattini
factorization in T_u writes each element of R=O₂(XT_u) as an element of
O₂(X) times an element centralizing P. Thus R normalizes K. This proves
the normalizer premise of C.2.7 directly with the point core; no normality
of K in C_G(u), or irreducibility of T_u, is required.

Source: Aschbacher--Smith, 13.1.12(3), printed pp.874--875.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.Section02 Chapter1.XiEmbedding Chapter1.RadicalExclusions
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L K : Subgroup G} {p : ℕ} [Fact p.Prime] {u : G}

/-- Centralizing the literal odd complement fixes its component axis. -/
theorem Context.swapped_centralizer_normalizes (h : Context T L p)
    (o : OrbitFacts T L p) (s : Selected T L u) (e : Escape T L p u K)
    (hr : ¬ ComponentNormalizerIrreducible L K p u) (P : Sylow p (XiP p L))
    (d : SwappedData T L p u K ((P : Subgroup (XiP p L)).map (XiP p L).subtype)) :
    centralizer ({u} : Set G) ⊓
      centralizer (((P : Subgroup (XiP p L)).map (XiP p L).subtype) : Set G) ≤
        normalizer (K : Set G) := by
  let P₀ := (P : Subgroup (XiP p L)).map (XiP p L).subtype
  let t := Classical.choose d.factors.2
  have ht := Classical.choose_spec d.factors.2
  have hH := h.hypothesis.simpleQTKE.involution_centralizer_sqtk
    (h.involution s.mem s.ne_one)
  obtain ⟨a,_,_,_,_,hall⟩ := h.exists_component_exchange o s e hH hr
  have hKt : K.conjBy t ≠ K := fun he => ht.2.1 (mem_normalizer_iff_map_conj_eq.mpr he)
  have he : K.conjBy t = K.conjBy a := (hall t ht.1.1.2).resolve_left hKt
  have hpair : ∀ g ∈ centralizer ({u} : Set G),
      K.conjBy g = K ∨ K.conjBy g = K.conjBy t := by
    intro g hg
    simpa only [he] using hall g hg
  have hconj : (P₀ ⊓ K).conjBy t = P₀ ⊓ K.conjBy t := by
    change (P₀ ⊓ K).map (MulAut.conj t).toMonoidHom = _
    rw [map_inf _ _ _ (MulAut.conj t).injective]
    change P₀.conjBy t ⊓ K.conjBy t = _
    rw [show P₀.conjBy t = P₀ from mem_normalizer_iff_map_conj_eq.mp ht.1.2]
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  rcases hpair g hg.1 with hf | hf
  · exact hf
  exfalso
  have hle : P₀ ⊓ K ≤ (P₀ ⊓ K).conjBy t := by
    rw [hconj]
    intro x hx
    refine ⟨hx.1,?_⟩
    have hfix : MulAut.conj g x = x := by
      change g * x * g⁻¹ = x
      rw [← hg.2 x hx.1]
      simp
    have hm : x ∈ K.conjBy g := hfix ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom hx.2
    exact hf ▸ hm
  have hb : P₀ ⊓ K = ⊥ := bot_unique (fun x hx => ht.2.2.2.1.le_bot ⟨hx,hle hx⟩)
  have hc := ModelReduction.swapped_intersection_card d.plane d.factors
  change Nat.card (P₀ ⊓ K : Subgroup G) = p at hc
  rw [hb,Subgroup.card_bot] at hc
  exact (Fact.out : p.Prime).ne_one hc.symm

/-- The point core, identified with O₂(XT_u), normalizes K. -/
theorem Context.swapped_core_normalizes (h : Context T L p)
    (o : OrbitFacts T L p) (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G))
    (e : Escape T L p u K) (hr : ¬ ComponentNormalizerIrreducible L K p u)
    (P : Sylow p (XiP p L))
    (d : SwappedData T L p u K ((P : Subgroup (XiP p L)).map (XiP p L).subtype)) :
    centralizerCore T L p u ≤ normalizer (K : Set G) := by
  let X := XiP p L
  let H := centralizer ({u} : Set G)
  let S := (T : Subgroup G) ⊓ H
  let P₀ := (P : Subgroup X).map X.subtype
  let R := (X ⊔ S).pCoreIn 2
  rw [h.core_eq_local_join o s hnt]
  have hXH := (SourceNonquasisimple.XiP_le_moved_centralizer h.hypothesis h.many
    h.maximal.1 h.nonquasisimple p s.mem).trans inf_le_right
  have hRH : R ≤ H := (pCoreIn_le 2 _).trans (sup_le hXH inf_le_right)
  have hRS : R ≤ S := by
    obtain ⟨Q,hQ⟩ := e.full_sylow.restrict (show S ≤ X ⊔ S from le_sup_right)
      (sup_le hXH inf_le_right)
    exact (pCoreIn_le_sylow (X ⊔ S) Q).trans_eq hQ
  have hSX : S ≤ normalizer (X : Set G) :=
    inf_le_left.trans (XiP_invariant p h.sylow_normalizes)
  have hCR : X.pCoreIn 2 ≤ R := pCoreIn_mono_of_normalizes le_sup_left
    (sup_le X.le_normalizer hSX)
  have hPR : P₀ ≤ normalizer (R : Set G) :=
    ((map_subtype_le (P : Subgroup X)).trans le_sup_left).trans
      ((X ⊔ S).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (X ⊔ S) (pCore 2 (X ⊔ S : Subgroup G))))
  have hdis : Disjoint R P₀ := (isPGroup_pCoreIn 2 _).disjoint_of_coprime
    (h.swapped_complement_shape P).isPGroup h.odd.coprime_two_left
  have hcentral : R ⊓ normalizer (P₀ : Set G) ≤ centralizer (P₀ : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    apply hdis.le_bot.trans' (le_inf ?_ ?_)
    · exact (commutator_mono inf_le_left le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp hPR)
    · exact le_normalizer_iff_commutator_le_right.mp inf_le_right
  have hfactor : (X.pCoreIn 2 : Set G) *
      ((S ⊓ normalizer (P₀ : Set G) : Subgroup G) : Set G) = S := by
    have hn : S ⊓ normalizer (P₀ : Set G) ≤ normalizer (X.pCoreIn 2 : Set G) :=
      inf_le_left.trans (hSX.trans
        (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))
    rw [← coe_mul_of_right_le_normalizer_left _ _ hn]
    exact congrArg (fun A : Subgroup G => (A : Set G)) (h.point_sylow_normalizer_factor s P).symm
  intro r hrR
  have hrS : r ∈ (S : Set G) := hRS hrR
  rw [← hfactor] at hrS
  obtain ⟨a,ha,b,hb,hab⟩ := hrS
  have hbR : b ∈ R := by
    have hh := R.mul_mem (R.inv_mem (hCR ha)) hrR
    rwa [← hab,inv_mul_cancel_left] at hh
  rw [← hab]
  exact (normalizer (K : Set G)).mul_mem (e.normalized (pCoreIn_le 2 X ha))
    (h.swapped_centralizer_normalizes o s e hr P d ⟨hRH hbR,hcentral ⟨hbR,hb.2⟩⟩)

/-- The characteristic-two exchanged branch supplies the genuine C.2.7 input. -/
theorem Context.swapped_characteristic_two_input (h : Context T L p)
    (o : OrbitFacts T L p) (c : Control T L p) (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G))
    (e : Escape T L p u K) (hr : ¬ ComponentNormalizerIrreducible L K p u)
    (P : Sylow p (XiP p L))
    (d : SwappedData T L p u K ((P : Subgroup (XiP p L)).map (XiP p L).subtype))
    (hf : generalizedFitting K = pCore 2 K) :
    ModelReduction.FullSieve.SourceInterface.Input KnownSimple.IsKnownSimple
      (centralizer ({u} : Set G)) (centralizerCore T L p u)
      (normalizer (L : Set G) ⊓ centralizer ({u} : Set G)) K := by
  refine ⟨c.pushing_up u s hnt,e.component,e.quotient,hf,?_,
    h.swapped_core_normalizes o s hnt e hr P d⟩
  intro hk
  exact e.escapes (hk.trans (inf_le_left.trans (normalizer_le_normalizer_XiP p L)))

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination

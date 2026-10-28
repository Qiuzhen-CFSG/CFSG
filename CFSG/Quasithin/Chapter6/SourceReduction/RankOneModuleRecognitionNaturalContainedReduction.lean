module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNatural
public import CFSG.Quasithin.Chapter6.Section01.SourceModelKernel
public import CFSG.Quasithin.ChapterE.Section03.WeakClosure
public import Theory.GroupTheory.NormalModuleCore
public import Theory.Representation.GeneralLinearNatural
public import Theory.GroupTheory.TwoLocalUniquenessControl

/-!
# The contained-centralizer reduction of 6.1.15

The faithful natural action detects O₂(L). The reduced module and the
Sylow supplement then identify C_{LT}([V,L]) with O₂(LT). If the zeroth
weak closure centralizes [V,L], its equality with the weak closure inside
O₂(LT) makes it LT-invariant. Uniqueness over LT controls its normalizer.
Consequently a normalizer escaping M supplies a noncentralizing conjugate
of the layer in T. Every M-conjugate of the layer, however, centralizes it.

The final theorem assembles this reduction with the two separate source
inputs: the weak-closure bounds in 6.1.12 and conjugate centralization for
n > 2 from 6.1.10--14 under C_G(Z_S) ≤ M. These inputs are not proved by
this conditional assembly. All weak closures are the literal Source.W.

Source: Aschbacher--Smith, 6.1.7--15, printed pp.669--672,
especially the first and last paragraphs of the proof of 6.1.15.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
  {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}

omit [Finite G] in
/-- Faithfulness of the marked natural action detects the component two-core. -/
theorem natural_centralizer_eq_core (hnatural : IsNaturalModule L (layer L V) n) :
    L ⊓ centralizer (layer L V : Set G) = L.pCoreIn 2 := by
  obtain ⟨F, _, _, _, _, hmodel⟩ := hnatural
  exact hmodel.centralizer_eq_core (Representation.specialLinearNatural_injective 2)

/-- Reducedness of the initial module makes the local two-core fix its layer. -/
theorem local_core_centralizes_layer (h : Hypothesis611 κ T L M V n) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ centralizer (layer L V : Set G) := by
  let H := L ⊔ (T : Subgroup G)
  let := h.V_mem.2.1
  have hr : IsPReduced 2 (V.subgroupOf H) :=
    ⟨h.V_mem.2.2.choose, IsElementaryAbelian.of_injective
      (subgroupOfEquivOfLe h.V_mem.1).toMonoidHom
      (subgroupOfEquivOfLe h.V_mem.1).injective, h.V_mem.2.2.choose_spec⟩
  have hc := map_mono (f := H.subtype) (le_centralizer_iff.mp hr.le_centralizer_pCore)
  rw [map_centralizer_subtype, map_subgroupOf_eq_of_le h.V_mem.1] at hc
  exact (hc.trans inf_le_right).trans (centralizer_le h.layer_le_V)

/-- The literal kernel identity used in the first paragraph of 6.1.15. -/
theorem local_layer_centralizer_eq_core (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n) :
    (L ⊔ (T : Subgroup G)) ⊓ centralizer (layer L V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hnL : L ≤ normalizer (layer L V : Set G) := by
    obtain ⟨F, _, _, _, _, hmodel⟩ := hnatural
    exact hmodel.normalizes
  exact ambient_centralizer_eq_core_of_normal_supplement L (layer L V) T
    h.sylow_normalizes_L (h.layer_le_L.trans le_sup_left)
    (sup_le hnL h.sylow_normalizes_layer)
    T.isPGroup' (natural_centralizer_eq_core hnatural) (local_core_centralizes_layer h)

/-- Relative normality in M keeps every M-conjugate in the detecting core. -/
theorem M_conjugate_layer_centralizes (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n) {g : G} (hg : g ∈ M) :
    (layer L V).map (MulAut.conj g).toMonoidHom ≤ centralizer (layer L V : Set G) := by
  have hnL : L ≤ normalizer (layer L V : Set G) := by
    obtain ⟨F, _, _, _, _, hmodel⟩ := hnatural
    exact hmodel.normalizes
  have hcore : layer L V ≤ L.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (T.isPGroup'.to_le h.layer_le_T) h.layer_le_L hnL
  have hn : M ≤ normalizer (L.pCoreIn 2 : Set G) :=
    ((normal_subgroupOf_iff_le_normalizer h.L_le).mp h.L_normal).trans
      (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have he := mem_normalizer_iff_map_conj_eq.mp (hn hg)
  exact ((map_mono hcore).trans_eq he).trans
    ((natural_centralizer_eq_core hnatural).symm.le.trans inf_le_right)

/-- Weak-closure transport inside the local two-core supplies normalizer
control. The uniqueness premise is discharged by the Chapter 12 adapter. -/
theorem normalizer_W_zero_le_of_centralizes (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ⊔ (T : Subgroup G) ≤ N → N = M)
    (hW : W (layer L V) (T : Subgroup G) 0 ≤ centralizer (layer L V : Set G)) :
    normalizer (W (layer L V) (T : Subgroup G) 0 : Set G) ≤ M := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hWQ : W (layer L V) (T : Subgroup G) 0 ≤ Q :=
    (le_inf ((W_le _ _ _).trans le_sup_right) hW).trans_eq
      (local_layer_centralizer_eq_core h hnatural)
  have he : W (layer L V) (T : Subgroup G) 0 = W (layer L V) Q 0 :=
    SubgroupFamily.span_eq_in_p_overgroup
      (ChapterE.conjugateCorankFamily_invariant (layer L V) 0)
      T Q (isPGroup_pCoreIn 2 _) hWQ
  have hnQ : L ⊔ (T : Subgroup G) ≤ normalizer (Q : Set G) :=
    (L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  apply normalizer_le_of_unique_maximalTwoLocal hunique
    (T.isPGroup'.to_le (W_le _ _ _))
  · intro heq
    exact h.nontrivial_action (bot_unique
      ((self_le_W_zero h.layer_le_T).trans_eq heq))
  · rw [he]
    exact hnQ.trans (ChapterE.normalizer_le_weakClosure_normalizer (layer L V) Q 0)

/-- A genuine escaping normalizer produces a whole conjugate, not merely
a subgroup or an element outside M. -/
theorem exists_noncentralizing_conjugate_of_normalizer_escape
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ⊔ (T : Subgroup G) ≤ N → N = M)
    (hescape : ¬ normalizer (W (layer L V) (T : Subgroup G) 0 : Set G) ≤ M) :
    ∃ g : G, (layer L V).map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) ∧
      ¬ (layer L V).map (MulAut.conj g).toMonoidHom ≤
        centralizer (layer L V : Set G) := by
  classical
  by_contra! hn
  apply hescape
  apply normalizer_W_zero_le_of_centralizes h hnatural hunique
  exact (W_zero_le_iff _ _ _).mpr hn

/-- Assemble the contained case after the independent weak-closure and
conjugate-geometry inputs have been proved. Neither input assumes 6.1.15. -/
theorem containedAlternative_of_weak_closure_and_conjugate_geometry
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ⊔ (T : Subgroup G) ≤ N → N = M)
    (hI : centralizer (ZS (T : Subgroup G) L V : Set G) ≤ M)
    (hsplit : ¬ normalizer (W (layer L V) (T : Subgroup G) 0 : Set G) ≤ M ∨
      ¬ centralizer (C (layer L V) (T : Subgroup G) 1 : Set G) ≤ M)
    (hhigh : 2 < n → ZS (T : Subgroup G) L V ≤ C (layer L V) (T : Subgroup G) 1)
    (hconj : 2 < n → ∀ g : G,
      (layer L V).map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
      (layer L V).map (MulAut.conj g).toMonoidHom ≤ centralizer (layer L V : Set G)) :
    ContainedAlternative (T : Subgroup G) L M V n := by
  have hn := h.n_gt_one
  rcases hsplit with hzero | hone
  · refine ⟨?_, Or.inl hzero⟩
    by_contra hne
    have hgt : 2 < n := by omega
    obtain ⟨g, hgT, hg⟩ :=
      exists_noncentralizing_conjugate_of_normalizer_escape h hnatural hunique hzero
    exact hg (hconj hgt g hgT)
  · have hnot : ¬ ZS (T : Subgroup G) L V ≤ C (layer L V) (T : Subgroup G) 1 :=
      fun hz => hone ((centralizer_le hz).trans hI)
    refine ⟨?_, Or.inr hnot⟩
    by_contra hne
    exact hnot (hhigh (by omega))

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

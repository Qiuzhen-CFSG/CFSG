module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.OriginalCoordinates
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Geometry
public import CFSG.Quasithin.ChapterF.Section09.Basic
public import Theory.GroupTheory.AlmostSpecialIntersection

/-!
# Initial reductions for the original nonabelian-span case

The kernel containment in 15.3.48 and the earlier conjugate-centralization
theorem imply that a nonabelian span has nontrivial image in H/O₂(H).
The same literal F.9 setup supplies both mutual-normalization commutator
bounds. Here the image on the four-dimensional V is kept separate from U/Z.

Source: Aschbacher–Smith, Lemma 15.3.51(1,4), printed p.1145.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50

variable {G : Type*} [Group G] [Finite G]

/-- This is the literal F.9 specialization used by 15.3.48 and 15.3.51. -/
noncomputable abbrev localSetup (d : CharacteristicTwo.LocalData G) (H : Subgroup G) :
    ChapterF.Section09.Setup G :=
  ⟨d.T, d.Y, d.V, d.ZS, d.Z, H⟩

variable (d : CharacteristicTwo.LocalData G) (H : Subgroup G)
  (h : (localSetup d H).Hypothesis)
include h

/-- A span contained in the local two-core is abelian by the earlier
conjugate-centralization theorem. This proves the first reduction of 15.3.51. -/
theorem elementary_span_of_module_le_core
    (hf : ∀ g : G, d.V.map (MulAut.conj g).toMonoidHom ≤ d.M →
      d.V.map (MulAut.conj g).toMonoidHom ≤ centralizer (d.V : Set G))
    (hVQ : d.V ≤ H.pCoreIn 2) :
    IsElementaryAbelian 2 (localSpan d.V H) := by
  have hspanQ : localSpan d.V H ≤ H.pCoreIn 2 :=
    conjugateSpanBy_le hVQ (ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH
      (D := localSetup d H))
  have hspanM : localSpan d.V H ≤ d.M :=
    hspanQ.trans (h.QH_le_T.trans d.sylow_le)
  have hspanC : localSpan d.V H ≤ centralizer (d.V : Set G) := by
    apply (closure_le _).mpr
    rintro x ⟨g, hg, v, hv, rfl⟩
    have hconj : d.V.map (MulAut.conj g).toMonoidHom ≤ d.M := by
      rintro x ⟨v, hv, rfl⟩
      exact hspanM (subset_closure ⟨g, hg, v, hv, rfl⟩)
    exact hf g hconj (mem_map_of_mem _ hv)
  let : IsElementaryAbelian 2 d.V := h.elementary
  let : IsMulCommutative (localSpan d.V H) :=
    (conjugateSpanBy_commutative_iff _ _).mpr (le_centralizer_iff.mp hspanC)
  exact conjugateSpanBy_elementary_of_commutative d.V H

/-- The nonabelian source case cannot have V inside O₂(H). -/
theorem module_not_le_core
    (hf : ∀ g : G, d.V.map (MulAut.conj g).toMonoidHom ≤ d.M →
      d.V.map (MulAut.conj g).toMonoidHom ≤ centralizer (d.V : Set G))
    (hnon : ¬ IsMulCommutative (localSpan d.V H)) : ¬ d.V ≤ H.pCoreIn 2 := by
  intro hVQ
  let := elementary_span_of_module_le_core d H h hf hVQ
  exact hnon inferInstance

/-- The exact starred assertion, for the actual quotient map H → H/O₂(H). -/
theorem module_actor_image_ne_bot
    (hf : ∀ g : G, d.V.map (MulAut.conj g).toMonoidHom ≤ d.M →
      d.V.map (MulAut.conj g).toMonoidHom ≤ centralizer (d.V : Set G))
    (hnon : ¬ IsMulCommutative (localSpan d.V H)) :
    (d.V.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) ≠ ⊥ := by
  intro he
  apply module_not_le_core d H h hf hnon
  have hker := (Subgroup.map_eq_bot_iff _).mp he
  intro v hv
  have hvH : v ∈ H := h.V_le_H hv
  have hk := hker (show (⟨v, hvH⟩ : H) ∈ d.V.subgroupOf H from hv)
  have hq : (⟨v, hvH⟩ : H) ∈ pCore 2 H :=
    (QuotientGroup.eq_one_iff _).mp hk
  exact ⟨⟨v, hvH⟩, hq, rfl⟩

/-- Both source commutator bounds follow from mutual normalization in the
literal Sylow group, with no quotient or cardinality assumptions. -/
theorem module_commutator_bounds :
    ⁅d.V, H.pCoreIn 2⁆ ≤ d.V ⊓ H.pCoreIn 2 ∧
      ⁅d.V, localSpan d.ZS H⁆ ≤ d.V ⊓ localSpan d.ZS H := by
  have hQV : H.pCoreIn 2 ≤ normalizer (d.V : Set G) :=
    h.QH_le_T.trans h.T_normalizes_V
  have hVQ : d.V ≤ normalizer (H.pCoreIn 2 : Set G) :=
    h.V_le_H.trans (ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH
      (D := localSetup d H))
  have hUV : localSpan d.ZS H ≤ normalizer (d.V : Set G) :=
    h.UH_le_QH.trans hQV
  have hVU : d.V ≤ normalizer (localSpan d.ZS H : Set G) :=
    h.V_le_H.trans (le_normalizer_conjugateSpanBy d.ZS H)
  constructor
  · exact le_inf (le_normalizer_iff_commutator_le_left.mp hQV)
      (le_normalizer_iff_commutator_le_right.mp hVQ)
  · exact le_inf (le_normalizer_iff_commutator_le_left.mp hUV)
      (le_normalizer_iff_commutator_le_right.mp hVU)

/-- If U is abelian, its elementary abelian conjugate generators make U
elementary abelian. This is the exponent assertion in 15.3.51(2b). -/
theorem elementary_U_of_commutative (hc : IsMulCommutative (localSpan d.ZS H)) :
    IsElementaryAbelian 2 (localSpan d.ZS H) := by
  let : IsElementaryAbelian 2 d.V := h.elementary
  let : IsElementaryAbelian 2 d.ZS := IsElementaryAbelian.of_le h.plus_le
  let := hc
  exact conjugateSpanBy_elementary_of_commutative d.ZS H

/-- Nontriviality of the action of U on V follows from the faithful
H/O₂(H)-action on U/Z; this does not assert any order for U/Z. -/
theorem span_action_ne_bot
    (hf : ∀ g : G, d.V.map (MulAut.conj g).toMonoidHom ≤ d.M →
      d.V.map (MulAut.conj g).toMonoidHom ≤ centralizer (d.V : Set G))
    (hnon : ¬ IsMulCommutative (localSpan d.V H)) :
    d.action.image (localSpan d.ZS H) ≠ ⊥ := by
  intro he
  have hUM : localSpan d.ZS H ≤ d.M :=
    h.UH_le_QH.trans (h.QH_le_T.trans d.sylow_le)
  have hUC := (d.action.image_eq_bot_iff hUM).mp he
  have hVC : d.V ≤ H ⊓ centralizer (localSpan d.ZS H : Set G) :=
    le_inf h.V_le_H (le_centralizer_iff.mp hUC)
  exact module_not_le_core d H h hf hnon (h.lemma_F_9_3.1.mpr hVC)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50

module

public import CFSG.Quasithin.ChapterE.Section02.Elementary
public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.Commutator.CentralizingFactor

/-!
# The hypotheses and core geometry of E.2.10

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), E.2.10, printed pp. 222–224.

Normality of `V` is relative to the Sylow subgroup. Two-closedness of the
normal core means that it has a normal Sylow 2-subgroup. That Sylow subgroup
is characteristic, so its ambient image lies in the ambient two-core. This
identifies the source intersections with the two-core intersections and lets
the elementary abelian-generator argument prove part (1). The Sylow image
in `X/J` proves part (3), while commutators of the two factors give part (5)
and quadratic action on `P`.

Conjugates use `x ↦ g*x*g⁻¹`; replace the source's conjugating element by its
inverse. This changes none of the hypotheses or conclusions.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterE.TwoConjugate

open Subgroup
open scoped Pointwise

variable {X : Type*} [Group X]

/-- Exactly the inputs of E.2.10. Finiteness is a separate ambient instance. -/
structure Hypotheses (T : Sylow 2 X) (V M : Subgroup X) (g : X) : Prop where
  elementary : IsElementaryAbelian 2 V
  le_sylow : V ≤ T
  normal_in_sylow : (V.subgroupOf (T : Subgroup X)).Normal
  normalizer_le : normalizer (V : Set X) ≤ M
  le_local_core : V ≤ (pCore 2 M).map M.subtype
  core_two_closed : ∃ S : Sylow 2 M.normalCore, (S : Subgroup M.normalCore).Normal
  generate : V ⊔ V.map (MulAut.conj g).toMonoidHom = ⊤

variable {T : Sylow 2 X} {V M : Subgroup X} {g : X}

abbrev J (M : Subgroup X) : Subgroup X := M.normalCore
abbrev W (V : Subgroup X) (g : X) : Subgroup X := V.map (MulAut.conj g).toMonoidHom
abbrev B (V M : Subgroup X) : Subgroup X := J M ⊓ V
abbrev A (V M : Subgroup X) (g : X) : Subgroup X := (B V M).map (MulAut.conj g).toMonoidHom
abbrev P (V M : Subgroup X) (g : X) : Subgroup X := B V M ⊔ A V M g
abbrev Z (V : Subgroup X) (g : X) : Subgroup X := V ⊓ W V g

namespace Hypotheses

theorem sylow_le_normalizer (h : Hypotheses T V M g) :
    (T : Subgroup X) ≤ normalizer (V : Set X) :=
  (normal_subgroupOf_iff_le_normalizer h.le_sylow).mp h.normal_in_sylow

theorem twoCore_le_J (h : Hypotheses T V M g) : pCore 2 X ≤ J M :=
  normal_le_normalCore.mpr
    ((pCore_isPGroup.le_sylow_of_normal T).trans
      (h.sylow_le_normalizer.trans h.normalizer_le))

/-- The intrinsic two-core of the normal core has precisely the ambient image
`O₂(X)`. In particular, the two different ambient groups are not conflated. -/
theorem intrinsic_core_image (h : Hypotheses T V M g) :
    (pCore 2 (J M)).map (J M).subtype = pCore 2 X := by
  apply le_antisymm
  · exact le_sSup ⟨ConjAct.normal_of_characteristic_of_normal,
      pCore_isPGroup.map (J M).subtype⟩
  · have hc : (pCore 2 X).subgroupOf (J M) ≤ pCore 2 (J M) :=
      le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩
    have hm := map_mono (f := (J M).subtype) hc
    rwa [map_subgroupOf_eq_of_le h.twoCore_le_J] at hm

/-- Two-closedness places every two-subgroup of the core in `O₂(X)`. -/
theorem le_twoCore_of_le_J [Finite X] (h : Hypotheses T V M g)
    (D : Subgroup X) (hD : IsPGroup 2 D) (hDJ : D ≤ J M) : D ≤ pCore 2 X := by
  obtain ⟨S, hS⟩ := h.core_two_closed
  let := Sylow.unique_of_normal S hS
  have hp : IsPGroup 2 (D.subgroupOf (J M)) := hD.comap_subtype
  obtain ⟨R, hR⟩ := hp.exists_le_sylow
  have hDS : D.subgroupOf (J M) ≤ (S : Subgroup (J M)) := by
    simpa only [Subsingleton.elim R S] using hR
  have hSc : (S : Subgroup (J M)) ≤ pCore 2 (J M) :=
    le_sSup ⟨hS, S.isPGroup'⟩
  have hm := map_mono (f := (J M).subtype) (hDS.trans hSc)
  rwa [map_subgroupOf_eq_of_le hDJ, h.intrinsic_core_image] at hm

/-- The equality required to pass from the elementary reduction to the
source's definition of `B`. -/
theorem B_eq_twoCore_inf [Finite X] (h : Hypotheses T V M g) :
    B V M = pCore 2 X ⊓ V := by
  let := h.elementary
  exact le_antisymm
    (le_inf (h.le_twoCore_of_le_J _
      ((IsElementaryAbelian.isPGroup 2 V).to_le inf_le_right) inf_le_left) inf_le_right)
    (inf_le_inf_right V h.twoCore_le_J)

theorem A_eq_J_inf (_h : Hypotheses T V M g) : A V M g = J M ⊓ W V g := by
  have he : (J M).map (MulAut.conj g).toMonoidHom = J M :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top g))
  rw [A, B, map_inf _ _ _ (MulAut.conj g).injective, he]

theorem A_eq_twoCore_inf [Finite X] (h : Hypotheses T V M g) :
    A V M g = pCore 2 X ⊓ W V g := by
  have he : (pCore 2 X).map (MulAut.conj g).toMonoidHom = pCore 2 X :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top g))
  rw [A, h.B_eq_twoCore_inf, map_inf _ _ _ (MulAut.conj g).injective, he]

theorem P_le_twoCore [Finite X] (h : Hypotheses T V M g) : P V M g ≤ pCore 2 X := by
  rw [P, h.B_eq_twoCore_inf, h.A_eq_twoCore_inf]
  exact sup_le inf_le_left inf_le_left

/-- E.2.10(1): the join is normal, is the setwise product, and contains the
central intersection of the generators. -/
theorem core_geometry [Finite X] (h : Hypotheses T V M g) :
    (P V M g).Normal ∧
    (P V M g : Set X) = (B V M : Set X) * (A V M g : Set X) ∧
    Z V g ≤ P V M g ⊓ center X := by
  let := h.elementary
  have hs := twoConjugate_twoCore_structure T V
    (IsElementaryAbelian.isPGroup 2 V) h.sylow_le_normalizer g h.generate
  have he : P V M g = (pCore 2 X ⊓ V) ⊔ (pCore 2 X ⊓ W V g) := by
    rw [P, h.B_eq_twoCore_inf, h.A_eq_twoCore_inf]
  refine ⟨he.symm ▸ hs.1, ?_, he.symm ▸ hs.2⟩
  rw [he, h.B_eq_twoCore_inf, h.A_eq_twoCore_inf]
  exact coe_sup_inf_eq_mul_of_normal_normalizes V _ _
    ((pCore_isPGroup.le_sylow_of_normal T).trans h.sylow_le_normalizer)

variable [Finite X]

theorem quotient_twoCore_eq_bot (h : Hypotheses T V M g) :
    pCore 2 (X ⧸ J M) = ⊥ := by
  let q := QuotientGroup.mk' (J M)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hmap : pCore 2 (X ⧸ J M) ≤ M.map q :=
    (pCore_isPGroup.le_sylow_of_normal (T.mapSurjective hq)).trans
      (map_mono (h.sylow_le_normalizer.trans h.normalizer_le))
  have hpre : (pCore 2 (X ⧸ J M)).comap q ≤ M := by
    have hc := comap_mono (f := q) hmap
    rw [comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr M.normalCore_le] at hc
    exact hc
  have hcore : (pCore 2 (X ⧸ J M)).comap q ≤ J M := normal_le_normalCore.mpr hpre
  have hm := map_mono (f := q) hcore
  rw [map_comap_eq, MonoidHom.range_eq_top.mpr hq, top_inf_eq] at hm
  exact bot_unique (hm.trans (by simp [q, J]))

omit [Finite X] in
theorem twoCore_normalizes_V (h : Hypotheses T V M g) :
    pCore 2 X ≤ normalizer (V : Set X) :=
  (pCore_isPGroup.le_sylow_of_normal T).trans h.sylow_le_normalizer

omit [Finite X] in
theorem twoCore_normalizes_W (h : Hypotheses T V M g) :
    pCore 2 X ≤ normalizer (W V g : Set X) := by
  have he : (pCore 2 X).map (MulAut.conj g).toMonoidHom = pCore 2 X :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top g))
  rw [W, ← map_equiv_normalizer_eq V (MulAut.conj g)]
  simpa only [he] using map_mono (f := (MulAut.conj g).toMonoidHom)
    h.twoCore_normalizes_V

theorem commutator_P_V_le_B (h : Hypotheses T V M g) : ⁅P V M g, V⁆ ≤ B V M := by
  rw [h.B_eq_twoCore_inf]
  exact le_inf ((commutator_mono h.P_le_twoCore le_rfl).trans
    (commutator_le_left _ _))
    (le_normalizer_iff_commutator_le_right.mp
      (h.P_le_twoCore.trans h.twoCore_normalizes_V))

theorem quadratic (h : Hypotheses T V M g) : ⁅⁅P V M g, V⁆, V⁆ = ⊥ := by
  let := h.elementary
  apply bot_unique
  exact (commutator_mono (h.commutator_P_V_le_B.trans inf_le_right) le_rfl).trans
    (commutator_eq_bot_iff_le_centralizer.mpr V.le_centralizer).le

theorem commutator_A_B_le_Z (h : Hypotheses T V M g) : ⁅A V M g, B V M⁆ ≤ Z V g := by
  have hBQ : B V M ≤ pCore 2 X := by rw [h.B_eq_twoCore_inf]; exact inf_le_left
  have hAQ : A V M g ≤ pCore 2 X := by rw [h.A_eq_twoCore_inf]; exact inf_le_left
  have hAW : A V M g ≤ W V g := by rw [h.A_eq_twoCore_inf]; exact inf_le_right
  apply le_inf
  · exact (commutator_mono le_rfl (show B V M ≤ V from inf_le_right)).trans
      (le_normalizer_iff_commutator_le_right.mp (hAQ.trans h.twoCore_normalizes_V))
  · rw [commutator_comm]
    exact (commutator_mono le_rfl hAW).trans
      (le_normalizer_iff_commutator_le_right.mp (hBQ.trans h.twoCore_normalizes_W))

theorem commutator_P_A_le_Z (h : Hypotheses T V M g) : ⁅P V M g, A V M g⁆ ≤ Z V g := by
  let := h.elementary
  have hAW : A V M g ≤ W V g := by rw [h.A_eq_twoCore_inf]; exact inf_le_right
  have hc : A V M g ≤ centralizer (A V M g : Set X) :=
    (hAW.trans (W V g).le_centralizer).trans (centralizer_le hAW)
  rw [commutator_comm, commutator_eq_of_product_centralizing_factor h.core_geometry.2.1 hc]
  exact h.commutator_A_B_le_Z

/-- E.2.10(5), in the source's left-normed commutator convention. -/
theorem cubic (h : Hypotheses T V M g) : ⁅⁅⁅V, A V M g⁆, A V M g⁆, A V M g⁆ = ⊥ := by
  have hn := h.core_geometry.1
  have hVP : ⁅V, A V M g⁆ ≤ P V M g :=
    (commutator_mono le_rfl le_sup_right).trans (commutator_le_right _ _)
  have hZ := h.core_geometry.2.2.trans inf_le_right
  apply bot_unique
  exact (commutator_mono
    (((commutator_mono hVP le_rfl).trans h.commutator_P_A_le_Z).trans hZ) le_rfl).trans
      (commutator_eq_bot_iff_le_centralizer.mpr (center_le_centralizer _)).le

/-- The image of `V` in `X/P` has the same kernel as its image in `X/J`. -/
theorem P_inf_V_eq_B (h : Hypotheses T V M g) : P V M g ⊓ V = B V M := by
  apply le_antisymm
  · rw [h.B_eq_twoCore_inf]
    exact inf_le_inf_right V h.P_le_twoCore
  · exact le_inf le_sup_left inf_le_right

/-- The generated two-subgroup is contained in the maximal-overgroup core. -/
theorem P_le_J (h : Hypotheses T V M g) : P V M g ≤ J M :=
  h.P_le_twoCore.trans h.twoCore_le_J

omit [Finite X] in
/-- The initial reduction in E.2.10(9): a proper generator cannot lie in
`O₂(X)`. This does not require a generalized-Fitting hypothesis. -/
theorem V_not_le_twoCore (h : Hypotheses T V M g) (hproper : V ≠ ⊤) :
    ¬ V ≤ pCore 2 X := by
  intro hVQ
  have he : (pCore 2 X).map (MulAut.conj g).toMonoidHom = pCore 2 X :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top g))
  have hWQ : W V g ≤ pCore 2 X := by
    simpa only [he] using map_mono (f := (MulAut.conj g).toMonoidHom) hVQ
  have hXQ : (⊤ : Subgroup X) ≤ pCore 2 X := by
    rw [← h.generate]
    exact sup_le hVQ hWQ
  have hn : V.Normal := normalizer_eq_top_iff.mp
    (top_unique (hXQ.trans h.twoCore_normalizes_V))
  have hW : W V g = V :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top g))
  apply hproper
  simpa only [hW, sup_idem] using h.generate

end Hypotheses

end CFSG.Quasithin.ChapterE.TwoConjugate

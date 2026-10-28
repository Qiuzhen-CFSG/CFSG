module

public import CFSG.Quasithin.ChapterG.Section02.CentralClosure
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan
public import Theory.GroupTheory.AbelianConjugateSpan
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# The original F.8 setup and its central closure

The hypotheses below are exactly F.8.1: an actual ambient Sylow, a two-reduced
seed in LT, the nonzero irreducible quotient V/V₁, the relative normal-core
bound in H, and trivial two-core of the generated group. In particular G.2.1
and the closure conclusions are deductions. All tildes use N_G(V₁)/V₁.

G.2.2 gives the central elementary image and Frattini bound. The centralizer
of the H-span is the normal core of the seed centralizer, so clause (c)
identifies its action kernel with O₂(H).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Hypothesis F.8.1 and Lemma F.8.2, printed pp.315–317, PDF pp.326–328.
Clause (a) also makes the closure elementary abelian directly, giving
F.8.5(2). The remaining coset-geometry results are proved in
F7Specialization, Track, and CriticalPairs and re-exported by Section08.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterF.Section08

variable {G : Type*} [Group G]

/-- The original five subgroups, shared literally with G.2. -/
abbrev Setup := ChapterG.Section02.Setup

namespace Setup
variable (D : Setup G)

/-- The source H* is the quotient of H, distinct from G.2’s quotient of LT. -/
abbrev HStar := D.H ⧸ pCore 2 D.H

/-- The actual centralizer in H of the image of A in N_G(V₁)/V₁. -/
def quotientCentralizer (hH : D.H ≤ D.G₁) (A : Subgroup G) : Subgroup D.H :=
  (centralizer (D.tilde A : Set D.Tilde)).comap
    ((QuotientGroup.mk' (D.V₁.subgroupOf D.G₁)).comp (inclusion hH))

/-- The literal quotient-centralizer membership criterion. -/
theorem mem_quotientCentralizer_iff (hH : D.H ≤ D.G₁)
    (A : Subgroup G) (hA : A ≤ D.G₁) (x : D.H) :
    x ∈ D.quotientCentralizer hH A ↔ ∀ a ∈ A, ⁅a, (x : G)⁆ ∈ D.V₁ := by
  constructor
  · intro hx a ha
    have hc := hx _ (mem_map_of_mem (QuotientGroup.mk' (D.V₁.subgroupOf D.G₁))
      (show (⟨a, hA ha⟩ : D.G₁) ∈ A.subgroupOf D.G₁ from ha))
    have he : (QuotientGroup.mk' (D.V₁.subgroupOf D.G₁))
        ⁅(⟨a, hA ha⟩ : D.G₁), inclusion hH x⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hc
    exact (QuotientGroup.eq_one_iff (⁅(⟨a, hA ha⟩ : D.G₁), inclusion hH x⁆)).mp he
  · intro hx
    rintro _ ⟨a, ha, rfl⟩
    apply commutatorElement_eq_one_iff_mul_comm.mp
    change ⁅(QuotientGroup.mk' (D.V₁.subgroupOf D.G₁)) a,
      (QuotientGroup.mk' (D.V₁.subgroupOf D.G₁)) (inclusion hH x)⁆ = 1
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff (⁅a, inclusion hH x⁆)).mpr (hx a ha)

/-- Comparing the normalizer quotient with the same quotient taken inside H. -/
theorem quotientCentralizer_eq_intrinsic (hH : D.H ≤ D.G₁)
    (A : Subgroup G) (hA : A ≤ D.H) :
    let : (D.V₁.subgroupOf D.H).Normal := normal_subgroupOf_of_le_normalizer hH
    D.quotientCentralizer hH A =
      centralizerModulo ⊤ (A.subgroupOf D.H) (D.V₁.subgroupOf D.H) := by
  let : (D.V₁.subgroupOf D.H).Normal := normal_subgroupOf_of_le_normalizer hH
  ext x
  rw [D.mem_quotientCentralizer_iff hH A (hA.trans hH), mem_centralizerModulo_iff]
  simp only [mem_top, true_and]
  constructor
  · intro hx a ha
    exact hx a ha
  · intro hx a ha
    exact hx ⟨a, hA ha⟩ ha

/-- The normal-core/conjugate-span identity in the literal tilde quotient. -/
theorem quotientCentralizer_span (hH : D.H ≤ D.G₁) (hV : D.V ≤ D.H) :
    D.quotientCentralizer hH D.U = (D.quotientCentralizer hH D.V).normalCore := by
  rw [D.quotientCentralizer_eq_intrinsic hH D.U (conjugateSpanBy_le_self hV),
    D.quotientCentralizer_eq_intrinsic hH D.V hV]
  let : (D.V₁.subgroupOf D.H).Normal := normal_subgroupOf_of_le_normalizer hH
  exact centralizerModulo_conjugateSpanBy_eq_normalCore D.V D.H D.V₁ hV

/-- Hypothesis F.8.1, including the nonzero convention in irreducibility.
Membership in R₂(LT) includes V≤LT; no G.2 or F.8 conclusion is a field. -/
structure Hypothesis [Finite G] : Prop where
  sylow : ∃ P : Sylow 2 G, (P : Subgroup G) = D.T
  elementary : IsElementaryAbelian 2 D.V
  residual : pResidual 2 D.L = ⊤
  T_normalizes_L : D.T ≤ normalizer (D.L : Set G)
  characteristic_L : generalizedFitting D.L = pCore 2 D.L
  V_le_LT : D.V ≤ D.LT
  reduced : IsPReduced 2 (D.V.subgroupOf D.LT)
  centralizer_eq : D.T ⊓ centralizer (D.V : Set G) = D.LT.pCoreIn 2
  point_ne_bot : D.V₁ ≠ ⊥
  point_le : D.V₁ ≤ D.V
  T_normalizes_point : D.T ≤ D.G₁
  conjugates_commute : ∀ g : G, D.V₁ ⊓ ChapterG.Section02.Setup.conjugate D.V g ≠ ⊥ →
    ⁅D.V, ChapterG.Section02.Setup.conjugate D.V g⁆ = ⊥
  quotient_nonzero : D.V₁ ≠ D.V
  irreducible : ∀ A : Subgroup G, D.V₁ ≤ A → A ≤ D.V →
    D.L₁ ⊔ D.T ≤ normalizer (A : Set G) → A = D.V₁ ∨ A = D.V
  H_le : D.H ≤ D.G₁
  local_le : D.L₁ ⊔ D.T ≤ D.H
  characteristic_H : generalizedFitting D.H = pCore 2 D.H
  centralizer_core_le : (D.quotientCentralizer H_le D.V).normalCore ≤ pCore 2 D.H
  generated_core : pCore 2 (D.LT ⊔ D.H : Subgroup G) = ⊥

variable {D} [Finite G]

/-- Reducedness normalizes the seed by all of LT. -/
theorem Hypothesis.LT_normalizes_V (h : D.Hypothesis) :
    D.LT ≤ normalizer (D.V : Set G) :=
  (normal_subgroupOf_iff_le_normalizer h.V_le_LT).mp h.reduced.normal

/-- Reducedness places the seed in the specified ambient Sylow. -/
theorem Hypothesis.V_le_T (h : D.Hypothesis) : D.V ≤ D.T := by
  obtain ⟨P, hP⟩ := h.sylow
  have hT : D.T ≤ D.LT := le_sup_right
  have hcore : D.V ≤ D.LT.pCoreIn 2 := by
    rw [← map_subgroupOf_eq_of_le h.V_le_LT]
    exact map_mono h.reduced.le_pCore
  exact hcore.trans ((pCoreIn_le_sylow D.LT (P.subtype (hP ▸ hT))).trans
    ((map_subgroupOf_eq_of_le (hP ▸ hT)).trans hP).le)

/-- F.8.2: construct G.2.1 from the original F.8.1 assumptions. -/
theorem Hypothesis.g2 (h : D.Hypothesis) : ChapterG.Section02.Setup.Hypothesis D := by
  obtain ⟨P, hP⟩ := h.sylow
  have hTLT : D.T ≤ D.LT := le_sup_right
  have hTH : D.T ≤ D.H := le_sup_right.trans h.local_le
  have hL1 : D.L₁ ≤ D.L := (map_subtype_le _).trans inf_le_left
  exact {
    elementary := h.elementary
    point_ne_bot := h.point_ne_bot
    point_le := h.point_le
    residual := h.residual
    V_le_T := h.V_le_T
    T_normalizes_point := h.T_normalizes_point
    T_normalizes_V := hTLT.trans h.LT_normalizes_V
    T_normalizes_L := h.T_normalizes_L
    sylow_LT := ⟨P.subtype (hP ▸ hTLT), (map_subgroupOf_eq_of_le (hP ▸ hTLT)).trans hP⟩
    H_le := h.H_le
    local_le := h.local_le
    sylow_H := ⟨P.subtype (hP ▸ hTH), (map_subgroupOf_eq_of_le (hP ▸ hTH)).trans hP⟩
    characteristic_two := h.characteristic_H
    local_normalizes_V := (sup_le_sup_right hL1 D.T).trans h.LT_normalizes_V
    quotient_nonzero := h.quotient_nonzero
    irreducible := h.irreducible }

/-- Normality of the actual quotient-action kernel in H. -/
theorem Hypothesis.quotientCentralizer_U_normal (h : D.Hypothesis) :
    (D.quotientCentralizer h.H_le D.U).Normal := by
  rw [D.quotientCentralizer_span h.H_le (h.V_le_T.trans (le_sup_right.trans h.local_le))]
  infer_instance

/-- F.8.2(3), in H: the actual tilde-action kernel is exactly its two-core. -/
theorem Hypothesis.quotientCentralizer_U_eq_pCore (h : D.Hypothesis) :
    D.quotientCentralizer h.H_le D.U = pCore 2 D.H := by
  apply le_antisymm
  · rw [D.quotientCentralizer_span h.H_le (h.V_le_T.trans (le_sup_right.trans h.local_le))]
    exact h.centralizer_core_le
  · have hc := (ChapterG.Section02.Setup.lemma_G_2_2 h.g2).1.2
    intro x hx u hu
    obtain ⟨z, hz, rfl⟩ := omegaOneAmbient_le _ (hc hu)
    have hq : (QuotientGroup.mk' (D.V₁.subgroupOf D.G₁)) (inclusion h.H_le x) ∈
        D.tilde D.QH :=
      ⟨inclusion h.H_le x, mem_map_of_mem D.H.subtype hx, rfl⟩
    exact (congrArg Subtype.val (mem_center_iff.mp hz ⟨_, hq⟩)).symm

/-- F.8.2(3) after embedding both subgroups in the original ambient group. -/
theorem Hypothesis.QH_eq_quotientCentralizer_image (h : D.Hypothesis) :
    D.QH = (D.quotientCentralizer h.H_le D.U).map D.H.subtype := by
  rw [h.quotientCentralizer_U_eq_pCore]
  rfl

/-- The normal core in the source clause (c) is also exactly O₂(H). -/
theorem Hypothesis.centralizer_core_eq_pCore (h : D.Hypothesis) :
    (D.quotientCentralizer h.H_le D.V).normalCore = pCore 2 D.H := by
  rw [← D.quotientCentralizer_span h.H_le (h.V_le_T.trans (le_sup_right.trans h.local_le))]
  exact h.quotientCentralizer_U_eq_pCore

/-- The literal H/C_H(Ũ_H) has trivial two-core, as in F.8.2(1). -/
theorem Hypothesis.quotient_pCore_eq_bot (h : D.Hypothesis) :
    let := h.quotientCentralizer_U_normal
    pCore 2 (D.H ⧸ D.quotientCentralizer h.H_le D.U) = ⊥ := by
  let := h.quotientCentralizer_U_normal
  let q := QuotientGroup.mk' (D.quotientCentralizer h.H_le D.U)
  have hq := QuotientGroup.mk'_surjective (D.quotientCentralizer h.H_le D.U)
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk', h.quotientCentralizer_U_eq_pCore]
    exact pCore_isPGroup
  have he := congrArg (map q) (q.comap_pCore_of_ker_isPGroup hq hk)
  rw [map_comap_eq_self_of_surjective hq] at he
  exact he.trans ((Subgroup.map_eq_bot_iff _).mpr (by
    rw [QuotientGroup.ker_mk', h.quotientCentralizer_U_eq_pCore]))

/-- All of F.8.2, including the literal centralizer quotient and embedded
Frattini subgroup. G.2.1 is constructed, not assumed. -/
theorem lemma_F_8_2 (h : D.Hypothesis) :
    ChapterG.Section02.Setup.Hypothesis D ∧
    (D.tilde D.U ≤ omegaOneAmbient
      ((center (D.tilde D.QH)).map (D.tilde D.QH).subtype)) ∧
    (letI := h.quotientCentralizer_U_normal;
      pCore 2 (D.H ⧸ D.quotientCentralizer h.H_le D.U) = ⊥) ∧
    IsPGroup 2 D.U ∧
    (frattini D.U).map D.U.subtype ≤ D.V₁ ∧
    D.quotientCentralizer h.H_le D.U = pCore 2 D.H := by
  have hg := ChapterG.Section02.Setup.lemma_G_2_2 h.g2
  exact ⟨h.g2, hg.1.2, h.quotient_pCore_eq_bot, h.g2.U_isPGroup,
    hg.2.1, h.quotientCentralizer_U_eq_pCore⟩

/-- Clause (a) makes all H-conjugates commute: their common nontrivial
point is fixed by H. -/
theorem Hypothesis.U_abelian (h : D.Hypothesis) : IsMulCommutative D.U := by
  have hc : D.U ≤ centralizer (D.V : Set G) := by
    apply (closure_le _).mpr
    rintro x ⟨a, ha, v, hv, rfl⟩
    have hfix : D.V₁.map (MulAut.conj a).toMonoidHom = D.V₁ :=
      mem_normalizer_iff_map_conj_eq.mp (h.H_le ha)
    have hp : D.V₁ ≤ ChapterG.Section02.Setup.conjugate D.V a⁻¹ := by
      simpa only [ChapterG.Section02.Setup.conjugate, inv_inv] using
        hfix.symm.le.trans (map_mono h.point_le)
    have hne : D.V₁ ⊓ ChapterG.Section02.Setup.conjugate D.V a⁻¹ ≠ ⊥ := by
      rw [inf_eq_left.mpr hp]
      exact h.point_ne_bot
    have he := le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (h.conjugates_commute a⁻¹ hne))
    apply he
    exact mem_map.mpr ⟨v, hv, by simp [MulAut.conj_apply]⟩
  apply le_centralizer_iff_isMulCommutative.mp
  exact le_centralizer_conjugateSpanBy_of_normalizes D.U D.V D.H
    (le_normalizer_conjugateSpanBy D.V D.H) hc

/-- F.8.5(2) already follows directly from clause (a): the commuting
generators are conjugates of elementary abelian subgroups. -/
theorem lemma_F_8_5_two (h : D.Hypothesis) : IsElementaryAbelian 2 D.U := by
  let := h.elementary
  let S : Set G := {x | ∃ a ∈ D.H, ∃ v ∈ D.V, a * v * a⁻¹ = x}
  let : IsMulCommutative (closure S) := h.U_abelian
  apply IsElementaryAbelian.closure_of_isMulCommutative S
  rintro x ⟨a, _, v, hv, rfl⟩
  rw [conj_pow, elemPow_eq_one_of_isElementaryAbelian v hv, mul_one, mul_inv_cancel]

end Setup
end CFSG.Quasithin.ChapterF.Section08


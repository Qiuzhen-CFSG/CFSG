module

public import CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup
public import Theory.GroupTheory.ConjugateIntersectionCore
public import Theory.GroupTheory.IntersectingConjugateFusion
public import Theory.GroupTheory.AbelianConjugateSpan

/-!
# Core transfer, abelian criteria, and fusion in Section 12.6

The F.9 hypothesis below is an explicit prerequisite: the amalgam argument
must establish it. With that input, F.9.3–4 prove all four equivalences of
12.6.25. The other results implement the normalizer bound and core transfer
in 12.6.24 and the fusion transport in 12.6.27. The latter still requires
the abelianness theorem 12.6.26 at the full point centralizer.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemmas 12.6.24–27, printed pp.830–833.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup
variable {G : Type*} [Group G] [Finite G] (D : Setup G)

/-- 12.6.24(4) from the earlier intersection bound. The two orders are the
five-dimensional hyperplane and the maximal singular three-space. -/
theorem G₅_le_normalizer
    (hcard : Nat.card D.V₅ = 2 ^ 5)
    (hbound : ∀ g : G, g ∉ normalizer (D.V : Set G) →
      Nat.card (D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3) :
    D.G₅ ≤ normalizer (D.V : Set G) := by
  apply normalizer_le_of_conjugate_intersection_card_bound D.V₅_le _ hbound
  rw [hcard]
  decide

/-- The source conclusions 12.6.24(2),(8) once the genuine F.9.1 bridge
has been proved. The kernel is computed on the literal U_H/V₁. -/
theorem span_core_and_kernel {H : Subgroup G} (h : (D.f9 H).Hypothesis) :
    D.UH H ≤ QH H ∧ QH H = h.kernel (D.UH H) :=
  ⟨h.UH_le_QH, h.kernel_UH_eq_QH.symm⟩

/-- 12.6.24(3): transfer V₅ through C_G(V₂), then use its L₂-span.
The centralizer is relatively normal in G₂=N_G(V₂). -/
theorem V_le_G₂_core (h : (D.f9 D.Gz).Hypothesis)
    (V₂ L₂ : Subgroup G) (hV₂ : V₂ ≤ D.V)
    (hC : centralizer (V₂ : Set G) ≤ D.Gz)
    (hL₂ : L₂ ≤ normalizer (V₂ : Set G))
    (hspan : D.V = conjugateSpanBy D.V₅ L₂) :
    D.V ≤ (normalizer (V₂ : Set G)).pCoreIn 2 := by
  let : IsElementaryAbelian 2 D.V := h.elementary
  exact conjugateSpanBy_le_pCoreIn_of_centralizer_le hspan
    ((le_conjugateSpanBy D.V₅ D.Gz).trans h.UH_le_QH)
    (D.V₅_le.trans ((le_centralizer D.V).trans (centralizer_le hV₂))) hC hL₂

omit [Finite G] in
/-- The 12.6.24(5) group-theoretic step. The positioning input is the
source singular-plane orbit calculation: a normalizer element carries V₂
into the conjugate. All two-group assertions then follow from the local
core and relative normality. -/
theorem pair_isTwoGroup_of_positioning
    (V₂ : Subgroup G) (hcore : D.V ≤ (normalizer (V₂ : Set G)).pCoreIn 2)
    (hposition : ∀ g : G, D.V₁ < D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom →
      ∃ n ∈ normalizer (D.V : Set G),
        V₂ ≤ (D.V.map (MulAut.conj g).toMonoidHom).map (MulAut.conj n).toMonoidHom)
    (g : G) (hinter : D.V₁ < D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom) :
    IsPGroup 2 (D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom : Subgroup G) := by
  let : IsElementaryAbelian 2 D.V := D.elementary
  obtain ⟨n, hn, hV₂⟩ := hposition g hinter
  let A := (D.V.map (MulAut.conj g).toMonoidHom).map (MulAut.conj n).toMonoidHom
  let : IsElementaryAbelian 2 (D.V.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hA : A ≤ normalizer (V₂ : Set G) :=
    ((le_centralizer A).trans (centralizer_le hV₂)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hp := isPGroup_sup_of_le_pCoreIn hcore hA (IsElementaryAbelian.isPGroup 2 A)
  have hnV : D.V.map (MulAut.conj n).toMonoidHom = D.V :=
    mem_normalizer_iff_map_conj_eq.mp hn
  have hm : IsPGroup 2 ((D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj n).toMonoidHom) := by
    rw [Subgroup.map_sup, hnV]
    exact hp
  exact hm.of_equiv (equivMapOfInjective _ _ (MulAut.conj n).injective).symm

/-- 12.6.25, with abelianness in the source statement rather than an
extra elementary-abelian assumption on either conjugate span. -/
theorem lemma_12_6_25 {H : Subgroup G} (h : (D.f9 H).Hypothesis)
    (hC : centralizer (D.V₅ : Set G) = centralizer (D.V : Set G)) :
    (IsMulCommutative (D.UH H) ↔ D.V ≤ QH H) ∧
    (D.V ≤ QH H ↔ D.V ≤ centralizer (D.UH H : Set G)) ∧
    (IsMulCommutative (D.UH H) ↔ IsMulCommutative (D.VH H)) := by
  let : IsElementaryAbelian 2 D.V := h.elementary
  let : IsElementaryAbelian 2 D.V₅ := IsElementaryAbelian.of_le D.V₅_le
  have hU : IsMulCommutative (D.UH H) ↔ IsElementaryAbelian 2 (D.f9 H).UH := by
    constructor
    · intro hu
      let : IsMulCommutative (conjugateSpanBy D.V₅ H) := hu
      exact conjugateSpanBy_elementary_of_commutative D.V₅ H
    · intro hu
      let : IsElementaryAbelian 2 (D.UH H) := hu
      infer_instance
  have hV : IsMulCommutative (D.VH H) ↔ IsElementaryAbelian 2 (D.f9 H).VH := by
    constructor
    · intro hv
      let : IsMulCommutative (conjugateSpanBy D.V H) := hv
      exact conjugateSpanBy_elementary_of_commutative D.V H
    · intro hv
      let : IsElementaryAbelian 2 (D.VH H) := hv
      infer_instance
  have hCN : (H ⊓ centralizer (D.V₅ : Set G)) ⊓
      (H ⊓ normalizer (D.V : Set G)) = H ⊓ centralizer (D.V : Set G) := by
    rw [hC]
    exact inf_eq_left.mpr (inf_le_inf_left H (Subgroup.centralizer_le_normalizer _))
  obtain ⟨hq, huv⟩ := h.lemma_F_9_4_three hCN
  refine ⟨hU.trans hq.symm, ?_, hU.trans (huv.trans hV.symm)⟩
  constructor
  · intro hv
    exact (h.lemma_F_9_3.1.mp hv).trans inf_le_right
  · intro hv
    exact h.lemma_F_9_3.1.mpr (le_inf h.V_le_H hv)

/-- The contrary-nonabelian assumption supplies precisely the nontrivial
star image needed in F.9.5; it is not assumed as an independent conclusion. -/
theorem nonabelian_inputs {H : Subgroup G} (h : (D.f9 H).Hypothesis)
    (hC : centralizer (D.V₅ : Set G) = centralizer (D.V : Set G))
    (hn : ¬ IsMulCommutative (D.VH H)) :
    ¬ IsMulCommutative (D.UH H) ∧ ¬ D.V ≤ QH H ∧ star H D.V ≠ ⊥ := by
  have he := D.lemma_12_6_25 h hC
  have hu : ¬ IsMulCommutative (D.UH H) := fun hU => hn (he.2.2.mp hU)
  have hq : ¬ D.V ≤ QH H := fun hQ => hu (he.1.mpr hQ)
  refine ⟨hu, hq, ?_⟩
  intro hv
  apply hq
  intro v hvV
  have hvm : (⟨v, h.V_le_H hvV⟩ : H) ∈ pCore 2 H := by
    apply (QuotientGroup.eq_one_iff _).mp
    apply mem_bot.mp
    rw [← hv]
    exact mem_map_of_mem (QuotientGroup.mk' (pCore 2 H)) hvV
  exact mem_map_of_mem H.subtype hvm

/-- The last order contradiction on p.833, on the actual quotient image.
The component and L₂(11) analysis must supply its lower bound, core
containment and core order; none is part of the setup. -/
theorem terminal_order_contradiction {H : Subgroup G} (h : (D.f9 H).Hypothesis)
    (hlower : 2 ^ 10 ≤ Nat.card ((D.f9 H).tilde (D.UH H)))
    (hcore : D.UH H ≤ D.L₁.pCoreIn 2) (horder : Nat.card (D.L₁.pCoreIn 2) = 2 ^ 9) :
    False := by
  have hUN : D.UH H ≤ (D.f9 H).g2.G₁ :=
    h.UH_le_H.trans h.g2_hypothesis.H_le
  have hq : Nat.card ((D.f9 H).tilde (D.UH H)) ≤
      Nat.card ((D.UH H).subgroupOf (D.f9 H).g2.G₁) :=
    Nat.le_of_dvd Nat.card_pos (card_map_dvd _ _)
  have he : Nat.card ((D.UH H).subgroupOf (D.f9 H).g2.G₁) = Nat.card (D.UH H) :=
    Nat.card_congr (subgroupOfEquivOfLe hUN).toEquiv
  have hc : Nat.card (D.UH H) ≤ Nat.card (D.L₁.pCoreIn 2) :=
    Nat.card_le_card_of_injective (inclusion hcore) (inclusion_injective hcore)
  rw [he] at hq
  rw [horder] at hc
  have hbad := hlower.trans (hq.trans hc)
  norm_num at hbad

omit [Finite G] in
/-- The actual fusion step of 12.6.27. Outside the normalizer only the
intersection must belong to the point orbit; V has a second, nonsingular
orbit, so transitivity on all nonidentity elements is not assumed. -/
theorem lemma_12_6_27_of_abelian
    (hspan : IsMulCommutative (D.VH D.Gz))
    (hfusion : ∀ a : G, MulAut.conj a D.z.val ∈ D.V →
      ∃ n ∈ normalizer (D.V : Set G),
        MulAut.conj n D.z.val = MulAut.conj a D.z.val)
    (horbit : ∀ g : G, g ∉ normalizer (D.V : Set G) →
      ∀ x ∈ D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom, x ≠ 1 →
        ∃ n ∈ normalizer (D.V : Set G), MulAut.conj n x = D.z.val)
    (g : G) (hinter : D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom ≠ ⊥) :
    ⁅D.V, D.V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  let : IsElementaryAbelian 2 D.V := D.elementary
  by_cases hg : g ∈ normalizer (D.V : Set G)
  · have he : D.V.map (MulAut.conj g).toMonoidHom = D.V :=
      mem_normalizer_iff_map_conj_eq.mp hg
    rw [he]
    exact commutator_self_eq_bot_iff.mpr inferInstance
  · have hc : IsMulCommutative (centralizerConjugateClosure D.V D.z.val) := by
      rw [centralizerConjugateClosure_eq_conjugateSpanBy, ← D.Gz_eq]
      exact hspan
    let := hc
    exact commutator_conjugate_eq_bot_of_intersection_fusion D.V D.z.val g
      hfusion hinter (horbit g hg)

end CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup

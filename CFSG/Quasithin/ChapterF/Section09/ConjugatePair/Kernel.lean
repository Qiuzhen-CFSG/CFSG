module
public import CFSG.Quasithin.ChapterF.Section09.ConjugatePair.Quaternion
public import Theory.GroupTheory.ConjugatePairSeed.Supplement

/-!
# Faithfulness on the original pair seed in F.9.5

The quaternion seed P has U_H = P C_U_H(P). The source centralizer bounds
make both module generators centralize the complementary factor modulo V₁.
Consequently the kernel of the pair action on P/V₁ is exactly its intersection
with O₂(H), as for the original action on U_H/V₁. All subgroups and quotient
kernels are retained in the original ambient group.
Source: Aschbacher–Smith F.9.5(5–6.i), printed p.319.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G} (h : D.Hypothesis)
include h

omit [Finite G] h in
/-- A non-two pair forces the original module outside O₂(H). -/
theorem pair_module_not_le_core (g : G) (hg : g ∈ D.H)
    (hn : ¬ IsPGroup 2 (D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    ¬ D.V ≤ D.QH := by
  intro hv
  have hq : D.QH.map (MulAut.conj g).toMonoidHom = D.QH :=
    mem_normalizer_iff_map_conj_eq.mp (H_normalizes_QH (D := D) hg)
  exact hn ((isPGroup_pCoreIn 2 D.H).to_le
    (sup_le hv ((map_mono hv).trans_eq hq)))

/-- Both module generators normalize the actual join of their moved seeds. -/
theorem pair_normalizes_seed_join
    (hi : D.Vplus.relIndex D.V = 2) (g : G) (hg : g ∈ D.H)
    (hn : ¬ IsPGroup 2 (D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom ≤
      normalizer (D.Vplus ⊔ D.Vplus.map (MulAut.conj g).toMonoidHom : Subgroup G) := by
  let f := (MulAut.conj g).toMonoidHom
  let P := D.Vplus ⊔ D.Vplus.map f
  have hPQ : P ≤ D.QH := sup_le ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
    ((pair_seed_conjugate_le_closure (D := D) g hg).trans h.UH_le_QH)
  have hv := h.core_module_commutator_le_seed hi (pair_module_not_le_core (D := D) g hg hn)
  have hvg : ⁅D.QH,D.V.map f⁆ ≤ D.Vplus.map f := by
    have hm := map_mono (f := f) hv
    have hq : D.QH.map f = D.QH :=
      mem_normalizer_iff_map_conj_eq.mp (H_normalizes_QH (D := D) hg)
    rwa [map_commutator,hq] at hm
  exact sup_le
    (le_normalizer_iff_commutator_le_left.mpr
      (((commutator_mono hPQ le_rfl).trans hv).trans le_sup_left))
    (le_normalizer_iff_commutator_le_left.mpr
      (((commutator_mono hPQ le_rfl).trans hvg).trans le_sup_right))

/-- The literal kernel on the pair seed is its intersection with O₂(H). -/
theorem pair_seed_kernel
    (hi : D.Vplus.relIndex D.V = 2) (hcard : Nat.card D.V = 16)
    (hp : ∀ g ∈ D.H, D.V₁ < D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom →
      IsPGroup 2 (D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom : Subgroup G))
    (hc : ⁅D.V,D.H ⊓ centralizer (D.Vplus : Set G)⁆ ≤ D.V₁)
    (g : G) (hg : g ∈ D.H)
    (hn : ¬ IsPGroup 2 (D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    commutatorPreimage (D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom)
      (D.Vplus ⊔ D.Vplus.map (MulAut.conj g).toMonoidHom) D.V₁ =
      (D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom) ⊓ D.QH := by
  let f := (MulAut.conj g).toMonoidHom
  let B := D.V.map f
  let E := D.Vplus.map f
  let I := D.V ⊔ B
  let P := D.Vplus ⊔ E
  let R := D.UH ⊓ centralizer (P : Set G)
  have hBH : B ≤ D.H := by
    rintro _ ⟨a,ha,rfl⟩
    exact D.H.mul_mem (D.H.mul_mem hg (h.V_le_H ha)) (D.H.inv_mem hg)
  have hIH : I ≤ D.H := sup_le h.V_le_H hBH
  have hPU : P ≤ D.UH := sup_le (le_conjugateSpanBy _ _)
    (pair_seed_conjugate_le_closure (D := D) g hg)
  obtain ⟨q⟩ := h.pair_seed_quaternion hi hcard hp hc g hg hn
  let : IsExtraspecial 2 P := q.extraspecial
  have hUP : ⁅D.UH,P⁆ ≤ D.V₁ :=
    (commutator_mono le_rfl (hPU.trans h.UH_le_QH)).trans h.commutator_UH_QH_le_point
  have hs : P ⊔ R = D.UH := extraspecial_sup_centralizer_eq P D.UH D.V₁ hPU
    (h.pair_seed_center hp hc g hg hn) hUP
  have hR1 : R ≤ D.H ⊓ centralizer (D.Vplus : Set G) :=
    le_inf (inf_le_left.trans h.UH_le_H) (inf_le_right.trans (centralizer_le (show D.Vplus ≤ P from le_sup_left)))
  have hR2 : R ≤ D.H ⊓ centralizer (E : Set G) :=
    le_inf (inf_le_left.trans h.UH_le_H) (inf_le_right.trans (centralizer_le (show E ≤ P from le_sup_right)))
  have hHZ : D.H ≤ normalizer (D.V₁ : Set G) :=
    h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)
  have hIR : ⁅I,R⁆ ≤ D.V₁ := by
    have hm : I ≤ commutatorPreimage D.H R D.V₁ := sup_le
      (le_commutatorPreimage h.V_le_H ((commutator_mono le_rfl hR1).trans hc))
      (le_commutatorPreimage hBH ((commutator_mono le_rfl hR2).trans
        (h.pair_conjugate_centralizer_bound hc g hg)))
    exact (commutator_mono hm le_rfl).trans
      (commutator_commutatorPreimage_le D.H R D.V₁ hHZ)
  have he := commutatorPreimage_eq_of_centralizer_supplement I P D.UH D.V₁
    (hIH.trans hHZ) (h.UH_le_H.trans hHZ) hPU hs hIR
  change commutatorPreimage I P D.V₁ = I ⊓ D.QH
  rw [he]
  ext x
  rw [mem_commutatorPreimage_iff I D.UH D.V₁ (hIH.trans hHZ)]
  constructor
  · rintro ⟨hx,hxc⟩
    refine ⟨hx,?_⟩
    rw [←h.kernel_UH_eq_QH]
    apply (h.mem_kernel_iff h.UH_le_H).mpr
    refine ⟨hIH hx,fun u hu => ?_⟩
    rw [←commutatorElement_inv]
    exact D.V₁.inv_mem (hxc u hu)
  · rintro ⟨hx,hxq⟩
    refine ⟨hx,fun u hu => ?_⟩
    rw [←commutatorElement_inv]
    exact D.V₁.inv_mem (h.commutator_UH_QH_le_point (commutator_mem_commutator hu hxq))
end CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis

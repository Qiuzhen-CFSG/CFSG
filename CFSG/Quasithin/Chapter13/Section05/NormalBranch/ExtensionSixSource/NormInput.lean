module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource.AbelianSpan
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource.ReturningCubic
public import Theory.GroupTheory.CubicNormFrattini

/-!
# The original inputs to the terminal cubic norm contradiction

The cyclic core-center generator lies outside L, while the returning
cubic actor belongs to L. The literal quotient M/L has order two and
detects the generator; its character on B is invariant under the actor.
Together with Φ(B) = V₂, these facts produce an involution a and a
two-subgroup X of O²(C_G(a)) with Φ(X) = V₂.

The residual endpoint uses precisely this witness. Source:
Aschbacher–Smith, Proposition 13.5.16, printed p.922.
-/

universe u

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource
open Section08.SourceCompletion
variable {G : Type u} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G} {g : G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
  (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH) (b : Conclusions D M 6 g)
  (hS : Nonempty ((M ⧸ pCore 2 M) ≃* Equiv.Perm (Fin 6)))

include d h in
theorem center_span_le_maximal :
    conjugateSpanBy ((center D.QH).map D.QH.subtype)
      (Section08.TransvectionParabolic.EarlierCore.localResidual D.L V₂) ≤ M := by
  have hTM : (D.T : Subgroup G) ≤ M := by rw [d.local_normalizer]; exact d.normalizes_L
  have hLM : D.L ≤ M := by rw [d.local_normalizer]; exact D.L.le_normalizer
  apply conjugateSpanBy_le ((map_subtype_le _).trans (h.QH_le_T.trans hTM))
  exact ((Section08.TransvectionParabolic.EarlierCore.localResidual_le _ _).trans hLM).trans
    M.le_normalizer

include d in
theorem local_normal_in_maximal : (D.L.subgroupOf M).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  rw [d.local_normalizer]

include d h e hseed hn hU b hS in
theorem exists_norm_input
    (z : G) (hz : z ∈ D.V₁) (hz1 : z ≠ 1) :
    ∃ (B : Subgroup G) (r : G) (j : B),
      IsMulCommutative B ∧ IsPGroup 2 B ∧
      (frattini B).map B.subtype = V₂ ∧
      r ∈ normalizer (B : Set G) ∧ orderOf r = 3 ∧
      j.val ^ 2 = z ∧ MulAut.conj r z ≠ z ∧
      ∃ (K : Type u) (_ : Group K) (χ : B →* K),
        Nat.card K = 2 ∧ χ j ≠ 1 ∧
        ∀ (hr : r ∈ normalizer (B : Set G)) (x : B),
          χ (B.normalizerMonoidHom ⟨r,hr⟩ x) = χ x := by
  let C := (center D.QH).map D.QH.subtype
  let R := Section08.TransvectionParabolic.EarlierCore.localResidual D.L V₂
  let B := conjugateSpanBy C R
  obtain ⟨j,hj4,hjz,hgen⟩ := exists_center_generator d h e hseed hn hU b hS z hz hz1
  have hjC : j ∈ C := by
    change j ∈ (center D.QH).map D.QH.subtype
    rw [hgen]
    exact mem_zpowers j
  have hjB : j ∈ B := le_conjugateSpanBy _ _ hjC
  have hjL := center_order_four_not_mem_local d h e hseed hn hU b j hjC hj4
  obtain ⟨r,hrR,_,hrH,hr3⟩ := exists_returning_cubic d h b
  have hrB : r ∈ normalizer (B : Set G) := le_normalizer_conjugateSpanBy _ _ hrR
  have hrL : r ∈ D.L := Section08.TransvectionParabolic.EarlierCore.localResidual_le _ _ hrR
  have hLM : D.L ≤ M := by rw [d.local_normalizer]; exact D.L.le_normalizer
  have hBM : B ≤ M := center_span_le_maximal d h
  let N := D.L.subgroupOf M
  let : N.Normal := local_normal_in_maximal d
  let K := M ⧸ N
  let π := QuotientGroup.mk' N
  let χ : B →* K := π.comp (inclusion hBM)
  refine ⟨B,r,⟨j,hjB⟩,center_span_abelian d h e hseed hn hU b hS,
    center_span_isPGroup d h e hseed hn hU b hS,
    center_span_frattini d h e hseed hn hU b hS,hrB,hr3,hjz,?_,
    K,inferInstance,χ,local_index_two_in_maximal d h e hseed hn hU b hS,?_,?_⟩
  · intro he
    apply hrH
    rw [←TypeU4.centralizer_eq h b z hz hz1]
    exact mem_centralizer_singleton_iff.mpr (by
      change r * z * r⁻¹ = z at he
      have hh := congrArg (fun x => x * r) he
      simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh)
  · intro he
    exact hjL ((QuotientGroup.eq_one_iff (N := N) (inclusion hBM ⟨j,hjB⟩)).mp he)
  · intro hr x
    have hrπ : π (⟨r,hLM hrL⟩ : M) = 1 := (QuotientGroup.eq_one_iff _).mpr hrL
    change π (inclusion hBM (B.normalizerMonoidHom ⟨r,hr⟩ x)) = π (inclusion hBM x)
    have he : inclusion hBM (B.normalizerMonoidHom ⟨r,hr⟩ x) =
        (⟨r,hLM hrL⟩ : M) * inclusion hBM x * (⟨r,hLM hrL⟩ : M)⁻¹ := rfl
    rw [he,map_mul,map_mul,map_inv,hrπ,inv_one,one_mul,mul_one]



include d h e hseed hn hU b hS in
/-- The original plane construction supplies the exact transfer contradiction witness. -/
theorem exists_terminal_frattini_witness
    (z : G) (hz : z ∈ D.V₁) (hz1 : z ≠ 1) :
    ∃ (a : G) (X : Subgroup G), orderOf a = 2 ∧ IsPGroup 2 X ∧
      X ≤ (pResidual 2 (centralizer ({a} : Set G))).map
        (centralizer ({a} : Set G)).subtype ∧
      (frattini X).map X.subtype = V₂ := by
  obtain ⟨B,r,j,hBc,hBp,hPhi,hrB,hr,hjz,hm,K,hKgroup,χ,hK,hχj,hχ⟩ :=
    exists_norm_input d h e hseed hn hU b hS z hz hz1
  let : Group K := hKgroup
  let : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; decide)
  let : IsMulCommutative B := hBc
  let : IsElementaryAbelian 2 D.V := h.elementary
  let : IsElementaryAbelian 2 V₂ := IsElementaryAbelian.of_le
    (d.plane_le_seed.trans d.seed_le)
  have hj : j ^ 2 ≠ 1 := by
    intro he
    exact hz1 (hjz.symm.trans (congrArg Subtype.val he))
  have hm' : r * (j : G) ^ 2 * r⁻¹ ≠ (j : G) ^ 2 := by
    rw [hjz]
    exact hm
  apply Subgroup.CubicNormFrattini.exists_involution_residual_frattini
    B V₂ hBp hPhi d.plane_card r hr hrB j hj hm' χ
  · intro k
    simpa only [hK] using (pow_card_eq_one' (x := k))
  · exact hχ hrB
  · exact hχj

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource

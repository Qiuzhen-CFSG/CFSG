module

public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Basic

/-!
# The vanishing centralizing residual in the natural L₃(2) case

For a two-perfect subgroup Y normalized by Q, adjoining the two-group Q
recovers Y as O²(YQ). Hence normalization of Y modulo Q lifts to normalization
of Y itself. Apply this with Q=O₂(L) and Y=O²(C_G(U)). In the L₃(2) natural
action, C_L(V)=O₂(L), and V₃=V, so the commutator calculation supplies the
normalization modulo Q. If Y were nontrivial, characteristic two in G₁
would give a nontrivial O₂(Y), whose normalizer contains both LT and G₁.
Uniqueness of M over LT then contradicts G₁ not contained in M.

This proves the L₃(2) instance of reduction (b). It does not prove the
remaining Fitting, component or diagonal-block contradictions in 13.3.14.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), p.891.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open Subgroup
open scoped commutatorElement
variable {G : Type*} [Group G]

/-- Lift normalization modulo a normalizing two-subgroup by recovering the
original two-perfect subgroup as the residual of its product. -/
theorem normalizes_of_commutator_le_twoGroup (A Y Q : Subgroup G)
    (hY : IsPPerfect 2 Y) (hQ : IsPGroup 2 Q)
    (hQY : Q ≤ normalizer (Y : Set G))
    (hAQ : A ≤ normalizer (Q : Set G)) (hcomm : ⁅A, Y⁆ ≤ Q) :
    A ≤ normalizer (Y : Set G) := by
  let P := Y ⊔ Q
  let : (Y.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le Y.le_normalizer hQY)
  have hYP : IsPPerfect 2 (Y.subgroupOf P) :=
    hY.of_surjective (subgroupOfEquivOfLe (show Y ≤ P from le_sup_left)).symm.toMonoidHom
      (subgroupOfEquivOfLe (show Y ≤ P from le_sup_left)).symm.surjective
  have hs : Y.subgroupOf P ⊔ Q.subgroupOf P = ⊤ := by
    rw [← subgroupOf_sup (show Y ≤ P from le_sup_left)
      (show Q ≤ P from le_sup_right)]
    exact subgroupOf_self P
  have he : (pResidual 2 P).map P.subtype = Y := by
    rw [pResidual_eq_of_isPPerfect_sup _ _ hYP hQ.comap_subtype hs,
      map_subgroupOf_eq_of_le (show Y ≤ P from le_sup_left)]
  have hAP : A ≤ normalizer (P : Set G) := by
    apply le_normalizer_iff.mpr
    intro a ha
    have hYmap : Y.map (MulAut.conj a).toMonoidHom ≤ P := by
      rintro x ⟨y, hy, rfl⟩
      have hc : ⁅a, y⁆ ∈ Q := hcomm (commutator_mem_commutator ha hy)
      have heq : a * y * a⁻¹ = ⁅a, y⁆ * y := by simp [commutatorElement_def, mul_assoc]
      change a * y * a⁻¹ ∈ P
      rw [heq]
      exact P.mul_mem (mem_sup_right hc) (mem_sup_left hy)
    have hQmap : Q.map (MulAut.conj a).toMonoidHom ≤ P := by
      rintro x ⟨q, hq, rfl⟩
      exact mem_sup_right (le_normalizer_iff.mp hAQ a ha q hq)
    have hm : P.map (MulAut.conj a).toMonoidHom ≤ P := by
      rw [Subgroup.map_sup]
      exact sup_le hYmap hQmap
    intro x hx
    exact hm (mem_map.mpr ⟨x, hx, rfl⟩)
  have hn := hAP.trans (normalizer_le_normalizer_characteristic_image P (pResidual 2 P))
  rwa [he] at hn

variable [Finite G]

/-- The normalizer-uniqueness paragraph of reduction (b), specialized to the
faithful natural kernel C_L(V)=O₂(L). All cores and normalizers are literal. -/
theorem residual_eq_bot_of_natural_kernel (L T V H Y : Subgroup G)
    (hHT : T ≤ H) (hYH : Y ≤ H) (hHY : H ≤ normalizer (Y : Set G))
    (hH : H ∈ Chapter1.He G) (hY : IsPPerfect 2 Y)
    (hYC : Y ≤ centralizer (V : Set G))
    (hCM : centralizer (V : Set G) ≤ normalizer (L : Set G))
    (hLV : L ≤ normalizer (V : Set G))
    (hkernel : L ⊓ centralizer (V : Set G) = L.pCoreIn 2)
    (hQT : L.pCoreIn 2 ≤ T)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ T ≤ N →
      N = normalizer (L : Set G))
    (hescape : ¬ H ≤ normalizer (L : Set G)) : Y = ⊥ := by
  by_contra hne
  have hLC : L ≤ normalizer (centralizer (V : Set G) : Set G) :=
    hLV.trans ((normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer _)).mp inferInstance)
  have hcomm : ⁅L, Y⁆ ≤ L.pCoreIn 2 := by
    rw [← hkernel]
    exact le_inf (le_normalizer_iff_commutator_le_left.mp (hYC.trans hCM))
      ((commutator_mono le_rfl hYC).trans
        (le_normalizer_iff_commutator_le_right.mp hLC))
  have hLY : L ≤ normalizer (Y : Set G) :=
    normalizes_of_commutator_le_twoGroup L Y (L.pCoreIn 2) hY
      (isPGroup_pCoreIn 2 L) (hQT.trans (hHT.trans hHY))
      (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
      hcomm
  let : (Y.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hYH).mpr hHY
  have hYe : Y ∈ Chapter1.He G := Chapter1.lemma_1_1_3_1 hH hne hYH
    (inferInstance : (Y.subgroupOf H).Normal).isSubnormal
  have hcore : Y.pCoreIn 2 ≠ ⊥ := by
    intro he
    apply hne
    apply bot_unique
    change Y ⊓ centralizer (Y.pCoreIn 2 : Set G) ≤ Y.pCoreIn 2 at hYe
    intro y hy
    rw [← he]
    apply hYe
    exact ⟨hy, by rw [he]; intro q hq; rw [mem_bot.mp hq]; simp⟩
  have hncore := normalizer_le_normalizer_characteristic_image Y (pCore 2 Y)
  have hNM : normalizer (Y.pCoreIn 2 : Set G) ≤ normalizer (L : Set G) :=
    normalizer_le_of_unique_maximalTwoLocal hunique (isPGroup_pCoreIn 2 Y) hcore
      ((sup_le hLY (hHT.trans hHY)).trans hncore)
  exact hescape (hHY.trans (hncore.trans hNM))

/-- The actual centralizing residual of the V-closure vanishes in the natural
kernel case. In the L₃(2) source branch V₃=V, so this is exactly its Y. -/
theorem centralizingResidual_eq_bot_of_natural_kernel (L T V V₁ : Subgroup G)
    (hTV₁ : T ≤ normalizer (V₁ : Set G)) (hV₁V : V₁ ≤ V)
    (hH : normalizer (V₁ : Set G) ∈ Chapter1.He G)
    (hCM : centralizer (V : Set G) ≤ normalizer (L : Set G))
    (hLV : L ≤ normalizer (V : Set G))
    (hkernel : L ⊓ centralizer (V : Set G) = L.pCoreIn 2)
    (hQT : L.pCoreIn 2 ≤ T)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ T ≤ N →
      N = normalizer (L : Set G))
    (hescape : ¬ normalizer (V₁ : Set G) ≤ normalizer (L : Set G)) :
    centralizingResidual (conjugateSpanBy V (normalizer (V₁ : Set G))) = ⊥ :=
  residual_eq_bot_of_natural_kernel L T V _ _ hTV₁
    (centralizingResidual_le_point_group V₁ V hV₁V)
    (normalizes_centralizingResidual _ _) hH
    (centralizingResidual_isPPerfect _) (centralizingResidual_le_seed_centralizer _ _)
    hCM hLV hkernel hQT hunique hescape

end CFSG.Quasithin.Chapter13.Section03.Noncentrality

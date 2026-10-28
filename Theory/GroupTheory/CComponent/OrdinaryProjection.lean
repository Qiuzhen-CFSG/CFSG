module
public import Theory.GroupTheory.CentralProductPrimeProjection
public import Theory.GroupTheory.ComponentSaturatedSylow
public import Theory.GroupTheory.CentralProductPerfectProjection
public import Theory.GroupTheory.GeneralizedFitting.ComponentContainingPerfect

/-!
# Placing an original C-component using its moved module

A projected prime subgroup in an ordinary component is controlled by the
original actor's saturation. Irreducibility then puts the whole moved module
inside that component. Perfect central-product projection, followed by
C-component minimality, places the original actor there as well.

The subgroup embeddings, central product factors and normalizer conditions
remain literal. Source: Aschbacher–Smith, C.3.2–3, printed p.149; the
irreducible-module specialization applies to the A₅ block in 4.3.2.
-/

public section
open Subgroup
open scoped Pointwise commutatorElement
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A central factor can be removed from a commutator calculation. -/
theorem commutator_le_of_le_sup_centralizing (A B C P : Subgroup G)
    (hAP : A ≤ P ⊔ C) (hPC : P ≤ centralizer (C : Set G))
    (hPB : P ≤ centralizer (B : Set G))
    (hBC : B ≤ normalizer (C : Set G)) : ⁅A,B⁆ ≤ C := by
  apply commutator_le.mpr
  intro a ha b hb
  have hap : a ∈ (P : Set G) * (C : Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right P C (hPC.trans (centralizer_le_normalizer _))]
    exact hAP ha
  obtain ⟨p,hp,c,hc,rfl⟩ := hap
  have hcb : ⁅c,b⁆ ∈ C := (le_normalizer_iff_commutator_le_left.mp hBC)
    (commutator_mem_commutator hc hb)
  have hpb : ⁅p,b⁆=1 := (show Commute p b from (hPB hp b hb).symm).commutator_eq
  rw [commutatorElement_mul_left_eq_conj_mul,hpb,mul_one]
  exact ((hPC.trans (centralizer_le_normalizer _) hp) _).mp hcb

/-- Saturation places an irreducible moved module in the original component.
The actor may initially permute components. -/
theorem IsComponent.module_le_of_stabilizer_saturation
    {K L M R V : Subgroup G} (hK : IsComponent G K)
    (hVL : V ≤ L) (hLM : L ≤ M)
    (hMV : M ≤ normalizer (V : Set G))
    (hinner : L ≤ K ⊔ centralizer (K : Set G))
    (hVp : IsPGroup 2 V) (hmoved : V = ⁅V,L⁆)
    (hRV : ⁅R,L⁆ ≤ V)
    (hsat : ∀ P : Subgroup G, IsPGroup 2 P → M ≤ normalizer (P : Set G) → P ≤ R)
    (hirr : ∀ W : Subgroup G, W ≤ V → L ≤ normalizer (W : Set G) → W ≠ ⊥ → V ≤ W)
    (hnc : ¬ V ≤ centralizer (K : Set G)) : V ≤ K := by
  let C := centralizer (K : Set G)
  let A := M ⊓ normalizer (K : Set G)
  have hLK : L ≤ normalizer (K : Set G) :=
    hinner.trans (sup_le K.le_normalizer (centralizer_le_normalizer _))
  have hLA : L ≤ A := le_inf hLM hLK
  obtain ⟨P,hPK,hPp,hAP,hVP⟩ := exists_prime_projection_of_central_product C K V A
    le_rfl hVp (hVL.trans (hinner.trans (by rw [sup_comm])))
    (inf_le_right.trans (normalizer_le_normalizer_centralizer K)) inf_le_right
    (inf_le_left.trans hMV)
  have hPR : P ≤ R := hK.stabilizer_saturation hsat P hPK hPp hAP
  have hPV : ⁅P,L⁆ ≤ V := (commutator_mono hPR le_rfl).trans hRV
  have hne : ⁅P,L⁆ ≠ ⊥ := by
    intro he
    apply hnc
    rw [hmoved]
    exact commutator_le_of_le_sup_centralizing V L C P (hVP.trans (by rw [sup_comm]))
      (hPK.trans (le_centralizer_iff.mp le_rfl))
      (commutator_eq_bot_iff_le_centralizer.mp he)
      (hLK.trans (normalizer_le_normalizer_centralizer K))
  exact (hirr ⁅P,L⁆ hPV (normalizer_commutator_ge_right P L) hne).trans
    ((commutator_mono hPK le_rfl).trans (le_normalizer_iff_commutator_le_left.mp hLK))

omit [Finite G] in
theorem perfect_projection_le_of_normalizes
    (P Q L : Subgroup G) [Group.IsPerfect P]
    (hc : P ≤ centralizer (Q : Set G))
    (hLP : L ≤ P ⊔ Q) (hPL : P ≤ L ⊔ Q)
    (hPN : P ≤ normalizer (L : Set G)) : P ≤ L := by
  have hLQ : L ≤ normalizer (Q : Set G) :=
    hLP.trans (sup_le (hc.trans (centralizer_le_normalizer _)) Q.le_normalizer)
  rw [←commutator_eq_self (H := P)]
  apply commutator_le.mpr
  intro p hp p' hp'
  have hprod : p ∈ (L : Set G)*(Q : Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right L Q hLQ]
    exact hPL hp
  obtain ⟨l,hl,q,hq,rfl⟩ := hprod
  have hqp : ⁅q,p'⁆=1 := (show Commute q p' from hc hp' q hq).commutator_eq
  rw [commutatorElement_mul_left_eq_conj_mul,hqp]
  simp only [mul_one,mul_inv_cancel,one_mul]
  exact (le_normalizer_iff_commutator_le_left.mp hPN) (commutator_mem_commutator hl hp')

omit [Finite G] in
/-- The original C-component is contained in the ordinary factor once its
moved module has been placed there. -/
theorem cComponent_le_of_inner_product_module
    (K L M V : Subgroup G) (hLM : L ≤ M)
    (hL : (L.subgroupOf M).IsCComponent)
    (hML : M ≤ normalizer (L : Set G))
    (hVL : V ≤ L) (hVK : V ≤ K) (hLV : L ≤ normalizer (V : Set G))
    (hNV : normalizer (V : Set G) ≤ M)
    (hinner : L ≤ K ⊔ centralizer (K : Set G))
    (hnc : ¬V ≤ centralizer (K : Set G)) : L ≤ K := by
  let := hL.perfect
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hLM).toMonoidHom) (subgroupOfEquivOfLe hLM).surjective
  have hLK : L ≤ normalizer (K : Set G) :=
    hinner.trans (sup_le K.le_normalizer (centralizer_le_normalizer _))
  obtain ⟨P,Q,hPK,hQC,hP,hQ,hLP,hPL,hPN⟩ :=
    exists_perfect_projections_of_central_product K (centralizer (K : Set G)) L
      (le_centralizer_iff.mp le_rfl) hinner
  let := hP
  have hPQ : P ≤ centralizer (Q : Set G) :=
    hPK.trans (le_centralizer_iff.mp hQC)
  have hPV : P ≤ normalizer (V : Set G) := hPL.trans
    (sup_le hLV ((hQC.trans (centralizer_le hVK)).trans (centralizer_le_normalizer _)))
  have hPM : P ≤ M := hPV.trans hNV
  have hPeL : P ≤ L := perfect_projection_le_of_normalizes P Q L hPQ hLP hPL (hPM.trans hML)
  have hnP : L ≤ normalizer (P : Set G) := hPN L hLK
    (hLK.trans (normalizer_le_normalizer_centralizer K)) L.le_normalizer
  have hne : P ≠ ⊥ := by
    intro he
    have hlq : L ≤ Q := by simpa only [he,bot_sup_eq] using hLP
    exact hnc (hVL.trans (hlq.trans hQC))
  have hsub : (P.subgroupOf M).IsSubnormal := by
    have hpL : (P.subgroupOf L).Normal := normal_subgroupOf_of_le_normalizer hnP
    have hpM : ((P.subgroupOf M).subgroupOf (L.subgroupOf M)).Normal := by
      apply normal_subgroupOf_of_le_normalizer
      intro l hl p
      exact hnP hl (p : G)
    exact Subgroup.IsSubnormal.trans (subgroupOf_mono M hPeL) hpM.isSubnormal hL.subnormal
  have hperfect : Group.IsPerfect (P.subgroupOf M) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hPM).symm.toMonoidHom) (subgroupOfEquivOfLe hPM).symm.surjective
  have hbot : P.subgroupOf M ≠ ⊥ := by
    intro he
    have he' := congrArg (map M.subtype) he
    exact hne (by simpa only [map_subgroupOf_eq_of_le hPM,Subgroup.map_bot] using he')
  have hm := hL.minimal (P.subgroupOf M) (subgroupOf_mono M hPeL) hbot hperfect hsub
  intro l hl
  exact hPK (hm (show (⟨l,hLM hl⟩ : M) ∈ L.subgroupOf M from hl))
end Theory.GroupTheory

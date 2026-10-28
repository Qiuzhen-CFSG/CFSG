module

public import Stellmacher.SectionFiveToSeven.Defs

/-!
# The orbit-closure contradiction in Stellmacher (6.1)

Under Hypothesis 2, suppose a nontrivial subgroup `W ≤ S` is normalized by
`L` and `U`, and the literal set products satisfy `P₁ = SL` and `P₂ = SU`.
Then the closure `X = ⟨W^S⟩` gives a contradiction to the trivial 2-core
of the actual subgroup `P₁ ⊔ P₂`.

To see that `P₁` normalizes `X`, conjugate a generator `sws⁻¹` by an
element `g` of `P₁`. Factor `gs = tl` with `t ∈ S` and `l ∈ L`.
The resulting element is `t(lwl⁻¹)t⁻¹`, another generator since `L`
normalizes `W`. Closure induction proves the claim; the same argument with
`U` handles `P₂`. Thus their join normalizes `X`. Meanwhile `W ≤ X ≤ S`,
so `X` is a nontrivial 2-group. Its intrinsic copy is normal in the join
and therefore lies in that join's 2-core, which Hypothesis 2 makes trivial.

This is the final paragraph of Stellmacher (6.1), Journal of Algebra 190
(1997), p.30, in `refs/latex/stellmacher-n-group.tex`. The factor-selection
and orbit-normalization arguments supply the explicit `L`, `U`, and `W`
inputs elsewhere. No equality of the generated join with the ambient group
is assumed, and no pending numbered theorem is used.
-/

open scoped Pointwise
namespace Stellmacher.SectionsFiveToSeven
universe u

private theorem le_left_of_set_product
    {G : Type*} [Group G] (P S L : Subgroup G)
    (hprod : (P : Set G) = (S : Set G) * (L : Set G)) : S ≤ P := by
  intro s hs
  change s ∈ (P : Set G)
  rw [hprod]
  exact Set.mem_mul.mpr ⟨s, hs, 1, L.one_mem, by simp⟩

private theorem product_le_normalizer_conjugateClosure
    {G : Type*} [Group G] (P S L W : Subgroup G)
    (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hprod : (P : Set G) = (S : Set G) * (L : Set G)) :
    P ≤ Subgroup.normalizer (conjugateClosure W S : Set G) := by
  have hSP : S ≤ P := le_left_of_set_product P S L hprod
  rw [Subgroup.le_normalizer_iff]
  intro g hg x hx
  change x ∈ conjugateClosure W S at hx
  rw [conjugateClosure] at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨s, w, rfl⟩ := hx
    have hgs : g * (s : G) ∈ P := P.mul_mem hg (hSP s.property)
    change g * (s : G) ∈ (P : Set G) at hgs
    rw [hprod] at hgs
    obtain ⟨t, ht, l, hl, htl⟩ := Set.mem_mul.mp hgs
    have hlw : l * (w : G) * l⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hLW hl) (w : G)).mp w.property
    apply Subgroup.subset_closure
    refine ⟨⟨t, ht⟩, ⟨l * (w : G) * l⁻¹, hlw⟩, ?_⟩
    change g * ((s : G) * (w : G) * (s : G)⁻¹) * g⁻¹ =
      t * (l * (w : G) * l⁻¹) * t⁻¹
    calc
      g * ((s : G) * (w : G) * (s : G)⁻¹) * g⁻¹ =
          (g * (s : G)) * (w : G) * (g * (s : G))⁻¹ := by group
      _ = (t * l) * (w : G) * (t * l)⁻¹ := by rw [← htl]
      _ = t * (l * (w : G) * l⁻¹) * t⁻¹ := by group
  | one => simp
  | mul x y hx hy ihx ihy =>
    convert Subgroup.mul_mem _ ihx ihy using 1 ; group
  | inv x hx ih =>
    convert Subgroup.inv_mem _ ih using 1 ; group

public theorem sixOne_orbitClosure_contradiction
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (h : HypothesisTwo H S0 S P1 P2)
    (L U W : Subgroup H)
    (hWS : W ≤ S) (hWne : W ≠ ⊥)
    (hLW : L ≤ Subgroup.normalizer (W : Set H))
    (hUW : U ≤ Subgroup.normalizer (W : Set H))
    (hP1 : (P1 : Set H) = (S : Set H) * (L : Set H))
    (hP2 : (P2 : Set H) = (S : Set H) * (U : Set H)) : False := by
  let X := conjugateClosure W S
  have hWX : W ≤ X := by
    intro w hw
    apply Subgroup.subset_closure
    exact ⟨1, ⟨w, hw⟩, by simp⟩
  have hXS : X ≤ S := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨s, w, rfl⟩
    exact S.mul_mem (S.mul_mem s.property (hWS w.property)) (S.inv_mem s.property)
  have hP1X : P1 ≤ Subgroup.normalizer (X : Set H) :=
    product_le_normalizer_conjugateClosure P1 S L W hLW hP1
  have hP2X : P2 ≤ Subgroup.normalizer (X : Set H) :=
    product_le_normalizer_conjugateClosure P2 S U W hUW hP2
  let J := P1 ⊔ P2
  have hXJ : X ≤ J :=
    hXS.trans ((le_left_of_set_product P1 S L hP1).trans le_sup_left)
  have hJN : J ≤ Subgroup.normalizer (X : Set H) := sup_le hP1X hP2X
  have hNormal : (X.subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXJ).mpr hJN
  have hXp : IsPGroup 2 X :=
    S0.isPGroup'.to_le (hXS.trans h.fiveOne.S_le_S0)
  have hXJp : IsPGroup 2 (X.subgroupOf J) :=
    hXp.comap_of_injective J.subtype J.subtype_injective
  have hXcore : X.subgroupOf J ≤ pCore 2 J := le_sSup ⟨hNormal, hXJp⟩
  have hXCoreIn : X ≤ twoCoreIn J := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hXJ]
    exact Subgroup.map_mono hXcore
  have hXbot : X ≤ ⊥ := hXCoreIn.trans (le_of_eq h.fiveOne.join_twoCore_eq_bot)
  exact hWne (le_bot_iff.mp (hWX.trans hXbot))

end Stellmacher.SectionsFiveToSeven

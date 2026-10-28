module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Basic
public import Theory.GroupTheory.PGroup.OmegaCoprimeNormalizer
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Transport

/-!
# The single-odd-prime normalizer argument

When Q = O_p(L/O₂(L)) is self-centralizing and abelian or of exponent p,
R = O₂(Ξ_p(L)T) fixes Ω₁(Q): lift omega elements to Ξ_p(L), and use the
commutator bound in its two-core. The coprime omega-action theorem then
shows that L normalizes R. We prove O₂(L) ≤ R using the Sylow hypothesis,
and work inside LT before transporting the result back to G.

Thus genuine uniqueness for LT gives C(G,R) ≤ M in the single-prime
case, once the quotient-structure witnesses from 1.2.1(4) are supplied.
Those witnesses are explicit; no equality Ω₁(Q) = Q is imposed in the
higher-exponent abelian case.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Proposition 1.3.8, printed p.513, single-odd-prime paragraph.
-/

open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers
variable {G : Type*} [Group G] [Finite G]

private theorem fixes_omega (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (L T : Subgroup G) [L.Normal] :
    ∀ r : radicalCore p L T, ∀ x ∈ omega (pCore p (XiQuotient L)) (p := p) 1,
      normalQuotientAction L (pCore 2 L) r (x : XiQuotient L) = x := by
  intro r x hx
  have hximage : (x : XiQuotient L) ∈ (xiPIn p L).map (QuotientGroup.mk' (pCore 2 L)) := by
    rw [xiPIn_map_quotient hp]
    exact mem_map.mpr ⟨x, hx, rfl⟩
  obtain ⟨z, hz, he⟩ := mem_map.mp hximage
  have hzX : (z : G) ∈ XiP p L := mem_map.mpr ⟨z, hz, rfl⟩
  have hcomm := commutator_radicalCore_le p (L := L) (T := T) le_normalizer_of_normal
  have hcore := pCoreIn_mono_of_normalizes (p := 2) (XiP_le p L)
    (L.le_normalizer.trans (normalizer_le_normalizer_XiP p L))
  have hm : ⁅(r : G), (z : G)⁆ ∈ L.pCoreIn 2 := by
    apply hcore
    apply hcomm
    rw [commutator_comm]
    exact commutator_mem_commutator r.property hzX
  let c : L := MulAut.conjNormal (r : G) z * z⁻¹
  have hc : c ∈ pCore 2 L := by
    obtain ⟨a, ha, heq⟩ := mem_map.mp hm
    have hac : a = c := Subtype.ext heq
    exact hac ▸ ha
  have hq := (QuotientGroup.eq_one_iff c).mpr hc
  change QuotientGroup.mk' (pCore 2 L) c = 1 at hq
  dsimp only [c] at hq
  rw [map_mul, map_inv] at hq
  rw [← he, normalQuotientAction_apply_mk]
  exact mul_inv_eq_one.mp hq

/-- The single-prime branch in a local ambient group where L is normal.
The omega fixation and O₂(L) containment are derived, not hypotheses. -/
public theorem L_normalizes_radicalCore_of_singlePrime (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (L T : Subgroup G) [L.Normal] (hSyl : IsSylowIn 2 T (L ⊔ T))
    (hshape : IsMulCommutative (pCore p (XiQuotient L)) ∨
      ∀ x : pCore p (XiQuotient L), x ^ p = 1)
    (hcentral : centralizer (pCore p (XiQuotient L) : Set (XiQuotient L)) ≤
      pCore p (XiQuotient L)) :
    L ≤ normalizer (radicalCore p L T : Set G) := by
  exact le_normalizer_of_twoGroup_fixes_omega L (radicalCore p L T) hp
    (radicalCore_isTwoGroup p L T)
    (twoCore_le_radicalCore p hSyl le_normalizer_of_normal)
    hshape hcentral (fixes_omega p hp L T)

private theorem core_conditions_equiv {A B : Type*} [Group A] [Group B]
    (p : ℕ) (e : A ≃* B)
    (hshape : IsMulCommutative (pCore p A) ∨ ∀ x : pCore p A, x ^ p = 1)
    (hcentral : centralizer (pCore p A : Set A) ≤ pCore p A) :
    (IsMulCommutative (pCore p B) ∨ ∀ x : pCore p B, x ^ p = 1) ∧
      centralizer (pCore p B : Set B) ≤ pCore p B := by
  let ep : pCore p A ≃* pCore p B :=
    ((pCore p A).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr (pCore_map_iso p e))
  constructor
  · rcases hshape with habelian | hexp
    · let := habelian
      left
      apply IsMulCommutative.of_comm
      intro x y
      apply ep.symm.injective
      simp only [map_mul, mul_comm]
    · right
      intro x
      apply ep.symm.injective
      simpa only [map_pow, map_one] using hexp (ep.symm x)
  · intro x hx
    have hb : e.symm x ∈ centralizer (pCore p A : Set A) := by
      apply mem_centralizer_iff.mpr
      intro a ha
      apply e.injective
      simp only [map_mul, e.apply_symm_apply]
      apply mem_centralizer_iff.mp hx
      rw [← pCore_map_iso p e]
      exact mem_map.mpr ⟨a, ha, rfl⟩
    rw [← pCore_map_iso p e]
    exact mem_map.mpr ⟨e.symm x, hcentral hb, e.apply_symm_apply x⟩

/-- The single-prime normality argument in G: L need only be normal in LT.
The two quotient conditions are the structural witnesses supplied by 1.2.1(4). -/
public theorem L_normalizes_radicalCore_of_singlePrime_relative
    (p : ℕ) [Fact p.Prime] (hp : Odd p) (L T : Subgroup G)
    (hSyl : IsSylowIn 2 T (L ⊔ T)) (hT : T ≤ normalizer (L : Set G))
    (hshape : IsMulCommutative (pCore p (XiQuotient L)) ∨
      ∀ x : pCore p (XiQuotient L), x ^ p = 1)
    (hcentral : centralizer (pCore p (XiQuotient L) : Set (XiQuotient L)) ≤
      pCore p (XiQuotient L)) :
    L ≤ normalizer (radicalCore p L T : Set G) := by
  let H := L ⊔ T
  let L₀ := L.subgroupOf H
  let T₀ := T.subgroupOf H
  let : L₀.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hT)
  have hLm : L₀.map H.subtype = L := map_subgroupOf_eq_of_le le_sup_left
  have hTm : T₀.map H.subtype = T := map_subgroupOf_eq_of_le le_sup_right
  have hSm : IsSylowIn 2 T₀ (L₀ ⊔ T₀) := by
    apply (IsSylowIn.map_iff H.subtype H.subtype_injective).mp
    rwa [Subgroup.map_sup, hLm, hTm]
  let e : L₀ ≃* L := subgroupOfEquivOfLe (show L ≤ H from le_sup_left)
  let eq : XiQuotient L ≃* XiQuotient L₀ :=
    QuotientGroup.congr _ _ e.symm (pCore_map_iso 2 e.symm)
  obtain ⟨hs, hc⟩ := core_conditions_equiv p eq hshape hcentral
  have hn := L_normalizes_radicalCore_of_singlePrime p hp L₀ T₀ hSm hs hc
  have hRm : (radicalCore p L₀ T₀).map H.subtype = radicalCore p L T := by
    rw [radicalCore, map_pCoreIn_of_injective 2 _ _ H.subtype_injective,
      Subgroup.map_sup, XiP_map_injective p L₀ H.subtype H.subtype_injective, hLm, hTm]
    rfl
  have hh := (map_mono (f := H.subtype) hn).trans (le_normalizer_map H.subtype)
  simpa only [hLm, hRm] using hh

/-- The completed single-prime reduction to characteristic-normalizer control.
Only the earlier uniqueness and quotient-structure witnesses remain explicit. -/
public theorem characteristicNormalizerClosure_le_of_singlePrime
    (p : ℕ) [Fact p.Prime] (hp : Odd p) (L T M : Subgroup G)
    (hSyl : IsSylowIn 2 T (L ⊔ T)) (hT : T ≤ normalizer (L : Set G))
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ T ≤ N → N = M)
    (hshape : IsMulCommutative (pCore p (XiQuotient L)) ∨
      ∀ x : pCore p (XiQuotient L), x ^ p = 1)
    (hcentral : centralizer (pCore p (XiQuotient L) : Set (XiQuotient L)) ≤
      pCore p (XiQuotient L)) :
    characteristicNormalizerClosure (radicalCore p L T) ≤ M :=
  characteristicNormalizerClosure_le_of_L_normalizes p hunique
    (L_normalizes_radicalCore_of_singlePrime_relative p hp L T hSyl hT hshape hcentral)

end CFSG.Quasithin.Chapter1.RadicalNormalizers

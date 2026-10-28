module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import Theory.GroupTheory.PResidual.PrimeSection

/-!
# The marked outside cubic in H/O₂(H)

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
13.8.20, printed p.955 (PDF p.972); Notation 13.2.1 and Lemma 13.2.2(3),
printed p.877 (PDF p.894).

The source writes L₁ = L₀L₁,+, where both marked subgroups are two-perfect,
have quotient of order three by their own two-cores, and are normalized by T.
If L₁ is outside K, at least one marked subgroup is outside K. Two-perfectness
keeps that subgroup outside K O₂(H). Apply the prime-section construction
inside H, then pass its cubic and its genuine product equality through the
actual quotient map H → H/O₂(H). The two-group kernel preserves cubic order.

All normality hypotheses are relative to their stated overgroups. In
particular neither marked two-core is assumed normal in H. These conditional
construction lemmas use no unitary model or appendix recognition result;
the owner of 13.8.20 supplies the source hypotheses and the remaining
unitary contradiction.
-/

public section
open scoped Pointwise

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.Unitary.MarkedCubic
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A single marked two-perfect section outside K supplies an outside cubic
in the actual H/O₂(H), permuting with the actual image of the Sylow subgroup.
Two-perfectness excludes containment in K O₂(H) before choosing the cubic. -/
theorem exists_of_marked (H K L T : Subgroup G)
    (hKH : K ≤ H) (hKN : (K.subgroupOf H).Normal) (hLH : L ≤ H)
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (hL : IsPPerfect 2 L) (hc : Nat.card (L ⧸ pCore 2 L) = 3)
    (hn : T ≤ normalizer (L : Set G)) (hout : ¬ L ≤ K) :
    ∃ x : Source.Hstar H, x ∈ Source.starImage H L ∧ orderOf x = 3 ∧
      x ∉ Source.starImage H K ∧
      (↑(zpowers x ⊔ Source.starImage H T) : Set (Source.Hstar H)) =
        (zpowers x : Set (Source.Hstar H)) * Source.starImage H T := by
  let K' := K.subgroupOf H
  let L' := L.subgroupOf H
  let : K'.Normal := hKN
  let e : L' ≃* L := subgroupOfEquivOfLe hLH
  have hp : IsPPerfect 2 L' :=
    hL.of_surjective e.symm.toMonoidHom e.symm.surjective
  have hc' : Nat.card (L' ⧸ pCore 2 L') = 3 :=
    (Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv).trans hc
  have hn' : (S : Subgroup H) ≤ normalizer (L' : Set H) := by
    rw [← subgroupOf_normalizer_eq hLH]
    intro s hs
    exact hn (hS ▸ mem_map.mpr ⟨s, hs, rfl⟩)
  have hout' : ¬ L' ≤ K' := by
    intro h
    apply hout
    have hm := map_mono (f := H.subtype) h
    simpa only [L', K', map_subgroupOf_eq_of_le hLH,
      map_subgroupOf_eq_of_le hKH] using hm
  have houtCore : ¬ L' ≤ K' ⊔ pCore 2 H := by
    intro h
    exact hout' (le_normal_of_isPPerfect_of_le_sup_pGroup L' K' (pCore 2 H) hp pCore_isPGroup h)
  obtain ⟨x, hxL, hx, hxK, hprod⟩ :=
    exists_outside_prime_order_permuting_sylow (by decide : Nat.Coprime 2 3)
      (K' ⊔ pCore 2 H) L' S hp hc' hn' houtCore
  let q := QuotientGroup.mk' (pCore 2 H)
  have hker : IsPGroup 2 q.ker := by
    dsimp [q]
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hxq : orderOf (q x) = 3 :=
    (q.orderOf_map_eq_of_coprime_of_isPGroup_ker hker x (hx ▸ by decide)).trans hx
  have hTH : T ≤ H := hS ▸ map_subtype_le (S : Subgroup H)
  have hST : (S : Subgroup H).map q = Source.starImage H T := by
    unfold Source.starImage
    congr 1
    apply map_injective H.subtype_injective
    rw [hS, map_subgroupOf_eq_of_le hTH]
  refine ⟨q x, mem_map.mpr ⟨x, hxL, rfl⟩, hxq, ?_, ?_⟩
  · intro h
    have hm : x ∈ (K'.map q).comap q := h
    have hq : q.ker = pCore 2 H := QuotientGroup.ker_mk' _
    rw [comap_map_eq, hq] at hm
    exact hxK hm
  · have hm : (↑((zpowers x ⊔ (S : Subgroup H)).map q) : Set (Source.Hstar H)) =
        (↑((zpowers x).map q) : Set (Source.Hstar H)) * ↑((S : Subgroup H).map q) := by
      simpa only [coe_map, Set.image_mul, Sylow.coe_coe] using
        congrArg (fun A : Set H => q '' A) hprod
    rwa [Subgroup.map_sup, MonoidHom.map_zpowers, hST] at hm

/-- The marked outside-cubic construction used in the external-L₁ branch
of 13.8.20. One of L₀ and L₁,+ is outside K; its prime section supplies the
cubic without assuming a T-invariant complement or a product equality. -/
theorem exists_of_two_marked (H K L₁ L₀ Lplus T : Subgroup G)
    (hKH : K ≤ H) (hKN : (K.subgroupOf H).Normal) (hL₁H : L₁ ≤ H)
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (hgen : L₁ = L₀ ⊔ Lplus)
    (hL₀ : IsPPerfect 2 L₀) (hLplus : IsPPerfect 2 Lplus)
    (hc₀ : Nat.card (L₀ ⧸ pCore 2 L₀) = 3)
    (hcplus : Nat.card (Lplus ⧸ pCore 2 Lplus) = 3)
    (hn₀ : T ≤ normalizer (L₀ : Set G)) (hnplus : T ≤ normalizer (Lplus : Set G))
    (hout : ¬ L₁ ≤ K) :
    ∃ x : Source.Hstar H, x ∈ Source.starImage H L₁ ∧ orderOf x = 3 ∧
      x ∉ Source.starImage H K ∧
      (↑(zpowers x ⊔ Source.starImage H T) : Set (Source.Hstar H)) =
        (zpowers x : Set (Source.Hstar H)) * Source.starImage H T := by
  classical
  have h₀ : L₀ ≤ L₁ := hgen ▸ le_sup_left
  have hplus : Lplus ≤ L₁ := hgen ▸ le_sup_right
  obtain ⟨L, hLL, hp, hc, hn, ho⟩ : ∃ L : Subgroup G,
      L ≤ L₁ ∧ IsPPerfect 2 L ∧ Nat.card (L ⧸ pCore 2 L) = 3 ∧
        T ≤ normalizer (L : Set G) ∧ ¬ L ≤ K := by
    by_cases h : L₀ ≤ K
    · refine ⟨Lplus, hplus, hLplus, hcplus, hnplus, ?_⟩
      intro h'
      exact hout (hgen ▸ sup_le h h')
    · exact ⟨L₀, h₀, hL₀, hc₀, hn₀, h⟩
  obtain ⟨x, hxL, hx, hxK, hprod⟩ :=
    exists_of_marked H K L T hKH hKN (hLL.trans hL₁H) S hS hp hc hn ho
  exact ⟨x, map_mono (subgroupOf_mono H hLL) hxL, hx, hxK, hprod⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.Unitary.MarkedCubic

end

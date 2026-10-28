module

public import Theory.SpecificGroups.PSL2.QuinticQuadraticAllOddFusion
public import Theory.GroupTheory.SylowNormalizedSupIntersection
public import Theory.GroupTheory.PCoreRestriction

/-!
# Restricting quadratic fusion inside a larger automorphism group

A whole elementary subgroup contained in N⟨a⟩ is fused inside that actual
subgroup. Its intersection with the supplied Sylow is a full Sylow subgroup,
since a already lies in that Sylow and N is normal. The returning conjugate
escapes the original larger quintic core by restriction of a normal two-core.
No normality or index assumption on N⟨a⟩ in the ambient group is needed.

This is the overgroup restriction in Aschbacher--Smith 6.1.4, printed p.666.
-/

public section
open Subgroup GorensteinWalter Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.PSL2

/-- Whole fusion in the marked field extension returns to the original
ambient Sylow and escapes the original ambient quintic core. -/
theorem quintic_quadratic_restricted_whole_fusion
    {G : Type*} [Group G] [Finite G]
    {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p ^ 2)
    (N : Subgroup G) [N.Normal] (e : N ≃* PSL(2,F))
    (hC : centralizer (N : Set G) = ⊥)
    (T : Sylow 2 G) (X : Subgroup G) (hXN : X ≤ N) (hfive : Nat.card X = 5)
    (hTX : (T : Subgroup G) ≤ normalizer X)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hAne : A ≠ ⊥)
    (a : G) (haA : a ∈ A) (haT : a ∈ (T : Subgroup G))
    (hAH : A ≤ N ⊔ zpowers a)
    (x : PGammaL2 F) (hx : orderOf x = 2) (hf : x.right ≠ 1)
    (hmark : MulAut.congr e (MulAut.conjNormal a) =
      pGammaL2ToMulAutPSL2 F
        ⟨p, 2, Fact.out, ho, by decide, hF⟩
        (by have hp := (Fact.out : p.Prime).two_le; rw [hF]; nlinarith) x) :
    ∃ g ∈ N, A.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) ∧
      ¬ A.map (MulAut.conj g).toMonoidHom ≤ (X ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let H := N ⊔ zpowers a
  have hNH : N ≤ H := le_sup_left
  have hXH : X ≤ H := hXN.trans hNH
  let N' := N.subgroupOf H
  let X' := X.subgroupOf H
  let A' := A.subgroupOf H
  let a' : H := ⟨a, hAH haA⟩
  let e' : N' ≃* PSL(2,F) := (subgroupOfEquivOfLe hNH).trans e
  obtain ⟨P, hP⟩ := T.exists_subgroupOf_sup_of_normalized N (zpowers a)
    (zpowers_le.mpr haT) (by rw [N.normalizer_eq_top]; exact le_top)
    (T.exists_subgroupOf_eq_of_normal N)
  have hPT : (P : Subgroup H).map H.subtype ≤ (T : Subgroup G) := by
    rw [hP, subgroupOf_map_subtype]
    exact inf_le_left
  have hC' : centralizer (N' : Set H) = ⊥ := by
    apply bot_unique
    intro c hc
    apply Subtype.ext
    apply mem_bot.mp
    rw [← hC]
    intro n hn
    exact congrArg Subtype.val ((mem_centralizer_iff.mp hc) ⟨n, hNH hn⟩ hn)
  have hX'N' : X' ≤ N' := comap_mono hXN
  have hfive' : Nat.card X' = 5 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hXH).toEquiv]
    exact hfive
  have hPX : (P : Subgroup H) ≤ normalizer X' := by
    intro v hv
    exact (le_normalizer_comap H.subtype) (hTX (hPT (mem_map_of_mem _ hv)))
  have hA' : IsElementaryAbelian 2 A' := by
    let : IsElementaryAbelian 2 A := hA
    exact IsElementaryAbelian.subgroupOf hAH
  have hAne' : A' ≠ ⊥ := by
    intro hh
    apply hAne
    have hm := congrArg (map H.subtype) hh
    rwa [map_subgroupOf_eq_of_le hAH, Subgroup.map_bot] at hm
  have hgen : N' ⊔ zpowers a' = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hNH, MonoidHom.map_zpowers,
      ← MonoidHom.range_eq_map, H.range_subtype]
    rfl
  have hmark' : MulAut.congr e' (MulAut.conjNormal a') =
      pGammaL2ToMulAutPSL2 F
        ⟨p, 2, Fact.out, ho, by decide, hF⟩
        (by have hp := (Fact.out : p.Prime).two_le; rw [hF]; nlinarith) x := by
    rw [← hmark]
    ext y
    rfl
  obtain ⟨g, hg, hgP, hgS⟩ := quintic_quadratic_all_odd_whole_fusion ho hF N' e' hC'
    P X' hX'N' hfive' hPX A' hA' hAne' a' haA hgen x hx hf hmark'
  let V := A.map (MulAut.conj (g : G)).toMonoidHom
  let D := X ⊔ (P : Subgroup H).map H.subtype
  have hmap : (A'.map (MulAut.conj g).toMonoidHom).map H.subtype = V := by
    change (A'.map (MulAut.conj g).toMonoidHom).map H.subtype =
      A.map (MulAut.conj (g : G)).toMonoidHom
    rw [← map_subgroupOf_eq_of_le hAH, map_map, map_map]
    congr 1
  have hVD : V ≤ D := by
    have hh := map_mono (f := H.subtype) hgP
    rw [hmap] at hh
    exact hh.trans le_sup_right
  have hD : D ≤ X ⊔ (T : Subgroup G) := sup_le_sup_left hPT X
  have hVcore : ¬ V ≤ D.pCoreIn 2 := by
    intro hh
    apply hgS
    apply (map_le_map_iff_of_injective (f := H.subtype) H.subtype_injective).mp
    rw [hmap, ← AmalgamLocalCores.pCoreIn_map_of_injective 2 _ H.subtype_injective,
      Subgroup.map_sup, map_subgroupOf_eq_of_le hXH]
    exact hh
  refine ⟨g, hg, ?_, not_le_pCoreIn_of_subgroup 2 hVD hD hVcore⟩
  have hh := map_mono (f := H.subtype) hgP
  rw [hmap] at hh
  exact hh.trans hPT

end Theory.PSL2

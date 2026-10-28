module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.Branches
public import Theory.GroupTheory.CComponent.LayerTransport

/-!
# Normal generation and the exchanged component residual

The exchanged complement factorization meets the selected component nontrivially
modulo its two-core. Simplicity of that quotient, then two-perfectness, makes
the H-normal closure of X contain the component. It therefore contains its
entire H-orbit. The reverse inclusion follows from X lying in the U-orbit.
An index-two component normalizer identifies both orbits with the actual pair
of conjugate components.

The earlier 1.2.2(a) parameter is applied only after verifying its two-element
H-orbit and divisibility in the actual image in H/O₂(H). Relative normality
in the component product follows from the C-component layer. Ambient normality
of the individual exchanged component is never asserted.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
1.2.2(a), printed p.504, and 15.4.20, printed p.1164.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction
universe u
variable {G : Type u} [Group G] [Finite G]
open Chapter1

omit [Finite G] in
/-- Nontrivial intersection with the simple two-core quotient forces a normal
subgroup of the overgroup to contain the entire two-perfect component. -/
theorem component_le_normal_of_intersection {L N H A : Subgroup G}
    (hLH : L ≤ H) (hNH : N ≤ H) (hN : (N.subgroupOf H).Normal)
    (hA : A ≤ N ⊓ L) (hne : ¬ A ≤ L.pCoreIn 2)
    (hp : IsPPerfect 2 L) (hs : IsSimpleGroup (L ⧸ pCore 2 L)) : L ≤ N := by
  let _ := hs
  have hHN : H ≤ normalizer N := (normal_subgroupOf_iff_le_normalizer hNH).mp hN
  let D := N.subgroupOf L
  let _ : D.Normal := normal_subgroupOf_of_le_normalizer (hLH.trans hHN)
  let q := QuotientGroup.mk' (pCore 2 L)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hd : (D.map q).Normal := (inferInstance : D.Normal).map q hq
  have ht : D.map q = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (D.map q) hd with hb | ht
    · exfalso
      apply hne
      have hD : D ≤ pCore 2 L := by
        simpa only [Subgroup.map_eq_bot_iff, q, QuotientGroup.ker_mk'] using hb
      intro a ha
      exact ⟨⟨a, (hA ha).2⟩, hD (hA ha).1, rfl⟩
    · exact ht
  have hgen : D ⊔ pCore 2 L = ⊤ := by
    have he := congrArg (Subgroup.comap q) ht
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using he
  have hD : D = ⊤ := hp D inferInstance
    (isPGroup_quotient_of_sup_eq_top D (pCore 2 L) pCore_isPGroup hgen)
  intro l hl
  exact (show (⟨l, hl⟩ : L) ∈ D from hD ▸ mem_top _)

/-- The selected factor in the exchanged complement survives modulo the component core. -/
theorem swapped_intersection_not_le_core {U X P H L : Subgroup G}
    (h : XiEmbedding.LocalInput 3 U X P H) (hs : XiEmbedding.SwappedFactors U P L) :
    ¬ P ⊓ L ≤ L.pCoreIn 2 := by
  have hAb : P ⊓ L ≠ ⊥ := by
    intro hb
    obtain ⟨_, t, _, _, hgen, _, _⟩ := hs
    have hPb : P = ⊥ := by
      simpa only [hb, Subgroup.conjBy, Subgroup.map_bot, bot_sup_eq] using hgen
    have hc := h.complement_not_cyclic
    rw [hPb] at hc
    exact hc inferInstance
  have hd : Disjoint (L.pCoreIn 2) P :=
    (isPGroup_pCoreIn 2 L).disjoint_of_coprime h.odd_complement.isPGroup (by decide)
  intro hle
  exact hAb (le_bot_iff.mp (fun a ha => hd.le_bot ⟨hle ha, ha.1⟩))

omit [Finite G] in
/-- An index-two normalizer gives the full orbit from any moving element. -/
theorem componentOrbit_eq_pair_of_index_two {L A H : Subgroup G}
    (hAH : A ≤ H) (hLH : L ≤ H)
    (hi : (normalizer (L.subgroupOf H : Set H)).index = 2)
    {t : G} (ht : t ∈ A) (hm : t ∉ normalizer L) :
    componentOrbit L A = L ⊔ L.conjBy t := by
  let tH : H := ⟨t, hAH ht⟩
  have htH : tH ∉ normalizer (L.subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq hLH]
    exact hm
  have hconj (s : A) : L.conjBy (s : G) = L ∨ L.conjBy (s : G) = L.conjBy t := by
    by_cases hs : (s : G) ∈ normalizer L
    · exact Or.inl (mem_normalizer_iff_map_conj_eq.mp hs)
    · have hsH : (⟨s, hAH s.property⟩ : H) ∉ normalizer (L.subgroupOf H : Set H) := by
        rw [← subgroupOf_normalizer_eq hLH]
        exact hs
      have he : tH⁻¹ * (⟨s, hAH s.property⟩ : H) ∈ normalizer (L.subgroupOf H : Set H) :=
        (mul_mem_iff_of_index_two hi).mpr (by simp [htH, hsH])
      rw [← subgroupOf_normalizer_eq hLH] at he
      have heq : L.conjBy (t⁻¹ * (s : G)) = L := mem_normalizer_iff_map_conj_eq.mp he
      have hh := congrArg (fun B : Subgroup G => B.conjBy t) heq
      rw [conjBy_mul, conjBy_inv'] at hh
      exact Or.inr hh
  apply le_antisymm
  · apply iSup_le
    intro s
    change L.conjBy (s : G) ≤ L ⊔ L.conjBy t
    rcases hconj s with he | he <;> rw [he]
    · exact le_sup_left
    · exact le_sup_right
  · exact sup_le (le_componentOrbit L A) (le_iSup (fun s : A => L.conjBy s) ⟨t, ht⟩)

/-- Relative component normality in its complete orbit follows from the
C-component layer, without imposing ambient normality of the component. -/
theorem componentOrbit_le_normalizer {H L : Subgroup G}
    (hL : L ∈ cComponentsIn H) : componentOrbit L H ≤ normalizer L := by
  let C := (cComponentLayer H).map H.subtype
  let _ := cComponentLayer_characteristic (G := H)
  have hCn : (C.subgroupOf H).Normal := by
    change (((cComponentLayer H).map H.subtype).comap H.subtype).Normal
    rw [comap_map_eq_self_of_injective H.subtype_injective]
    infer_instance
  have hLC : L ≤ C := by
    intro l hl
    exact ⟨⟨l, hL.1 hl⟩, le_cComponentLayer hL.2 hl, rfl⟩
  have hHC : H ≤ normalizer C :=
    (normal_subgroupOf_iff_le_normalizer (map_subtype_le _)).mp hCn
  apply (iSup_conjugates_le_of_le_normalizer L H C hLC hHC).trans
  rintro x ⟨y, hy, rfl⟩
  have hn := cComponentLayer_le_normalizer hL.2 hy
  rwa [← subgroupOf_normalizer_eq hL.1] at hn

/-- The actual H-normal closure of X is the complete component orbit in the
exchanged case. Nontriviality is supplied by the complement factorization. -/
theorem swapped_normalClosure_eq_orbit {U X P H L : Subgroup G}
    (h : XiEmbedding.LocalInput 3 U X P H) (hL : L ∈ cComponentsIn H)
    (hq : IsSimpleGroup (XiQuotient L)) (hX : X ≤ componentOrbit L U)
    (hs : XiEmbedding.SwappedFactors U P L)
    (hi : (normalizer (L.subgroupOf H : Set H)).index = 2) :
    normalClosureIn X H = componentOrbit L H ∧
      componentOrbit L H = componentOrbit L U := by
  have hUH : U ≤ H := le_sup_right.trans h.overgroup
  obtain ⟨t, ht, hm, _⟩ := hs.2
  have heH := componentOrbit_eq_pair_of_index_two le_rfl hL.1 hi (hUH ht.1) hm
  have heU := componentOrbit_eq_pair_of_index_two hUH hL.1 hi ht.1 hm
  have he : componentOrbit L H = componentOrbit L U := heH.trans heU.symm
  have hKH : componentOrbit L H ≤ H :=
    (componentOrbit_le_sup L H).trans (sup_le hL.1 le_rfl)
  have hKn : ((componentOrbit L H).subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hKH).mpr (le_normalizer_componentOrbit L H)
  let N := normalClosureIn X H
  have hNH : N ≤ H := normalClosureIn_le_overgroup X H
  have hXN : X ≤ N := le_normalClosureIn (le_sup_left.trans h.overgroup)
  have hLN : L ≤ N := component_le_normal_of_intersection hL.1 hNH
    (normalClosureIn_normal X H)
    (show P ⊓ L ≤ N ⊓ L from inf_le_inf
      ((le_sup_right.trans h.complement.le).trans hXN) le_rfl)
    (swapped_intersection_not_le_core h hs) (cComponent_twoPerfect hL) hq
  have hHN : H ≤ normalizer N :=
    (normal_subgroupOf_iff_le_normalizer hNH).mp (normalClosureIn_normal X H)
  exact ⟨le_antisymm (normalClosureIn_le (hX.trans he.ge) hKH hKn)
    (iSup_conjugates_le_of_le_normalizer L H N hLN hHN), he⟩

/-- Exact 1.2.2(a) applies to the verified two-element H-orbit and actual
quotient-image divisibility, and identifies the X-normal closure with O^{3′}(H). -/
theorem swapped_normalClosure_eq_residual {κ : GroupClass.{u}}
    (hG : IsSimpleQTKE κ G) (residual : TwoOrbitResidualTheorem κ)
    {U X P H L : Subgroup G} (hH : H ∈ Chapter1.H G)
    (h : XiEmbedding.LocalInput 3 U X P H) (hL : L ∈ cComponentsIn H)
    (hq : IsSimpleGroup (XiQuotient L)) (hX : X ≤ componentOrbit L U)
    (hs : XiEmbedding.SwappedFactors U P L)
    (hi : (normalizer (L.subgroupOf H : Set H)).index = 2) :
    normalClosureIn X H = (primeToResidual 3 H).map H.subtype := by
  have horbit : (Set.range fun x : H =>
      (L.subgroupOf H).map (MulAut.conj x).toMonoidHom).ncard = 2 := by
    rwa [ncard_conjugates_eq_index_normalizer]
  have hr := residual G hG H hH L hL 3 (by decide) (by decide) horbit
    (swapped_three_dvd_quotient_image h hs)
  exact (swapped_normalClosure_eq_orbit h hL hq hX hs hi).1.trans hr.symm

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction

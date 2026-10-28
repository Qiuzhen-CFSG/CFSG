module

public import Theory.GroupTheory.CComponent.RadicalFreeProduct
public import Mathlib.GroupTheory.IndexNormal

/-!
# Index two from a component normalizer and an ambient interchange

Let M be a maximal proper subgroup of a finite group. Suppose M has trivial
solvable radical and has distinct commuting C-components L and K. If the
normalizer of L inside M is contained in L ⊔ K, multiplication coordinates and
the trivial center of L give C_M(L) ≤ K. Distinct components commute, so the
only components are L and K. Conjugation therefore makes their join normal in M.

If the ambient normalizer of that join is proper and contains an element
interchanging the two factors, maximality puts that element in M. The two
possible images of L then give index two for its normalizer, which is L ⊔ K.
No ambient simplicity, component count, relative normality, or splitting is
assumed.

This is a finite-group reduction for the Suzuki-wreath case of Malle,
J. Algebra 139 (1991), 52--69, DOI 10.1016/0021-8693(91)90283-E. Its component
calculus is Aschbacher--Smith A.3.3(5)--(6), printed pp.42--43 of
`refs/quasithin.pdf`. The geometric normalizer and interchange hypotheses
remain explicit.
-/

public section

namespace Subgroup

private theorem centralizer_le_of_normalizer_le_join
    {H : Type*} [Group H] [Finite H] {L K : Subgroup H}
    (hR : solvableRadical H = ⊥) (hL : L.IsCComponent) (hc : ⁅L, K⁆ = ⊥)
    (hN : normalizer (L : Set H) ≤ L ⊔ K) : centralizer (L : Set H) ≤ K := by
  have hK : K ≤ centralizer (L : Set H) :=
    commutator_eq_bot_iff_le_centralizer.mp (by rwa [commutator_comm])
  have hd : Disjoint L (centralizer (L : Set H)) :=
    hL.disjoint_of_commutator_eq_bot_of_solvableRadical_eq_bot hR
      (by rw [commutator_comm]; exact commutator_eq_bot_iff_le_centralizer.mpr le_rfl)
  obtain ⟨e, he⟩ := hL.exists_mulEquiv_prod_sup_of_solvableRadical_eq_bot hR hc
  intro x hx
  have hxJ := hN (centralizer_le_normalizer (L : Set H) hx)
  obtain ⟨⟨l, k⟩, h⟩ := e.surjective ⟨x, hxJ⟩
  have hxmul : (l : H) * (k : H) = x := (he l k).symm.trans (congrArg Subtype.val h)
  have hlC : (l : H) ∈ centralizer (L : Set H) := by
    have ht := (centralizer (L : Set H)).mul_mem hx
      ((centralizer (L : Set H)).inv_mem (hK k.property))
    rwa [← hxmul, mul_inv_cancel_right] at ht
  have hl : (l : H) = 1 := Subgroup.disjoint_def.mp hd l.property hlC
  rw [← hxmul, hl, one_mul]
  exact k.property

private theorem all_components_eq_pair
    {H : Type*} [Group H] [Finite H] {L K : Subgroup H}
    (hR : solvableRadical H = ⊥) (hL : L.IsCComponent) (hK : K.IsCComponent)
    (hC : centralizer (L : Set H) ≤ K) {D : Subgroup H} (hD : D.IsCComponent) :
    D = L ∨ D = K := by
  by_cases h : D = L
  · exact Or.inl h
  · exact Or.inr (hD.eq_of_le hK
      ((commutator_eq_bot_iff_le_centralizer.mp
        (hD.commutator_eq_bot_of_ne_of_solvableRadical_eq_bot hR hL h)).trans hC))

private theorem pair_join_normal
    {H : Type*} [Group H] [Finite H] {L K : Subgroup H}
    (hR : solvableRadical H = ⊥) (hL : L.IsCComponent) (hK : K.IsCComponent)
    (hne : L ≠ K) (hC : centralizer (L : Set H) ≤ K) :
    (L ⊔ K).Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  intro g _
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hLg := all_components_eq_pair hR hL hK hC (hL.map_equiv (MulAut.conj g))
  have hKg := all_components_eq_pair hR hL hK hC (hK.map_equiv (MulAut.conj g))
  have hg : L.map (MulAut.conj g).toMonoidHom ≠ K.map (MulAut.conj g).toMonoidHom :=
    fun h => hne ((map_injective (MulAut.conj g).injective) h)
  change (L ⊔ K).map (MulAut.conj g).toMonoidHom = L ⊔ K
  rw [Subgroup.map_sup]
  rcases hLg with hLg | hLg <;> rcases hKg with hKg | hKg
  · exact (hg (hLg.trans hKg.symm)).elim
  · rw [hLg, hKg]
  · rw [hLg, hKg, sup_comm]
  · exact (hg (hLg.trans hKg.symm)).elim

private theorem index_two_of_component_swap
    {H : Type*} [Group H] [Finite H] {L K : Subgroup H}
    (hR : solvableRadical H = ⊥) (hL : L.IsCComponent) (hK : K.IsCComponent)
    (hne : L ≠ K) (hc : ⁅L, K⁆ = ⊥) (hC : centralizer (L : Set H) ≤ K)
    (hN : normalizer (L : Set H) ≤ L ⊔ K)
    (s : H) (hsL : L.map (MulAut.conj s).toMonoidHom = K)
    (hsK : K.map (MulAut.conj s).toMonoidHom = L) : (L ⊔ K).index = 2 := by
  have hnormalizer : normalizer (L : Set H) = L ⊔ K := by
    apply le_antisymm hN
    apply sup_le L.le_normalizer
    exact ((commutator_eq_bot_iff_le_centralizer.mp (by rwa [commutator_comm])).trans
      (centralizer_le_normalizer (L : Set H)))
  rw [← hnormalizer]
  apply index_eq_two_iff_exists_notMem_and'.mpr
  refine ⟨s, fun hs => hne ((mem_normalizer_iff_map_conj_eq.mp hs).symm.trans hsL), ?_⟩
  intro g
  rcases all_components_eq_pair hR hL hK hC (hL.map_equiv (MulAut.conj g)) with hg | hg
  · exact Or.inr (mem_normalizer_iff_map_conj_eq.mpr hg)
  · apply Or.inl
    apply mem_normalizer_iff_map_conj_eq.mpr
    have he : (MulAut.conj (s * g)).toMonoidHom =
        (MulAut.conj s).toMonoidHom.comp (MulAut.conj g).toMonoidHom := by
      ext x
      change (s * g) * x * (s * g)⁻¹ = s * (g * x * g⁻¹) * s⁻¹
      group
    change L.map (MulAut.conj (s * g)).toMonoidHom = L
    rw [he, ← map_map, hg, hsK]

private theorem map_conjugate_subtype
    {G : Type*} [Group G] (M : Subgroup G) (L : Subgroup M) (s : M) :
    (L.map (MulAut.conj s).toMonoidHom).map M.subtype =
      (L.map M.subtype).map (MulAut.conj (s : G)).toMonoidHom := by
  rw [map_map, map_map]
  rfl

private theorem index_two_of_ambient_swap
    {G : Type*} [Group G] [Finite G] {M : Subgroup G} (hM : IsCoatom M)
    {L K : Subgroup M} (hR : solvableRadical M = ⊥)
    (hL : L.IsCComponent) (hK : K.IsCComponent) (hne : L ≠ K) (hc : ⁅L, K⁆ = ⊥)
    (hC : centralizer (L : Set M) ≤ K) (hN : normalizer (L : Set M) ≤ L ⊔ K)
    (hp : normalizer (((L ⊔ K).map M.subtype) : Set G) ≠ ⊤)
    (s : G) (hsL : (L.map M.subtype).map (MulAut.conj s).toMonoidHom = K.map M.subtype)
    (hsK : (K.map M.subtype).map (MulAut.conj s).toMonoidHom = L.map M.subtype) :
    (L ⊔ K).index = 2 := by
  let := pair_join_normal hR hL hK hne hC
  have hle : M ≤ normalizer (((L ⊔ K).map M.subtype) : Set G) := by
    have h := (L ⊔ K).le_normalizer_map M.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using h
  have he := (hM.le_iff_eq hp).mp hle
  have hs : s ∈ M := by
    rw [← he]
    apply mem_normalizer_iff_map_conj_eq.mpr
    change ((L ⊔ K).map M.subtype).map (MulAut.conj s).toMonoidHom =
      (L ⊔ K).map M.subtype
    rw [Subgroup.map_sup, Subgroup.map_sup, hsL, hsK, sup_comm]
  apply index_two_of_component_swap hR hL hK hne hc hC hN (⟨s, hs⟩ : M)
  · apply map_injective M.subtype_injective
    rw [map_conjugate_subtype]
    exact hsL
  · apply map_injective M.subtype_injective
    rw [map_conjugate_subtype]
    exact hsK

/-- A factor-normalizer bound and an interchange in a proper ambient
normalizer force the actual component join to have index two inside M. -/
theorem index_sup_eq_two_of_isCComponent_of_normalizer_le_of_ambient_swap
    {G : Type*} [Group G] [Finite G] {M : Subgroup G} (hM : IsCoatom M)
    {L K : Subgroup M} (hR : solvableRadical M = ⊥)
    (hL : L.IsCComponent) (hK : K.IsCComponent) (hne : L ≠ K) (hc : ⁅L, K⁆ = ⊥)
    (hN : normalizer (L : Set M) ≤ L ⊔ K)
    (hp : normalizer (((L ⊔ K).map M.subtype) : Set G) ≠ ⊤)
    (s : G) (hsL : (L.map M.subtype).map (MulAut.conj s).toMonoidHom = K.map M.subtype)
    (hsK : (K.map M.subtype).map (MulAut.conj s).toMonoidHom = L.map M.subtype) :
    (L ⊔ K).index = 2 :=
  index_two_of_ambient_swap hM hR hL hK hne hc
    (centralizer_le_of_normalizer_le_join hR hL hc hN) hN hp s hsL hsK

end Subgroup

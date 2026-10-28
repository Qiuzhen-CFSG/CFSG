module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BinaryInspection.LinearInspection.Contracts
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.AutomorphismActions


/-!
# Selection from the actual degree-four centralizer flag

The transvection flag places the local component intersection between the
middle minimal parabolic and one of the two endpoint parabolics. If the
Sylow image were contained in the component, that endpoint would be invariant;
maximality would give equality. After excluding these endpoint equalities,
an outer Sylow element reverses the full flag and forces both endpoint
containments, hence equality with the middle minimal parabolic.

The flag and endpoint exclusions are explicit intermediate inputs here. They
must be constructed from the source involution and cubic residual before
claiming the degree-four inspection.

Source: Aschbacher--Smith, 15.3.43, n = 1 paragraph, printed p.1140.
-/

@[expose] public section

open Subgroup
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.BinaryInspection.LinearInspection
variable {G : Type*} [Group G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}
variable (c : ReducedConfiguration Yplus S M I L V₁ V₂)

/-- The actual full Sylow flag and its transvection-centralizer overgroup bounds. -/
structure FourFlagData where
  linear : c.toComponentAction.image L ≃* LinearGroup 4
  basis : Basis 3
  sylow : ((c.toComponentAction.image S).subgroupOf
    (c.toComponentAction.image L)).map linear.toMonoidHom = cutStabilizer basis Set.univ
  contains : minimalParabolic basis 1 ≤ ((c.toComponentAction.image (M ⊓ L)).subgroupOf
    (c.toComponentAction.image L)).map linear.toMonoidHom
  cover : ((c.toComponentAction.image (M ⊓ L)).subgroupOf
    (c.toComponentAction.image L)).map linear.toMonoidHom ≤ parabolic (cutSpace basis 0) ∨
    ((c.toComponentAction.image (M ⊓ L)).subgroupOf
    (c.toComponentAction.image L)).map linear.toMonoidHom ≤ parabolic (cutSpace basis 2)

private theorem middle_eq_endpoints (b : Basis 3) :
    minimalParabolic b 1 = parabolic (cutSpace b 0) ⊓ parabolic (cutSpace b 2) := by
  ext g
  simp only [minimalParabolic, mem_cutStabilizer, mem_inf]
  change (∀ i : Fin 3, i ≠ 1 → g ∈ parabolic (cutSpace b i)) ↔ _
  constructor
  · exact fun h => ⟨h 0 (by decide), h 2 (by decide)⟩
  · intro h i hi
    fin_cases i <;> simp_all

private theorem endpoint_ne_top (b : Basis 3) (i : Fin 3) :
    parabolic (cutSpace b i) ≠ ⊤ := by
  intro he
  have hle : cutStabilizer b ∅ ≤ parabolic (cutSpace b i) := he ▸ le_top
  obtain ⟨j, hj, _⟩ := (cutStabilizer_le_parabolic_iff b ∅ _
    (cutSpace_ne_bot b i) (cutSpace_ne_top b i)).mp hle
  exact hj

private theorem mapped_invariant (e : c.toComponentAction.image L ≃* LinearGroup 4)
    (H : Subgroup c.toComponentAction.Quotient) (hHK : H ≤ c.toComponentAction.image L)
    (s : c.toComponentAction.Quotient) (hs : s ∈ normalizer (H : Set _)) :
    ((H.subgroupOf (c.toComponentAction.image L)).map e.toMonoidHom).map
      (componentAction (c.toComponentAction.image L) e s).toMonoidHom =
      (H.subgroupOf (c.toComponentAction.image L)).map e.toMonoidHom :=
  componentAction_map_subgroup _ e H hHK s hs

private theorem endpoint_map_outer (b : Basis 3) (a : MulAut (LinearGroup 4))
    (ha : a ∉ MulAut.innerSubgroup _) (hB : (cutStabilizer b Set.univ).map
      a.toMonoidHom = cutStabilizer b Set.univ) (i : Fin 3) :
    (parabolic (cutSpace b i)).map a.toMonoidHom = parabolic (cutSpace b i.rev) := by
  obtain ⟨g, rfl⟩ := outer_eq_graph_inner (by decide : 3 ≤ 4) (by decide : 4 ≤ 5) a ha
  rw [graph_inner_map_parabolic, graph_inner_cutSpace_of_fullFlag b g hB]

/-- Conditional geometric assembly; the source involution must supply the flag,
and the cubic residual must exclude both endpoint equalities. -/
theorem middle_node_of_flag_and_endpoint_exclusion (hp : ParabolicInspection.QuotientParabolic c)
    (h : FourFlagData c)
    (hne : ∀ i : Fin 3, i = 0 ∨ i = 2 →
      ((c.toComponentAction.image (M ⊓ L)).subgroupOf
        (c.toComponentAction.image L)).map h.linear.toMonoidHom ≠
          parabolic (cutSpace h.basis i)) : Nonempty (MiddleNodeData c) := by
  let d := c.toComponentAction
  let K := d.image L
  let T := d.image S
  let J := d.image (M ⊓ L)
  let P := (J.subgroupOf K).map h.linear.toMonoidHom
  have hJK : J ≤ K := map_mono (comap_mono inf_le_right)
  have hJT : T ⊓ K ≤ J := by
    dsimp only [J, d]
    rw [quotient_intersection_eq c]
    exact inf_le_inf_right _ (map_mono (comap_mono c.sylow_le_M))
  have houter : ¬ T ≤ K := by
    intro hTK
    obtain ⟨i, hi, hPi⟩ : ∃ i : Fin 3, (i = 0 ∨ i = 2) ∧
        P ≤ parabolic (cutSpace h.basis i) := by
      rcases h.cover with he | he
      · exact ⟨0, Or.inl rfl, he⟩
      · exact ⟨2, Or.inr rfl, he⟩
    let Q := ((parabolic (cutSpace h.basis i)).map h.linear.symm.toMonoidHom).map K.subtype
    have hQK : Q ≤ K := map_subtype_le _
    have hPQ : J ≤ Q := by
      intro x hx
      refine ⟨⟨x, hJK hx⟩, ?_, rfl⟩
      exact mem_map.mpr ⟨h.linear ⟨x, hJK hx⟩, hPi ⟨_, hx, rfl⟩,
        h.linear.symm_apply_apply _⟩
    have hTQ : T ≤ Q := fun _ hx => hPQ (hJT ⟨hx, hTK hx⟩)
    have hQproper : Q < K := by
      apply lt_of_le_of_ne hQK
      intro he
      apply endpoint_ne_top h.basis i
      apply top_unique
      intro x _
      have hx : (h.linear.symm x : d.Quotient) ∈ Q := he ▸ (h.linear.symm x).property
      obtain ⟨y, ⟨w, hw, hwy⟩, hy⟩ := hx
      have hy' : y = h.linear.symm x := Subtype.ext hy
      have hwx : w = x := h.linear.symm.injective (hwy.trans hy')
      exact hwx ▸ hw
    have hQP : Q ≤ J := by
      dsimp only [J, d]
      rw [quotient_intersection_eq c]
      apply hp.maximal Q
      · exact hp.contains_borel.trans (by rw [← quotient_intersection_eq c]; exact hPQ)
      · exact hQproper
      · exact hTQ.trans Q.le_normalizer
      · rwa [← quotient_intersection_eq c]
    apply hne i hi
    apply le_antisymm hPi
    intro x hx
    refine mem_map.mpr ⟨h.linear.symm x, ?_, h.linear.apply_symm_apply x⟩
    exact hQP ⟨h.linear.symm x, ⟨x, hx, rfl⟩, rfl⟩
  obtain ⟨s, hsT, hsK⟩ := SetLike.not_le_iff_exists.mp houter
  let a := componentAction K h.linear s
  let : Group.IsPerfect L := SporadicModels.reduced_component_perfect c
  have hcentral : centralizer (K : Set d.Quotient) = ⊥ :=
    SporadicModels.component_image_centralizer_eq_bot d
  have ha : a ∉ MulAut.innerSubgroup _ := fun he =>
    hsK ((componentAction_mem_inner K h.linear hcentral s).mp he)
  have hTJ : T ≤ normalizer (J : Set d.Quotient) := by
    dsimp only [J, T, d]
    rw [quotient_intersection_eq c]
    exact hp.invariant
  have hP : P.map a.toMonoidHom = P := mapped_invariant c h.linear J hJK s (hTJ hsT)
  have hB : (cutStabilizer h.basis Set.univ).map a.toMonoidHom =
      cutStabilizer h.basis Set.univ := by
    have hn : T ≤ normalizer (T ⊓ K : Set d.Quotient) := by
      apply (le_inf T.le_normalizer (show T ≤ normalizer (K : Set _) from by
        rw [normalizer_eq_top]; exact le_top)).trans inf_normalizer_le_normalizer_inf
    have he := mapped_invariant c h.linear (T ⊓ K) inf_le_right s (hn hsT)
    rw [inf_subgroupOf_right] at he
    rwa [h.sylow] at he
  have hmid : P ≤ minimalParabolic h.basis 1 := by
    rw [middle_eq_endpoints]
    rcases h.cover with he | he
    · have hm := map_mono (f := a.toMonoidHom) he
      rw [hP, endpoint_map_outer h.basis a ha hB] at hm
      exact le_inf he hm
    · have hm := map_mono (f := a.toMonoidHom) he
      rw [hP, endpoint_map_outer h.basis a ha hB] at hm
      exact le_inf hm he
  exact ⟨⟨h.linear, h.basis, le_antisymm hmid h.contains, houter⟩⟩

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.BinaryInspection.LinearInspection

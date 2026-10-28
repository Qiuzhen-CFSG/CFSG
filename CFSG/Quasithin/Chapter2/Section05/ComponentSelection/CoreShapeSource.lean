module

public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CrossingMarksSource
public import Theory.GroupTheory.ConjugateKernelEmbedding
public import Theory.GroupTheory.SpecificGroups.DihedralSubgroupModels
public import ABG.ChapterII.Section1.SmallSubgroupModels

/-!
# The actual two-core embeds in the source automizer Sylow

The original 2.5.5 disjointness theorem makes the conjugate of SC faithful
under the actual source automizer map. Conjugation transports that embedding
back to SC, with range in the image of the original Sylow S. The dihedral
and semidihedral-sixteen subgroup calculations give precisely the initial
alternatives used in 2.5.21. The surjection and its marked kernel belong to
2.5.16; normality of the original K belongs to 2.5.20. No core shape or
noncommutativity is assumed in these alternatives.

Source: Aschbacher--Smith 2.5.21, printed p.565, first paragraph.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory ComponentRefinement
variable {G Q : Type*} [Group G] [Finite G] [Group Q]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The precise core embedding in the actual automizer Sylow image. -/
theorem MathieuSourceSetup.twoCore_embedding_in_sylow_image
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (f : H →* Q)
    (hker : f.ker = (((S : Subgroup H).map H.subtype) ⊓ centralizer (K : Set G)).subgroupOf H)
    (x : G) (hxT : x ∈ c.T) (hxS : x ∉ (S : Subgroup H).map H.subtype)
    (hxN : x ∈ normalizer ((S : Subgroup H).map H.subtype : Set G))
    (hx2 : x ^ 2 ∈ (S : Subgroup H).map H.subtype) :
    ∃ j : twoCore H →* (S : Subgroup H).map f, Function.Injective j := by
  let Y := (S : Subgroup H).map H.subtype
  have hcore := MathieuSourceSetup.core_eq_sylow_centralizer c hgen
  have hCY : twoCore H ≤ Y := hcore ▸ inf_le_left
  have hdis := (generated_twoCore_disjoint S (MathieuSourceSetup.sourceTuple c)
    ⟨c.component_le, c.component⟩ hgen hxT hxS hxN hx2).1
  have hk : f.ker = (twoCore H).subgroupOf H := by rwa [hcore]
  obtain ⟨j, hj, hr⟩ := exists_conjugate_kernel_embedding H Y (twoCore H)
    (map_subtype_le _) hCY f hk x hxN hdis
  have hY : Y.subgroupOf H = (S : Subgroup H) := by
    exact comap_map_eq_self (by rw [H.ker_subtype]; exact bot_le)
  rw [hY] at hr
  refine ⟨j.codRestrict _ (fun a => hr ⟨a, rfl⟩), ?_⟩
  intro a b hab
  exact hj (congrArg Subtype.val hab)

/-- An actual dihedral Sylow image gives the cyclic-or-dihedral core alternatives. -/
theorem MathieuSourceSetup.twoCore_cyclic_or_dihedral
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (f : H →* Q)
    (hker : f.ker = (((S : Subgroup H).map H.subtype) ⊓ centralizer (K : Set G)).subgroupOf H)
    (x : G) (hxT : x ∈ c.T) (hxS : x ∉ (S : Subgroup H).map H.subtype)
    (hxN : x ∈ normalizer ((S : Subgroup H).map H.subtype : Set G))
    (hx2 : x ^ 2 ∈ (S : Subgroup H).map H.subtype)
    {n : ℕ} (e : (S : Subgroup H).map f ≃* DihedralGroup (2 ^ n)) :
    IsCyclic (twoCore H) ∨
      ∃ k : ℕ, Nonempty (twoCore H ≃* DihedralGroup (2 ^ k)) := by
  obtain ⟨j, hj⟩ := MathieuSourceSetup.twoCore_embedding_in_sylow_image c hgen f hker x hxT hxS hxN hx2
  let g := e.toMonoidHom.comp j
  have hg : Function.Injective g := e.injective.comp hj
  let eg : twoCore H ≃* g.range := MonoidHom.ofInjective hg
  rcases DihedralGroup.subgroup_cyclic_or_dihedral_two_power g.range with hc | ⟨k, ⟨ek⟩⟩
  · let := hc
    exact Or.inl (isCyclic_of_injective eg.toMonoidHom eg.injective)
  · exact Or.inr ⟨k, ⟨eg.trans ek⟩⟩

/-- An actual semidihedral image of order sixteen gives all five core alternatives. -/
theorem MathieuSourceSetup.twoCore_models_of_semidihedral_sixteen
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (f : H →* Q)
    (hker : f.ker = (((S : Subgroup H).map H.subtype) ⊓ centralizer (K : Set G)).subgroupOf H)
    (x : G) (hxT : x ∈ c.T) (hxS : x ∉ (S : Subgroup H).map H.subtype)
    (hxN : x ∈ normalizer ((S : Subgroup H).map H.subtype : Set G))
    (hx2 : x ^ 2 ∈ (S : Subgroup H).map H.subtype)
    (e : (S : Subgroup H).map f ≃* Semidihedral.StandardModel 4 (by decide)) :
    IsCyclic (twoCore H) ∨ IsKleinFour (twoCore H) ∨
      Nonempty (twoCore H ≃* DihedralGroup 4) ∨
      Nonempty (twoCore H ≃* QuaternionGroup 2) ∨
      Nonempty (twoCore H ≃* Semidihedral.StandardModel 4 (by decide)) := by
  obtain ⟨j, hj⟩ := MathieuSourceSetup.twoCore_embedding_in_sylow_image c hgen f hker x hxT hxS hxN hx2
  let g := e.toMonoidHom.comp j
  have hg : Function.Injective g := e.injective.comp hj
  let eg : twoCore H ≃* g.range := MonoidHom.ofInjective hg
  have hcard : Nat.card (Semidihedral.StandardModel 4 (by decide)) = 16 :=
    Semidihedral.standardModel_card 4 (by decide)
  by_cases htop : g.range = ⊤
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨MulEquiv.ofBijective g
      ⟨hg, MonoidHom.range_eq_top.mp htop⟩⟩)))
  have hsmall : Nat.card g.range ≤ 8 := by
    have hi : 2 ≤ g.range.index := one_lt_index_of_ne_top htop
    have hm := g.range.card_mul_index
    rw [hcard] at hm
    have hh := Nat.mul_le_mul_left (Nat.card g.range) hi
    omega
  have hsd : Stellmacher.IsSemidihedralGroup (Semidihedral.StandardModel 4 (by decide)) := by
    exact ⟨4, by decide, hcard,
      Semidihedral.standardRotation 4 (by decide), Semidihedral.standardReflection 4 (by decide),
      Semidihedral.standardRotation_order 4 (by decide), Semidihedral.standardReflection_order 4 (by decide),
      Semidihedral.standard_conjugation 4 (by decide), Semidihedral.standard_generators 4 (by decide)⟩
  rcases ABG.QuasiDihedral.small_subgroup_models hsd g.range hsmall with hc | hrest
  · let := hc
    exact Or.inl (isCyclic_of_injective eg.toMonoidHom eg.injective)
  · rcases hrest with hk | hrest
    · exact Or.inr (Or.inl {
        card_four := (Nat.card_congr eg.toEquiv).trans hk.card_four
        exponent_two := (Monoid.exponent_eq_of_mulEquiv eg).trans hk.exponent_two })
    · rcases hrest with hd | hq
      · obtain ⟨ed⟩ := hd
        exact Or.inr (Or.inr (Or.inl ⟨eg.trans ed⟩))
      · obtain ⟨eq⟩ := hq
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨eg.trans eq⟩)))

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection

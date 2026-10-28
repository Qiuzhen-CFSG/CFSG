module
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.LocalGeometry.CentralizerReselection.Selection
public import Theory.GroupTheory.DihedralGeneratedFactor
public import Theory.GroupTheory.SemidihedralSquareData

/-!
# Exceptional factors after centralizer Sylow reselection

This discharges the exceptional-alternative premise of the centralizer
induction in `Selection`, using the actual right-conjugation equivalence.
For dihedral or semidihedral factors larger than a four-group, the common
order-two intersection equals both centers. Factoring the centralizing element
then puts both full ambient factors in its centralizer, so every clause of the
local exception, including the fused conjugator, lifts to the ambient group.

In the four-group case, rank and the return-to-union condition identify the
transported old factors with the two new factors. Nonnesting rules out equal
images. Pulling back the conjugator (or its inverse for swapped factors) and
the concrete model contradicts the original model exclusion.

The first export has the literal universal `hexclude` contract of
`MinimalCounterexample.centralizer_alternative_of_reselection_exclusions`.
The second applies that consumer; the source pair-permutation hypothesis
remains explicit for the parent assembly to supply.

Source: M. Aschbacher, *On finite groups of component type*, Illinois J. Math.
19 (1975), Lemma 3.4(d), printed p.95, DOI 10.1215/ijm/1256050927.
-/

open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1
open scoped Pointwise
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
universe u
variable {G : Type u} [Group G]

private theorem model_transport {X : Type*} {Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (h : DihedralOrSemidihedral X) : DihedralOrSemidihedral Y := by
  rcases h with ⟨n, hn, ⟨f⟩⟩ | ⟨n, hn, ⟨f⟩⟩
  · exact Or.inl ⟨n, hn, ⟨e.symm.trans f⟩⟩
  · exact Or.inr ⟨n, hn, ⟨e.symm.trans f⟩⟩

private theorem model_small_or_center {X : Type*} [Group X]
    (h : DihedralOrSemidihedral X) : Nat.card X = 4 ∨ Nat.card (center X) = 2 := by
  rcases h with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · by_cases hn1 : n = 1
    · left
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hn1]
      rfl
    · exact Or.inr (DihedralGroup.center_card_of_equiv (by omega) e)
  · right
    rw [Nat.card_congr (centerCongr e).toEquiv]
    exact (Semidihedral.square_data hn _ _ (Semidihedral.standardRotation_order n hn)
      (Semidihedral.standardReflection_order n hn) (Semidihedral.standard_conjugation n hn)
      (Semidihedral.standard_generators n hn)).1

private theorem map_conjugate {Q : Type*} [Group Q] (q : G →* Q)
    (A : Subgroup G) (g : G) :
    (conjugate A g).map q = conjugate (A.map q) (q g) := by
  unfold conjugate
  rw [map_map, map_map]
  congr 1
  ext x
  simp

private theorem exceptional_map {Q : Type*} [Group Q] (q : G →* Q)
    (hq : Function.Injective q) {A B : Subgroup G} (h : Exceptional A B) :
    Exceptional (A.map q) (B.map q) := by
  obtain ⟨⟨g, hg, k, hk⟩, hm, hi⟩ := h
  refine ⟨⟨q g, ?_, q k, ?_⟩, ?_, ?_⟩
  · rw [← map_conjugate, hg]
  · simpa only [map_mul, map_inv] using mem_map_of_mem q hk
  · exact model_transport (A.equivMapOfInjective q hq) hm
  · rw [← map_inf A B q hq, card_map_of_injective hq, hi]

private theorem intersection_le_center {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, Commute a b) :
    A ⊓ B ≤ (center A).map A.subtype := by
  intro x hx
  refine ⟨⟨x, hx.1⟩, mem_center_iff.mpr ?_, rfl⟩
  intro a
  apply Subtype.ext
  exact (hc a a.property x hx.2).eq

private theorem centralizer_pair_full [Finite G] {A B : Subgroup G} {v : G}
    (hc : ⁅A, B⁆ = ⊥) (hv : v ∈ A ⊔ B)
    (hzA : Nat.card (center (A.subgroupOf (centralizer ({v} : Set G)))) = 2)
    (hzB : Nat.card (center (B.subgroupOf (centralizer ({v} : Set G)))) = 2)
    (hi : Nat.card (A.subgroupOf (centralizer ({v} : Set G)) ⊓
      B.subgroupOf (centralizer ({v} : Set G)) : Subgroup (centralizer ({v} : Set G))) = 2) :
    A ≤ centralizer ({v} : Set G) ∧ B ≤ centralizer ({v} : Set G) := by
  let L := centralizer ({v} : Set G)
  let C := A.subgroupOf L
  let D := B.subgroupOf L
  have hab : ∀ a ∈ A, ∀ b ∈ B, Commute a b := by
    intro a ha b hb
    exact (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc ha) b hb).symm
  have hcd : ∀ c ∈ C, ∀ d ∈ D, Commute c d := by
    intro c hc d hd
    exact Subtype.ext ((hab c hc d hd).eq)
  have hZC : C ⊓ D = (center C).map C.subtype :=
    eq_of_le_of_card_ge (intersection_le_center hcd) (by
      rw [card_map_of_injective C.subtype_injective, hzA, hi])
  have hZD : D ⊓ C = (center D).map D.subtype :=
    eq_of_le_of_card_ge (intersection_le_center (fun d hd c hc => (hcd c hc d hd).symm)) (by
      rw [card_map_of_injective D.subtype_injective, hzB, inf_comm, hi])
  obtain ⟨a, ha, b, hb, habv, haL, hbL⟩ := centralizer_reselection_factorization hc hv
  have haZ : (⟨⟨a, haL⟩, ha⟩ : C) ∈ center C := by
    apply mem_center_iff.mpr
    intro c
    apply Subtype.ext
    apply Subtype.ext
    change (c : G) * a = a * (c : G)
    apply mul_right_cancel (b := b)
    calc
      (c : G) * a * b = (c : G) * v := by rw [mul_assoc, habv]
      _ = v * (c : G) := mem_centralizer_singleton_iff.mp c.val.property
      _ = a * b * (c : G) := by rw [habv]
      _ = (a * (c : G)) * b := by rw [mul_assoc, (hab c c.property b hb).symm.eq, ← mul_assoc]
  have hbZ : (⟨⟨b, hbL⟩, hb⟩ : D) ∈ center D := by
    apply mem_center_iff.mpr
    intro d
    apply Subtype.ext
    apply Subtype.ext
    change (d : G) * b = b * (d : G)
    apply mul_left_cancel (a := a)
    calc
      a * ((d : G) * b) = (d : G) * v := by rw [← mul_assoc, (hab a ha d d.property).eq, mul_assoc, habv]
      _ = v * (d : G) := mem_centralizer_singleton_iff.mp d.val.property
      _ = a * (b * (d : G)) := by rw [← mul_assoc, habv]
  have haD : a ∈ B := by
    have h := mem_map_of_mem C.subtype haZ
    rw [← hZC] at h
    exact h.2
  have hbC : b ∈ A := by
    have h := mem_map_of_mem D.subtype hbZ
    rw [← hZD] at h
    exact h.2
  have hvA : v ∈ A := habv ▸ A.mul_mem ha hbC
  have hvB : v ∈ B := habv ▸ B.mul_mem haD hb
  exact ⟨fun x hx => mem_centralizer_singleton_iff.mpr (hab x hx v hvB).eq,
    fun x hx => mem_centralizer_singleton_iff.mpr (hab v hvA x hx).symm.eq⟩

private theorem rank_card [Finite G] (h : TwoRankAtLeastTwo G) : 4 ≤ Nat.card G := by
  obtain ⟨E, hE, _⟩ := h
  exact hE ▸ card_le_card_group E

private theorem pullback_model_conjugacy {Q : Type*} [Group Q] (e : G ≃* Q)
    (C D : Subgroup G) (x : Q)
    (hx : conjugate (C.map e.toMonoidHom) x = D.map e.toMonoidHom)
    (hm : DihedralOrSemidihedral (C.map e.toMonoidHom)) :
    ∃ y : G, conjugate C y = D ∧ DihedralOrSemidihedral C := by
  refine ⟨e.symm x, ?_, model_transport (e.subgroupMap C).symm hm⟩
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [map_conjugate, MulEquiv.coe_toMonoidHom, e.apply_symm_apply]
  exact hx

private theorem four_pair_pullback [Finite G] {Q : Type*} [Group Q] [Finite Q]
    (e : G ≃* Q) (C D : Subgroup G) (A B : Subgroup Q)
    (hrC : TwoRankAtLeastTwo C) (hrD : TwoRankAtLeastTwo D) (hne : C ≠ D)
    (hC : C.map e.toMonoidHom ≤ A ∨ C.map e.toMonoidHom ≤ B)
    (hD : D.map e.toMonoidHom ≤ A ∨ D.map e.toMonoidHom ≤ B)
    (hA : Nat.card A = 4) (hex : Exceptional A B) :
    ∃ y : G, conjugate C y = D ∧ DihedralOrSemidihedral C := by
  obtain ⟨⟨x, hx, _⟩, hm, _⟩ := hex
  have hB : Nat.card B = 4 := by
    rw [← hx, show Nat.card (conjugate A x) = Nat.card A from
      card_map_of_injective (MulAut.conj x⁻¹).injective, hA]
  have heq {E : Subgroup G} (hr : TwoRankAtLeastTwo E) {F : Subgroup Q}
      (hF : Nat.card F = 4) (hEF : E.map e.toMonoidHom ≤ F) : E.map e.toMonoidHom = F :=
    eq_of_le_of_card_ge hEF (by rw [hF, card_map_of_injective e.injective]; exact rank_card hr)
  have hC' : C.map e.toMonoidHom = A ∨ C.map e.toMonoidHom = B :=
    hC.imp (heq hrC hA) (heq hrC hB)
  have hD' : D.map e.toMonoidHom = A ∨ D.map e.toMonoidHom = B :=
    hD.imp (heq hrD hA) (heq hrD hB)
  rcases hC' with hC' | hC' <;> rcases hD' with hD' | hD'
  · exact (hne (map_injective e.injective (hC'.trans hD'.symm))).elim
  · apply pullback_model_conjugacy e C D x
    · rwa [hC', hD']
    · rwa [hC']
  · apply pullback_model_conjugacy e C D x⁻¹
    · rw [hC', hD', ← hx, conjugate_conjugate, mul_inv_cancel, conjugate_one]
    · rw [hC', ← hx]
      exact model_transport ((MulAut.conj x⁻¹).subgroupMap A) hm
  · exact (hne (map_injective e.injective (hC'.trans hD'.symm))).elim

variable [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

/-- The exceptional alternative cannot arise after centralizer reselection.
This has precisely the universal form required by the `hexclude` argument
of `centralizer_alternative_of_reselection_exclusions`. -/
public theorem MinimalCounterexample.reselection_not_exceptional
    (m : MinimalCounterexample S A₁ A₂)
    (u : G) (_hu : u ∈ A₁ ⊔ A₂) (_hou : orderOf u = 2)
    (hr₁ : TwoRankAtLeastTwo (A₁.subgroupOf (centralizer ({u} : Set G))))
    (hr₂ : TwoRankAtLeastTwo (A₂.subgroupOf (centralizer ({u} : Set G))))
    (hn₁ : ¬ A₁ ⊓ centralizer ({u} : Set G) ≤ A₂)
    (_hn₂ : ¬ A₂ ⊓ centralizer ({u} : Set G) ≤ A₁)
    (hmodel : ∀ x : centralizer ({u} : Set G),
      conjugate (A₁.subgroupOf (centralizer ({u} : Set G))) x =
        A₂.subgroupOf (centralizer ({u} : Set G)) →
      ¬ DihedralOrSemidihedral (A₁.subgroupOf (centralizer ({u} : Set G)))) :
    ∀ g ∈ intersectionGenerated A₁ A₂,
      let v := g⁻¹ * u * g
      v ∈ A₁ ⊔ A₂ →
      (∀ x ∈ (A₁ : Set G) ∪ A₂, x ∈ centralizer ({u} : Set G) →
        g⁻¹ * x * g ∈ (A₁ : Set G) ∪ A₂) →
      ¬ Exceptional (A₁.subgroupOf (centralizer ({v} : Set G)))
        (A₂.subgroupOf (centralizer ({v} : Set G))) := by
  intro g _hg v hv hreturn hex
  let K := centralizer ({u} : Set G)
  let L := centralizer ({v} : Set G)
  let C₁ := A₁.subgroupOf K
  let C₂ := A₂.subgroupOf K
  let B₁ := A₁.subgroupOf L
  let B₂ := A₂.subgroupOf L
  let e : K ≃* L := centralizerReselectionEquiv u g
  rcases model_small_or_center hex.2.1 with hfour | hcenter
  · have hmap₁ : C₁.map e.toMonoidHom ≤ B₁ ∨ C₁.map e.toMonoidHom ≤ B₂ := by
      apply SubgroupClass.subset_union.mp
      rintro _ ⟨x, hx, rfl⟩
      change (e x : G) ∈ (A₁ : Set G) ∪ A₂
      rw [show (e x : G) = g⁻¹ * (x : G) * g from centralizerReselectionEquiv_apply u g x]
      exact hreturn x (Or.inl hx) x.property
    have hmap₂ : C₂.map e.toMonoidHom ≤ B₁ ∨ C₂.map e.toMonoidHom ≤ B₂ := by
      apply SubgroupClass.subset_union.mp
      rintro _ ⟨x, hx, rfl⟩
      change (e x : G) ∈ (A₁ : Set G) ∪ A₂
      rw [show (e x : G) = g⁻¹ * (x : G) * g from centralizerReselectionEquiv_apply u g x]
      exact hreturn x (Or.inr hx) x.property
    have hne : C₁ ≠ C₂ := by
      intro heq
      apply hn₁
      intro x hx
      have hxC : (⟨x, hx.2⟩ : K) ∈ C₁ := hx.1
      rw [heq] at hxC
      exact hxC
    obtain ⟨x, hx, hm⟩ := four_pair_pullback e C₁ C₂ B₁ B₂ hr₁ hr₂ hne hmap₁ hmap₂ hfour hex
    exact hmodel x hx hm
  · obtain ⟨x, hx, _⟩ := hex.1
    have hcenter₂ : Nat.card (center B₂) = 2 := by
      let f : B₁ ≃* B₂ := ((MulAut.conj x⁻¹).subgroupMap B₁).trans (MulEquiv.subgroupCongr hx)
      rw [← Nat.card_congr (centerCongr f).toEquiv]
      exact hcenter
    obtain ⟨hA₁, hA₂⟩ := centralizer_pair_full m.setup.commute hv hcenter hcenter₂ hex.2.2
    have hamb : Exceptional A₁ A₂ := by
      have he := exceptional_map L.subtype L.subtype_injective hex
      rwa [map_subgroupOf_eq_of_le hA₁, map_subgroupOf_eq_of_le hA₂] at he
    exact m.fails (Or.inr (Or.inr hamb))

/-- Applying the exceptional transport to the actual reselection consumer
removes its `hexclude` premise. The permutation premise is source (b), which
is supplied by the parent local-geometry assembly. -/
public theorem MinimalCounterexample.centralizer_alternative_of_reselection_model_exclusion
    (m : MinimalCounterexample S A₁ A₂)
    (hperm : ∀ s ∈ S,
      (conjugate A₁ s = A₁ ∧ conjugate A₂ s = A₂) ∨
      (conjugate A₁ s = A₂ ∧ conjugate A₂ s = A₁))
    (u : G) (hu : u ∈ A₁ ⊔ A₂) (hou : orderOf u = 2)
    (hr₁ : TwoRankAtLeastTwo (A₁.subgroupOf (centralizer ({u} : Set G))))
    (hr₂ : TwoRankAtLeastTwo (A₂.subgroupOf (centralizer ({u} : Set G))))
    (hn₁ : ¬ A₁ ⊓ centralizer ({u} : Set G) ≤ A₂)
    (hn₂ : ¬ A₂ ⊓ centralizer ({u} : Set G) ≤ A₁)
    (hmodel : ∀ x : centralizer ({u} : Set G),
      conjugate (A₁.subgroupOf (centralizer ({u} : Set G))) x =
        A₂.subgroupOf (centralizer ({u} : Set G)) →
      ¬ DihedralOrSemidihedral (A₁.subgroupOf (centralizer ({u} : Set G)))) :
    centralizer ({u} : Set G) = ⊤ ∨
      centralizer ({u} : Set G) ≤ intersectionGenerated A₁ A₂ :=
  m.centralizer_alternative_of_reselection_exclusions hperm u hu hr₁ hr₂ hn₁ hn₂
    (m.reselection_not_exceptional u hu hou hr₁ hr₂ hn₁ hn₂ hmodel)

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75

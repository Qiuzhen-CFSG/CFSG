module

public import Theory.GroupTheory.CComponent.PrimeGroupOvergroup
public import Theory.GroupTheory.CComponent.CommutatorDichotomy

/-!
# Fixed C-components in a central product of component orbits

A C-component of a subgroup centralizer contained in the ordinary layer lies
in one orbit of ambient components. Fixed elements of a central product may
have nonfixed coordinates, but their coordinate defects are central. Thus
the commutator of the fixed group lies in the product of the fixed factors.
Perfectness and the C-component commutator dichotomy select one orbit.

This extends the coordinate argument of `OrdinaryCentralizerOrbit` to arbitrary
subgroup actors and C-component seeds. No two-group, odd-core or ordinary-seed
assumption is needed here. In GLS II, Proposition 5.22(i), it is applied after
the odd-core quotient; the seed there need not be quasisimple.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement
namespace Subgroup
variable {G : Type*} [Group G]

private theorem fixed_coordinate_defect {A B : Subgroup G} {t a b : G}
    (hA : t ∈ Subgroup.normalizer (A : Set G)) (hB : t ∈ Subgroup.normalizer (B : Set G))
    (ha : a ∈ A) (hb : b ∈ B) (hx : t * (a * b) * t⁻¹ = a * b) :
    a⁻¹ * (t * a * t⁻¹) ∈ A ⊓ B := by
  refine ⟨A.mul_mem (A.inv_mem ha) ((mem_normalizer_iff.mp hA a).mp ha), ?_⟩
  have he : a⁻¹ * (t * a * t⁻¹) = b * (t * b * t⁻¹)⁻¹ := by
    calc
      _ = a⁻¹ * (t * (a * b) * t⁻¹) * (t * b * t⁻¹)⁻¹ := by group
      _ = b * (t * b * t⁻¹)⁻¹ := by rw [hx]; group
  rw [he]
  exact B.mul_mem hb (B.inv_mem ((mem_normalizer_iff.mp hB b).mp hb))

/-- Central coordinate defects do not affect the coordinate commutator. -/
private theorem fixed_coordinate_commutator {A B : Subgroup G} {t a b c d : G}
    (hcomm : A ≤ centralizer (B : Set G))
    (hA : t ∈ Subgroup.normalizer (A : Set G)) (hB : t ∈ Subgroup.normalizer (B : Set G))
    (ha : a ∈ A) (hb : b ∈ B) (hc : c ∈ A) (hd : d ∈ B)
    (hx : t * (a * b) * t⁻¹ = a * b) (hy : t * (c * d) * t⁻¹ = c * d) :
    t * ⁅a, c⁆ * t⁻¹ = ⁅a, c⁆ := by
  let r := a⁻¹ * (t * a * t⁻¹)
  let s := c⁻¹ * (t * c * t⁻¹)
  have hr : r ∈ A ⊓ B := fixed_coordinate_defect hA hB ha hb hx
  have hs : s ∈ A ⊓ B := fixed_coordinate_defect hA hB hc hd hy
  have hrc : ⁅r, c * s⁆ = 1 :=
    (show Commute r (c * s) from hcomm (A.mul_mem hc hs.1) r hr.2).commutator_eq
  have has : ⁅a, s⁆ = 1 :=
    (show Commute a s from (hcomm ha s hs.2).symm).commutator_eq
  have hea : t * a * t⁻¹ = a * r := by dsimp [r]; group
  have hec : t * c * t⁻¹ = c * s := by dsimp [s]; group
  rw [conjugate_commutatorElement, hea, hec,
    commutatorElement_mul_left_eq_conj_mul, hrc]
  simp only [mul_one, mul_inv_cancel, one_mul]
  rw [commutatorElement_mul_right_eq_mul_conj, has]
  simp only [mul_one, mul_inv_cancel_right]

/-- Only the derived subgroup, rather than the entire fixed subgroup, needs
to split over a central product. -/
private theorem fixed_product_commutator_le {A B : Subgroup G} (P : Subgroup G)
    (hcomm : A ≤ centralizer (B : Set G))
    (hA : P ≤ Subgroup.normalizer (A : Set G)) (hB : P ≤ Subgroup.normalizer (B : Set G)) :
    ⁅(A ⊔ B) ⊓ centralizer (P : Set G),
      (A ⊔ B) ⊓ centralizer (P : Set G)⁆ ≤
      (A ⊓ centralizer (P : Set G)) ⊔ (B ⊓ centralizer (P : Set G)) := by
  have hBA := le_centralizer_iff.mp hcomm
  have hn : B ≤ Subgroup.normalizer (A : Set G) := hBA.trans (centralizer_le_normalizer _)
  apply commutator_le.mpr
  intro x hx y hy
  have hxp : x ∈ (A : Set G) * (B : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left A B hn]
    exact hx.1
  have hyp : y ∈ (A : Set G) * (B : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left A B hn]
    exact hy.1
  obtain ⟨a, ha, b, hb, rfl⟩ := hxp
  obtain ⟨c, hc, d, hd, rfl⟩ := hyp
  have hfixx (t : P) : (t : G) * (a * b) * (t : G)⁻¹ = a * b := by
    rw [hx.2 t t.property, mul_inv_cancel_right]
  have hfixy (t : P) : (t : G) * (c * d) * (t : G)⁻¹ = c * d := by
    rw [hy.2 t t.property, mul_inv_cancel_right]
  have hac : ⁅a, c⁆ ∈ A ⊓ centralizer (P : Set G) := by
    refine ⟨commutator_le_self A (commutator_mem_commutator ha hc), ?_⟩
    intro z hz
    exact mul_inv_eq_iff_eq_mul.mp (fixed_coordinate_commutator hcomm (hA hz) (hB hz) ha hb hc hd
      (hfixx ⟨z, hz⟩) (hfixy ⟨z, hz⟩))
  have hbd : ⁅b, d⁆ ∈ B ⊓ centralizer (P : Set G) := by
    refine ⟨commutator_le_self B (commutator_mem_commutator hb hd), ?_⟩
    intro z hz
    apply mul_inv_eq_iff_eq_mul.mp
    apply fixed_coordinate_commutator hBA (hB hz) (hA hz) hb ha hd hc
    · simpa only [hcomm ha b hb] using hfixx ⟨z, hz⟩
    · simpa only [hcomm hc d hd] using hfixy ⟨z, hz⟩
  have hbc : ⁅b, c⁆ = 1 := (show Commute b c from hcomm hc b hb).commutator_eq
  have had : ⁅a, d⁆ = 1 := (show Commute a d from hBA hd a ha).commutator_eq
  have hcbd : c * ⁅b, d⁆ * c⁻¹ = ⁅b, d⁆ := by
    rw [← hcomm hc _ hbd.1, mul_inv_cancel_right]
  have habd : a * ⁅b, d⁆ * a⁻¹ = ⁅b, d⁆ := by
    rw [← hcomm ha _ hbd.1, mul_inv_cancel_right]
  have he : ⁅a * b, c * d⁆ = ⁅b, d⁆ * ⁅a, c⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul,
      commutatorElement_mul_right_eq_mul_conj b c d,
      commutatorElement_mul_right_eq_mul_conj a c d, hbc, had]
    simp only [one_mul, mul_one, mul_inv_cancel_right, hcbd, habd]
  rw [he]
  exact mul_mem (mem_sup_right hbd) (mem_sup_left hac)


private theorem cComponent_le_normal_sup [Finite G] {A B D : Subgroup G}
    [A.Normal] [B.Normal] (hD : D.IsCComponent) (hle : D ≤ A ⊔ B) :
    D ≤ A ∨ D ≤ B := by
  by_cases hDA : D ≤ A
  · exact Or.inl hDA
  by_cases hDB : D ≤ B
  · exact Or.inr hDB
  have hcomm (N : Subgroup G) [N.Normal] (hn : ¬ D ≤ N) :
      ⁅D, N⁆ ≤ solvableRadical G := by
    rcases hD.commutator_le_radical_or_eq_iSup_conjugates N with h | h
    · exact h
    · exact (hn ((le_iSup_conjugates D N).trans
        (h.symm.le.trans (commutator_le_right D N)))).elim
  let q := QuotientGroup.mk' (solvableRadical G)
  have hcent (N : Subgroup G) [N.Normal] (hn : ¬ D ≤ N) :
      N.map q ≤ centralizer (D.map q : Set (G ⧸ solvableRadical G)) := by
    apply le_centralizer_iff.mp
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← map_commutator, map_eq_bot_iff]
    simpa only [q, QuotientGroup.ker_mk'] using hcomm N hn
  have hDC : D.map q ≤ centralizer (D.map q : Set (G ⧸ solvableRadical G)) :=
    (map_mono hle).trans (by rw [map_sup]; exact sup_le (hcent A hDA) (hcent B hDB))
  let := hD.perfect
  let : Group.IsPerfect (D.map q) := Group.IsPerfect.map q
  have he : D.map q = ⊥ := by
    rw [← commutator_eq_self (H := D.map q)]
    exact commutator_eq_bot_iff_le_centralizer.mpr hDC
  exact (hD.map_quotient_ne_bot (solvableRadical G) he).elim

private theorem component_le_factor [Finite G] {A B D M : Subgroup G}
    (hD : (D.subgroupOf M).IsCComponent) (hDM : D ≤ M)
    (hAle : A ≤ M) (hBle : B ≤ M)
    (hAM : M ≤ normalizer (A : Set G)) (hBM : M ≤ normalizer (B : Set G))
    (hprod : D ≤ A ⊔ B) : D ≤ A ∨ D ≤ B := by
  let : (A.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hAM
  let : (B.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hBM
  have hh : D.subgroupOf M ≤ A.subgroupOf M ⊔ B.subgroupOf M := by
    apply (map_le_map_iff_of_injective M.subtype_injective).mp
    simpa only [map_sup, map_subgroupOf_eq_of_le hDM,
      map_subgroupOf_eq_of_le hAle, map_subgroupOf_eq_of_le hBle] using hprod
  exact (cComponent_le_normal_sup hD hh).imp
    (fun h x hx => h (show (⟨x, hDM hx⟩ : M) ∈ D.subgroupOf M from hx))
    (fun h x hx => h (show (⟨x, hDM hx⟩ : M) ∈ D.subgroupOf M from hx))

/-- A fixed C-component selects a factor of an invariant central product. -/
theorem IsCComponent.le_or_le_of_commuting_fixed_product [Finite G] {A B D : Subgroup G} (P : Subgroup G)
    (hDC : D ≤ centralizer (P : Set G))
    (hD : (D.subgroupOf (centralizer (P : Set G))).IsCComponent)
    (hcomm : A ≤ centralizer (B : Set G))
    (hA : P ≤ normalizer (A : Set G)) (hB : P ≤ normalizer (B : Set G))
    (hprod : D ≤ A ⊔ B) : D ≤ A ∨ D ≤ B := by
  let C := centralizer (P : Set G)
  let M := (A ⊔ B) ⊓ C
  have hDM : D ≤ M := le_inf hprod hDC
  have hAM : A ⊓ C ≤ M := inf_le_inf le_sup_left le_rfl
  have hBM : B ⊓ C ≤ M := inf_le_inf le_sup_right le_rfl
  have hNA : A ⊔ B ≤ Subgroup.normalizer (A : Set G) :=
    sup_le A.le_normalizer ((le_centralizer_iff.mp hcomm).trans (centralizer_le_normalizer _))
  have hNB : A ⊔ B ≤ Subgroup.normalizer (B : Set G) :=
    sup_le (hcomm.trans (centralizer_le_normalizer _)) B.le_normalizer
  have hnA : M ≤ Subgroup.normalizer ((A ⊓ C : Subgroup G) : Set G) :=
    (le_inf (inf_le_left.trans hNA) (inf_le_right.trans C.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hnB : M ≤ Subgroup.normalizer ((B ⊓ C : Subgroup G) : Set G) :=
    (le_inf (inf_le_left.trans hNB) (inf_le_right.trans C.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hsplit : D ≤ (A ⊓ C) ⊔ (B ⊓ C) := by
    let := hD.perfect
    let : Group.IsPerfect D := Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe hDC).toMonoidHom) (subgroupOfEquivOfLe hDC).surjective
    calc
      D = ⁅D, D⁆ := commutator_eq_self.symm
      _ ≤ ⁅M, M⁆ := commutator_mono hDM hDM
      _ ≤ _ := fixed_product_commutator_le P hcomm hA hB
  exact (component_le_factor (hD.subgroupOf_of_le hDM inf_le_right) hDM hAM hBM hnA hnB hsplit).imp
    (fun h => h.trans inf_le_left) (fun h => h.trans inf_le_left)

private theorem component_le_commuting_family [Finite G] {ι : Type*} [Finite ι]
    (K : ι → Subgroup G) {D : Subgroup G} (P : Subgroup G)
    (hDC : D ≤ centralizer (P : Set G))
    (hD : (D.subgroupOf (centralizer (P : Set G))).IsCComponent)
    (hcomm : ∀ i j, i ≠ j → K i ≤ centralizer (K j : Set G))
    (hn : ∀ i, P ≤ Subgroup.normalizer (K i : Set G)) (hle : D ≤ ⨆ i, K i) :
    ∃ i, D ≤ K i := by
  classical
  let := Fintype.ofFinite ι
  have hnS (s : Finset ι) : P ≤ Subgroup.normalizer ((s.sup K : Subgroup G) : Set G) := by
    induction s using Finset.induction_on with
    | empty =>
      change P ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G)
      rw [Subgroup.normalizer_eq_top]
      exact le_top
    | @insert j s hj ihs =>
      rw [Finset.sup_insert]
      exact (le_inf (hn j) ihs).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hDne : D ≠ ⊥ := by
    intro hb
    apply hD.ne_bot
    simp only [hb, bot_subgroupOf]
  have hs (s : Finset ι) : D ≤ s.sup K → ∃ i ∈ s, D ≤ K i := by
    induction s using Finset.induction_on with
    | empty =>
      intro h
      exact (hDne (le_bot_iff.mp (by simpa using h))).elim
    | @insert i s hi ih =>
      intro h
      rw [Finset.sup_insert] at h
      have hc : K i ≤ centralizer ((s.sup K : Subgroup G) : Set G) :=
        le_centralizer_iff.mp (Finset.sup_le fun j hj =>
          hcomm j i (ne_of_mem_of_not_mem hj hi))
      rcases hD.le_or_le_of_commuting_fixed_product P hDC hc (hn i) (hnS s) h with h | h
      · exact ⟨i, Finset.mem_insert_self i s, h⟩
      · obtain ⟨j, hj, hjD⟩ := ih h
        exact ⟨j, Finset.mem_insert_of_mem hj, hjD⟩
  obtain ⟨i, _, hi⟩ := hs Finset.univ (by simpa only [Finset.sup_univ_eq_iSup] using hle)
  exact ⟨i, hi⟩

private theorem componentOrbit_eq_of_conjugate_eq (J K A : Subgroup G) (a b : A)
    (he : J.map (MulAut.conj (a : G)).toMonoidHom =
      K.map (MulAut.conj (b : G)).toMonoidHom) : componentOrbit J A = componentOrbit K A := by
  have hseed (J K : Subgroup G) (a b : A)
      (he : J.map (MulAut.conj (a : G)).toMonoidHom =
        K.map (MulAut.conj (b : G)).toMonoidHom) : J ≤ componentOrbit K A := by
    intro j hj
    have hm : (MulAut.conj (a : G)) j ∈ componentOrbit K A := by
      apply (le_iSup (fun b : A => K.map (MulAut.conj (b : G)).toMonoidHom) b)
      rw [← he]
      exact mem_map_of_mem _ hj
    have hn := le_normalizer_componentOrbit K A a.property
    exact (mem_normalizer_iff.mp hn j).mpr hm
  apply le_antisymm
  · exact iSup_conjugates_le_of_le_normalizer J A _ (hseed J K a b he)
      (le_normalizer_componentOrbit K A)
  · exact iSup_conjugates_le_of_le_normalizer K A _ (hseed K J b a he.symm)
      (le_normalizer_componentOrbit J A)

private theorem distinct_componentOrbits_commute {J K : Subgroup G}
    (hJ : IsComponent G J) (hK : IsComponent G K) (A : Subgroup G)
    (hne : componentOrbit J A ≠ componentOrbit K A) :
    componentOrbit J A ≤ centralizer (componentOrbit K A : Set G) := by
  apply iSup_le
  intro a
  apply le_centralizer_iff.mpr
  apply iSup_le
  intro b
  apply commutator_eq_bot_iff_le_centralizer.mp
  exact (hK.map_conj b).commutator_eq_bot_of_ne (hJ.map_conj a) (fun he =>
    hne (componentOrbit_eq_of_conjugate_eq J K A a b he.symm))

/-- The seed lies in a single actual actor orbit of ambient components. -/
theorem IsCComponent.le_componentOrbit_of_le_componentLayer [Finite G]
    {D : Subgroup G} (P : Subgroup G) (hDC : D ≤ centralizer (P : Set G))
    (hD : (D.subgroupOf (centralizer (P : Set G))).IsCComponent)
    (hlayer : D ≤ componentLayer G) :
    ∃ J : Subgroup G, IsComponent G J ∧ D ≤ componentOrbit J P := by
  classical
  let A := P
  let ι := {Q : Subgroup G // ∃ J : Subgroup G, IsComponent G J ∧ Q = componentOrbit J A}
  let K : ι → Subgroup G := Subtype.val
  have hcomm : ∀ i j, i ≠ j → K i ≤ centralizer (K j : Set G) := by
    intro i j hij
    obtain ⟨L, hL, hLi⟩ := i.property
    obtain ⟨M, hM, hMj⟩ := j.property
    change i.val ≤ centralizer (j.val : Set G)
    rw [hLi, hMj]
    exact distinct_componentOrbits_commute hL hM A (fun he =>
      hij (Subtype.ext (hLi.trans (he.trans hMj.symm))))
  have hn : ∀ i, A ≤ Subgroup.normalizer (K i : Set G) := by
    intro i
    obtain ⟨L, hL, hLi⟩ := i.property
    change A ≤ Subgroup.normalizer (i.val : Set G)
    rw [hLi]
    exact le_normalizer_componentOrbit L A
  have hcover : componentLayer G ≤ ⨆ i, K i := by
    apply sSup_le
    intro J hJ
    exact (le_componentOrbit J A).trans (le_iSup K ⟨componentOrbit J A, J, hJ, rfl⟩)
  obtain ⟨i, hi⟩ := component_le_commuting_family K P hDC hD hcomm hn (hlayer.trans hcover)
  obtain ⟨J, hJ, he⟩ := i.property
  exact ⟨J, hJ, he ▸ hi⟩

end Subgroup

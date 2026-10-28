module

public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Outer.Defs
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.CentralProduct

/-!
# Reducing J.2.6 to the outer-involution orbit

The natural Q/H_C coordinates move every element of Q outside H_C into
L outside S. For an L-conjugate A of U, J.2.2(5) gives an image of order two
under the literal H → H/Q map and A ∩ H_C = V. Thus A ∩ Q has order sixteen,
whereas V has order eight. An element of their difference is an involution
fused to z, using the proved U-fusion theorem.

The last theorem uses this seed and transport from L outside S to H outside K
to deduce every fusion clause of J.2.6 from the outer orbit and its count.
Transport, transitivity and the count are explicit remaining obligations;
this module does not claim to have completed J.2.5 or J.2.6.

Source: Aschbacher–Smith, J.2.6, printed pp.434–435 (PDF pp.445–446
of `refs/quasithin.pdf`). The natural head and conjugate geometry are
preceding J.2.2–3 conclusions, not new type-Ru hypotheses.
-/

public section
open Subgroup Representation
noncomputable section
namespace CFSG.Quasithin.ChapterJ.Fusion.Outer
variable {G : Type*} [Group G] [Finite G]

/-- The relative index is the order of the literal image under H → H/Q. -/
theorem relativeIndex_eq_star_card (d : TypeRuSetup G) (A : Subgroup G) (hA : A ≤ d.H) :
    (d.Q.subgroupOf A).index = Nat.card ((A.subgroupOf d.H).map d.ru2.quotientMap) := by
  have h := relIndex_ker (A.subgroupOf d.H) d.ru2.quotientMap
  rw [d.ru2.quotient_kernel] at h
  change (d.Q.comap d.H.subtype).relIndex (A.subgroupOf d.H) = _ at h
  rw [relIndex_comap, map_subgroupOf_eq_of_le hA] at h
  exact h

theorem NaturalHead.conjugate_difference {d : TypeRuSetup G} (head : NaturalHead d)
    {x y : G} (hx : x ∈ d.Q) (hy : y ∈ d.Q)
    (hxC : x ∉ d.HC) (hyC : y ∉ d.HC) :
    ∃ h : d.H, ((h : G) * x * (h : G)⁻¹) * y⁻¹ ∈ d.HC := by
  let xQ : d.Q := ⟨x, hx⟩
  let yQ : d.Q := ⟨y, hy⟩
  have hx0 : (head.sectionData.coordinates xQ).toAdd ≠ 0 :=
    fun h => hxC ((head.sectionData.coordinates_eq_one_iff xQ).mp h)
  have hy0 : (head.sectionData.coordinates yQ).toAdd ≠ 0 :=
    fun h => hyC ((head.sectionData.coordinates_eq_one_iff yQ).mp h)
  obtain ⟨g, hg⟩ := SL2FourNatural.transitive_nonzero _ _ hx0 hy0
  obtain ⟨h, hh⟩ := d.ru2.quotient_surjective (head.action.marking g)
  let c : d.Q := ⟨(h : G) * x * (h : G)⁻¹,
    (mem_normalizer_iff.mp (head.sectionData.normalized h.property) x).mp hx⟩
  have hc : head.sectionData.coordinates c = head.sectionData.coordinates yQ := by
    apply Multiplicative.toAdd.injective
    calc
      _ = head.action.action (d.ru2.quotientMap h)
          (head.sectionData.coordinates xQ).toAdd := head.sectionData.equivariant h xQ
      _ = _ := by rw [hh, head.action.restriction]; exact hg
  refine ⟨h, (head.sectionData.coordinates_eq_one_iff (c * yQ⁻¹)).mp ?_⟩
  rw [map_mul, map_inv, hc, mul_inv_cancel]

theorem conjugate_Q_outside_S (d : TypeRuSetup G) (head : NaturalHead d)
    (hQL : d.Q ≤ d.L) (hCS : d.HC ≤ d.S) (hQS : ¬ d.Q ≤ d.S)
    {x : G} (hx : x ∈ d.Q) (hxC : x ∉ d.HC) :
    ∃ h : d.H, (h : G) * x * (h : G)⁻¹ ∈ d.L ∧
      (h : G) * x * (h : G)⁻¹ ∉ d.S := by
  obtain ⟨y, hyQ, hyS⟩ : ∃ y : G, y ∈ d.Q ∧ y ∉ d.S := by
    by_contra! hn
    exact hQS hn
  obtain ⟨h, hh⟩ := head.conjugate_difference hx hyQ hxC (fun hyC => hyS (hCS hyC))
  refine ⟨h, hQL ((mem_normalizer_iff.mp (head.sectionData.normalized h.property) x).mp hx), ?_⟩
  intro hcS
  have he := d.S.mul_mem (d.S.inv_mem (hCS hh)) hcS
  apply hyS
  convert he using 1; group

theorem fusion_Q_of_fusion_L (d : TypeRuSetup G) (head : NaturalHead d)
    (hQL : d.Q ≤ d.L) (hCS : d.HC ≤ d.S) (hQS : ¬ d.Q ≤ d.S)
    {z : G} (he : ElementaryFusion d z)
    (hL : ∀ i ∈ involutionsOutside d.L d.S, IsConj i z) :
    ∀ i ∈ d.Q, orderOf i = 2 → IsConj i z := by
  intro i hi hi2
  by_cases hiC : i ∈ d.HC
  · have hiU := (omegaOneAmbient_le_iff d.HC d.U).mp he.1.le i hiC
      (hi2 ▸ pow_orderOf_eq_one i)
    exact he.2.2 i hiU (by intro hi1; simp [hi1] at hi2)
  obtain ⟨h, hhL, hhS⟩ := conjugate_Q_outside_S d head hQL hCS hQS hi hiC
  have hconj : IsConj i ((h : G) * i * (h : G)⁻¹) := isConj_iff.mpr ⟨h, rfl⟩
  apply hconj.trans (hL _ ⟨hhL, hhS, ?_⟩)
  exact ((MulAut.conj (h : G)).orderOf_eq i).trans hi2

theorem exists_Q_seed_of_conjugate (d : TypeRuSetup G)
    (hZ : Nat.card d.Z = 2) (hZV : d.Z ≤ d.V)
    {z : G} (hz : z ∈ d.Z) (hz1 : z ≠ 1) (l : G)
    (hindex : (d.Q.subgroupOf (d.U.map (MulAut.conj l).toMonoidHom)).index = 2)
    (hinter : d.U.map (MulAut.conj l).toMonoidHom ⊓ d.HC = d.V) :
    ∃ x : G, x ∈ d.Q ∧ x ∉ d.HC ∧ orderOf x = 2 ∧ IsConj x z := by
  let A := d.U.map (MulAut.conj l).toMonoidHom
  have hA : Nat.card A = 32 := by
    rw [card_map_of_injective (MulAut.conj l).injective, d.ru2.card_U hZ]
  have hAQ : Nat.card (d.Q.subgroupOf A) = 16 := by
    have hc := (d.Q.subgroupOf A).card_mul_index
    rw [hindex, hA] at hc
    omega
  obtain ⟨x, hxC⟩ : ∃ x : d.Q.subgroupOf A, ((x : A) : G) ∉ d.HC := by
    by_contra! hn
    have hle : d.Q.subgroupOf A ≤ d.V.subgroupOf A := by
      intro x hx
      change (x : G) ∈ d.V
      rw [← hinter]
      exact ⟨x.property, hn ⟨x, hx⟩⟩
    have hVA : d.V ≤ A := by rw [← hinter]; exact inf_le_left
    have he : Nat.card (d.V.subgroupOf A) = Nat.card d.V :=
      Nat.card_congr (subgroupOfEquivOfLe hVA).toEquiv
    have hc' := card_le_of_le hle
    rw [hAQ, he, d.ru1.card_V] at hc'
    omega
  obtain ⟨u, hu, heu⟩ := (x : A).property
  have hxQ : ((x : A) : G) ∈ d.Q := x.property
  have hx1 : ((x : A) : G) ≠ 1 := by
    intro hx1
    exact hxC (hx1 ▸ d.HC.one_mem)
  have hu1 : u ≠ 1 := by
    intro hu1
    apply hx1
    rw [← heu, hu1, map_one]
  let := d.elementary_U_of_card_Z hZ
  have hx2 : (((x : A) : G)) ^ 2 = 1 := by
    rw [← heu, ← map_pow, elemPow_eq_one_of_isElementaryAbelian u hu, map_one]
  refine ⟨x, hxQ, hxC, orderOf_eq_prime hx2 hx1, ?_⟩
  have hux : IsConj u (((x : A) : G)) := isConj_iff.mpr ⟨l, heu⟩
  exact hux.symm.trans (d.fusion_U hZ hZV hz hz1 hu hu1)

/-- The conjugate needed in J.2.6 exists because L is larger than H. -/
theorem exists_L_not_H (d : TypeRuSetup G) (hZ : Nat.card d.Z = 2) :
    ∃ l : d.L, (l : G) ∉ d.H := by
  by_contra! hn
  have hc := card_le_of_le (show d.L ≤ d.H from fun l hl => hn ⟨l, hl⟩)
  rw [d.ru1.card_L, d.ru2.card_H hZ] at hc
  omega

theorem exists_Q_seed (d : TypeRuSetup G)
    (hZ : Nat.card d.Z = 2) (hZV : d.Z ≤ d.V)
    {z : G} (hz : z ∈ d.Z) (hz1 : z ≠ 1)
    (hconjugates : ∀ l : d.L, (l : G) ∉ d.H →
      (d.Q.subgroupOf (d.U.map (MulAut.conj (l : G)).toMonoidHom)).index = 2 ∧
        d.U.map (MulAut.conj (l : G)).toMonoidHom ⊓ d.HC = d.V) :
    ∃ x : G, x ∈ d.Q ∧ x ∉ d.HC ∧ orderOf x = 2 ∧ IsConj x z := by
  obtain ⟨l, hl⟩ := exists_L_not_H d hZ
  exact exists_Q_seed_of_conjugate d hZ hZV hz hz1 l
    (hconjugates l hl).1 (hconjugates l hl).2

/-- J.2.2(5), stated using its actual quotient image, supplies the seed. -/
theorem exists_Q_seed_of_source_conjugates (d : TypeRuSetup G)
    (hZ : Nat.card d.Z = 2) (hZV : d.Z ≤ d.V)
    {z : G} (hz : z ∈ d.Z) (hz1 : z ≠ 1)
    (hconjugates : ∀ l : d.L, (l : G) ∉ d.H →
      let A := d.U.map (MulAut.conj (l : G)).toMonoidHom
      A ≤ d.H ∧ Nat.card ((A.subgroupOf d.H).map d.ru2.quotientMap) = 2 ∧
        A ⊓ d.HC = d.V) :
    ∃ x : G, x ∈ d.Q ∧ x ∉ d.HC ∧ orderOf x = 2 ∧ IsConj x z := by
  apply exists_Q_seed d hZ hZV hz hz1
  intro l hl
  obtain ⟨hA, hcard, hinter⟩ := hconjugates l hl
  exact ⟨(relativeIndex_eq_star_card d _ hA).trans hcard, hinter⟩

theorem exists_outer_seed (d : TypeRuSetup G) (head : NaturalHead d)
    (hQL : d.Q ≤ d.L) (hCS : d.HC ≤ d.S) (hQS : ¬ d.Q ≤ d.S)
    {z : G} (hseed : ∃ x : G, x ∈ d.Q ∧ x ∉ d.HC ∧ orderOf x = 2 ∧ IsConj x z)
    (htransport : ∀ i ∈ involutionsOutside d.L d.S,
      ∃ j ∈ involutionsOutside d.H d.K, IsConj i j) :
    ∃ j ∈ involutionsOutside d.H d.K, IsConj j z := by
  obtain ⟨x, hxQ, hxC, hx2, hxz⟩ := hseed
  obtain ⟨h, hhL, hhS⟩ := conjugate_Q_outside_S d head hQL hCS hQS hxQ hxC
  have hh2 : orderOf ((h : G) * x * (h : G)⁻¹) = 2 :=
    ((MulAut.conj (h : G)).orderOf_eq x).trans hx2
  obtain ⟨j, hj, hxj⟩ := htransport _ ⟨hhL, hhS, hh2⟩
  exact ⟨j, hj, hxj.symm.trans
    ((isConj_iff.mpr ⟨(h : G), rfl⟩).symm.trans hxz)⟩

/-- The source's reduction of all fusion clauses to the single outer orbit.
The transport and orbit hypotheses remain genuine obligations. -/
theorem sourceJ26_of_outer_orbit (d : TypeRuSetup G) (head : NaturalHead d)
    (B : Sylow 3 d.L₁) (cp : CentralProductData d B)
    (hZ : Nat.card d.Z = 2) (hZV : d.Z ≤ d.V)
    (hQL : d.Q ≤ d.L) (hCS : d.HC ≤ d.S) (hQS : ¬ d.Q ≤ d.S)
    {z : G} (hz : z ∈ d.Z) (hz1 : z ≠ 1)
    (hconjugates : ∀ l : d.L, (l : G) ∉ d.H →
      (d.Q.subgroupOf (d.U.map (MulAut.conj (l : G)).toMonoidHom)).index = 2 ∧
        d.U.map (MulAut.conj (l : G)).toMonoidHom ⊓ d.HC = d.V)
    (htransport : ∀ i ∈ involutionsOutside d.L d.S,
      ∃ j ∈ involutionsOutside d.H d.K, IsConj i j)
    (htrans : TransitiveOn d.H (involutionsOutside d.H d.K))
    (hcard : Nat.card (involutionsOutside d.H d.K) = 640) : SourceJ26 d z := by
  obtain ⟨j, hj, hjz⟩ := exists_outer_seed d head hQL hCS hQS
    (exists_Q_seed d hZ hZV hz hz1 hconjugates) htransport
  have houter : ∀ i ∈ involutionsOutside d.H d.K, IsConj i z := by
    intro i hi
    obtain ⟨h, hh⟩ := htrans hi hj
    exact (isConj_iff.mpr ⟨(h : G), hh⟩).trans hjz
  have hL : ∀ i ∈ involutionsOutside d.L d.S, IsConj i z := by
    intro i hi
    obtain ⟨j, hj, hij⟩ := htransport i hi
    exact hij.trans (houter j hj)
  have he := elementaryFusion_of_centralProduct d B cp hZ hZV hz hz1
  exact ⟨⟨htrans, hcard, houter⟩, hL,
    fusion_Q_of_fusion_L d head hQL hCS hQS he hL, he⟩

end CFSG.Quasithin.ChapterJ.Fusion.Outer

module
public import Theory.GroupTheory.FrattiniHyperplaneNormalizer
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
/-!
# Odd prime sections in hyperplane quotients

An odd prime line moved by an elementary two-group, modulo a fixing
hyperplane, is a self-centralizing minimal normal subgroup of index two.
The quotient retains failure of coverage by an original overgroup of the
hyperplane. A relative Frattini product identifies the corresponding
quotient in the actual normalizer, with the quotient maps specified.

Source: GLS, Number 2, G.26.18(a), printed pp.152–153.
-/

public section
open Subgroup
open scoped IsMulCommutative Pointwise
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- The odd prime image has index two and is self-centralizing and minimal. -/
theorem prime_hyperplane_quotient (D A B : Subgroup G) [D.Normal] [B.Normal]
    {r : ℕ} [Fact r.Prime] (hc : Nat.card D = r)
    (hBA : B ≤ A) (hi : B.relIndex A = 2) (hd : Disjoint D A)
    (hg : D ⊔ A = ⊤) (hm : ⁅D,A⁆ = D) :
    let Y := D.map (QuotientGroup.mk' B)
    Nat.card Y = r ∧ Y.index = 2 ∧
      centralizer (Y : Set (G ⧸ B)) ≤ Y ∧
      (∀ Z : Subgroup (G ⧸ B), Z ≤ Y → Z = ⊥ ∨ Z = Y) := by
  let q := QuotientGroup.mk' B
  let Y := D.map q
  have hDB : D ⊓ B = ⊥ := bot_unique ((inf_le_inf_left D hBA).trans hd.eq_bot.le)
  have hcard : Nat.card Y = r := by
    rw [←relIndex_ker,QuotientGroup.ker_mk',←inf_relIndex_left,hDB,relIndex_bot_left,hc]
  have hix : (D ⊔ B) ⊓ A = B := by
    apply le_antisymm _ (le_inf le_sup_right hBA)
    rintro x ⟨hx,hxA⟩
    obtain ⟨d,hd',b,hb,rfl⟩ := mem_sup_of_normal_left.mp hx
    have hdA : d ∈ A := by
      have hh := A.mul_mem hxA (A.inv_mem (hBA hb))
      simpa only [mul_inv_cancel_right] using hh
    have he : d = 1 := mem_bot.mp (hd.eq_bot ▸ (show d ∈ D ⊓ A from ⟨hd',hdA⟩))
    simpa only [he,one_mul] using hb
  have hidx : Y.index = 2 := by
    rw [index_map D q, q.range_eq_top_of_surjective (QuotientGroup.mk'_surjective B),
      index_top,mul_one,QuotientGroup.ker_mk']
    have hgen : (D ⊔ B) ⊔ A = ⊤ := by rw [sup_assoc,sup_of_le_right hBA,hg]
    rw [←relIndex_top_right,←hgen,relIndex_sup_left,←inf_relIndex_right,hix,hi]
  have hne : Y ≠ ⊥ := by
    intro he
    have hh : Nat.card Y = 1 := (eq_bot_iff_card Y).mp he
    have := (Fact.out : r.Prime).one_lt
    omega
  have hYY : Y ≤ centralizer (Y : Set (G ⧸ B)) := by
    let : IsCyclic Y := isCyclic_of_prime_card hcard
    intro y hy z hz
    exact congrArg Subtype.val (mul_comm (⟨z,hz⟩ : Y) ⟨y,hy⟩)
  have hcent : centralizer (Y : Set (G ⧸ B)) ≤ Y := by
    have hdiv := index_dvd_of_le hYY
    rw [hidx] at hdiv
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hone | htwo
    · have ht := index_eq_one.mp hone
      have hz : ⁅Y,A.map q⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
        (le_centralizer_iff.mp (by rw [ht]; exact le_top))
      have hh := congrArg (map q) hm
      rw [map_commutator] at hh
      exact (hne (hz ▸ hh.symm)).elim
    · by_contra hh
      have hlt := index_strictAnti (lt_iff_le_not_ge.mpr ⟨hYY,hh⟩)
      omega
  refine ⟨hcard,hidx,hcent,?_⟩
  intro Z hZY
  have hdvd := card_dvd_of_le hZY
  rw [hcard] at hdvd
  rcases (Nat.dvd_prime (Fact.out : r.Prime)).mp hdvd with h1 | hr
  · exact Or.inl ((eq_bot_iff_card Z).mpr h1)
  · exact Or.inr (eq_of_le_of_card_ge hZY (show Nat.card Y ≤ Nat.card Z by rw [hcard,hr]))

omit [Finite G] in
/-- The original odd line remains uncovered after quotienting by a subgroup
already contained in the covering candidate. -/
theorem map_not_le_map_of_kernel_le {K : Type*} [Group K]
    (f : G →* K) (D V : Subgroup G) (hker : f.ker ≤ V) (hn : ¬ D ≤ V) :
    ¬ D.map f ≤ V.map f := by
  intro hh
  apply hn
  have hc := (le_comap_map f D).trans (comap_mono hh)
  rwa [comap_map_eq,sup_of_le_left hker] at hc

/-- The prime line and actor hyperplane give the literal self-centralizing
minimal normal section, retaining noncoverage by V. -/
theorem odd_line_hyperplane_section (D A B V : Subgroup G)
    {r : ℕ} [Fact r.Prime] (ho : Odd r) (hc : Nat.card D = r)
    [IsElementaryAbelian 2 A]
    (hBA : B ≤ A) (hi : B.relIndex A = 2)
    (hAD : A ≤ normalizer (D : Set G)) (hm : ⁅D,A⁆ = D)
    (hDB : D ≤ centralizer (B : Set G)) (hBV : B ≤ V) (hout : ¬ D ≤ V) :
    let H := D ⊔ A
    ∃ n : (B.subgroupOf H).Normal, letI := n
      let Y := (D.subgroupOf H).map (QuotientGroup.mk' (B.subgroupOf H))
      Y.Normal ∧ Nat.card Y = r ∧ Y.index = 2 ∧
        centralizer (Y : Set (H ⧸ B.subgroupOf H)) ≤ Y ∧
        (∀ Z : Subgroup (H ⧸ B.subgroupOf H), Z ≤ Y → Z = ⊥ ∨ Z = Y) ∧
        ¬ Y ≤ (V.subgroupOf H).map (QuotientGroup.mk' (B.subgroupOf H)) := by
  let H := D ⊔ A
  let D' := D.subgroupOf H
  let A' := A.subgroupOf H
  let B' := B.subgroupOf H
  have hDH : D ≤ H := le_sup_left
  have hAH : A ≤ H := le_sup_right
  have hBH : B ≤ H := hBA.trans hAH
  have hAB : A ≤ centralizer (B : Set G) := by
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm (⟨b,hBA hb⟩ : A) ⟨a,ha⟩)
  let n : B'.Normal := normal_subgroupOf_of_le_normalizer
    ((sup_le hDB hAB).trans (centralizer_le_normalizer _))
  let : D'.Normal := normal_subgroupOf_of_le_normalizer (sup_le D.le_normalizer hAD)
  have hdmap : D'.map H.subtype = D := map_subgroupOf_eq_of_le hDH
  have hamap : A'.map H.subtype = A := map_subgroupOf_eq_of_le hAH
  have hbmap : B'.map H.subtype = B := map_subgroupOf_eq_of_le hBH
  have hc' : Nat.card D' = r := by
    rw [←card_map_of_injective H.subtype_injective,hdmap,hc]
  have hi' : B'.relIndex A' = 2 := by
    rw [←relIndex_map_map_of_injective B' A' H.subtype_injective,hbmap,hamap,hi]
  have hpD : IsPGroup r D := IsPGroup.of_card (n := 1) (by simpa only [pow_one] using hc)
  have hd : Disjoint D A := hpD.disjoint_of_coprime
    (IsElementaryAbelian.isPGroup 2 A) ho.coprime_two_right
  have hd' : Disjoint D' A' := by
    apply disjoint_iff.mpr
    change D.comap H.subtype ⊓ A.comap H.subtype = ⊥
    rw [←comap_inf,hd.eq_bot,MonoidHom.comap_bot,H.subtype.ker_eq_bot H.subtype_injective]
  have hg' : D' ⊔ A' = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,hdmap,hamap,←MonoidHom.range_eq_map,H.range_subtype]
  have hm' : ⁅D',A'⁆ = D' := by
    apply map_injective H.subtype_injective
    rw [map_commutator,hdmap,hamap,hm]
  obtain ⟨hcY,hiY,hCY,hmin⟩ := prime_hyperplane_quotient D' A' B' hc'
    (subgroupOf_mono H hBA) hi' hd' hg' hm'
  refine ⟨n,Normal.map inferInstance _ (QuotientGroup.mk'_surjective _),hcY,hiY,hCY,hmin,?_⟩
  apply map_not_le_map_of_kernel_le
  · rw [QuotientGroup.ker_mk']
    exact subgroupOf_mono H hBV
  · intro hh
    have hh' := map_mono (f := H.subtype) hh
    rw [hdmap] at hh'
    exact hout (hh'.trans (by rw [subgroupOf_map_subtype]; exact inf_le_left))

omit [Finite G] in
/-- Frattini coverage identifies the literal quotient in N with the quotient
of the chosen subgroup in the original image. -/
theorem frattini_quotient_equiv {K : Type*} [Group K]
    (q : G →* K) (hq : Function.Surjective q) (J B : Subgroup K)
    [(B.subgroupOf J).Normal] (hBJ : B ≤ J)
    (N : Subgroup G) (hNJ : N ≤ J.comap q)
    (hNI : N ≤ normalizer (B.comap q : Set G))
    (hgen : N ⊔ B.comap q = J.comap q) :
    ∃ n : ((B.comap q).subgroupOf N).Normal, letI := n
      ∃ e : (N ⧸ (B.comap q).subgroupOf N) ≃* (J ⧸ B.subgroupOf J),
        ∀ x : N, e (QuotientGroup.mk' _ x) =
          QuotientGroup.mk' _ ⟨q x,hNJ x.property⟩ := by
  let n := normal_subgroupOf_of_le_normalizer hNI
  let f : N →* J := (q.comp N.subtype).codRestrict J (fun x => hNJ x.property)
  let φ : N →* (J ⧸ B.subgroupOf J) := (QuotientGroup.mk' _).comp f
  have hk : (B.comap q).subgroupOf N = φ.ker := by
    ext x
    exact (@QuotientGroup.eq_one_iff J _ (B.subgroupOf J) _ (f x)).symm
  have hs : Function.Surjective φ := by
    intro z
    obtain ⟨j,rfl⟩ := QuotientGroup.mk'_surjective (B.subgroupOf J) z
    obtain ⟨x,hx⟩ := hq j
    have hxH : x ∈ J.comap q := by change q x ∈ J; rw [hx]; exact j.property
    rw [←hgen] at hxH
    have hp : x ∈ (N : Set G) * (B.comap q : Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right N (B.comap q) hNI]
      exact hxH
    obtain ⟨a,ha,b,hb,rfl⟩ := hp
    refine ⟨⟨a,ha⟩,?_⟩
    have hj : j = f ⟨a,ha⟩ * (⟨q b,hBJ hb⟩ : J) := Subtype.ext (hx.symm.trans (q.map_mul a b))
    rw [hj,map_mul]
    have hb1 : QuotientGroup.mk' (B.subgroupOf J) (⟨q b,hBJ hb⟩ : J) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hb
    rw [hb1,mul_one]
    rfl
  exact ⟨n,QuotientGroup.liftEquiv _ hs hk,fun _ => rfl⟩
end Theory.GroupTheory

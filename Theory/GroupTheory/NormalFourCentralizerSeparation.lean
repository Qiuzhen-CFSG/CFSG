module

public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.NormalFourCentralizer

/-!
# Separating involutions by Sylow centralizer order

A p-subgroup which is Sylow in a local subgroup remains Sylow in a larger
subgroup if its normalizer in the larger subgroup stays local. The normalizer
index congruence proves this without choosing additional Sylow representatives.
Conjugate elements have centralizers of the same order, so a Sylow subgroup of
one centralizer cannot be smaller than a p-subgroup of the other.

For a normal elementary four in a Sylow two-subgroup S, each element centralizer
has order at least |S|/2. Thus an element with a smaller Sylow centralizer avoids
all ambient conjugacy classes meeting that four.

Source motivation: Janko–Thompson, Math. Z. 113 (1970), §4, printed pp.392–393,
the final centralizer comparison in Case 1. The local Sylow and normalizer
hypotheses below are explicit; the application must establish its geometry.
-/

open Subgroup

namespace Subgroup

/-- Normalizer control promotes local Sylow maximality, expressed by relative index. -/
public theorem not_dvd_relIndex_of_normalizer_inf_le
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (Q L C : Subgroup G) (hp : IsPGroup p Q)
    (hQC : Q ≤ C)
    (hlocal : ¬ p ∣ Q.relIndex L)
    (hcontrol : normalizer (Q : Set G) ⊓ C ≤ L) :
    ¬ p ∣ Q.relIndex C := by
  let R := Q.subgroupOf C
  have hR : IsPGroup p R := hp.comap_subtype
  have hnormalizer : normalizer (R : Set C) =
      (normalizer (Q : Set G) ⊓ C).subgroupOf C := by
    change normalizer (Q.subgroupOf C : Set C) = _
    rw [inf_subgroupOf_right, subgroupOf_normalizer_eq hQC]
  have hindex : R.relIndex (normalizer (R : Set C)) =
      Q.relIndex (normalizer (Q : Set G) ⊓ C) := by
    rw [hnormalizer]
    exact relIndex_subgroupOf inf_le_right
  have hdiv : Q.relIndex (normalizer (Q : Set G) ⊓ C) ∣ Q.relIndex L :=
    dvd_of_mul_right_eq _ (relIndex_mul_relIndex Q _ L
      (le_inf le_normalizer hQC) hcontrol)
  obtain ⟨n, hn⟩ := hR.exists_card_eq
  have hcongr := Sylow.card_quotient_normalizer_modEq_card_quotient hn
  intro h
  apply hlocal
  apply dvd_trans _ hdiv
  rw [← hindex]
  exact (hcongr.dvd_iff dvd_rfl).mpr h

end Subgroup

/-- Conjugate elements cannot have a Sylow centralizer subgroup smaller than
another p-subgroup of the other element centralizer. -/
public theorem Subgroup.not_isConj_of_sylow_centralizer_card_lt
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (x y : G) (Q R : Subgroup G)
    (hQ : IsPGroup p Q) (hR : IsPGroup p R)
    (hQx : Q ≤ centralizer ({x} : Set G))
    (hRy : R ≤ centralizer ({y} : Set G))
    (hmax : ¬ p ∣ Q.relIndex (centralizer ({x} : Set G)))
    (hsmall : Nat.card Q < Nat.card R) : ¬ IsConj x y := by
  intro hconj
  let C := centralizer ({x} : Set G)
  let D := centralizer ({y} : Set G)
  have hcard : Nat.card D = Nat.card C := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    let f : G ≃* G := MulAut.conj g
    have hfx : f x = y := hg
    apply (Nat.card_congr (Equiv.subtypeEquiv f.toEquiv ?_)).symm
    intro a
    change a ∈ C ↔ f a ∈ D
    simp only [C, D, mem_centralizer_singleton_iff]
    constructor
    · intro ha
      simpa only [map_mul, hfx] using congrArg f ha
    · intro ha
      apply f.injective
      simpa only [map_mul, hfx] using ha
  let P : Sylow p C := (hQ.comap_subtype : IsPGroup p (Q.subgroupOf C)).toSylow hmax
  obtain ⟨T, hT⟩ := (hR.comap_subtype : IsPGroup p (R.subgroupOf D)).exists_le_sylow
  have hTP : Nat.card T = Nat.card P := by
    rw [T.card_eq_multiplicity, P.card_eq_multiplicity, hcard]
  have hPc : Nat.card P = Nat.card Q :=
    Nat.card_congr (subgroupOfEquivOfLe hQx).toEquiv
  have hRc : Nat.card (R.subgroupOf D) = Nat.card R :=
    Nat.card_congr (subgroupOfEquivOfLe hRy).toEquiv
  have hle := card_le_of_le hT
  change Nat.card (R.subgroupOf D) ≤ Nat.card T at hle
  rw [hRc, hTP, hPc] at hle
  exact hsmall.not_ge hle

/-- A sufficiently small centralizer, Sylow in the local common centralizer
and with its normalizer still local, avoids every class of a normal four. -/
public theorem Sylow.not_isConj_mem_normal_four_of_local_centralizer
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4) (z x : S)
    (hlocal : ¬ 2 ∣ ((centralizer ({x} : Set S)).map (S : Subgroup G).subtype).relIndex
      (centralizer ({(z : G)} : Set G) ⊓ centralizer ({(x : G)} : Set G)))
    (hcontrol : normalizer
      (((centralizer ({x} : Set S)).map (S : Subgroup G).subtype : Subgroup G) : Set G) ≤
      centralizer ({(z : G)} : Set G))
    (hsmall : 2 * Nat.card (centralizer ({x} : Set S)) < Nat.card S) :
    ∀ w : S, w ∈ W → ¬ IsConj (x : G) (w : G) := by
  let Q := (centralizer ({x} : Set S)).map (S : Subgroup G).subtype
  have hQ : IsPGroup 2 Q := (S.isPGroup'.to_subgroup _).map (S : Subgroup G).subtype
  have hQx : Q ≤ centralizer ({(x : G)} : Set G) := by
    simpa [Q] using
      map_centralizer_le_centralizer_image ({x} : Set S) (S : Subgroup G).subtype
  have hmax : ¬ 2 ∣ Q.relIndex (centralizer ({(x : G)} : Set G)) :=
    Subgroup.not_dvd_relIndex_of_normalizer_inf_le Q _ _ hQ hQx hlocal
      (le_inf (inf_le_left.trans hcontrol) inf_le_right)
  intro w hw
  let R := (centralizer ({w} : Set S)).map (S : Subgroup G).subtype
  have hR : IsPGroup 2 R := (S.isPGroup'.to_subgroup _).map (S : Subgroup G).subtype
  have hRw : R ≤ centralizer ({(w : G)} : Set G) := by
    simpa [R] using
      map_centralizer_le_centralizer_image ({w} : Set S) (S : Subgroup G).subtype
  apply Subgroup.not_isConj_of_sylow_centralizer_card_lt (x : G) (w : G) Q R hQ hR hQx hRw hmax
  have hi := centralizer_index_le_two_of_normal_four S.isPGroup' W hW
  have hcard := (centralizer (W : Set S)).index_mul_card
  have hle : Nat.card (centralizer (W : Set S)) ≤
      Nat.card (centralizer ({w} : Set S)) :=
    card_le_of_le (centralizer_le (Set.singleton_subset_iff.mpr hw))
  change Nat.card ((centralizer ({x} : Set S)).map (S : Subgroup G).subtype) <
    Nat.card ((centralizer ({w} : Set S)).map (S : Subgroup G).subtype)
  rw [card_map_of_injective (S : Subgroup G).subtype_injective,
    card_map_of_injective (S : Subgroup G).subtype_injective]
  nlinarith

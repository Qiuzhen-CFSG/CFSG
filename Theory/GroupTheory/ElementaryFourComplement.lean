module
public import Theory.ElementaryAbelian.Injective
public import Theory.Representation.CoprimeElementaryComplement
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Invariant four-group complements in elementary sixteen-groups

A coprime actor normalizing an elementary sixteen-group and a four-subgroup
has an invariant four-group complement, by Maschke's theorem on the actual
conjugation action. The resulting subgroup retains its ambient inclusion
and normalization statement.

The companion order argument shows that a four-group in a group of order
sixty-four, disjoint from an index-four intersection with a normalized
subgroup, supplements that subgroup in their join. It uses cardinalities
inside the finite group and requires no finiteness of the ambient group.

Source application: Delgado--Goldschmidt--Stellmacher, Groups and Graphs
(1985), the two complements in (10.9), p.163, used by (5.16), pp.116--117.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

theorem invariant_four_complement (A Z T : Subgroup G) [Finite A] [Finite T]
    [IsElementaryAbelian 2 A] (hZA : Z ≤ A) (hA : Nat.card A = 16) (hZ : Nat.card Z = 4)
    (hcop : Nat.Coprime 2 (Nat.card T))
    (hTA : T ≤ normalizer (A : Set G)) (hTZ : T ≤ normalizer (Z : Set G)) :
    ∃ D : Subgroup G, D ≤ A ∧ Nat.card D = 4 ∧ IsElementaryAbelian 2 D ∧
      Disjoint Z D ∧ Z ⊔ D = A ∧ T ≤ normalizer (D : Set G) := by
  let Z₀ := Z.subgroupOf A
  let ρ : T →* MulAut A := A.normalizerMonoidHom.comp (inclusion hTA)
  have hs : ∀ t : T, ∀ x ∈ Z₀, ρ t x ∈ Z₀ := by
    intro t x hx
    exact (mem_normalizer_iff.mp (hTZ t.property) x).mp hx
  obtain ⟨D,hD,hDs⟩ := IsElementaryAbelian.exists_invariant_complement ρ hcop Z₀ hs
  have hZ₀ : Nat.card Z₀ = 4 := (Nat.card_congr (subgroupOfEquivOfLe hZA).toEquiv).trans hZ
  have hDc : Nat.card D = 4 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes Z₀ D
      (by rw [normalizer_eq_top]; exact le_top)
    rw [hD.inf_eq_bot,hD.sup_eq_top,card_bot,card_top,one_mul,hZ₀,hA] at hh
    omega
  let D₀ := D.map A.subtype
  have hmapZ : Z₀.map A.subtype = Z := map_subgroupOf_eq_of_le hZA
  have hgen : Z ⊔ D₀ = A := by
    have hh := congrArg (Subgroup.map A.subtype) hD.sup_eq_top
    simpa only [Subgroup.map_sup,hmapZ,←MonoidHom.range_eq_map,range_subtype] using hh
  have hd : Disjoint Z D₀ := by
    have hh := disjoint_map A.subtype_injective hD.disjoint
    rwa [hmapZ] at hh
  have hn : T ≤ normalizer (D₀ : Set G) := by
    apply le_normalizer_iff.mpr
    rintro t ht _ ⟨x,hx,rfl⟩
    exact mem_map_of_mem A.subtype (hDs ⟨t,ht⟩ x hx)
  refine ⟨D₀,map_subtype_le _,?_,?_,hd,hgen,hn⟩
  · rw [card_map_of_injective A.subtype_injective,hDc]
  · let : IsElementaryAbelian 2 D := IsElementaryAbelian.of_injective D.subtype D.subtype_injective
    exact IsElementaryAbelian.map A.subtype

theorem sup_eq_of_disjoint_four (Q R D : Subgroup G) [Finite Q]
    (hQ : Nat.card Q = 64) (hI : Nat.card (R.subgroupOf Q) = 16)
    (hDQ : D ≤ Q) (hD : Nat.card D = 4) (hd : Disjoint R D)
    (hn : Q ≤ normalizer (R : Set G)) : R ⊔ D = R ⊔ Q := by
  let A := R.subgroupOf Q
  let B := D.subgroupOf Q
  let : A.Normal := normal_subgroupOf_of_le_normalizer hn
  have hdAB : Disjoint A B := by
    apply Subgroup.disjoint_def.mpr
    intro x hxA hxB
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp hd hxA hxB
  have hBc : Nat.card B = 4 := (Nat.card_congr (subgroupOfEquivOfLe hDQ).toEquiv).trans hD
  have hgen : A ⊔ B = ⊤ := by
    apply eq_top_of_card_eq
    rw [card_sup_eq_mul_of_normalizes_of_disjoint A B le_normalizer_of_normal hdAB,
      hI,hBc,hQ]
  have hmap : (R ⊓ Q) ⊔ D = Q := by
    have hh := congrArg (Subgroup.map Q.subtype) hgen
    dsimp only [A,B] at hh
    simpa only [Subgroup.map_sup,subgroupOf_map_subtype,inf_eq_left.mpr hDQ,
      ←MonoidHom.range_eq_map,range_subtype] using hh
  apply le_antisymm (sup_le le_sup_left (hDQ.trans le_sup_right))
  apply sup_le le_sup_left
  rw [←hmap]
  exact sup_le (inf_le_left.trans le_sup_left) le_sup_right
end Theory.GroupTheory

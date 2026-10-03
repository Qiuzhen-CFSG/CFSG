module

public import Stellmacher.Recognition.Parrott.OmegaOrbit
public import Stellmacher.Recognition.Parrott.OmegaStabilizer
public import Theory.GroupTheory.ElementarySixteenSolvableTwoFive

/-!
# The order-sixteen case of Parrott's outer-fusion argument

Let H=C_G(z), J=O₂(H), and E be the ambient image of J′. If z is weakly
closed in E and G is an N₂-group, the normalizer of the fixed join
⟨y⟩ ∨ C_E(y) is contained in H for every outer involution y of H.
If its normalizer moved z, the order-sixteen orbit calculation would give
an orbit of length five. The solvable action image would have order 2^n·5
while containing the elementary order-four image of E, contrary to the
solvable automorphism bound.

The fixed join always lies in the actual Ω₁(C_H(y)) and has order sixteen.
If that omega subgroup also has order sixteen, they are equal. When y is
fused to z, the generalized normalizer-movement theorem contradicts the
preceding containment. This uses only weak closure, without assuming
that all core involutions belong to E.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
Lemma 3 on p.675 and the order-sixteen case in the first paragraph of p.676.
-/

open Subgroup

namespace Stellmacher.Recognition

/-- Weak closure in the derived core confines the fixed-join normalizer to H. -/
public theorem parrott_outer_fixed_join_normalizer_le_centralizer
    {G : Type*} [Group G] [Finite G]
    (hN : IsNTwoGroup G) (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    (∀ t : G, t ∈ E → IsConj z t → t = z) →
    ∀ y : H, orderOf y = 2 → y ∉ J →
      normalizer ((zpowers (y : G) ⊔
        (E ⊓ centralizer ({(y : G)} : Set G)) : Subgroup G) : Set G) ≤ H := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  change (∀ t : G, t ∈ E → IsConj z t → t = z) → _
  intro hweak y hy hyJ
  let Z := E ⊓ centralizer ({(y : G)} : Set G)
  let X := zpowers (y : G) ⊔ Z
  change normalizer (X : Set G) ≤ H
  by_contra hnot
  let N := normalizer (X : Set G)
  let T := H.subgroupOf N
  obtain ⟨hEcard, hZcard, hXcard, hEelem, hXelem, hzZ, hZX, _, hEN, hCX, _, _⟩ :=
    parrott_outer_fixed_join_geometry z h y hy hyJ
  change E ≤ N at hEN
  change E ⊓ centralizer (X : Set G) = Z at hCX
  let : IsElementaryAbelian 2 E := hEelem
  let : IsElementaryAbelian 2 X := hXelem
  have hzX : z ∈ X := hZX hzZ
  have hXne : X ≠ ⊥ := by
    intro hbot
    change Nat.card X = 16 at hXcard
    rw [hbot, card_bot] at hXcard
    omega
  let : Group.IsSolvable N := hN N ⟨X, hXne, IsElementaryAbelian.isPGroup 2 X, rfl⟩
  let f : N →* MulAut X := X.normalizerMonoidHom
  let K := f.range
  have hKsolv : Group.IsSolvable K := Group.isSolvable_of_surjective f.rangeRestrict_surjective
  have hkerT : f.rangeRestrict.ker ≤ T := by
    intro a ha
    have hfa : f a = 1 := congrArg (fun k : K => (k : MulAut X)) ha
    have hca : a ∈ f.ker := hfa
    change a ∈ X.normalizerMonoidHom.ker at hca
    rw [normalizerMonoidHom_ker] at hca
    exact mem_centralizer_singleton_iff.mpr (hca z hzX).symm
  have hTp : IsPGroup 2 T := parrott_outer_fixed_join_normalizer_stabilizer_isPGroup z h y hy hyJ
  have hTindex : T.index = 5 := parrott_outer_fixed_join_normalizer_index z h hweak y hy hyJ hnot
  obtain ⟨n, hn⟩ := (hTp.map f.rangeRestrict).exists_card_eq
  have hKcard : Nat.card K = 2 ^ n * 5 := by
    have hc := (T.map f.rangeRestrict).index_mul_card
    rw [T.index_map_eq f.rangeRestrict_surjective hkerT, hTindex, hn] at hc
    exact hc.symm.trans (Nat.mul_comm _ _)
  let EN := E.subgroupOf N
  let : IsElementaryAbelian 2 EN := IsElementaryAbelian.subgroupOf hEN
  let A : Subgroup K := EN.map f.rangeRestrict
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map f.rangeRestrict
  let g : EN →* K := f.rangeRestrict.comp EN.subtype
  let embed : EN →* G := N.subtype.comp EN.subtype
  have hembed : Function.Injective embed := N.subtype_injective.comp EN.subtype_injective
  have hker (a : EN) : a ∈ g.ker ↔ ((a : N) : G) ∈ centralizer (X : Set G) := by
    change f.rangeRestrict (a : N) = 1 ↔ _
    rw [Subtype.ext_iff]
    change (a : N) ∈ X.normalizerMonoidHom.ker ↔ _
    rw [normalizerMonoidHom_ker]
    rfl
  have hkerMap : g.ker.map embed = Z := by
    rw [← hCX]
    apply le_antisymm
    · rintro a ⟨b, hb, rfl⟩
      exact ⟨b.property, (hker b).mp hb⟩
    · intro a ha
      let b : EN := ⟨⟨a, hEN ha.1⟩, ha.1⟩
      exact ⟨b, (hker b).mpr ha.2, rfl⟩
  have hgker : Nat.card g.ker = 8 := by
    have hc := card_map_of_injective (K := g.ker) (f := embed) hembed
    rw [hkerMap] at hc
    exact hc.symm.trans hZcard
  have hENcard : Nat.card EN = 32 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEN).toEquiv).trans hEcard
  have hgrange : g.range = A := by
    rw [MonoidHom.range_comp, range_subtype]
  have hAcard : Nat.card A = 4 := by
    have hc := g.ker.card_mul_index
    rw [index_ker, hgker, hgrange, hENcard] at hc
    omega
  have hbound := card_elementary_two_le_two_of_solvable_aut16_two_five hXcard K hKsolv hKcard A
  rw [hAcard] at hbound
  omega


/-- Under core weak closure a fused outer involution cannot have omega of order sixteen. -/
public theorem parrott_outer_omega_card_ne_sixteen_of_core_weakClosure
    {G : Type*} [Group G] [Finite G]
    (hN : IsNTwoGroup G) (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    (∀ t : G, t ∈ J.map H.subtype → IsConj z t → t = z) →
    ∀ y : H, orderOf y = 2 → y ∉ J → IsConj z (y : G) →
      let P := centralizer ({y} : Set H)
      let X := (omega₁ P (p := 2)).map (H.subtype.comp P.subtype)
      Nat.card X ≠ 16 := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  change (∀ t : G, t ∈ J.map H.subtype → IsConj z t → t = z) → _
  intro hcore y hy hyJ hconj
  dsimp only
  intro hcard
  let P := centralizer ({y} : Set H)
  let X := (omega₁ P (p := 2)).map (H.subtype.comp P.subtype)
  let X₀ := zpowers (y : G) ⊔ (E ⊓ centralizer ({(y : G)} : Set G))
  obtain ⟨_, hcard₀, hle⟩ := parrott_outer_fixed_join_data z h y hy hyJ
  have heq : X₀ = X := eq_of_le_of_card_ge hle (by rw [hcard, hcard₀])
  have hweak : ∀ t : G, t ∈ E → IsConj z t → t = z := by
    intro t ht htconj
    obtain ⟨a, _, rfl⟩ := ht
    exact hcore _ (mem_map_of_mem H.subtype a.property) htconj
  have hleN := parrott_outer_fixed_join_normalizer_le_centralizer hN z h hweak y hy hyJ
  change normalizer (X₀ : Set G) ≤ H at hleN
  rw [heq] at hleN
  exact parrott_outer_omega_normalizer_not_le_centralizer z h y hy hyJ hconj hleN

end Stellmacher.Recognition

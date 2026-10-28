module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CubicTerminal.InvariantSource
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.InvariantSubgroups.SylowAction

/-!
# Rigidity of the actual ambient crossing subgroup

The original common nine-group acts through the equivariant root marking.
Its image still has order nine because the action kernel is three-prime.
The source cover's non-elementary invariant-subgroup rigidity therefore
identifies the original ambient crossing subgroup with the component Sylow.
All subgroup images retain their literal ambient inclusion maps.

Source: Aschbacher--Smith 2.5.7, printed p.556.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement Stellmacher Matrix.PSL3Four.RootNormalizerModel
variable {G : Type*} [Group G] [Finite G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

theorem MathieuSourceSetup.linear_four_nine_invariant_eq_sylow
    (c : MathieuSourceSetup H L M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (e : L ⧸ center L ≃* Matrix.PSL3Four.PSL) (P : Sylow 2 L)
    (N : Subgroup G) (f : P →* Root) (hk : f.ker = (center L).subgroupOf P)
    (β : N →* MulAut Root) (hβker : Nat.Coprime 3 (Nat.card β.ker))
    (hact : ∀ (n : N) (a b : P), ((b : L) : G) = n * ((a : L) : G) * (n : G)⁻¹ →
      β n (f a) = f b)
    (Y Q : Subgroup G) (hYN : Y ≤ N) (hYcard : Nat.card Y = 9)
    (hQP : Q ≤ (P : Subgroup L).map L.subtype)
    (hYQ : Y ≤ normalizer (Q : Set G)) (hne : ¬ IsElementaryAbelian 2 Q) :
    Q = (P : Subgroup L).map L.subtype := by
  let i : P →* G := L.subtype.comp (P : Subgroup L).subtype
  let A : Subgroup P := Q.comap i
  have hAQ : A.map i = Q := by
    apply le_antisymm (map_comap_le _ _)
    intro u hu
    obtain ⟨a, ha, rfl⟩ := hQP hu
    exact ⟨⟨a, ha⟩, hu, rfl⟩
  have hAne : ¬ IsElementaryAbelian 2 A := by
    intro heA
    let := heA
    have heQ : IsElementaryAbelian 2 (A.map i) := IsElementaryAbelian.map i
    exact hne (hAQ ▸ heQ)
  let YN := Y.subgroupOf N
  have hYNcard : Nat.card YN = 9 :=
    (Nat.card_congr (subgroupOfEquivOfLe hYN).toEquiv).trans hYcard
  have hp : IsPGroup 3 YN := IsPGroup.of_card (n := 2) hYNcard
  have hi := injective_comp_subtype_of_coprime_ker β hβker YN hp
  let B := YN.map β
  have hB : Nat.card B = 9 := by
    change Nat.card (YN.map β) = 9
    rw [← YN.range_subtype, ← MonoidHom.range_comp]
    rw [Nat.card_congr (MonoidHom.ofInjective hi).toEquiv.symm]
    exact hYNcard
  have hinv : ∀ b ∈ B, ∀ u ∈ A.map f, b u ∈ A.map f := by
    rintro b ⟨n, hn, rfl⟩ u ⟨a, ha, rfl⟩
    have hbQ : (n : G) * ((a : L) : G) * (n : G)⁻¹ ∈ Q :=
      (mem_normalizer_iff.mp (hYQ hn) _).mp ha
    obtain ⟨b, hb, he⟩ := hQP hbQ
    have heq : ((⟨b, hb⟩ : P) : L).val = n * ((a : L) : G) * (n : G)⁻¹ := he
    rw [hact n a ⟨b, hb⟩ heq]
    apply mem_map_of_mem
    change (b : G) ∈ Q
    exact heq.symm ▸ hbQ
  have hAtop := MathieuSourceSetup.linear_four_nine_rigidity_of_mark
    c hG hempty e P f hk B hB A hinv hAne
  rw [← hAQ, hAtop]
  ext u
  constructor
  · rintro ⟨a, _, rfl⟩
    exact mem_map_of_mem L.subtype a.property
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, mem_top _, rfl⟩

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection

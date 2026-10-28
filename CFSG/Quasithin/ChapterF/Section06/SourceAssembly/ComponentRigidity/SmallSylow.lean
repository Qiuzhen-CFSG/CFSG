module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentRigidity

/-!
# The actual component Sylow subgroup in the exceptional-left branch

Apply the source normal-subgroup setup to the original component K.
The intersection Q₂ ∩ K is its literal Sylow two-subgroup. When the first
vertex fails characteristic two, Q₂ is elementary of order at most eight;
these properties pass to that intersection and its image in K/Z(K).
The latter quotient is the actual nonabelian simple quotient of K.

This constructs the input to the elementary-Sylow case of the catalogue
in F.6.17 from its genuine exceptional-left source case. The separate
characteristic-two-left exclusion and the catalogue remain with their
source producers. Source: Aschbacher--Smith F.6.17, printed p.309.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

private theorem elementary_of_injective {A B : Type*} [Group A] [Group B]
    [IsElementaryAbelian 2 B] (f : A →* B) (hf : Function.Injective f) :
    IsElementaryAbelian 2 A := by
  refine { toIsMulCommutative := ⟨⟨fun x y => hf ?_⟩⟩, exponent_dvd_p := ?_ }
  · simp only [map_mul]
    exact IsMulCommutative.is_comm.comm _ _
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply hf
    rw [map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 B), map_one]

/-- The actual Sylow two-subgroup of a normal X is elementary of order at
most eight in the exceptional-left case; its ambient image is retained. -/
theorem normal_subgroup_small_sylow_of_exceptional_left
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hbad : generalizedFitting G₁ ≠ pCore 2 G₁)
    (X : Subgroup G) [X.Normal]
    (h₂ : ¬ (pResidual 2 G₂).map G₂.subtype ≤ X) :
    ∃ S : Sylow 2 X, (S : Subgroup X).map X.subtype =
      (pCore 2 G₂).map G₂.subtype ⊓ X ∧
      IsElementaryAbelian 2 S ∧ Nat.card S ≤ 8 ∧ primeRank 2 S ≤ 3 := by
  obtain ⟨hE, hcard, _⟩ := right_core_small_elementary_of_not_characteristic_two h hcore hbad
  let Q := (pCore 2 G₂).map G₂.subtype
  let : IsElementaryAbelian 2 Q := hE
  obtain ⟨S, hS⟩ := sylow_in_normal_eq_right_core_intersection h X h₂
  have hSQ : (S : Subgroup X).map X.subtype ≤ Q := hS.le.trans inf_le_left
  let f : S →* Q := (X.subtype.comp (S : Subgroup X).subtype).codRestrict Q
    (fun s => hSQ (mem_map_of_mem X.subtype s.property))
  have hf : Function.Injective f := by
    intro s t he
    exact Subtype.ext (Subtype.ext (congrArg (fun q : Q => (q : G)) he))
  have hbound : Nat.card S ≤ 8 := (Nat.card_le_card_of_injective f hf).trans hcard
  refine ⟨S, hS, elementary_of_injective f hf, hbound, ?_⟩
  apply (primeRank_le_iff_elementary_card_le S).mpr
  intro E _
  exact (card_le_card_group E).trans hbound

/-- The component application retains its genuine simple quotient and the
image of the same chosen Sylow under the literal quotient map. -/
theorem component_quotient_small_sylow_of_exceptional_left
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hbad : generalizedFitting G₁ ≠ pCore 2 G₁)
    (K : Subgroup G) [K.Normal] (hK : IsComponent G K)
    (h₂ : ¬ (pResidual 2 G₂).map G₂.subtype ≤ K) :
    IsSimpleGroup (K ⧸ center K) ∧
      ∃ S : Sylow 2 K, (S : Subgroup K).map K.subtype =
        (pCore 2 G₂).map G₂.subtype ⊓ K ∧
        IsElementaryAbelian 2 S ∧ Nat.card S ≤ 8 ∧
        IsElementaryAbelian 2 (S.mapSurjective (QuotientGroup.mk'_surjective (center K))) ∧
        Nat.card (S.mapSurjective (QuotientGroup.mk'_surjective (center K))) ≤ 8 := by
  let : IsQuasisimple K := hK.2
  obtain ⟨S, hS, hE, hcard, _⟩ := normal_subgroup_small_sylow_of_exceptional_left
    h hcore hbad K h₂
  let : IsElementaryAbelian 2 S := hE
  refine ⟨IsQuasisimple.simple, S, hS, hE, hcard, ?_, ?_⟩
  · exact IsElementaryAbelian.map (QuotientGroup.mk' (center K))
  · exact (Nat.le_of_dvd (Nat.card_pos (α := S))
      ((S : Subgroup K).card_map_dvd (QuotientGroup.mk' (center K)))).trans hcard

/-- F.6.13's source conclusions required by F.6.17, for the exceptional-left
source branch, with every cubic, elementary and Sylow premise constructed. -/
theorem component_rigidity_of_exceptional_left
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hbad : generalizedFitting G₁ ≠ pCore 2 G₁)
    (K : Subgroup G) [K.Normal] (hK : IsComponent G K)
    (h₁ : (pResidual 2 G₁).map G₁.subtype ≤ K)
    (h₂ : ¬ (pResidual 2 G₂).map G₂.subtype ≤ K) :
    K ⊔ G₂ = ⊤ ∧ (K ⊔ (pCore 2 G₂).map G₂.subtype : Subgroup G).Normal ∧
      (∃ S : Sylow 2 (K ⊔ (pCore 2 G₂).map G₂.subtype : Subgroup G),
        (S : Subgroup (K ⊔ (pCore 2 G₂).map G₂.subtype : Subgroup G)).map
          (K ⊔ (pCore 2 G₂).map G₂.subtype : Subgroup G).subtype =
          (pCore 2 G₂).map G₂.subtype) ∧
      Nonempty (((pResidual 2 G₁).map G₁.subtype) ≃* Multiplicative (ZMod 3)) ∧
      IsElementaryAbelian 2 ((pCore 2 G₂).map G₂.subtype) ∧
      primeRank 2 ((pCore 2 G₂).map G₂.subtype) ≤ 3 ∧
      IsSimpleGroup (K ⧸ center K) ∧
      ∃ S : Sylow 2 (K ⧸ center K), IsElementaryAbelian 2 S ∧ Nat.card S ≤ 8 := by
  obtain ⟨hg, hn, hs⟩ := normal_subgroup_rigidity_setup h K h₁ h₂
  obtain ⟨he, _, hr⟩ := right_core_small_elementary_of_not_characteristic_two h hcore hbad
  obtain ⟨hqs, S, _, _, _, hE, hc⟩ := component_quotient_small_sylow_of_exceptional_left
    h hcore hbad K hK h₂
  exact ⟨hg, hn, hs, left_residual_cubic_of_not_characteristic_two h hbad,
    he, hr, hqs, S.mapSurjective (QuotientGroup.mk'_surjective (center K)), hE, hc⟩

end CFSG.Quasithin.ChapterF.SourceAssembly

module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Sieve.ComponentPlacement
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Sieve.LieModels
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.InvariantCubicGeneration
public import Theory.AtlasPort.LinearGroups.G2.FieldTransport

/-!
# Excluding the binary derived G₂ row of the terminal component list

The two actual cubic parabolics of G₂(2)′ are invariant under every
Sylow-preserving automorphism and generate the group. ComponentPlacement
puts their lifts in M, forcing the original component into M, contrary
to SourceOrbit. Coefficientwise field transport applies this exclusion to
the field-independent F.9.18 predicate. Its final consumer removes this
row from the broader list, after the proved A₇ and M₂₂ exclusions.

Source: Aschbacher--Smith 14.6.20, printed p.1037, using the concrete
parabolics behind 14.3.6(2), printed pp.991--992. Original 14.6.18 remains
with qt-e-14625-source; the remaining Lie-model rows and F.9.18 input
instantiation remain with qt-e-suitable-component-supports.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter13.Section08.Components.Models
variable {G : Type*} [Group G] [Finite G]

private theorem component_le_of_invariant_cubic_generation
    (T : Sylow 2 G) (M : Subgroup G) (hTM : (T : Subgroup G) ≤ M)
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
    (H : Subgroup G) (hH : H ∈ Chapter1.HOver G (T : Set G))
    (K : Subgroup G) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent)
    {B : Type*} [Group B] [Finite B] (eK : (K ⧸ pCore 2 K) ≃* B)
    (hgen : ∀ (P : Sylow 2 B) (N : Subgroup B), (P : Subgroup B) ≤ N →
      (∀ J : Subgroup B, (P : Subgroup B) ≤ J → (P : Subgroup B).relIndex J = 3 →
        (∀ b : MulAut B, (P : Subgroup B).map b.toMonoidHom = P →
          J.map b.toMonoidHom = J) → J ≤ N) → N = ⊤) : K ≤ M := by
  obtain ⟨P,hP⟩ := source_component_sylow T H K hH.2 hKH hK
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := eK.surjective.comp (QuotientGroup.mk'_surjective _)
  let N := M.subgroupOf K
  have hPN : (P : Subgroup K) ≤ N := by
    rw [hP]
    exact fun _ hx => hTM hx
  have hker : q.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ eK.injective,QuotientGroup.ker_mk']
  have hkerN : q.ker ≤ N :=
    (hker ▸ pCore_isPGroup.le_sylow_of_normal P).trans hPN
  have hm : N.map q = ⊤ := hgen (P.mapSurjective hq) (N.map q) (map_mono hPN)
    (fun J _ hi hinv =>
      source_component_cubic_le_image T M hsolv H hH K hKH hK eK P hP J hi hinv)
  have hN : N = ⊤ := by
    have hh := congrArg (Subgroup.comap q) hm
    rwa [comap_map_eq,sup_eq_left.mpr hkerN,comap_top] at hh
  intro k hk
  exact show (⟨k,hk⟩ : K) ∈ N from hN ▸ mem_top _

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)


include hG hempty hM hunique hmany hcard e hab hsolv in
/-- Both invariant cubic parabolics of G₂(2)′ lift into M and generate the
component quotient. The original component cannot therefore have this model. -/
theorem source_component_binary_g2_false
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (eK : (K ⧸ pCore 2 K) ≃* Atlas.G2.BinaryParabolicPair.DerivedModel) : False := by
  exact source_component_not_le hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK
    (component_le_of_invariant_cubic_generation T M hM.1.2 hsolv H hH.1 K hKH hK eK
      Atlas.G2.BinaryParabolicPair.InvariantCubicGeneration.sylow_invariant_cubic_generation)

include hG hempty hM hunique hmany hcard e hab hsolv in
/-- The exclusion applies to the actual F.9.18 field-independent model predicate. -/
theorem source_component_not_binary_g2_model
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) :
    ¬ IsG2DerivedAt (K ⧸ pCore 2 K) 2 := by
  rintro ⟨F,_,_,hF,⟨a⟩⟩
  let := Fintype.ofFinite F
  let f : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  let b := Atlas.G2.fieldEquiv f
  have hb : (commutator (Atlas.G2.Model F)).map b.toMonoidHom =
      commutator (Atlas.G2.Model (ZMod 2)) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top_of_surjective _ b.surjective]
    rfl
  let c := (b.subgroupMap (commutator (Atlas.G2.Model F))).trans (MulEquiv.subgroupCongr hb)
  exact source_component_binary_g2_false hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK (a.trans c)

/-- The precise Lie-type remainder after also excluding the binary derived G₂ row. -/
@[expose] def RemainingLieQuotientModels (D : Type*) [Group D] : Prop :=
  ClassificationModels.IsBenderModel D ∨
  (∃ n : ℕ, 1 ≤ n ∧ ClassicalGroup.IsPSL D 3 (2 ^ n)) ∨
  (∃ n : ℕ, 1 ≤ n ∧ IsSp4DerivedAt D (2 ^ n)) ∨
  (∃ n : ℕ, 2 ≤ n ∧ IsG2DerivedAt D (2 ^ n)) ∨
  ClassicalGroup.IsPSL D 4 2 ∨ ClassicalGroup.IsPSL D 5 2

include hG hempty hM hunique hmany hcard e hab hsolv in
/-- Application to the broader F.9.18 input removes A₇, M₂₂ and G₂(2)′.
The remaining rank-one, larger-field and higher-rank rows are still explicit. -/
theorem source_component_remaining_lie_models_of_f918
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hm : F918Models (K ⧸ pCore 2 K)) : RemainingLieQuotientModels (K ⧸ pCore 2 K) := by
  have hh := source_component_lie_models_of_f918 hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK hm
  rcases hh with hb | hl | hs | ⟨n,hn,hg⟩ | hl4 | hl5
  · exact Or.inl hb
  · exact Or.inr (Or.inl hl)
  · exact Or.inr (Or.inr (Or.inl hs))
  · have hlarge : 2 ≤ n := by
      by_contra hsmall
      have he : n = 1 := by omega
      subst n
      exact source_component_not_binary_g2_model hG T hempty hM hunique hmany hcard e hab hsolv
        H hH K hKH hK (by simpa using hg)
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n,hlarge,hg⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl4))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl5))))
end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve

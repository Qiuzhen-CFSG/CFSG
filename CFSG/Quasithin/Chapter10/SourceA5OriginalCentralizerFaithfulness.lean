module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalCentralizerPassage
public import CFSG.Quasithin.Chapter10.SourceA5OriginalIrreducibility.FaithfulAction
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.PrimeFreeCentralizer
public import Theory.GroupTheory.CenterlessCentralizer


/-!
# Starred-offender faithfulness in the original A5 passage

For the actual full actor `Q = M / C_M(V_M)`, the local orbit has image
`J ≃ A₅ × A₅`. Its trivial center embeds `C_Q(J)` into `Q / J`, so the
centralizer has order prime to three and five. The K-group hypothesis is
inherited from the actual full actor. Prime-to-fifteen K-group solvability
therefore supplies the solvable-centralizer premise of D.2.13, which makes
every starred cubic offender act faithfully on the literal subgroup `J`.

The final application retains the minimal full-quotient representation and
its conjugation formula. Catalogue solvability remains an explicit premise;
no SQTK hypothesis is asserted for the arbitrary centralizer quotient.
Source: Aschbacher--Smith D.2.13 and D.3.21, printed pp.184--185 and204--207,
as applied in the Chapter 10 A5 passage.
-/

public section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))

local instance centralizerFullElementary : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

include D e in
/-- The actual full actor centralizer has order prime to three and five. -/
theorem source_a5_original_actor_centralizer_coprime
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G)) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
    let J := ((localOrbit T L).subgroupOf D.maximalLocal).map q
    Nat.Coprime 3 (Nat.card (centralizer (J : Set
      (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal))))) ∧
    Nat.Coprime 5 (Nat.card (centralizer (J : Set
      (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal))))) := by
  dsimp only
  let M := D.maximalLocal
  let U := D.fullModule.subgroupOf M
  let := (source_full_module_reduced D).normal
  let q := QuotientGroup.mk' (centralizer (U : Set M))
  let J := ((localOrbit T L).subgroupOf M).map q
  let _ : J.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hd := centralizer_card_dvd_index_of_center_eq_bot J
    (source_a5_original_actor_orbit_center D e hn ht htn)
  have hi := source_a5_original_actor_orbit_index_coprime D e hn
  exact ⟨hi.1.coprime_dvd_right hd, hi.2.coprime_dvd_right hd⟩

include D e in
/-- Solvability of the actual centralizer gives faithful starred-offender conjugation. -/
theorem source_a5_original_actor_starred_conjugation_of_solvable
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G)) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
    let J := ((localOrbit T L).subgroupOf D.maximalLocal).map q
    let _ : J.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
    Group.IsSolvable (centralizer (J : Set
      (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal)))) →
    ∀ {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
      [FiniteDimensional (ZMod 2) V]
      (ρ : Representation (ZMod 2)
        (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal)) V),
      Function.Injective ρ → ∀ A ∈ ChapterD.QhatStar ρ,
        Function.Injective ((MulAut.conjNormal :
          (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal)) →* MulAut J).comp A.subtype) := by
  dsimp only
  intro hs V _ _ _ ρ hf A hA
  let := (source_full_module_reduced D).normal
  let := hs
  have hc := source_a5_original_actor_centralizer_coprime D e hn ht htn
  exact ChapterD.starred_conjugation_injective_of_solvable_centralizer ρ hf
    (source_full_module_reduced D).quotient_pCore_eq_bot _ hc.1 hc.2 hA

/-- The actual centralizer inherits the known-simple K-group hypothesis. -/
theorem source_a5_original_actor_centralizer_isKGroup :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
    let J := ((localOrbit T L).subgroupOf D.maximalLocal).map q
    IsKGroup KnownSimple.IsKnownSimple (centralizer (J : Set
      (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal)))) := by
  dsimp only
  let := (source_full_module_reduced D).normal
  exact (source_full_actor_isKGroup D).subgroup _

omit e in
/-- The catalogue prime-to-fifteen result supplies actual centralizer solvability. -/
theorem source_a5_original_actor_centralizer_solvable_of_prime_to_fifteen
    (hsolv : ∀ (X : Type u) [Group X] [Finite X],
      IsKGroup KnownSimple.IsKnownSimple X →
      Nat.Coprime 3 (Nat.card X) → Nat.Coprime 5 (Nat.card X) → Group.IsSolvable X)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G)) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
    let J := ((localOrbit T L).subgroupOf D.maximalLocal).map q
    Group.IsSolvable (centralizer (J : Set
      (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal)))) := by
  dsimp only
  let := (source_full_module_reduced D).normal
  have hc := source_a5_original_actor_centralizer_coprime D e hn ht htn
  exact hsolv _ (source_a5_original_actor_centralizer_isKGroup D) hc.1 hc.2

include D e in
/-- The original minimal full-quotient action has faithful starred-offender conjugation,
with exactly its original quotient and action coordinates. -/
theorem source_minimal_full_quotient_starred_conjugation_of_prime_to_fifteen
    (hsolv : ∀ (X : Type u) [Group X] [Finite X],
      IsKGroup KnownSimple.IsKnownSimple X →
      Nat.Coprime 3 (Nat.card X) → Nat.Coprime 5 (Nat.card X) → Group.IsSolvable X)
    (hD : D.IsMinimalFullModule) (hbound : SourceFullModuleCubicBound D)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G)) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
    let J := ((localOrbit T L).subgroupOf D.maximalLocal).map q
    let _ : J.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
    ∃ ρ : Representation (ZMod 2) (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal))
      (Additive D.fullCentralQuotient),
      Function.Injective ρ ∧ ρ.IsIrreducible ∧ cubicRatio ρ ≤ 2 ∧
      (∀ A ∈ ChapterD.QhatStar ρ,
        Function.Injective ((MulAut.conjNormal :
          (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal)) →* MulAut J).comp A.subtype)) ∧
      (∀ (m : D.maximalLocal) (v : D.fullModule),
        ρ (q m) (Additive.ofMul (QuotientGroup.mk' D.fullCentralizer v)) =
          Additive.ofMul (QuotientGroup.mk' D.fullCentralizer
            ⟨(m : G) * (v : G) * (m : G)⁻¹,
              (mem_normalizer_iff.mp (D.maximalLocal_normalizes_fullModule m.property) v).mp
                v.property⟩)) := by
  dsimp only
  let := (source_full_module_reduced D).normal
  obtain ⟨ρ,hf,hi,hb,hρ⟩ := source_minimal_full_quotient_faithful_cubic_action D hD hbound
  have hs := source_a5_original_actor_centralizer_solvable_of_prime_to_fifteen D hsolv e hn ht htn
  exact ⟨ρ,hf,hi,hb,source_a5_original_actor_starred_conjugation_of_solvable
    D e hn ht htn hs ρ hf,hρ⟩

end CFSG.Quasithin.Chapter10

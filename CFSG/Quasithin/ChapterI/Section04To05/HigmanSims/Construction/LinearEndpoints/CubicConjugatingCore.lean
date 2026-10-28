module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.NormalizerCubicCentralizer
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.SeedPointTypes
public import Theory.GroupAction.PrimeOrderConjugation
import all CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.PairNormalizer

/-!
# A cubic-centralizing conjugator for the original paired radicals

The specified common cubic fixes a nonidentity point of the original seed,
but fixes no nonidentity point of the first natural endpoint radical. Its
fixed seed point therefore lies outside the actual shared plane. Transport
within the unchanged seed gives the whole cyclic-four normalizer core's
fixed cyclic four, whose generator sends the first radical to the same
second radical as the original conjugator.

The import-all edge intentionally reuses the same-package proof that all
core elements with square outside the fixed plane give the same conjugate.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- The same marked endpoint pair admits an actual order-four conjugator
in the whole original normalizer core which centralizes its specified
common cubic. Its square is the original seed's unique fixed point. -/
theorem TypeAt.paired_endpoint_cubic_conjugating_core (h : TypeAt z V)
    (W A B : Subgroup G) [IsElementaryAbelian 2 A]
    (hWV : W ≤ V) (hW4 : Nat.card W = 4) (hA16 : Nat.card A = 16)
    (hWA : W ≤ A) (hAC : A ≤ centralizer (W : Set G))
    (hAP : A ⊓ (normalizer (V : Set G)).pCoreIn 2 = W)
    (p : G) (hp : p ∈ (normalizer (V : Set G)).pCoreIn 2) (hpW : p ^ 2 ∉ W)
    (hB : B = A.map (MulAut.conj p).toMonoidHom)
    (d : NaturalEndpointData A) (t : G) (ht : t ∈ d.carrier)
    (htW : t ∈ normalizer (W : Set G)) (ht3 : orderOf t = 3) :
    ∃ u c : G, u ∈ V ∧ u ≠ 1 ∧ u ∉ W ∧ TypeAt u V ∧
      V ⊓ centralizer ({t} : Set G) = zpowers u ∧
      c ∈ (normalizer (V : Set G)).pCoreIn 2 ∧ c ^ 2 = u ∧
      orderOf c = 4 ∧ Commute c t ∧
      (normalizer (V : Set G)).pCoreIn 2 ⊓ centralizer ({t} : Set G) = zpowers c ∧
      B = A.map (MulAut.conj c).toMonoidHom := by
  have htV : t ∈ normalizer (V : Set G) :=
    h.plane_normalizer_le_seed_normalizer W hWV hW4 htW
  obtain ⟨u, huV, hu1, htu⟩ :=
    Theory.GroupAction.exists_commuting_nonidentity_of_prime_order V
      (by decide : Nat.Prime 3) ht3 htV (by rw [h.seed_card]; decide)
  have huW : u ∉ W := by
    intro huW
    have hu : u ∈ A ⊓ centralizer ({t} : Set G) :=
      ⟨hWA huW, mem_centralizer_singleton_iff.mpr htu.symm.eq⟩
    rw [d.cubic_radical_centralizer t ht ht3] at hu
    exact hu1 hu
  have huT : TypeAt u V := h.at_seed_point u huV hu1
  have htI : t ∈ involutionCentralizer u ⊓ normalizer (V : Set G) :=
    ⟨mem_centralizer_singleton_iff.mpr htu.eq, htV⟩
  obtain ⟨c, hcP, hc2, hc4, hcfix⟩ := huT.cubic_normalizer_core t htI ht3
  have hct : Commute c t := mem_centralizer_singleton_iff.mp
    (hcfix.ge (mem_zpowers c)).2
  have hcW : c ^ 2 ∉ W := by rwa [hc2]
  have hsame : A.map (MulAut.conj p).toMonoidHom = A.map (MulAut.conj c).toMonoidHom :=
    same_exterior_conjugate h W A hWV hW4 hA16 hWA hAC hAP p c hp hcP hpW hcW
  exact ⟨u, c, huV, hu1, huW, huT, huT.cubic_seed_fixed t htI ht3,
    hcP, hc2, hc4, hct, hcfix, hB.trans hsame⟩

end CFSG.Quasithin.HigmanSims

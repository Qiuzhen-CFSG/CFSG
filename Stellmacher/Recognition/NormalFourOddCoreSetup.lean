module

public import Stellmacher.Recognition.RankTwoSylowReduction
public import Theory.GroupTheory.PGroup.RankTwoNormalFour
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# The central-involution normal-four setup

Let `S` be a Sylow two-subgroup, `Z = Ω₁(Z(S))`, and `N = N_G(Z)`.
This module sets up the actual image of a four-group in `N/O₂′(N)` and
proves that `S` and its four-groups lie in `N`. Under the elementary rank
bound, `Z` lies in every four-group; when `|Z| = 2`, `N` is a solvable
two-local subgroup and each normal four has centralizer of index two in `S`.
Normality of the quotient image also controls conjugates returning to `S`
whose conjugator belongs to `N`; this does not assume normality before quotienting.

The remaining classification uses three ambient inputs: MacWilliams's
multiple-normal-four theorem, the nonnormal-image argument of §4, and the
normal-image fusion argument of §6. None of those inputs is assumed or
replaced by a condition on the four-group before taking the quotient here.

Source: Janko–Thompson, Math. Z. 113 (1970), 1.2 and §§3–6, especially
pp.393–395. See `normal-four-case-split.md` beside the saved source PDF.
-/

namespace Stellmacher.Recognition.NormalFourCentralOmegaTwo

open Subgroup

variable {G : Type*} [Group G]

/-- The ambient image of the first omega subgroup of the Sylow center. -/
public abbrev centralOmega (S : Sylow 2 G) : Subgroup G :=
  ((omega₁ (center S) (p := 2)).map (center S).subtype).map (S : Subgroup G).subtype

/-- The source's subgroup `N = N_G(Ω₁(Z(S)))`. -/
public abbrev omegaNormalizer (S : Sylow 2 G) : Subgroup G :=
  normalizer (centralOmega S : Set G)

/-- The source's barred four-group: its image in `N/O₂′(N)`. -/
public abbrev fourImage (S : Sylow 2 G) (E : Subgroup S) :
    Subgroup (omegaNormalizer S ⧸ pPrimeCore 2 (omegaNormalizer S)) :=
  ((E.map (S : Subgroup G).subtype).subgroupOf (omegaNormalizer S)).map
    (QuotientGroup.mk' (pPrimeCore 2 (omegaNormalizer S)))

/-- The Sylow subgroup normalizes the ambient central omega subgroup. -/
public theorem sylow_le_omegaNormalizer (S : Sylow 2 G) :
    (S : Subgroup G) ≤ omegaNormalizer S := by
  let Z := (omega₁ (center S) (p := 2)).map (center S).subtype
  let : Z.Normal := ⟨fun a ha b => by
    have hcentral : a ∈ center S := map_subtype_le _ ha
    simpa [mem_center_iff.mp hcentral b] using ha⟩
  simpa only [Z.normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
    Z.le_normalizer_map (S : Subgroup G).subtype

/-- Taking `subgroupOf N` in `fourImage` does not truncate the four-group. -/
public theorem four_le_omegaNormalizer (S : Sylow 2 G) (E : Subgroup S) :
    E.map (S : Subgroup G).subtype ≤ omegaNormalizer S :=
  (map_subtype_le E).trans (sylow_le_omegaNormalizer S)

/-- The ambient central omega has the same order as the intrinsic one. -/
public theorem card_centralOmega (S : Sylow 2 G) :
    Nat.card (centralOmega S) = Nat.card (omega₁ (center S) (p := 2)) := by
  rw [card_map_of_injective (S : Subgroup G).subtype_injective,
    card_map_of_injective (center S).subtype_injective]

/-- The image in the odd-core quotient is still elementary abelian. -/
public theorem fourImage_elementary (S : Sylow 2 G) (E : Subgroup S)
    [IsElementaryAbelian 2 E] : IsElementaryAbelian 2 (fourImage S E) := by
  let : IsElementaryAbelian 2 (E.map (S : Subgroup G).subtype) :=
    IsElementaryAbelian.map_subtype
  let : IsElementaryAbelian 2
      ((E.map (S : Subgroup G).subtype).subgroupOf (omegaNormalizer S)) :=
    IsElementaryAbelian.subgroupOf (four_le_omegaNormalizer S E)
  exact IsElementaryAbelian.map _

variable [Finite G]

/-- Quotienting by the odd core preserves the order of the four-group. -/
public theorem fourImage_card (S : Sylow 2 G) (E : Subgroup S)
    [IsElementaryAbelian 2 E] (hE : Nat.card E = 4) :
    Nat.card (fourImage S E) = 4 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let A := E.map (S : Subgroup G).subtype
  let W := A.subgroupOf (omegaNormalizer S)
  let q := QuotientGroup.mk' (pPrimeCore 2 (omegaNormalizer S))
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map_subtype
  let : IsElementaryAbelian 2 W :=
    IsElementaryAbelian.subgroupOf (four_le_omegaNormalizer S E)
  have hinj : Function.Injective (q.comp W.subtype) :=
    injective_comp_subtype_of_coprime_ker q
      (by simpa only [q, QuotientGroup.ker_mk'] using
        (pPrimeCore_coprime_card (p := 2) (G := omegaNormalizer S))) W
      (IsElementaryAbelian.isPGroup 2 W)
  let e : W ≃* W.map q := MulEquiv.ofBijective (q.subgroupMap W)
    ⟨fun x y h => hinj (congrArg Subtype.val h), q.subgroupMap_surjective W⟩
  change Nat.card (W.map q) = 4
  rw [← Nat.card_congr e.toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (four_le_omegaNormalizer S E)).toEquiv,
    card_map_of_injective (S : Subgroup G).subtype_injective, hE]

/-- Central omega lies in the ambient image of every elementary four. -/
public theorem centralOmega_le_four
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (E : Subgroup S) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4) : centralOmega S ≤ E.map (S : Subgroup G).subtype :=
  map_mono (omega_one_center_le_four_of_elementary_card_lt_eight
    (elementary_card_lt_eight_of_subgroup hrank (S : Subgroup G)) E hE)

/-- The normalizer in the source is solvable by the N₂ hypothesis. -/
public theorem omegaNormalizer_solvable (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2) :
    Group.IsSolvable (omegaNormalizer S) := by
  apply hN _
  refine ⟨centralOmega S, ?_, ?_, rfl⟩
  · intro hbot
    have hc := card_centralOmega S
    rw [hbot, hZ, card_bot] at hc
    omega
  · exact ((S.isPGroup'.to_subgroup _).to_subgroup _).map _ |>.map _

/-- The centralizer of a normal four has index exactly two in this case. -/
public theorem centralizer_index_two (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4) : (centralizer (E : Set S)).index = 2 :=
  centralizer_index_eq_two_of_normal_four_of_card_omega_one_center_eq_two
    S.isPGroup' hZ E hE

/-- Normality of the quotient image controls conjugates returning to this Sylow,
when the conjugator belongs to the omega normalizer. -/
public theorem conjugate_four_eq_of_mem_omegaNormalizer {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (E : Subgroup S) [(fourImage S E).Normal]
    (g : G) (hg : g ∈ omegaNormalizer S)
    (hconj : (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
      (S : Subgroup G)) :
    (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom =
      E.map (S : Subgroup G).subtype := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N := omegaNormalizer S
  let A := E.map (S : Subgroup G).subtype
  let W := A.subgroupOf N
  let P := (S : Subgroup G).subgroupOf N
  let q := QuotientGroup.mk' (pPrimeCore 2 N)
  let gN : N := ⟨g, hg⟩
  have hP : IsPGroup 2 P := S.isPGroup'.comap_of_injective N.subtype N.subtype_injective
  have hWP : W ≤ P := fun x hx => (map_subtype_le E) hx
  have hconjP : W.map (MulAut.conj gN).toMonoidHom ≤ P := by
    rintro x ⟨w, hw, rfl⟩
    exact hconj (mem_map_of_mem (MulAut.conj g).toMonoidHom hw)
  have heq := map_conj_eq_of_normal_map_of_le_prime_group q
    (by simpa only [q, QuotientGroup.ker_mk'] using
      (pPrimeCore_coprime_card (p := 2) (G := N))) P W hP hWP gN hconjP
  have hWA : W.map N.subtype = A := map_subgroupOf_eq_of_le (four_le_omegaNormalizer S E)
  have hmaps : (W.map (MulAut.conj gN).toMonoidHom).map N.subtype =
      (W.map N.subtype).map (MulAut.conj g).toMonoidHom := by
    rw [map_map, map_map]
    rfl
  have hout := congrArg (Subgroup.map N.subtype) heq
  rw [hmaps, hWA] at hout
  exact hout

end Stellmacher.Recognition.NormalFourCentralOmegaTwo

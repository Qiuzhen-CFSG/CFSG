module
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.Action
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.Setup
public import Theory.GroupTheory.ElementSubgroupIncidence

/-!
# From the full A₆ Sylow family to five-point fusion

Sylow conjugacy inside C_G(z) turns a transitive family of elementary
sixteen-groups in T into centralizer transitivity. The exact incidence
lemma A.1.7(1) then gives transitivity of N_G(A) on β = zᴳ ∩ A.

The same Sylow family bounds every Sylow subgroup of N_G(A) by the
relative normalizer order in T. If β had four points, orbit–stabilizer
would give an image of order 24 and a Sylow image of order eight. Its
preimage contains A in the kernel, contradicting the normalizer bound
32. The binary classification therefore forces the total product into
β and gives five points.

These are conditional reductions. The actual two-member Sylow family
and its order-32 relative normalizer must still be constructed from the
full automorphism case; they are not source hypotheses of 16.4.9.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 16.4.9(2), printed p.1192 (PDF p.1209).
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter16.Intersections.Six.FullFusion
variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {z r : G}

def SylowFamilyTransitive (T : Sylow 2 G) (M : AlternatingProductModel L z r 6) : Prop :=
  ∀ E : Subgroup G, E ≤ T → IsElementaryAbelian 2 E → Nat.card E = 16 →
    ∃ t ∈ (T : Subgroup G), (elementary M).conjBy t = E

theorem centralizer_elementary_family (T : Sylow 2 G) (M : AlternatingProductModel L z r 6)
    (hTC : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hfamily : SylowFamilyTransitive T M) (E : Subgroup G)
    [IsElementaryAbelian 2 E] (hE : Nat.card E = 16)
    (hEC : E ≤ centralizer ({z} : Set G)) :
    ∃ c ∈ centralizer ({z} : Set G),
      (elementary M).conjBy c = E := by
  let C := centralizer ({z} : Set G)
  let : IsElementaryAbelian 2 (E.subgroupOf C) := IsElementaryAbelian.subgroupOf hEC
  obtain ⟨P, hEP⟩ := (IsElementaryAbelian.isPGroup 2 (E.subgroupOf C)).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C P (T.subtype hTC)
  have hEt : E.conjBy (c : G) ≤ T := by
    rintro _ ⟨a, ha, rfl⟩
    have hp : (MulAut.conj c) (⟨a, hEC ha⟩ : C) ∈
        ((c • P : Sylow 2 C) : Subgroup C) := ⟨⟨a, hEC ha⟩, hEP ha, rfl⟩
    rw [hc] at hp
    exact hp
  let : IsElementaryAbelian 2 (E.conjBy (c : G)) := IsElementaryAbelian.map _
  have hEcard : Nat.card (E.conjBy (c : G)) = 16 := by
    rw [conjBy, card_map_of_injective (MulAut.conj (c : G)).injective]
    exact hE
  obtain ⟨t, ht, he⟩ := hfamily _ hEt inferInstance hEcard
  refine ⟨(c : G)⁻¹ * t, C.mul_mem (C.inv_mem c.property) (hTC ht), ?_⟩
  rw [conjBy_mul, he, conjBy_inv]

theorem centralizer_incidence (T : Sylow 2 G) (M : AlternatingProductModel L z r 6)
    (hTC : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hfamily : SylowFamilyTransitive T M) (g : G)
    (hz : z ∈ (elementary M).conjBy g) :
    ∃ c ∈ centralizer ({z} : Set G),
      (elementary M).conjBy c = (elementary M).conjBy g := by
  let E := (elementary M).conjBy g
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  apply centralizer_elementary_family T M hTC hfamily E
  · change Nat.card ((elementary M).map (MulAut.conj g).toMonoidHom) = 16
    rw [card_map_of_injective (MulAut.conj g).injective, elementary_card]
  · intro a ha
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm (⟨a, ha⟩ : E) ⟨z, hz⟩))

omit [Finite G] in
theorem sylowFamilyTransitive_of_pair (T : Sylow 2 G) (M : AlternatingProductModel L z r 6)
    (s : G) (hs : s ∈ T)
    (hpair : ∀ E : Subgroup G, E ≤ T → IsElementaryAbelian 2 E → Nat.card E = 16 →
      E = elementary M ∨ E = (elementary M).conjBy s) : SylowFamilyTransitive T M := by
  intro E hET hEe hEc
  rcases hpair E hET hEe hEc with rfl | rfl
  · exact ⟨1, one_mem _, conjBy_one _⟩
  · exact ⟨s, hs, rfl⟩

theorem normalizerTransitive_of_sylowFamily (T : Sylow 2 G)
    (M : AlternatingProductModel L z r 6)
    (hTC : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hfamily : SylowFamilyTransitive T M) : NormalizerTransitive M := by
  have hf := (element_fusion_iff_centralizer_incidence (elementary M) z).mpr
    (centralizer_incidence T M hTC hfamily)
  intro a ha
  exact hf a ha.1 ha.2

theorem normalizer_sylow_card_le (T : Sylow 2 G)
    (M : AlternatingProductModel L z r 6)
    (hfamily : SylowFamilyTransitive T M)
    (hN : Nat.card ↥((T : Subgroup G) ⊓ normalizer (elementary M : Set G)) = 32)
    (P : Sylow 2 (normalizer (elementary M : Set G))) : Nat.card P ≤ 32 := by
  let A := elementary M
  let N := normalizer (A : Set G)
  let AN := A.subgroupOf N
  let : IsElementaryAbelian 2 AN := IsElementaryAbelian.subgroupOf A.le_normalizer
  have hAP : AN ≤ P := (IsElementaryAbelian.isPGroup 2 AN).le_sylow_of_normal P
  let Q := (P : Subgroup N).map N.subtype
  have hAQ : A ≤ Q := by
    intro a ha
    exact ⟨⟨a, A.le_normalizer ha⟩, hAP ha, rfl⟩
  obtain ⟨S, hQS⟩ := (P.isPGroup'.map N.subtype).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S T
  have hQT : Q.conjBy g ≤ T := by
    rw [← hg]
    exact map_mono hQS
  have hAT : A.conjBy g ≤ T := (map_mono hAQ).trans hQT
  let : IsElementaryAbelian 2 (A.conjBy g) := IsElementaryAbelian.map _
  have hcA : Nat.card (A.conjBy g) = 16 := by
    rw [conjBy, card_map_of_injective (MulAut.conj g).injective]
    exact elementary_card M
  obtain ⟨t, ht, he⟩ := hfamily _ hAT inferInstance hcA
  have hQTN : (Q.conjBy g).conjBy t⁻¹ ≤
      (T : Subgroup G) ⊓ normalizer (A : Set G) := by
    apply le_inf
    · rintro _ ⟨a, ha, rfl⟩
      exact (T : Subgroup G).mul_mem
        ((T : Subgroup G).mul_mem ((T : Subgroup G).inv_mem ht) (hQT ha))
        (by simpa using ht)
    · have hQN : Q ≤ normalizer (A : Set G) := map_subtype_le _
      have hh := map_mono (f := (MulAut.conj t⁻¹).toMonoidHom)
        (map_mono (f := (MulAut.conj g).toMonoidHom) hQN)
      rw [map_equiv_normalizer_eq, map_equiv_normalizer_eq] at hh
      change (Q.conjBy g).conjBy t⁻¹ ≤ normalizer ((A.conjBy g).conjBy t⁻¹ : Set G) at hh
      rwa [← he, conjBy_inv] at hh
  have hh := card_le_of_le hQTN
  rw [hN, conjBy, card_map_of_injective (MulAut.conj t⁻¹).injective,
    conjBy, card_map_of_injective (MulAut.conj g).injective,
    card_map_of_injective N.subtype_injective] at hh
  exact hh

omit [Finite G] in
theorem relative_normalizer_index (T : Sylow 2 G)
    (M : AlternatingProductModel L z r 6) (hAT : elementary M ≤ T)
    (hN : Nat.card ↥((T : Subgroup G) ⊓ normalizer (elementary M : Set G)) = 32) :
    (elementary M).relIndex
      ((T : Subgroup G) ⊓ normalizer (elementary M : Set G)) = 2 := by
  have hAN := le_inf hAT (elementary M).le_normalizer
  have hh := ((elementary M).subgroupOf
    ((T : Subgroup G) ⊓ normalizer (elementary M : Set G))).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hAN).toEquiv, elementary_card, hN] at hh
  change ((elementary M).subgroupOf
    ((T : Subgroup G) ⊓ normalizer (elementary M : Set G))).index = 2
  omega

theorem beta_card_ne_four_of_sylow_bound (M : AlternatingProductModel L z r 6)
    (hr : IsConj z r) (htrans : NormalizerTransitive M)
    (hs : Nat.card (normalizerStabilizer M) = 6)
    (hbound : ∀ P : Sylow 2 (normalizer (elementary M : Set G)), Nat.card P ≤ 32) :
    Nat.card (beta M) ≠ 4 := by
  intro hb
  have hI : Nat.card (normalizerImage M) = 24 := by
    rw [normalizerImage_card M htrans, hb, hs]
  let R : Sylow 2 (normalizerImage M) := default
  have hR : Nat.card R = 8 := by
    rw [R.card_eq_multiplicity, hI]
    decide +kernel
  let f := (normalizerAction M).rangeRestrict
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective
    (normalizerAction M).rangeRestrict_surjective 2 R
  let N := normalizer (elementary M : Set G)
  let AN := (elementary M).subgroupOf N
  let : IsElementaryAbelian 2 AN := IsElementaryAbelian.subgroupOf (elementary M).le_normalizer
  have hAP : AN ≤ P := (IsElementaryAbelian.isPGroup 2 AN).le_sylow_of_normal P
  have hAK : AN ≤ f.ker := by
    rw [MonoidHom.ker_rangeRestrict, normalizerAction_kernel M hr]
    exact comap_mono (elementary M).le_centralizer
  have hkernel : 16 ≤ Nat.card (f.ker.subgroupOf (P : Subgroup N)) := by
    have hh := card_le_of_le (comap_mono (f := (P : Subgroup N).subtype) hAK)
    rw [← subgroupOf, Nat.card_congr (subgroupOfEquivOfLe hAP).toEquiv] at hh
    have hAc : Nat.card AN = 16 :=
      (Nat.card_congr (subgroupOfEquivOfLe (elementary M).le_normalizer).toEquiv).trans
        (elementary_card M)
    rwa [hAc] at hh
  have hmap : Nat.card ((P : Subgroup N).map f) = 8 := by
    exact (congrArg (fun Q : Sylow 2 (normalizerImage M) => Nat.card Q) hP).trans hR
  have hmul := (f.ker.subgroupOf (P : Subgroup N)).card_mul_index
  rw [show (f.ker.subgroupOf (P : Subgroup N)).index =
    Nat.card ((P : Subgroup N).map f) from relIndex_ker _ f, hmap] at hmul
  have hPc := hbound P
  nlinarith

omit [Finite G] in
theorem total_conjugate_of_beta_card_ne_four (M : AlternatingProductModel L z r 6)
    (hr : IsConj z r) (hex : ProductExclusions M)
    (hb : Nat.card (beta M) ≠ 4) : IsConj z (total M) := by
  classical
  by_contra ht
  have he : beta M = (alpha M : Set G) := by
    apply Set.Subset.antisymm ?_ (alpha_subset_beta M hr)
    intro a ha
    rcases beta_subset M hex.1 hex.2 ha with h | h
    · exact h
    · exact (ht (h ▸ ha.2)).elim
  apply hb
  rw [he, Nat.card_coe_set_eq, Set.ncard_coe_finset, alpha_card]

theorem fusion_of_sylowFamily (T : Sylow 2 G)
    (M : AlternatingProductModel L z r 6)
    (hTC : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hr : IsConj z r) (hex : ProductExclusions M)
    (hs : Nat.card (normalizerStabilizer M) = 6)
    (hfamily : SylowFamilyTransitive T M)
    (hN : Nat.card ↥((T : Subgroup G) ⊓ normalizer (elementary M : Set G)) = 32) :
    NormalizerTransitive M ∧ IsConj z (total M) ∧ Nat.card (beta M) = 5 := by
  have htrans := normalizerTransitive_of_sylowFamily T M hTC hfamily
  have ht := total_conjugate_of_beta_card_ne_four M hr hex
    (beta_card_ne_four_of_sylow_bound M hr htrans hs
      (normalizer_sylow_card_le T M hfamily hN))
  exact ⟨htrans, ht, beta_card_of_total_conjugate M hr hex.1 hex.2 ht⟩

end CFSG.Quasithin.Chapter16.Intersections.Six.FullFusion

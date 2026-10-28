module
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.Source
public import Theory.Mathieu.M11.Properties.ThreeInvolutions
public import Theory.Representation.BinaryPrimeDegree
public import Theory.Representation.BinaryOffender.InnerInvolutions
public import Theory.Representation.BinaryOffender.CubicConjugateDimension
public import Theory.Representation.BinaryOffender.ThreeConjugateNormalizer.CentralCover

/-!
# The only possible cubic actor for an M11 source module

The prime eleven forces degree at least ten. Three conjugates of each ambient
involution generate a group containing the component image, so that involution
has fixed codimension at least four. The automorphism two-rank is at most two.
Consequently any actor witnessing cubic ratio at most two has rank two and
codimension exactly four; all its nonidentity elements have the same fixed space.
Innerness of automorphisms and the binary Schur argument put the actor inside
the original component, without discarding any central cover or outer action.

These are reductions, not the remaining representation exclusion. In particular
the already proved degree-at-most-twelve bound is not reproved here.
Source: Aschbacher--Smith K.4, printed p.457, and the degree estimate preceding
Guralnick--Malle, Classification of 2F-modules I, (2.6).
-/

public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue
open Theory.GroupTheory Subgroup Representation.BinaryOffender
open _root_.Sporadic.Mathieu
universe u v

private theorem m11_threeConjugateAutomorphisms : ThreeConjugateAutomorphisms M11 := by
  intro t ht ht2
  obtain ⟨a, rfl⟩ := m11_automorphism_inner t
  have hinj := MulAut.conj_injective_of_center_eq_bot m11_center_eq_bot
  have ha : a ≠ 1 := fun h => ht (by rw [h, map_one])
  have ha2 : a ^ 2 = 1 := hinj (by rw [map_pow, ht2, map_one])
  obtain ⟨g, k, hgk⟩ := m11_three_involution_conjugates a (orderOf_eq_prime ha2 ha)
  refine ⟨g, k, ?_⟩
  have he := congrArg (fun H : Subgroup M11 => H.map MulAut.conj) hgk
  simpa only [Subgroup.map_sup, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map,
    map_mul, map_inv] using he.ge

variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : SourceHypotheses ρ)
  (e : generalizedFitting G ⧸ center (generalizedFitting G) ≃*
    KnownSimple.SporadicName.m11.Carrier)

include ρ h e

/-- The central quotient retains the prime-eleven obstruction through every cover. -/
theorem m11_finrank_ge_ten : 10 ≤ Module.finrank (ZMod 2) V := by
  have h11 : 11 ∣ Nat.card (generalizedFitting G) := by
    apply dvd_trans _ (center (generalizedFitting G)).card_quotient_dvd_card
    rw [Nat.card_congr e.toEquiv]
    change 11 ∣ Nat.card M11
    rw [m11_order]
    norm_num
  have hlo := Representation.BinaryPrimeDegree.orderOf_le_finrank
    (ρ.comp (generalizedFitting G).subtype)
    (h.faithful.comp Subtype.val_injective)
    (by decide : Nat.Prime 11) (by decide : 11 ≠ 2) h11
  rwa [Representation.BinaryPrimeDegree.orderOf_two_mod_eleven] at hlo

/-- Every ambient involution moves at least four binary dimensions. -/
theorem m11_involution_fixedCodim_ge_four (t : G) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    4 ≤ fixedCodim ρ (zpowers t) := by
  let L := generalizedFitting G
  let σ := ρ.comp L.subtype
  let := h.quasisimple
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  have hσ : Function.Injective σ := h.faithful.comp Subtype.val_injective
  let j : G →* linearNormalizer σ := ρ.asGroupHom.codRestrict _
    (fun g => actionImage_le_linearNormalizer ρ L ⟨g, rfl⟩)
  have hj : Function.Injective j := by
    intro a b hab
    apply h.faithful
    exact congrArg (fun x : linearNormalizer σ => (x.val : Module.End (ZMod 2) V)) hab
  have hgen := normalizerThreeConjugates_of_centralCover σ hσ h.irreducible e
    m11_threeConjugateAutomorphisms
  obtain ⟨a, b, hab⟩ := hgen (j t)
    (fun he => ht (hj (he.trans j.map_one.symm)))
    (by rw [← map_pow, ht2, map_one])
  have hd := SL2SevenCentralProduct.finrank_le_three_mul_fixedCodim_of_three_conjugates
    (normalizerRepresentation σ) _
    (normalizerImage_subspaceCommutator_eq_top σ hσ h.irreducible) (j t) a b hab
  have he : fixedCodim (normalizerRepresentation σ) (zpowers (j t)) =
      fixedCodim ρ (zpowers t) := by
    rw [fixedCodim_zpowers_eq_displacement_rank, fixedCodim_zpowers_eq_displacement_rank]
    rfl
  rw [he] at hd
  have hlo := m11_finrank_ge_ten ρ h e
  omega

/-- No ambient involution lies outside the irreducibly acting M11 component,
including when that component is a nontrivial central cover. -/
theorem m11_involution_mem_generalizedFitting (t : G) (ht2 : t ^ 2 = 1) :
    t ∈ generalizedFitting G := by
  let := h.quasisimple
  let := h.irreducible
  let t' : normalizer (generalizedFitting G : Set G) :=
    ⟨t, le_normalizer_of_normal (mem_top t)⟩
  exact involution_mem_of_inner ρ (generalizedFitting G) h.faithful t' ht2
    (automorphism_inner_of_central_quotient_m11 e _)

/-- A cubic source witness is a component four-group whose three involutions
all have precisely its codimension-four fixed space. -/
theorem m11_cubic_actor : ∃ A : Subgroup G,
    IsElementaryTwo A ∧ IsCubic ρ A ∧ rank A = 2 ∧ fixedCodim ρ A = 4 ∧
    A ≤ generalizedFitting G ∧ ∀ t ∈ A, t ≠ 1 → fixedSpace ρ (zpowers t) = fixedSpace ρ A := by
  let := h.quasisimple
  have hr := (primeRank_le_central_quotient_automorphisms ρ (generalizedFitting G)
    h.faithful h.irreducible e).trans m11_automorphism_twoRank_le_two
  obtain ⟨A, hA, hc, hd⟩ := (cubicRatio_le_nat_iff ρ 2).mp h.cubic_le_two
  let : IsElementaryAbelian 2 A := hA.2
  have har := hA.rank_le_of_primeRank_le hr
  have hle (t : G) (ht : t ∈ A) : fixedSpace ρ A ≤ fixedSpace ρ (zpowers t) := by
    intro v hv a
    exact hv ⟨a, (zpowers_le.mpr ht) a.property⟩
  have hcod (t : G) (ht : t ∈ A) : fixedCodim ρ (zpowers t) ≤ fixedCodim ρ A := by
    have hm := Submodule.finrank_mono (hle t ht)
    have h₁ := fixedCodim_add_finrank ρ A
    have h₂ := fixedCodim_add_finrank ρ (zpowers t)
    omega
  obtain ⟨t, ht, htn⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  have hlow := m11_involution_fixedCodim_ge_four ρ h e t htn
    (elemPow_eq_one_of_isElementaryAbelian t ht)
  have hct := hcod t ht
  have hdim : fixedCodim ρ A = 4 := by omega
  refine ⟨A, hA, hc, by omega, hdim, ?_, ?_⟩
  · intro a ha
    exact m11_involution_mem_generalizedFitting ρ h e a
      (elemPow_eq_one_of_isElementaryAbelian a ha)
  intro a ha han
  apply (Submodule.eq_of_le_of_finrank_eq (hle a ha) ?_).symm
  have hlow := m11_involution_fixedCodim_ge_four ρ h e a han
    (elemPow_eq_one_of_isElementaryAbelian a ha)
  have hm := hcod a ha
  have h₁ := fixedCodim_add_finrank ρ A
  have h₂ := fixedCodim_add_finrank ρ (zpowers a)
  omega

end CFSG.Quasithin.ChapterK.SporadicCatalogue

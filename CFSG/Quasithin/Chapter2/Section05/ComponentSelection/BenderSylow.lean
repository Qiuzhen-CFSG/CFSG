module

public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.Projections
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.OmegaNormalizer.Models
public import Theory.SpecificGroups.PSL2.SylowIntersections
public import Theory.SpecificGroups.Suzuki.SylowIntersections
public import Theory.SpecificGroups.SU3.SylowFixedInvolutions

/-!
# Bender Sylow uniqueness and the normal-component application

Concrete binary linear and Suzuki root centralizers, and the unitary
common-involution theorem, show that all three Bender models have trivial
intersections of distinct Sylow two-subgroups. Hermitian basis transport
retains the actual model equivalence and both field cardinalities.

For a normal Bender component, saturation and the original nontrivial
inner marker then give the full Sylow intersection with O2(H_U).
The nonnormal component-orbit product is a separate remaining assembly.

Source: Aschbacher--Smith 2.5.3(3), printed p.552.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
variable {K : Type*} [Group K] [Finite K]

private theorem sylow_map_injective {J : Type*} [Group J] [Finite J]
    (e : K ≃* J) (P Q : Sylow 2 K)
    (h : P.mapSurjective (f := e.toMonoidHom) e.surjective =
      Q.mapSurjective (f := e.toMonoidHom) e.surjective) : P = Q := by
  apply Sylow.ext
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  exact congrArg Sylow.toSubgroup h

/-- Each of the three exact Bender models has a unique Sylow subgroup
containing a given involution. -/
theorem bender_sylow_eq_of_common_involution
    (hm : ClassificationModels.IsBenderModel K)
    (P Q : Sylow 2 K) (z : K) (hzP : z ∈ P) (hzQ : z ∈ Q)
    (hzo : orderOf z = 2) : P = Q := by
  have hzne : z ≠ 1 := by intro h; simp [h] at hzo
  have hpow : z ^ 2 = 1 := by simpa only [hzo] using pow_orderOf_eq_one z
  have himage {J : Type} [Group J] (e : K ≃* J) :
      (P : Subgroup K).map e.toMonoidHom ⊓ (Q : Subgroup K).map e.toMonoidHom ≠ ⊥ := by
    intro hb
    have he : e z = 1 := mem_bot.mp (hb ▸
      (show e z ∈ (P : Subgroup K).map e.toMonoidHom ⊓
        (Q : Subgroup K).map e.toMonoidHom from
        ⟨mem_map_of_mem e.toMonoidHom hzP, mem_map_of_mem e.toMonoidHom hzQ⟩))
    exact hzne (e.injective (he.trans (map_one e).symm))
  cases hm with
  | linear n hn h =>
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [← Nat.card_eq_fintype_card] using hF)
    exact sylow_map_injective e P Q (Theory.PSL2.sylow_eq_of_inf_ne_bot _ _ (himage e))
  | unitary n hn h =>
    obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := h
    have hf : Nat.card {x : F // J.conj x = x} = 2 ^ n :=
      FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hF hconj
    obtain ⟨eJ⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
      J (2 ^ n) hF hf
    let J0 := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
    let e0 := e.trans eJ
    let : Finite _ := Finite.of_injective e0.symm e0.symm.injective
    apply sylow_map_injective e0 P Q
    exact HermitianForm.SylowFixedInvolutions.projective_sylow_eq_of_common_involution
      J0 hn rfl hF hf _ _ (e0 z) (mem_map_of_mem e0.toMonoidHom hzP)
      (mem_map_of_mem e0.toMonoidHom hzQ)
      (fun he => hzne (e0.injective (he.trans (map_one e0).symm)))
      (by rw [← map_pow, hpow, map_one])
  | suzuki m hm h =>
    obtain ⟨e⟩ := h
    exact sylow_map_injective e P Q
      (suzuki_sylow_eq_of_inf_ne_bot m (by omega) _ _ (himage e))

/-- A nontrivial common two-subgroup determines the same Sylow subgroup
in every model on the full Bender list. -/
theorem bender_sylow_eq_of_inf_ne_bot
    (hm : ClassificationModels.IsBenderModel K) (P Q : Sylow 2 K)
    (hi : (P : Subgroup K) ⊓ (Q : Subgroup K) ≠ ⊥) : P = Q := by
  let I := (P : Subgroup K) ⊓ (Q : Subgroup K)
  let : Nontrivial I := (Subgroup.nontrivial_iff_ne_bot _).mpr hi
  have hp : IsPGroup 2 I := P.isPGroup'.to_le inf_le_left
  have hd : 2 ∣ Nat.card I := hp.card_eq_or_dvd.resolve_left
    (by have := Finite.one_lt_card (α := I); omega)
  obtain ⟨z, hzo⟩ := exists_prime_orderOf_dvd_card' (G := I) 2 hd
  exact bender_sylow_eq_of_common_involution hm P Q z z.property.1 z.property.2
    (by simpa only [Subgroup.orderOf_coe] using hzo)

variable {G : Type*} [Group G] [Finite G] {M H U HU : Subgroup G}

/-- The normal-component branch of 2.5.3(3): all projection and Sylow
uniqueness inputs are proved from the genuine earlier inner marker. -/
theorem normal_bender_component_sylow_intersection
    (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (hsat : ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
      HU ≤ normalizer (P : Set G) → P ≤ twoCore HU)
    (D : Subgroup H) [D.Normal] (hD : IsComponent H D)
    (hm : ClassificationModels.IsBenderModel D)
    (z : H) (hz : (z : G) ∈ twoCore HU)
    (hinner : z ∈ D ⊔ centralizer (D : Set H))
    (hnoncentral : z ∉ centralizer (D : Set H)) :
    ∃ P : Sylow 2 D, ((P : Subgroup D).map D.subtype).map H.subtype =
      D.map H.subtype ⊓ twoCore HU := by
  let : IsQuasisimple D := hD.2
  let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
  let : Nontrivial D := (QuotientGroup.mk'_surjective (center D)).nontrivial
  have hc := BenderFusion.OmegaNormalizerModels.centerless_of_bender_model hm
  have hZ : IsPGroup 2 (center D) := hc ▸ IsPGroup.of_bot
  obtain ⟨d, hd, hdc⟩ := saturated_pair_noncentral_projection hpair hsat D hZ z hz hinner hnoncentral
  apply saturated_pair_sylow_intersection hpair hsat D
  intro P R hP hR
  apply bender_sylow_eq_of_inf_ne_bot hm P R
  intro hb
  have hd1 : (⟨d, hd.1⟩ : D) = 1 := mem_bot.mp (hb ▸
    (show (⟨d, hd.1⟩ : D) ∈ (P : Subgroup D) ⊓ (R : Subgroup D) from
      ⟨hP hd.2, hR hd.2⟩))
  have hdval : d = 1 := congrArg Subtype.val hd1
  exact hdc (hdval.symm ▸ (centralizer (D : Set H)).one_mem)

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection

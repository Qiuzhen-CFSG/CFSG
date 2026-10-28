module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.Quotients

/-!
# A cubic conjugate centralized by the source involution

The actual `quotientAction` on `U/Z`, together with its swapped binary
summands, gives transitivity in the involution fiber of `H/Z → H/O₂(H)`.
A cubic subgroup of the actor centralizer lifts through these two maps.
Sylow conjugacy then supplies an ambient conjugate of the chosen `D_H`
centralized by `t`.

The model calculation producing a cubic in the actor centralizer remains
explicit. The theorem does not assume the centralizing conjugate or any
nonfusion assertion. The recognition and local-core hypotheses belong to
15.3.58 and 15.3.59(1).

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
proof of 15.3.61(1), printed p.1150.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
attribute [local instance] denominator_normal_H

/-- The swap on the genuine vector quotient supplies the involution-fiber
transitivity in `H/Z → H/O₂(H)`. -/
theorem source_involution_fiber
    (Z ZS : Subgroup G) [(Z.subgroupOf (closureU Z ZS)).Normal]
    (hZS : ZS ≤ centralizerH Z) (hZZS : Z ≤ ZS)
    (hU : closureU Z ZS = coreQ Z)
    (t : centralizerH Z) (ht : (t : G) ^ 2 = 1)
    (e : VectorQuotient Z ZS ≃* Multiplicative W) (s : W ≃ₗ[ZMod 2] W)
    (he : ∀ q, e (quotientAction Z ZS t q) = Multiplicative.ofAdd (s (e q).toAdd))
    (A B : Submodule (ZMod 2) W) (hAB : IsCompl A B)
    (hA : ∀ w ∈ A, s w ∈ B) (hB : ∀ w ∈ B, s w ∈ A) :
    ∀ x : CentralQuotient Z, x ^ 2 = 1 →
      actorProjection Z (denominator_le_core Z ZS hZZS hU) x =
        actorProjection Z (denominator_le_core Z ZS hZZS hU) (centralProjection Z t) →
      ∃ u ∈ (actorProjection Z (denominator_le_core Z ZS hZZS hU)).ker,
        u⁻¹ * centralProjection Z t * u = x := by
  intro x hx hsame
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf (centralizerH Z)) x
  have hsq : (h : G) ^ 2 ∈ Z := by
    have hh : centralProjection Z (h ^ 2) = 1 := by
      rw [map_pow]
      exact hx
    have hz : h ^ 2 ∈ Z.subgroupOf (centralizerH Z) :=
      (QuotientGroup.eq_one_iff (h ^ 2)).mp hh
    exact hz
  have hdiff : (h : G) * (t : G)⁻¹ ∈ closureU Z ZS := by
    have hh := QuotientGroup.eq_iff_div_mem.mp hsame
    change h / t ∈ pCore 2 (centralizerH Z) at hh
    rw [← closure_subgroupOf_H_eq_core Z ZS hU] at hh
    change (h : G) / (t : G) ∈ closureU Z ZS at hh
    simpa only [div_eq_mul_inv] using hh
  let a : closureU Z ZS := ⟨(h : G) * (t : G)⁻¹, hdiff⟩
  have ha : ((a : G) * (t : G)) ^ 2 ∈ Z := by
    simpa only [a, mul_assoc, inv_mul_cancel, mul_one] using hsq
  obtain ⟨u, hu⟩ := swapped_quotient_coset_transitive Z ZS t ht e s he A B hAB hA hB a ha
  let uH : centralizerH Z := ⟨u, closureU_le_H hZS u.property⟩
  refine ⟨centralProjection Z uH, ?_, ?_⟩
  · rw [MonoidHom.mem_ker, actorProjection_mk]
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [← closure_subgroupOf_H_eq_core Z ZS hU]
    exact u.property
  · change (QuotientGroup.mk' _) uH⁻¹ * (QuotientGroup.mk' _) t *
        (QuotientGroup.mk' _) uH = (QuotientGroup.mk' _) h
    rw [← map_mul, ← map_mul]
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (u : G)⁻¹ * (t : G) * (u : G) / (h : G) ∈ Z
    simpa only [a, mul_assoc, inv_mul_cancel, mul_one, div_eq_mul_inv] using hu

/-- A cubic subgroup in the actual actor centralizer lifts to a cubic subgroup
of `H` centralized by `t`, using the swapped natural/dual action. -/
theorem source_exists_centralized_cubic [Finite G]
    (Z ZS : Subgroup G) [(Z.subgroupOf (closureU Z ZS)).Normal]
    (hZS : ZS ≤ centralizerH Z) (hZZS : Z ≤ ZS) (hZ : Nat.card Z = 2)
    (hU : closureU Z ZS = coreQ Z)
    (t : centralizerH Z) (ht : (t : G) ^ 2 = 1)
    (e : VectorQuotient Z ZS ≃* Multiplicative W) (s : W ≃ₗ[ZMod 2] W)
    (he : ∀ q, e (quotientAction Z ZS t q) = Multiplicative.ofAdd (s (e q).toAdd))
    (A B : Submodule (ZMod 2) W) (hAB : IsCompl A B)
    (hA : ∀ w ∈ A, s w ∈ B) (hB : ∀ w ∈ B, s w ∈ A)
    (D : Subgroup (ActorQuotient Z)) (hD : Nat.card D = 3)
    (hDC : D ≤ centralizer ({QuotientGroup.mk' (pCore 2 (centralizerH Z)) t} :
      Set (ActorQuotient Z))) :
    ∃ E : Subgroup (centralizerH Z), Nat.card E = 3 ∧
      E ≤ centralizer ({t} : Set (centralizerH Z)) ∧
      E.map (QuotientGroup.mk' (pCore 2 (centralizerH Z))) = D := by
  let f := centralProjection Z
  let g := actorProjection Z (denominator_le_core Z ZS hZZS hU)
  have hker : f.ker = Z.subgroupOf (centralizerH Z) := QuotientGroup.ker_mk' _
  have hcentral : f.ker ≤ center (centralizerH Z) := by
    rw [hker]
    exact denominator_le_center_H Z
  have hp : IsPGroup 2 f.ker := by
    rw [hker]
    exact (IsPGroup.of_card (p := 2) (n := 1) (by simpa using hZ)).comap_subtype
  obtain ⟨E, hc, hE, hm⟩ := exists_cubic_in_centralizer_of_involution_fiber f
    (QuotientGroup.mk'_surjective _) hcentral hp g (actorProjection_surjective _ _)
    (actorProjection_kernel_two _ _) t (Subtype.ext ht)
    (source_involution_fiber Z ZS hZS hZZS hU t ht e s he A B hAB hA hB) D hD hDC
  refine ⟨E, hc, hE, ?_⟩
  rw [map_map] at hm
  exact hm

/-- The lifted cubic is conjugate to the chosen Sylow three-group of `H`.
The conjugator and the subgroup equality are in the original ambient group. -/
theorem source_centralizes_conjugate [Finite G]
    (Z ZS : Subgroup G) [(Z.subgroupOf (closureU Z ZS)).Normal]
    (hZS : ZS ≤ centralizerH Z) (hZZS : Z ≤ ZS) (hZ : Nat.card Z = 2)
    (hU : closureU Z ZS = coreQ Z)
    (t : centralizerH Z) (ht : (t : G) ^ 2 = 1)
    (e : VectorQuotient Z ZS ≃* Multiplicative W) (s : W ≃ₗ[ZMod 2] W)
    (he : ∀ q, e (quotientAction Z ZS t q) = Multiplicative.ofAdd (s (e q).toAdd))
    (A B : Submodule (ZMod 2) W) (hAB : IsCompl A B)
    (hA : ∀ w ∈ A, s w ∈ B) (hB : ∀ w ∈ B, s w ∈ A)
    (D : Subgroup (ActorQuotient Z)) (hD : Nat.card D = 3)
    (hDC : D ≤ centralizer ({QuotientGroup.mk' (pCore 2 (centralizerH Z)) t} :
      Set (ActorQuotient Z)))
    (P : Sylow 3 (centralizerH Z)) (hP : Nat.card P = 3) :
    ∃ g : G, ((P : Subgroup (centralizerH Z)).map (centralizerH Z).subtype).map
      (MulAut.conj g).toMonoidHom ≤ centralizer ({(t : G)} : Set G) := by
  obtain ⟨E, hcE, hE, _⟩ := source_exists_centralized_cubic Z ZS hZS hZZS hZ hU
    t ht e s he A B hAB hA hB D hD hDC
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 1) (by simpa using hcE)
  obtain ⟨S, hES⟩ := hEp.exists_le_sylow
  have hcS : Nat.card S = 3 := by
    rw [S.card_eq_multiplicity, ← P.card_eq_multiplicity, hP]
  have heq : E = (S : Subgroup (centralizerH Z)) :=
    eq_of_le_of_card_ge hES (by rw [hcS, hcE])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (centralizerH Z) P S
  have hgE : (P : Subgroup (centralizerH Z)).map (MulAut.conj g).toMonoidHom = E := by
    change ((g • P : Sylow 3 (centralizerH Z)) : Subgroup (centralizerH Z)) = E
    rw [hg, heq]
  refine ⟨g, ?_⟩
  have hm : ((P : Subgroup (centralizerH Z)).map (centralizerH Z).subtype).map
      (MulAut.conj (g : G)).toMonoidHom = E.map (centralizerH Z).subtype := by
    rw [← hgE, map_map, map_map]
    rfl
  rw [hm]
  rintro _ ⟨x, hx, rfl⟩
  exact mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_centralizer_singleton_iff.mp (hE hx)))

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic

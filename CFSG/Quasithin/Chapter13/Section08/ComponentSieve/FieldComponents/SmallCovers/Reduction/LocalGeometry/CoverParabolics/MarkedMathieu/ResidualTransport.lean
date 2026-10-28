module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics.NativeWitness


/-!
# Residual transport through the actual hexad cover

The canonical residual has the genuine triple-cover quotient already
constructed by HexadCoverRestriction. That quotient accounts for the full
odd part of the hexad lift, so the lift modulo its residual is a two-group.
Consequently order-three generators in the lift belong to its residual.

For the other direction, the cover residual of the new component lies in
the six-point kernel. Its image in the native elementary two-kernel is
trivial by two-perfectness. It therefore lies in O₂,Z(K), and functoriality
of the two-residual places it in the original Y. This suffices to preserve
Y < L₁ without an unnecessary equality of cover residuals.

Source: Aschbacher–Smith 13.8.21(2), printed p.956 (PDF p.973),
the replacement of the covered Mathieu component by its hexad component.
-/

@[expose] public section

open Subgroup Sporadic.Mathieu Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics
namespace MarkedMathieu
variable {G : Type*} [Group G] [Finite G]

private theorem card_of_surjective {X Z : Type*} [Group X] [Group Z]
    (f : X →* Z) (hf : Function.Surjective f) :
    Nat.card X = Nat.card f.ker * Nat.card Z := by
  rw [← f.ker.card_mul_index]
  congr 1
  exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv

private theorem tripleCoverSix_card {X : Type*} [Group X]
    (h : SolvableExclusion.IsTripleCoverSix X) : Nat.card X = 1080 := by
  obtain ⟨_, hc, ⟨e⟩⟩ := h
  have he : Nat.card (X ⧸ center X) = 360 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hh := (center X).card_mul_index
  change Nat.card (center X) * Nat.card (X ⧸ center X) = Nat.card X at hh
  rw [hc, he] at hh
  exact hh.symm

/-- The remaining quotient of the actual hexad lift is a two-group. The
odd part is already present in the genuinely constructed triple cover. -/
theorem hexadLift_quotient_residual_isTwoGroup (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (hc : Nat.card (center (K ⧸ pCore 2 K)) = 3)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    IsPGroup 2 (hexadLift K e B ⧸ solvableResidual (hexadLift K e B)) := by
  let E := hexadPreimage K e B
  let E' := hexadStarPreimage K e B
  let F := hexadLift K e B
  let R := hexadResidualIn K e B
  have hcE' : Nat.card E' = 17280 := by
    rw [card_of_surjective (hexadStarRestriction K e B)
      (hexadStarRestriction_surjective K e B), hexadStarRestriction_ker,
      Nat.card_congr (subgroupOfEquivOfLe (center_le_hexadStarPreimage K e B)).toEquiv,
      hc, m22Hexad_stabilizer_card hB]
  have hk : IsPGroup 2 (hexadStarReduction K e B).ker := by
    rw [hexadStarReduction_ker]
    exact pCore_isPGroup.comap_of_injective _ E.subtype_injective
  obtain ⟨n, hn⟩ := hk.exists_card_eq
  have hcF : Nat.card F = 1080 * 2 ^ (n + 4) := by
    have heF : Nat.card F = Nat.card E :=
      (Nat.card_congr (E.equivMapOfInjective K.subtype K.subtype_injective).toEquiv).symm
    rw [heF, card_of_surjective (hexadStarReduction K e B)
        (hexadStarReduction_surjective K e B), hn, hcE', pow_add]
    ring
  have hdiv : 1080 ∣ Nat.card R := by
    rw [← tripleCoverSix_card (hexadResidualIn_isTripleCoverSix K e hc hB)]
    exact (pCore 2 R).index_dvd_card
  have hcR : Nat.card R = Nat.card (solvableResidual F) :=
    (Nat.card_congr ((solvableResidual F).equivMapOfInjective F.subtype
      F.subtype_injective).toEquiv).symm
  rw [hcR] at hdiv
  apply isPGroup_iff_card_dvd_pow.mpr
  refine ⟨n + 4, ?_⟩
  apply Nat.dvd_of_mul_dvd_mul_left (show 0 < 1080 by decide)
  have hd := Nat.mul_dvd_mul_right hdiv (Nat.card (F ⧸ solvableResidual F))
  change 1080 * (solvableResidual F).index ∣
    Nat.card (solvableResidual F) * (solvableResidual F).index at hd
  rw [(solvableResidual F).card_mul_index, hcF] at hd
  exact hd


omit [Finite G] in
/-- Any two-perfect subgroup of the literal central preimage lies in the
ambient cover residual. -/
private theorem le_coverResidualIn_of_isPPerfect (K A : Subgroup G)
    (hA : IsPPerfect 2 A)
    (hle : A ≤ (centralPreimage (pCore 2 K)).map K.subtype) :
    A ≤ coverResidualIn K := by
  let C := (centralPreimage (pCore 2 K)).map K.subtype
  let d := (centralPreimage (pCore 2 K)).equivMapOfInjective K.subtype K.subtype_injective
  let f : A →* centralPreimage (pCore 2 K) := d.symm.toMonoidHom.comp (inclusion hle)
  have hm := map_pResidual_le 2 f
  rw [(pResidual_eq_top_iff 2 A).mpr hA] at hm
  intro x hx
  have hr := hm (mem_map.mpr ⟨⟨x, hx⟩, mem_top _, rfl⟩)
  exact mem_map.mpr ⟨(f ⟨x, hx⟩).val,
    mem_map.mpr ⟨f ⟨x, hx⟩, hr, rfl⟩,
    congrArg Subtype.val (d.apply_symm_apply (inclusion hle ⟨x, hx⟩))⟩

/-- The two-residual of the six-point kernel maps trivially to its native
elementary two-kernel. Thus the replacement residual lies in the original
cover residual; no equality of the two ambient two-cores is asserted. -/
theorem hexadResidual_coverResidual_le (K : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (hc : Nat.card (center (K ⧸ pCore 2 K)) = 3)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    coverResidualIn (hexadResidualIn K e B) ≤ coverResidualIn K := by
  let R := hexadResidualIn K e B
  let a := hexadResidualEmbeddingEquiv K e B
  let f : R →* MulAction.stabilizer M22 B :=
    (hexadRestriction K e B).comp
      ((solvableResidual (hexadPreimage K e B)).subtype.comp a.symm.toMonoidHom)
  have hfker (z : coverResidual R) : f z.val ∈ (m22SetAction B).ker := by
    rw [← hexadNativeSixProjection_ker hB]
    change hexadResidualInSixProjection K e hB z.val = 1
    apply (hexadResidualInSixProjection_ker K e hc hB).symm ▸
      (coverResidual_le_centralPreimage (G := R)) z.property
  let u : coverResidual R →* (m22SetAction B).ker :=
    (f.comp (coverResidual R).subtype).codRestrict _ hfker
  have hu := (coverResidual_isPPerfect (G := R)).hom_eq_one_of_isPGroup
    (IsPGroup.of_card (p := 2) (n := 4) (m22HexadKernel_card hB)) u
  apply le_coverResidualIn_of_isPPerfect K _ (coverResidualIn_isPPerfect R)
  rintro x ⟨z, hz, rfl⟩
  let zC : coverResidual R := ⟨z, hz⟩
  have huf : f z = 1 := congrArg (fun v : coverResidual R →* (m22SetAction B).ker =>
    (v zC).val) hu
  have hfz : mathieuProjection K e (a.symm z).val.val = 1 :=
    congrArg Subtype.val huf
  have hzK : (a.symm z).val.val ∈ centralPreimage (pCore 2 K) := by
    rw [← mathieuProjection_ker K e]
    exact hfz
  refine mem_map.mpr ⟨(a.symm z).val.val, hzK, ?_⟩
  exact (hexadResidualEmbeddingEquiv_apply K e B (a.symm z)).symm.trans
    (congrArg Subtype.val (a.apply_symm_apply z))

end MarkedMathieu
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics

module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.Support
public import Theory.Representation.BinaryOffender.InnerNormalizerActors
public import Theory.Representation.BinaryOffender.NormalizerImage
public import Theory.SpecificGroups.BinaryLinear.AutomorphismTwoRank.Five

/-!
# Inner pullback and graph actors for binary SL₅

Conjugation on the faithful image gives the actual action of the full linear
normalizer on SL₅. A normalizing involution inducing an inner automorphism is
itself in the action image: centerlessness makes the inner representative an
involution, and binary Schur's lemma kills their centralizing quotient.
Consequently any elementary actor outside the image induces a graph actor.
The existing full-automorphism geometry bounds its rank by five.

Actors contained in the image pull back to genuine elementary subgroups of
SL₅, preserving the cubic identity, rank and common fixed-space codimension.
The consumer in `FiveDisplacement` uses these equalities to apply the inner
estimate to exactly the original linear operators.

Source: Guralnick–Malle, *Classification of 2F-modules, II*, author manuscript,
Propositions 4.7 and 4.8(3), pp.25–28; Aschbacher–Smith K.3.2,
printed pp.454–455 (PDF pp.465–466).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open BinaryLinear.OuterCyclic

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (σ : Representation (ZMod 2) SL5TenDimensional.Group V)

/-- Faithfulness identifies SL₅ with its literal action image. -/
noncomputable def imageEquiv (hf : Function.Injective σ) :
    SL5TenDimensional.Group ≃* actionImage σ :=
  MonoidHom.ofInjective (fun _ _ h => hf (congrArg Units.val h))

/-- The full normalizer acting on the original SL₅ group by conjugation. -/
noncomputable def conjugation (hf : Function.Injective σ) :
    linearNormalizer σ →* MulAut SL5TenDimensional.Group :=
  (MulAut.congr (imageEquiv σ hf).symm).toMonoidHom.comp
    (actionImage σ).normalizerMonoidHom

/-- The marked automorphism acts by the original normalizer operators. -/
theorem conjugation_apply (hf : Function.Injective σ)
    (t : linearNormalizer σ) (g : SL5TenDimensional.Group) :
    σ.asGroupHom (conjugation σ hf t g) =
      t.val * σ.asGroupHom g * t.val⁻¹ := by
  let e := imageEquiv σ hf
  change (e (e.symm ((actionImage σ).normalizerMonoidHom t (e g)))).val = _
  rw [e.apply_symm_apply]
  rfl

/-- The same conjugation action in the binary linear-group coordinates. -/
noncomputable def linearConjugation (hf : Function.Injective σ) :
    linearNormalizer σ →* MulAut (LinearGroup 5) :=
  (MulAut.congr (slEquivLinear 5)).toMonoidHom.comp (conjugation σ hf)

/-- Binary Schur removes the conjugation kernel on elementary actors. -/
theorem conjugation_injective_on_elementary (hf : Function.Injective σ)
    (hi : IsIrreducible σ) (A : Subgroup (linearNormalizer σ))
    [IsElementaryAbelian 2 A] :
    Function.Injective ((conjugation σ hf).comp A.subtype) :=
  (MulAut.congr (imageEquiv σ hf).symm).injective.comp
    (normalizer_elementary_conjugation_injective σ hi A)

/-- An inner normalizing involution is a literal SL₅ operator. -/
theorem involution_mem_image_of_inner (hf : Function.Injective σ)
    (hi : IsIrreducible σ) (t : linearNormalizer σ) (ht : t ^ 2 = 1)
    (hinner : conjugation σ hf t ∈ MulAut.innerSubgroup SL5TenDimensional.Group) :
    t.val ∈ actionImage σ := by
  obtain ⟨x, hx⟩ := hinner
  have hx2 : x ^ 2 = 1 := by
    apply MulAut.conj_injective_of_center_eq_bot SL5TenDimensional.center_eq_bot
    rw [map_pow, hx, ← map_pow, ht, map_one, map_one]
  let e := imageEquiv σ hf
  let α := (actionImage σ).normalizerMonoidHom t
  have ha : α = MulAut.conj (e x) := by
    apply (MulAut.congr e.symm).injective
    rw [MulAut.congr_conj, e.symm_apply_apply]
    exact hx.symm
  let y : (Module.End (ZMod 2) V)ˣ := (e x).val
  have hy2 : y ^ 2 = 1 := by
    change σ.asGroupHom x ^ 2 = 1
    rw [← map_pow, hx2, map_one]
  have ht2 : t.val ^ 2 = 1 := congrArg Subtype.val ht
  have he (g : actionImage σ) : t.val * g.val * t.val⁻¹ = y * g.val * y⁻¹ :=
    congrArg Subtype.val (MulEquiv.congr_fun ha g)
  have hty : Commute t.val y := by
    have h := he (e x)
    change t.val * y * t.val⁻¹ = y * y * y⁻¹ at h
    simp only [mul_assoc, mul_inv_cancel, mul_one] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  have hu2 : (y⁻¹ * t.val) ^ 2 = 1 := by
    rw [hty.symm.inv_left.mul_pow, inv_pow, hy2, ht2, inv_one, one_mul]
  have huc : y⁻¹ * t.val ∈ centralizer (actionImage σ : Set _) := by
    apply mem_centralizer_iff.mpr
    intro g hg
    have hconj : (y⁻¹ * t.val) * g * (y⁻¹ * t.val)⁻¹ = g := by
      calc
        _ = y⁻¹ * (t.val * g * t.val⁻¹) * y := by group
        _ = y⁻¹ * (y * g * y⁻¹) * y := by rw [he ⟨g, hg⟩]
        _ = g := by group
    exact (mul_inv_eq_iff_eq_mul.mp hconj).symm
  let : IsIrreducible ((Units.coeHom (Module.End (ZMod 2) V)).comp
      (actionImage σ).subtype) := imageRepresentation_isIrreducible σ hi
  have hu := BinaryIrreducibleCentralizer.centralizing_square_one_eq_one
    (Units.coeHom (Module.End (ZMod 2) V)) (actionImage σ)
    (fun _ _ h => Units.ext h) hu2 huc
  have htval : t.val = (e x).val := (inv_mul_eq_one.mp hu).symm
  rw [htval]
  exact (e x).property

/-- An elementary actor outside the image has rank at most five. -/
theorem outer_rank_le_five (hf : Function.Injective σ) (hi : IsIrreducible σ)
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (hout : ¬ A ≤ (actionImage σ).subgroupOf (linearNormalizer σ)) : rank A ≤ 5 := by
  let : Finite (LinearGroup 5) := Finite.of_injective
    (fun g : LinearGroup 5 => (g : Space 5 → Space 5)) DFunLike.coe_injective
  let : IsElementaryAbelian 2 A := hA.2
  let f := linearConjugation σ hf
  let E := A.map f
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map f
  have hE : ¬ E ≤ MulAut.innerSubgroup (LinearGroup 5) := by
    intro hE
    apply hout
    intro t ht
    apply involution_mem_image_of_inner σ hf hi t
      (elemPow_eq_one_of_isElementaryAbelian t ht)
    obtain ⟨x, hx⟩ := hE (mem_map_of_mem f ht)
    obtain ⟨g, hg⟩ := (MulAut.congr_inner_iff (slEquivLinear 5)
      (conjugation σ hf t)).mp ⟨x, hx.symm⟩
    exact ⟨g, hg.symm⟩
  have hr := BinaryLinear.AutomorphismTwoRank.five_outer_elementary_rank_le E hE
  have hj : Function.Injective (f.comp A.subtype) :=
    (MulAut.congr (slEquivLinear 5)).injective.comp
      (conjugation_injective_on_elementary σ hf hi A)
  have heq : Nat.card A = Nat.card E := by
    have he : (f.comp A.subtype).range = E := by
      ext x
      change (∃ a : A, f a = x) ↔ ∃ a, a ∈ A ∧ f a = x
      constructor
      · rintro ⟨a, ha⟩
        exact ⟨a, a.property, ha⟩
      · rintro ⟨a, ha, hax⟩
        exact ⟨⟨a, ha⟩, hax⟩
    rw [← he]
    exact Nat.card_congr (MonoidHom.ofInjective hj).toEquiv
  have ht : IsElementaryAbelian 2 (⊤ : Subgroup E) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
      Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 E) x.val)) }
  have hcard := (primeRank_le_iff_elementary_card_le E).mp hr ⊤ ht
  have hcardA : Nat.card A ≤ 2 ^ 5 := by
    rw [heq]
    simpa only [Nat.card_congr Subgroup.topEquiv.toEquiv] using hcard
  have hl := Nat.log_mono_right (b := 2) hcardA
  simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using hl

/-- An actor outside the image contains an involution inducing the actual
inverse-transpose automorphism composed with an inner automorphism. -/
theorem exists_graph_actor (hf : Function.Injective σ) (hi : IsIrreducible σ)
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (hout : ¬ A ≤ (actionImage σ).subgroupOf (linearNormalizer σ)) :
    ∃ t ∈ A, t ^ 2 = 1 ∧ t.val ∉ actionImage σ ∧
      ∃ g : LinearGroup 5,
        linearConjugation σ hf t = graphLinear 5 * MulAut.conj g := by
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨t, ht, htout⟩ := SetLike.not_le_iff_exists.mp hout
  have ht2 : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian t ht
  refine ⟨t, ht, ht2, htout, ?_⟩
  obtain ⟨g, hg | hg⟩ := inner_graph (Or.inr rfl) (linearConjugation σ hf t)
  · have hin : conjugation σ hf t ∈ MulAut.innerSubgroup SL5TenDimensional.Group := by
      obtain ⟨x, hx⟩ := (MulAut.congr_inner_iff (slEquivLinear 5)
        (conjugation σ hf t)).mp ⟨g, hg⟩
      exact ⟨x, hx.symm⟩
    exact (htout (involution_mem_image_of_inner σ hf hi t ht2 hin)).elim
  · exact ⟨g, hg⟩

/-- Pull an inner actor back to SL₅ while preserving all three quantities
used in the cubic common-fixed-space estimate. -/
theorem inner_actor_pullback (hf : Function.Injective σ)
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (hin : A ≤ (actionImage σ).subgroupOf (linearNormalizer σ))
    (hc : IsCubic (normalizerRepresentation σ) A) :
    ∃ B : Subgroup SL5TenDimensional.Group,
      IsElementaryTwo B ∧ IsCubic σ B ∧ rank B = rank A ∧
      fixedCodim σ B = fixedCodim (normalizerRepresentation σ) A ∧
      B.map (normalizerEmbedding σ) = A := by
  let : IsElementaryAbelian 2 A := hA.2
  let j := normalizerEmbedding σ
  have hj : Function.Injective j := normalizerEmbedding_injective σ hf
  let B := A.comap j
  have hm : B.map j = A := by
    apply le_antisymm (map_comap_le _ _)
    intro t ht
    obtain ⟨x, hx⟩ := hin ht
    have hjx : j x = t := Subtype.ext hx
    exact ⟨x, show j x ∈ A from hjx.symm ▸ ht, hjx⟩
  have hB : IsElementaryAbelian 2 B := {
    toIsMulCommutative := A.comap_injective_isMulCommutative hj
    exponent_dvd_p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro x
      apply Subtype.ext
      apply hj
      change j ((x : SL5TenDimensional.Group) ^ 2) = j 1
      rw [map_pow, map_one]
      exact elemPow_eq_one_of_isElementaryAbelian (j x) x.property }
  have hnontrivial : B ≠ ⊥ := by
    intro hb
    apply hA.1
    rw [← hm, hb, Subgroup.map_bot]
  refine ⟨B, ⟨hnontrivial, hB⟩, ?_, ?_, ?_, hm⟩
  · intro a ha b hb c hc' v
    exact hc (j a) ha (j b) hb (j c) hc' v
  · rw [← hm, rank_map_injective j hj]
  · have he := fixedCodim_map_equivariant σ (normalizerRepresentation σ)
      j (LinearEquiv.refl _ _) (fun _ _ => rfl) B
    rwa [hm] at he

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement

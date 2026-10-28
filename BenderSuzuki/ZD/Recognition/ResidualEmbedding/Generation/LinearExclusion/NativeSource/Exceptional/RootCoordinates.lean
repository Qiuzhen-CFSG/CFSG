module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.Setup
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels.LocalStructure.LinearBorel
public import Theory.SpecificGroups.PSL2.RootSemilinearFixedBound
public import Theory.SpecificGroups.PSL2.SemilinearCoverage

/-!
# Coordinates for the original distinguished root

The simultaneous Borel–Weyl marking of the proper residual PSL₂ subgroup
identifies the actual distinguished closure A inside M with the additive
field of order 2ⁿ. The original torus K = D ∩ L becomes the diagonal torus.
Every scalar is realized because squaring is bijective in the finite binary
field. Conjugation by M ∩ N_G(L) induces a root-preserving automorphism of
PSL₂; the proved automorphism coverage and root calculation make it scalar
semilinear in the same coordinates.

The two actor descriptions share one root equivalence, and the action is
literal left conjugation inside the original M. These are the coordinates
used by the exceptional affine-action construction after GLS IV, Chapter 2,
Lemma 15.7. No exceptional field-action certificate is an input.

Source: refs/KGroup/GLS4/Chapter2.tex, lines 2745–2758, using Chapter 4,
Lemma 3.2 and the automorphism description of binary PSL₂.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion
open Subgroup Theory.GroupTheory BenderSuzuki.Converse PFchapter1section1 PFAppendixIII
universe u

private theorem borel_square_one_mem_unip {F : Type*} [Field F] [CharP F 2]
    {x : SL2 F} (hx : x ∈ Borel F) (h2 : x ^ 2 = 1) : x ∈ Unip F := by
  have h10 := (mem_Borel_iff _).mp hx
  have h00 : x.val 0 0 = 1 := by
    have hh := congrArg (fun a : SL2 F => a.val 0 0) h2
    have hs : x.val 0 0 ^ 2 = 1 := by
      simpa [pow_two, Matrix.mul_apply, Fin.sum_univ_two, h10] using hh
    rcases sq_eq_one_iff.mp hs with h | h
    · exact h
    · simpa only [CharTwo.neg_eq] using h
  have h11 : x.val 1 1 = 1 := by rw [Borel_lower_right hx, h00, inv_one]
  apply (mem_Unip_iff _).mpr
  refine ⟨x.val 0 1, ?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]

private theorem marked_pair_torus
    {G : Type*} [Group G] {M L : Subgroup G}
    {F : Type*} [Field F] [CharP F 2] (e : L ≃* SL2 F)
    (he : ∀ x : L, e x ∈ Borel F ↔ (x : G) ∈ M)
    {t : G} (htL : t ∈ L) (het : e ⟨t, htL⟩ = weyl F) (x : L) :
    e x ∈ Torus F ↔ (x : G) ∈ residualPairStabilizer M t := by
  have hconj (N : Subgroup G) (a b : G) :
      b ∈ rightConjugate N a ↔ a * b * a⁻¹ ∈ N := by
    rw [rightConjugate, Subgroup.conjBy, mem_map_equiv]
    simp [MulAut.conj_apply]
  have hconjF (N : Subgroup (SL2 F)) (a b : SL2 F) :
      b ∈ rightConjugate N a ↔ a * b * a⁻¹ ∈ N := by
    rw [rightConjugate, Subgroup.conjBy, mem_map_equiv]
    simp [MulAut.conj_apply]
  have ht : Torus F = Borel F ⊓ rightConjugate (Borel F) (weyl F) := by
    rw [Borel, rightConjugate_stabilizer, weyl_inv, weyl_smul_pInf]
    rfl
  rw [ht, mem_inf, hconjF, residualPairStabilizer, mem_inf, hconj, he]
  have hh := he (⟨t, htL⟩ * x * ⟨t, htL⟩⁻¹)
  simpa only [map_mul, map_inv, het, Subgroup.coe_mul, Subgroup.coe_inv] using
    and_congr_right (fun _ => hh)

private theorem scalar_coefficient_ne_zero
    {E : Type*} [Field E] [CharP E 2]
    (a : MulAut (Theory.PSL2.Group E)) (σ : E ≃+* E) (c : E)
    (h : ∀ t : Multiplicative E,
      a (Matrix.ProjectiveSpecialLinearGroup.OddBorel.unipotentHom E t) =
        Matrix.ProjectiveSpecialLinearGroup.OddBorel.unipotentHom E
          (Multiplicative.ofAdd (c * σ t.toAdd))) : c ≠ 0 := by
  let root := Matrix.ProjectiveSpecialLinearGroup.OddBorel.unipotentHom E
  intro hc
  have hh := h (Multiplicative.ofAdd (1 : E))
  rw [hc, zero_mul] at hh
  have he : a (root (Multiplicative.ofAdd (1 : E))) = a (root 1) := by
    simpa only [show Multiplicative.ofAdd (0 : E) = 1 from rfl, map_one] using hh
  have he' : Multiplicative.ofAdd (1 : E) = (1 : Multiplicative E) :=
    Matrix.ProjectiveSpecialLinearGroup.OddBorel.unipotentHom_injective E (a.injective he)
  exact one_ne_zero (congrArg (fun x : Multiplicative E => x.toAdd) he')

variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
local notation "A" => Subgroup.subgroupOf (closure (Z ∩ (M : Set G))) M
local notation "L" => residualGenerated M z t
local notation "𝔽" => BinaryGaloisField n
local notation "K" => Subgroup.subgroupOf (residualPairStabilizer M t ⊓ L) M

/-- Conjugation by the original point stabilizer on the distinguished root. -/
@[expose] public def Context.distinguishedConjugation : M →* MulAut A := by
  let : (A).Normal := distinguishedClosure_normal d.minimal.disconnected
  exact MulAut.conjNormal

/-- These are left-conjugation coordinates, with both elements inside M. -/
public theorem Context.distinguishedConjugation_apply (m : M) (a : A) :
    (d.distinguishedConjugation m a : M) = m * (a : M) * m⁻¹ := rfl

include d in
private theorem root_coordinates_from_marking
    (e : L ≃* SL2 𝔽) (he : ∀ x : L, e x ∈ Borel 𝔽 ↔ (x : G) ∈ M) :
    ∃ eA : A ≃* Multiplicative 𝔽, ∀ a : A,
      e ⟨a, d.distinguished_le a.property⟩ = uniHom 𝔽 (eA a) := by
  let f : A →* SL2 𝔽 := {
    toFun := fun a => e ⟨a, d.distinguished_le a.property⟩
    map_one' := map_one e
    map_mul' := by
      intro a b
      calc
        e ⟨a * b, d.distinguished_le (a * b).property⟩ =
            e ((⟨a, d.distinguished_le a.property⟩ : L) *
              ⟨b, d.distinguished_le b.property⟩) := congrArg e (Subtype.ext rfl)
        _ = _ := map_mul e _ _ }
  have hf : Function.Injective f := by
    intro a b hab
    have hh := e.injective hab
    exact Subtype.ext (Subtype.ext (congrArg (fun x : L => (x : G)) hh))
  have hle : f.range ≤ Unip 𝔽 := by
    rintro _ ⟨a, rfl⟩
    apply borel_square_one_mem_unip ((he _).mpr a.val.property)
    rw [← map_pow, ← map_one e]
    apply congrArg e
    apply Subtype.ext
    exact congrArg (fun x : closure (Z ∩ (M : Set G)) => (x : G))
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        d.distinguished_elementary_card.1.exponent_dvd_p
        (⟨a, a.property⟩ : closure (Z ∩ (M : Set G))))
  have hcardA : Nat.card A = 2 ^ n :=
    (Nat.card_congr (subgroupOfEquivOfLe distinguishedClosure_le).toEquiv).trans
      d.distinguished_elementary_card.2
  have hUnip : Unip 𝔽 = (uniHom 𝔽).range := by
    ext x
    rw [mem_Unip_iff, MonoidHom.mem_range]
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨Multiplicative.ofAdd b, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨b.toAdd, rfl⟩
  have hcardU : Nat.card (Unip 𝔽) = 2 ^ n := by
    rw [hUnip, ← Nat.card_congr (MonoidHom.ofInjective (uniHom_injective (F := 𝔽))).toEquiv]
    have htag : Nat.card (Multiplicative 𝔽) = Nat.card 𝔽 :=
      Nat.card_congr {
        toFun := Multiplicative.toAdd
        invFun := Multiplicative.ofAdd
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact htag.trans (card_binaryGaloisField n (by have := d.parameter; omega : n ≠ 0))
  have hcardf : Nat.card f.range = Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm
  have heq : f.range = Unip 𝔽 := eq_of_le_of_card_ge hle (by
    rw [hcardf, hcardA, hcardU])
  let c : A ≃* Unip 𝔽 :=
    (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr heq)
  let w : Multiplicative 𝔽 ≃* Unip 𝔽 := MonoidHom.ofInjective (uniHom_injective (F := 𝔽))
  refine ⟨c.trans w.symm, ?_⟩
  intro a
  exact (congrArg (fun x : Unip 𝔽 => (x : SL2 𝔽)) (w.apply_symm_apply (c a))).symm

private theorem semilinear_from_coordinates
    (e : L ≃* SL2 𝔽) (eA : A ≃* Multiplicative 𝔽)
    (heA : ∀ a : A, e ⟨a, d.distinguished_le a.property⟩ = uniHom 𝔽 (eA a))
    (m : M) (hm : (m : G) ∈ normalizer (L : Set G)) :
    ∃ (c : 𝔽ˣ) (σ : 𝔽 ≃+* 𝔽), ∀ a : A,
      eA (d.distinguishedConjugation m a) =
        Multiplicative.ofAdd ((c : 𝔽) * σ (eA a).toAdd) := by
  let eP := e.trans (Theory.PSL2.sl2QuotientEquiv 𝔽)
  let aL : MulAut L := Subgroup.normalizerMonoidHom (H := L) ⟨m, hm⟩
  let α : MulAut (Theory.PSL2.Group 𝔽) := MulAut.congr eP aL
  let U := Matrix.ProjectiveSpecialLinearGroup.OddBorel.kernel 𝔽
  let root := Matrix.ProjectiveSpecialLinearGroup.OddBorel.unipotentHom 𝔽
  have hp (a : A) : eP ⟨a, d.distinguished_le a.property⟩ = root (eA a) := by
    change Theory.PSL2.quotientMap 𝔽 (e ⟨a, d.distinguished_le a.property⟩) = _
    rw [heA]
    rfl
  have hact (a : A) : α (root (eA a)) = root (eA (d.distinguishedConjugation m a)) := by
    rw [← hp a]
    change eP (aL (eP.symm (eP ⟨a, d.distinguished_le a.property⟩))) = _
    rw [eP.symm_apply_apply]
    calc
      eP (aL ⟨a, d.distinguished_le a.property⟩) =
          eP ⟨d.distinguishedConjugation m a,
            d.distinguished_le (d.distinguishedConjugation m a).property⟩ := by
        apply congrArg eP
        apply Subtype.ext
        have hh := congrArg (fun x : M => (x : G))
          (d.distinguishedConjugation_apply m a)
        exact hh.symm
      _ = _ := hp (d.distinguishedConjugation m a)
  have hnorm : U.map α.toMonoidHom = U := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨a, rfl⟩ := hx
      have hh := hact (eA.symm a)
      rw [eA.apply_symm_apply] at hh
      exact ⟨eA (d.distinguishedConjugation m (eA.symm a)), hh.symm⟩
    · rw [card_map_of_injective α.injective]
  obtain ⟨g, σ, hα⟩ := Theory.PSL2.semilinear_coverage α
  obtain ⟨c, hc⟩ := Theory.PSL2.RootSemilinear.scalar_action α hnorm g σ hα
  have hc0 : c ≠ 0 := scalar_coefficient_ne_zero α σ c hc
  refine ⟨Units.mk0 c hc0, σ, fun a => ?_⟩
  apply Matrix.ProjectiveSpecialLinearGroup.OddBorel.unipotentHom_injective 𝔽
  exact (hact a).symm.trans (hc (eA a))

private theorem scalars_from_coordinates
    (e : L ≃* SL2 𝔽) (he : ∀ x : L, e x ∈ Borel 𝔽 ↔ (x : G) ∈ M)
    (het : ∀ htL : t ∈ L, e ⟨t, htL⟩ = weyl 𝔽)
    (eA : A ≃* Multiplicative 𝔽)
    (heA : ∀ a : A, e ⟨a, d.distinguished_le a.property⟩ = uniHom 𝔽 (eA a)) :
    ∀ c : 𝔽ˣ, ∃ k : K, ∀ a : A,
      eA (d.distinguishedConjugation (k : M) a) =
        Multiplicative.ofAdd ((c : 𝔽) * (eA a).toAdd) := by
  intro c
  obtain ⟨b, hb⟩ := (Finite.surjective_of_injective (CharTwo.sq_injective (R := 𝔽))) (c : 𝔽)
  have hb0 : b ≠ 0 := fun h0 => c.ne_zero (by simpa only [h0, zero_pow (by decide : 2 ≠ 0)] using hb.symm)
  let β : 𝔽ˣ := Units.mk0 b hb0
  let kL : L := e.symm (torHom 𝔽 β)
  have htL : t ∈ L :=
    (show zpowers t ≤ L from le_trans le_sup_right le_sup_left) (mem_zpowers t)
  have hkT : e kL ∈ Torus 𝔽 := by
    rw [e.apply_symm_apply, Torus_eq_range]
    exact ⟨β, rfl⟩
  have hkD : (kL : G) ∈ residualPairStabilizer M t :=
    (marked_pair_torus e he htL (het htL) kL).mp hkT
  let k : K := ⟨⟨kL, hkD.1⟩, hkD, kL.property⟩
  refine ⟨k, fun a => ?_⟩
  apply uniHom_injective (F := 𝔽)
  rw [← heA]
  have hmul : e ⟨d.distinguishedConjugation (k : M) a,
      d.distinguished_le (d.distinguishedConjugation (k : M) a).property⟩ =
      e kL * e ⟨a, d.distinguished_le a.property⟩ * (e kL)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    apply congrArg e
    rfl
  rw [hmul, heA, e.apply_symm_apply]
  have hB : torHom 𝔽 β ∈ Borel 𝔽 := by
    apply (mem_Borel_iff _).mpr
    rfl
  change torHom 𝔽 β * uni (eA a).toAdd * (torHom 𝔽 β)⁻¹ = uni _
  rw [Borel_conj_uni hB]
  change uni (b ^ 2 * (eA a).toAdd) = uni ((c : 𝔽) * (eA a).toAdd)
  rw [← hb]

/-- The actual distinguished root has simultaneous scalar and semilinear
coordinates for its literal torus and local normalizer. -/
public theorem Context.distinguishedRootCoordinates :
    ∃ eA : A ≃* Multiplicative 𝔽,
      (∀ m : M, (m : G) ∈ normalizer (L : Set G) →
        ∃ (c : 𝔽ˣ) (σ : 𝔽 ≃+* 𝔽), ∀ a : A,
          eA (d.distinguishedConjugation m a) =
            Multiplicative.ofAdd ((c : 𝔽) * σ (eA a).toAdd)) ∧
      (∀ c : 𝔽ˣ, ∃ k : K, ∀ a : A,
        eA (d.distinguishedConjugation (k : M) a) =
          Multiplicative.ofAdd ((c : 𝔽) * (eA a).toAdd)) := by
  obtain ⟨e, he, het⟩ := residual_equiv_sl2_borel_weyl d.minimal.disconnected d.reduction
    d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper ⟨d.model⟩
  obtain ⟨eA, heA⟩ := root_coordinates_from_marking d e he
  exact ⟨eA, semilinear_from_coordinates d e eA heA,
    scalars_from_coordinates d e he het eA heA⟩

end BenderSuzuki.ZD.LinearExclusion

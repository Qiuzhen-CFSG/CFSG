module
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.SmallQuotients
public import Theory.SpecificGroups.SL2.OddSylowCentralizer
public import Theory.SpecificGroups.SL2.SylowKernelCardinality

/-!
# Cubic chief length on a defining-characteristic SL₂ Sylow

For an SL₂ quotient with two-group kernel, an actual cubic normalizing a
Sylow two-subgroup has no fixed point on the quotient Sylow. Coprime
fixed-point lifting therefore adds log₄(|F|) to the kernel's cubic length.
The proof retains the original homomorphism and relative quotient; no
normality of the Sylow in the whole group is used.

Source application: Aschbacher--Smith 5.1.23, printed p.645,
refs/quasithin.pdf, the additional noncentral factor above the module.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace NoncentralChiefRefinement.CubicComparison
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- The actual Sylow quotient contributes exactly log₄(|F|). -/
theorem sl2_sylow_length (f : G →* SL(2,F)) (hf : Function.Surjective f)
    (hp : IsPGroup 2 f.ker) (P : Sylow 2 G)
    (A : Subgroup G) (hA : Nat.card A = 3)
    (hAP : A ≤ normalizer (P : Set G)) :
    conjugationCubicLength A (P : Subgroup G) =
      conjugationCubicLength A f.ker + Nat.log 4 (Nat.card F) := by
  have hKP : f.ker ≤ (P : Subgroup G) := hp.le_sylow_of_normal P
  let Q := P.mapSurjective hf
  let φ : P →* Q := (f.comp (P : Subgroup G).subtype).codRestrict _
    (fun x => mem_map_of_mem f x.property)
  have hφ : Function.Surjective φ := by
    rintro ⟨y,x,hx,rfl⟩
    exact ⟨⟨x,hx⟩,rfl⟩
  have hk : f.ker.subgroupOf (P : Subgroup G) = φ.ker := by
    ext x
    change f x = 1 ↔ φ x = 1
    exact ⟨fun hx => Subtype.ext hx,fun hx => congrArg Subtype.val hx⟩
  let e : (P ⧸ f.ker.subgroupOf (P : Subgroup G)) ≃* Q :=
    QuotientGroup.liftEquiv _ hφ hk
  have hAN : A ≤ normalizer (f.ker : Set G) := le_normalizer_of_normal
  let := quotientConjugationAction A (P : Subgroup G) f.ker hAP hAN
  have he (a : A) (x : P ⧸ f.ker.subgroupOf (P : Subgroup G)) :
      (e (a • x) : SL(2,F)) = f a * (e x : SL(2,F)) * (f a)⁻¹ := by
    obtain ⟨p,rfl⟩ := QuotientGroup.mk'_surjective (f.ker.subgroupOf (P : Subgroup G)) x
    change f ((a : G) * (p : G) * (a : G)⁻¹) = f a * f p * (f a)⁻¹
    simp only [map_mul,map_inv]
  have hB : Nat.card (A.map f) = 3 :=
    GLS3.Chapter5.cubic_image_card_of_two_kernel f hp A hA
  have hBne : A.map f ≠ ⊥ := by
    intro hh
    have hc := card_eq_one.mpr hh
    omega
  obtain ⟨b,hb⟩ := ne_bot_iff_exists_ne_one.mp hBne
  obtain ⟨a,ha,hab⟩ := b.property
  have hfa : f a ≠ 1 := by
    intro hh
    exact hb (Subtype.ext (hab.symm.trans hh))
  have ha3 : a ^ 3 = 1 := by
    exact congrArg Subtype.val (hA ▸ pow_card_eq_one' (x := (⟨a,ha⟩ : A)))
  have hfix : FixedPoints.subgroup A (P ⧸ f.ker.subgroupOf (P : Subgroup G)) = ⊥ := by
    apply bot_unique
    intro x hx
    apply e.injective
    rw [map_one]
    apply Subtype.ext
    change (e x : SL(2,F)) = 1
    apply Matrix.SpecialLinearGroup.eq_one_of_sylow_commutes_nontrivial_odd Q
      (e x) (f a) (e x).property hfa (by decide : Odd 3)
      (by rw [← map_pow,ha3,map_one])
    have hh := he ⟨a,ha⟩ x
    rw [hx ⟨a,ha⟩] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  have hsection : sectionCubicLength A f.ker (P : Subgroup G) = Nat.log 4 (Nat.card F) := by
    rw [sectionCubicLength_eq_quotient_of_twoGroup A (P : Subgroup G) f.ker
      (IsPGroup.of_card (n := 1) (by simpa using hA)) P.isPGroup' hKP hAP hAN]
    unfold FixedPoints.cubicLength
    rw [hfix,index_bot,Nat.card_congr e.toEquiv]
    rw [Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 Q).symm.toEquiv]
    rfl
  have hm := conjugationCubicLength_mono A hKP
  unfold sectionCubicLength at hsection
  omega
end NoncentralChiefRefinement.CubicComparison

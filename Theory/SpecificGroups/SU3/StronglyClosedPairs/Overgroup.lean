module
public import Theory.SpecificGroups.SU3.StronglyClosedPairs.Overgroup.InnerReduction
public import Theory.SpecificGroups.SU3.StronglyClosedPairs.Overgroup.RootClosure
public import Theory.SpecificGroups.SU3.StronglyClosedPairs.Overgroup.Transport

/-!
# Commuting strongly closed pairs in binary PSU₃ automorphism overgroups

Pull the overgroup Sylow back through the faithful inner embedding. The
inner-pair theorem nests the two inner intersections, with the smaller one
elementary. Their larger union is strongly closed, so the full-torus subgroup
dichotomy makes it elementary or the whole inner Sylow.

Every factor therefore has elementary inner intersection or contains that
Sylow. The root–diagonal–graph calculation excludes outer elements in either
case, including those of order eight or higher. Transport is through an actual
Sylow conjugacy, with the entire automorphism configuration carried along.
Both factors are thus inner; the completed inner theorem supplies nesting
and the square-one smaller factor. All hypotheses of the published contract
are retained, although its two rank assumptions are unnecessary here.

Source: Huppert II.10.12; GLS3, Theorem 2.5.12 and §2.7; the unitary model
calculation used for Aschbacher, *On finite groups of component type* (1975),
Lemma 3.4, pp.94–96. This module proves the intrinsic model input to the
source theorem, whose ambient quotient transport is owned by its consumers.
-/

open Subgroup Theory.GroupTheory
namespace BenderSuzuki.MatrixGroups.HermitianForm.StronglyClosedPairs
variable {E : Type*} [Field E] [Finite E]
variable (J : HermitianForm 3 E)

/-- Commuting factors with strongly closed union and only inner involutions
are wholly inner in an automorphism overgroup of the binary unitary group. -/
public theorem factors_inner
    {n : ℕ} (hn : 2 ≤ n) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (K : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hK : (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* _).range ≤ K)
    (T : Sylow 2 K) (B C : Subgroup K)
    (hBT : B ≤ T) (hCT : C ≤ T) (hBC : ⁅B,C⁆ = ⊥)
    (hclosed : IsStronglyClosedSet ((B : Set K) ∪ C) (T : Subgroup K) ⊤)
    (hinv : ∀ b : K, b ∈ (B : Set K) ∪ C → BenderSuzuki.PFAppendixIII.IsInvolution b →
      (b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) ∈
        (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* _).range) :
    B ≤ (innerHom J K hK).range ∧ C ≤ (innerHom J K hK).range := by
  let X : Type _ := ProjectiveSpecialUnitaryMatrixGroup J
  let : Finite X := Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let f := innerHom J K hK
  obtain ⟨P, hP⟩ := innerHom_sylow J hn hJ hcard hfixed K hK T
  let D := B.comap f
  let F := C.comap f
  have hc : IsStronglyClosedSet ((D : Set X) ∪ F) (P : Subgroup X) ⊤ := by
    constructor
    · intro x hx
      rw [hP]
      exact hclosed.1 hx
    · intro x hx g _ hr
      have ht : f (g⁻¹*x*g) ∈ (T : Subgroup K) := by simpa only [hP, mem_comap] using hr
      have hh := hclosed.2 (f x) hx (f g) (mem_top _) (by simpa only [map_mul, map_inv] using ht)
      change f (g⁻¹*x*g) ∈ (B : Set K) ∪ C
      simpa only [map_mul, map_inv] using hh
  have larger (D F : Subgroup X) (hle : D ≤ F)
      (hc : IsStronglyClosedSet ((D : Set X) ∪ F) (P : Subgroup X) ⊤) :
      (∀ x ∈ F, x^2 = 1) ∨ F = (P : Subgroup X) := by
    apply sylow_stronglyClosed_dichotomy J hn hJ hcard hfixed P F
    constructor
    · intro x hx; exact hc.1 (Or.inr hx)
    · intro x hx g hg hr
      exact (hc.2 x (Or.inr hx) g hg hr).elim (fun hy => hle hy) id
  have hparts : ((∀ x ∈ D, x^2 = 1) ∨ D = (P : Subgroup X)) ∧
      ((∀ x ∈ F, x^2 = 1) ∨ F = (P : Subgroup X)) := by
    rcases inner_parts_nested_elementary J hn hJ hcard hfixed K hK T B C hBT hCT hBC hclosed
      with ⟨hle, hs⟩ | ⟨hle, hs⟩
    · exact ⟨Or.inl hs, larger D F hle hc⟩
    · exact ⟨larger F D hle (by simpa only [Set.union_comm] using hc), Or.inl hs⟩
  let A := (T : Subgroup K).map K.subtype
  have hA : IsPGroup 2 A := T.isPGroup'.map K.subtype
  have hPA : (P : Subgroup X).map MulAut.conj ≤ A := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨f x, (by simpa only [hP, mem_comap, SetLike.mem_coe, f] using hx), rfl⟩
  have hstable : ∀ a ∈ A, (P : Subgroup X).map a.toMonoidHom = P := by
    rintro _ ⟨a, ha, rfl⟩
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      rw [hP]
      change f (a.val x) ∈ (T : Subgroup K)
      have hfx : f x ∈ (T : Subgroup K) := by simpa only [hP, mem_comap, SetLike.mem_coe, f] using hx
      have he : f (a.val x) = a * f x * a⁻¹ := by
        apply Subtype.ext
        ext y
        simp [f, innerHom, MulAut.conj_apply]
      rw [he]
      exact (T : Subgroup K).mul_mem ((T : Subgroup K).mul_mem ha hfx) ((T : Subgroup K).inv_mem ha)
    · exact le_of_eq (Subgroup.card_map_of_injective a.val.injective).symm
  have lift (L : Subgroup K) (hLT : L ≤ T)
      (hLI : ∀ b ∈ L, b^2 = 1 → b.val ∈ (MulAut.conj : X →* _).range)
      (hp : (∀ x ∈ L.comap f, x^2 = 1) ∨ L.comap f = (P : Subgroup X)) :
      L ≤ f.range := by
    have hm (x : X) : MulAut.conj x ∈ L.map K.subtype ↔ f x ∈ L := by
      constructor
      · rintro ⟨a, ha, he⟩
        have he' : a = f x := Subtype.ext he
        exact he' ▸ ha
      · intro hx
        exact ⟨f x, hx, rfl⟩
    have hout : L.map K.subtype ≤ (MulAut.conj : X →* _).range := by
      apply sylow_normalizing_factor_inner J hn hJ hcard hfixed P A (L.map K.subtype)
        hA (map_mono hLT) hPA hstable
      · rintro _ ⟨b, hb, rfl⟩ hs
        exact hLI b hb (Subtype.ext hs)
      · rcases hp with hs | he
        · exact Or.inl (fun x hx => hs x ((hm x).mp hx))
        · right
          rintro _ ⟨x, hx, rfl⟩
          apply (hm x).mpr
          change x ∈ L.comap f
          rwa [he]
    intro b hb
    obtain ⟨x, hx⟩ := hout (mem_map_of_mem K.subtype hb)
    exact ⟨x, Subtype.ext hx⟩
  have hinv' (b : K) (hb : b ∈ (B : Set K) ∪ C) (hs : b^2 = 1) :
      b.val ∈ (MulAut.conj : X →* _).range := by
    by_cases he : b = 1
    · subst b
      exact ⟨1, map_one _⟩
    · exact hinv b hb ⟨he, hs⟩
  exact ⟨lift B hBT (fun b hb hs => hinv' b (Or.inl hb) hs) hparts.1,
    lift C hCT (fun b hb hs => hinv' b (Or.inr hb) hs) hparts.2⟩

/-- Whole-factor innerness in the literal ambient automorphism group. This
also supplies the independent nested-pair consumer without assuming nesting. -/
public theorem factors_inner_images
    {n : ℕ} (hn : 2 ≤ n) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (K : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hK : (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* _).range ≤ K)
    (T : Sylow 2 K) (B C : Subgroup K)
    (hBT : B ≤ T) (hCT : C ≤ T) (hBC : ⁅B,C⁆ = ⊥)
    (hclosed : IsStronglyClosedSet ((B : Set K) ∪ C) (T : Subgroup K) ⊤)
    (hinv : ∀ b : K, b ∈ (B : Set K) ∪ C → BenderSuzuki.PFAppendixIII.IsInvolution b →
      (b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) ∈
        (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* _).range) :
    B.map K.subtype ≤ (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* _).range ∧
      C.map K.subtype ≤ (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* _).range := by
  obtain ⟨hB, hC⟩ := factors_inner J hn hJ hcard hfixed K hK T B C hBT hCT hBC hclosed hinv
  have lift (L : Subgroup K) (hL : L ≤ (innerHom J K hK).range) :
      L.map K.subtype ≤ (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* _).range := by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨x, rfl⟩ := hL hb
    exact ⟨x, rfl⟩
  exact ⟨lift B hB, lift C hC⟩

/-- The full binary PSU₃ automorphism-overgroup pair rigidity contract. -/
public theorem stronglyClosedPairRigidity
    {n : ℕ} (hn : 2 ≤ n) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n) : J.StronglyClosedPairRigidity := by
  intro K hK T B C hBT hCT hBC _ _ hclosed hinv
  obtain ⟨hB, hC⟩ := factors_inner J hn hJ hcard hfixed K hK T B C hBT hCT hBC hclosed hinv
  exact factors_nested_elementary_of_inner J hn hJ hcard hfixed K hK T B C
    hBT hCT hBC hclosed hB hC

end BenderSuzuki.MatrixGroups.HermitianForm.StronglyClosedPairs

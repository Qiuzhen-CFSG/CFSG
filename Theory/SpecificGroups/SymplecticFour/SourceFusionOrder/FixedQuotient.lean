module
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.TwoSylowSource
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Nonbinary
public import Theory.GroupTheory.PResidual.NormalizerCore
public import Theory.GroupTheory.PResidual.PGroupFactor
public import Mathlib.Algebra.CharP.Reduced

/-!
# Removing field and scalar factors from a fixed residual core

At field order four the full outer automorphism group of Sp4 is a two-group.
Consequently every two-residual acting on Sp4 has inner image. In a marked
full endpoint the exact inner intersection places that residual in the pure
parabolic. Its two-core has trivial determinant in characteristic two, and
therefore lies in the local factor. Both steps use the same endpoint map.

Source: Aschbacher--Smith F.4.37, printed p.293 of refs/quasithin.pdf.
Chapter6's SymplecticExtensionOrder.FixedQuotient applies this to the original
fixed endpoint cores inside the same conjugate full root normalizer.
-/

@[expose] public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.SourceFusionOrder
variable {G : Type*} [Group G]
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Over field order four, a two-residual has inner image under every action
on the native symplectic group. -/
theorem residual_image_inner_four (hq : Nat.card F=4) {A : Type*} [Group A]
    (a : A →* MulAut (Sp F)) {x : A} (hx : x∈pResidual 2 A) :
    a x ∈ MulAut.innerSubgroup (Sp F) := by
  have hc : Nat.card (MulAut.Outer (Sp F))=2^2 :=
    DiagramAutomorphisms.card_outer_eq_two_mul (m := 2) hq (by decide)
  have hp : IsPGroup 2 (MulAut.Outer (Sp F)) := IsPGroup.of_card hc
  exact (QuotientGroup.eq_one_iff _).mp
    (pResidual_le_ker_of_isPGroup 2 ((QuotientGroup.mk' _).comp a) hp hx)

omit [Finite F] in
/-- The determinant character kills a two-subgroup of a parabolic. -/
theorem two_subgroup_le_local {U : Subgroup G} (hU : IsPGroup 2 U)
    (W : Submodule F (Vector F)) (a : U →* stabilizer W) (u : U) :
    (a u).val∈determinantKernel W := by
  obtain ⟨n,hn⟩ := hU.exists_pow_pow_eq_one u
  have hp : ((determinantCharacter W (a u) : Fˣ) : F) ^ (2^n)=1 := by
    have hh := congrArg (fun v : U => ((determinantCharacter W (a v) : Fˣ) : F)) hn
    simpa only [map_pow,map_one,Units.val_pow_eq_pow_val,Units.val_one] using hh
  refine ⟨a u,?_,rfl⟩
  apply Units.ext
  simpa only [pow_one,Units.val_one] using
    (ExpChar.pow_prime_pow_mul_eq_one_iff 2 n 1
      ((determinantCharacter W (a u) : Fˣ) : F)).mp (by simpa using hp)

/-- Remove the field and scalar contributions using the same marked endpoint.
The input subgroup may be any subgroup of the full endpoint. -/
theorem residual_core_le_marked_local (hq : Nat.card F=4)
    (M P K A : Subgroup G) (hAP : A≤M)
    (W : Submodule F (Vector F)) (e : P ≃* stabilizer W)
    (b : M →* MulAut (Sp F))
    (hi : ∀ x : M, b x∈MulAut.innerSubgroup (Sp F) ↔ x.val∈P)
    (hK : (K.subgroupOf P).map ((stabilizer W).subtype.comp e.toMonoidHom)=
      determinantKernel W) :
    ((pResidual 2 A).map A.subtype).pCoreIn 2 ≤ K := by
  let R := (pResidual 2 A).map A.subtype
  let U := R.pCoreIn 2
  have hRP : R≤P := by
    rintro x ⟨a,ha,rfl⟩
    exact (hi (inclusion hAP a)).mp
      (residual_image_inner_four hq (b.comp (inclusion hAP)) ha)
  have hUP : U≤P := (pCoreIn_le 2 R).trans hRP
  let a : U →* stabilizer W := e.toMonoidHom.comp (inclusion hUP)
  intro u hu
  have hdet := two_subgroup_le_local (isPGroup_pCoreIn 2 R) W a ⟨u,hu⟩
  rw [←hK] at hdet
  obtain ⟨v,hv,hvu⟩ := hdet
  have he : e v=e (inclusion hUP ⟨u,hu⟩) := Subtype.ext hvu
  have hval : v.val = u := congrArg Subtype.val (e.injective he)
  change v.val ∈ K at hv
  exact hval ▸ hv
omit [Finite F] [CharP F 2] in
/-- Exact native inner intersection reflects to the original pure endpoint. -/
theorem marked_inner_preimage
    (M P : Subgroup G) (N : Subgroup (MulAut (Sp F))) (R : Subgroup (Sp F))
    (hPM : P≤M) (e : P≃*R) (f : M≃*N)
    (hi : N⊓MulAut.innerSubgroup (Sp F)=R.map MulAut.conj)
    (hag : ∀ x : P, (f (inclusion hPM x)).val=MulAut.conj (e x).val)
    (x : M) : (f x).val∈MulAut.innerSubgroup (Sp F) ↔ x.val∈P := by
  constructor
  · intro hx
    have hh : (f x).val∈R.map MulAut.conj := hi ▸ ⟨(f x).property,hx⟩
    obtain ⟨y,hy,hyx⟩ := hh
    let p := e.symm ⟨y,hy⟩
    have heq : inclusion hPM p=x := by
      apply f.injective
      apply Subtype.ext
      rw [hag]
      simpa only [p,e.apply_symm_apply] using hyx
    exact congrArg Subtype.val heq ▸ p.property
  · intro hx
    have heq : inclusion hPM (⟨x.val,hx⟩ : P)=x := rfl
    rw [←heq,hag]
    exact ⟨_,rfl⟩
end Theory.SpecificGroups.SymplecticFour.SourceFusionOrder

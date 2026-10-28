module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlanes

/-!
# Transvections and paired-plane fixers on the binary doubled orbit

An inner transvection fixes sixteen vectors on the natural plus dual module.
Transport through the marked component gives the involution parameter m≤2
for the original larger actor. A pointwise fixer of a paired plane fixes a
nonzero vector on the natural axis, so the graph coset is excluded. The
last theorem carries this fact through the literal normalizer homomorphism.

The chosen-module applications, including m=2 and the local seed-normalizer
containment, are in `NonFFSourceDoubledBinaryParameters`.
Source: Aschbacher–Smith H.4.1–3, Table 7.2.1 and 7.7.4,
printed pp.380,698,704, in `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open ChapterE BinaryLinearThree

/-- A transvection in the marked component fixes a four-space. -/
theorem doubledBinary_moduleM_le_two
    {H J U : Type*} [_root_.Group H] [_root_.Group J]
    [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) H U) (i : J →* H)
    (q : J →* Group) (hq : Function.Surjective q)
    (E : U ≃ₗ[ZMod 2] NaturalDual.Space)
    (hE : ∀ j v, E (ρ (i j) v) = NaturalDual.action (q j) (E v))
    (f : H ≃* MulAut Group) (hf : ∀ j, f (i j) = MulAut.conj (q j)) :
    moduleM ρ ≤ 2 := by
  let g := FourGroupGeometry.FixedSpaces.involution
  let a := f.symm (MulAut.conj g)
  have hg : g ≠ 1 := by decide
  have hg2 : g * g = 1 := by decide
  have ha (v : U) : E (ρ a v) = NaturalDual.action g (E v) := by
    obtain ⟨j,hj⟩ := hq g
    have hj' : i j = a := by apply f.injective; rw [hf,hj]; exact (f.apply_symm_apply _).symm
    rw [← hj',← hj]
    exact hE j v
  have ha2 : orderOf a = 2 := by
    apply orderOf_eq_prime
    · apply f.injective
      rw [map_pow,map_one,f.apply_symm_apply,← map_pow]
      simp only [pow_two,hg2,map_one]
    · intro hh
      have he := congrArg f hh
      rw [f.apply_symm_apply,map_one] at he
      exact hg (Matrix.PSL3Two.MarkedAutomorphisms.conj_injective
        (he.trans (map_one MulAut.conj).symm))
  have hm (v : U) : v ∈ fixedSpace ρ (zpowers a) ↔
      NaturalDual.action g (E v) = E v := by
    rw [mem_fixedSpace_zpowers_iff,← ha]
    exact E.injective.eq_iff.symm
  let e : fixedSpace ρ (zpowers a) ≃ TransvectionFixed.Fixed g :=
    E.toEquiv.subtypeEquiv hm
  have hc : Nat.card (fixedSpace ρ (zpowers a)) = 2 ^ 4 :=
    (Nat.card_congr e).trans (TransvectionFixed.card_fixed g hg hg2)
  let : Finite NaturalDual.Space := Module.finite_of_finite (ZMod 2)
  let : Finite U := Finite.of_equiv NaturalDual.Space E.toEquiv.symm
  have hd : Module.finrank (ZMod 2) U = 6 := by
    rw [E.finrank_eq]
    simp [NaturalDual.Space,BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector,Module.finrank_prod]
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hc
  have hfix : Module.finrank (ZMod 2) (fixedSpace ρ (zpowers a)) = 4 :=
    Nat.pow_right_injective (by decide) hc
  have hcod := fixedCodim_add_finrank ρ (zpowers a)
  exact (moduleM_le_involution ρ ha2).trans (by omega)

/-- Fixing a nonzero vector on the natural axis excludes the graph coset. -/
theorem doubledBinary_inner_of_fixed_natural
    (α : MulAut Group) (e : NaturalDual.Space ≃ₗ[ZMod 2] NaturalDual.Space)
    (he : ∀ g x, e (NaturalDual.action g x) = NaturalDual.action (α g) (e x))
    (v : Vector) (hv : v ≠ 0) (hfix : e (v,0) = (v,0)) :
    α ∈ MulAut.innerSubgroup Group := by
  by_contra hout
  have hz := (NaturalDual.outer_swaps α e he hout).1 v
  rw [hfix] at hz
  exact hv hz

/-- A pointwise fixer of a paired plane is inner, through the literal
normalizer homomorphism of the original orbit. -/
theorem doubledBinary_ambientPlane_fixer_inner
    {G : Type*} [_root_.Group G] (W₀ : Subgroup G) [IsElementaryAbelian 2 W₀]
    (E : Additive W₀ ≃ₗ[ZMod 2] NaturalDual.Space)
    (a : Automizer W₀ ≃* MulAut Group)
    (hcov : ∀ b g w, E (automizerRepresentation W₀ b (E.symm (NaturalDual.action g (E w)))) =
      NaturalDual.action (a b g) (E (automizerRepresentation W₀ b w)))
    (n : normalizer (W₀ : Set G)) (v : Vector) (f : Module.Dual (ZMod 2) Vector)
    (hfv : f v = 1)
    (hn : (n : G) ∈ centralizer (DoubledBinaryPlanes.ambientPlane W₀ E v f : Set G)) :
    a (W₀.normalizerMonoidHom.rangeRestrict n) ∈ MulAut.innerSubgroup Group := by
  let b := W₀.normalizerMonoidHom.rangeRestrict n
  let c : NaturalDual.Space ≃ₗ[ZMod 2] NaturalDual.Space :=
    E.symm.trans ((LinearMap.GeneralLinearGroup.toLinearEquiv
      ((automizerRepresentation W₀).asGroupHom b)).trans E)
  have hc (g : Group) (x : NaturalDual.Space) :
      c (NaturalDual.action g x) = NaturalDual.action (a b g) (c x) := by
    change E (automizerRepresentation W₀ b (E.symm (NaturalDual.action g x))) =
      NaturalDual.action (a b g) (E (automizerRepresentation W₀ b (E.symm x)))
    simpa only [E.apply_symm_apply] using hcov b g (E.symm x)
  apply doubledBinary_inner_of_fixed_natural (a b) c hc v
    (by intro he; simp [he] at hfv)
  have hv := ((DoubledBinaryPlanes.ambientPlane_le_iff W₀ E v f
    (DoubledBinaryPlanes.ambientPlane W₀ E v f)).mp le_rfl).1
  have he : automizerRepresentation W₀ b (E.symm (v,0)) = E.symm (v,0) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change (n : G) * ((E.symm (v,0)).toMul : G) * (n : G)⁻¹ = ((E.symm (v,0)).toMul : G)
    rw [← hn _ hv,mul_inv_cancel_right]
  change E (automizerRepresentation W₀ b (E.symm (v,0))) = (v,0)
  rw [he,E.apply_symm_apply]

end CFSG.Quasithin.Chapter7.NormalizedSource

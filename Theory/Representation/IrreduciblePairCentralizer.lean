module
public import Theory.Representation.BinaryIrreducibleCentralizer
public import Theory.Representation.BinaryOffender.NormalizerRank

/-!
# Involutions centralizing two inequivalent simple binary constituents

The off-diagonal blocks vanish by Schur's lemma. On each diagonal block,
the displacement of an involution has square zero and is again an
intertwiner, hence vanishes. Consequently conjugation on the component
image is injective on each elementary two-subgroup of the full normalizer.
This supplies the actual automizer rank bound for the original doubled
linear-three orbit in Chapter12, with its scalar center retained.
Source: Aschbacher--Smith Table7.2.1 and H.4, printed pp.698 and383–385.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Representation
variable {H U W : Type*} [Group H]
  [AddCommGroup U] [Module (ZMod 2) U]
  [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) H U) (σ : Representation (ZMod 2) H W)
  [IsIrreducible ρ] [IsIrreducible σ]

private theorem intertwiner_square_zero {X : Type*} [AddCommGroup X]
    [Module (ZMod 2) X] (τ : Representation (ZMod 2) H X) [IsIrreducible τ]
    (a : τ.IntertwiningMap τ) (hsq : ∀ x, a (a x) = 0) : a = 0 := by
  rcases IsIrreducible.injective_or_eq_zero a with hi | hz
  · ext x
    apply hi
    simpa using hsq x
  · exact hz

/-- An involution commuting with two inequivalent simple constituents is trivial. -/
theorem irreducible_pair_centralizing_involution
    (hne : ¬ Nonempty (ρ.Equiv σ))
    (f : (U × W) ≃ₗ[ZMod 2] (U × W)) (hsq : ∀ v, f (f v) = v)
    (hf : ∀ h v, f ((ρ.prod σ) h v) = (ρ.prod σ) h (f v)) :
    f = LinearEquiv.refl _ _ := by
  let a : ρ.IntertwiningMap σ := {
    toLinearMap := (LinearMap.snd _ _ _).comp (f.toLinearMap.comp (LinearMap.inl _ _ _))
    isIntertwining' := by
      intro h
      ext v
      simpa using congrArg Prod.snd (hf h (v,0)) }
  let b : σ.IntertwiningMap ρ := {
    toLinearMap := (LinearMap.fst _ _ _).comp (f.toLinearMap.comp (LinearMap.inr _ _ _))
    isIntertwining' := by
      intro h
      ext v
      simpa using congrArg Prod.fst (hf h (0,v)) }
  have ha : a = 0 := (IsIrreducible.bijective_or_eq_zero a).resolve_left
    (fun h => hne ⟨a.ofBijective h⟩)
  have hb : b = 0 := (IsIrreducible.bijective_or_eq_zero b).resolve_left
    (fun h => hne ⟨(b.ofBijective h).symm⟩)
  have haz (v : U) : (f (v,0)).2 = 0 := congrArg (fun z : ρ.IntertwiningMap σ => z v) ha
  have hbz (v : W) : (f (0,v)).1 = 0 := congrArg (fun z : σ.IntertwiningMap ρ => z v) hb
  let c : ρ.IntertwiningMap ρ := {
    toLinearMap := (LinearMap.fst _ _ _).comp (f.toLinearMap.comp (LinearMap.inl _ _ _))
    isIntertwining' := by
      intro h
      ext v
      simpa using congrArg Prod.fst (hf h (v,0)) }
  let d : σ.IntertwiningMap σ := {
    toLinearMap := (LinearMap.snd _ _ _).comp (f.toLinearMap.comp (LinearMap.inr _ _ _))
    isIntertwining' := by
      intro h
      ext v
      simpa using congrArg Prod.snd (hf h (0,v)) }
  have hcf (v : U) : f (v,0) = (c v,0) := Prod.ext rfl (haz v)
  have hdf (v : W) : f (0,v) = (0,d v) := Prod.ext (hbz v) rfl
  have hcc (v : U) : c (c v) = v := by
    have h := hsq (v,0)
    rw [hcf,hcf] at h
    exact congrArg Prod.fst h
  have hdd (v : W) : d (d v) = v := by
    have h := hsq (0,v)
    rw [hdf,hdf] at h
    exact congrArg Prod.snd h
  have hc : c - 1 = 0 := intertwiner_square_zero ρ (c-1) (by
    intro v
    change c (c v-v) - (c v-v) = 0
    rw [map_sub,hcc]
    have htwo (x : U) : x+x=0 := by
      have hh := @two_smul (ZMod 2) U _ _ _ x
      rw [show (2 : ZMod 2) = 0 from rfl,zero_smul] at hh
      exact hh.symm
    have hn (x : U) : -x=x := neg_eq_iff_add_eq_zero.mpr (htwo x)
    simp only [sub_eq_add_neg,hn,add_assoc]
    rw [←add_assoc (c v),htwo,zero_add,htwo])
  have hd : d - 1 = 0 := intertwiner_square_zero σ (d-1) (by
    intro v
    change d (d v-v) - (d v-v) = 0
    rw [map_sub,hdd]
    have htwo (x : W) : x+x=0 := by
      have hh := @two_smul (ZMod 2) W _ _ _ x
      rw [show (2 : ZMod 2) = 0 from rfl,zero_smul] at hh
      exact hh.symm
    have hn (x : W) : -x=x := neg_eq_iff_add_eq_zero.mpr (htwo x)
    simp only [sub_eq_add_neg,hn,add_assoc]
    rw [←add_assoc (d v),htwo,zero_add,htwo])
  have hc1 : c = 1 := sub_eq_zero.mp hc
  have hd1 : d = 1 := sub_eq_zero.mp hd
  apply LinearEquiv.ext
  intro v
  have he : f v = f (v.1,0) + f (0,v.2) := by rw [←map_add]; simp
  rw [he,hcf,hdf,hc1,hd1]
  simp

/-- The whole normalizer has two-rank at most that of the component image's automorphism group. -/
theorem irreducible_pair_normalizer_rank_le
    [FiniteDimensional (ZMod 2) U] [FiniteDimensional (ZMod 2) W]
    (hne : ¬ Nonempty (ρ.Equiv σ)) :
    primeRank 2 (BinaryOffender.linearNormalizer (ρ.prod σ)) ≤
      primeRank 2 (MulAut (BinaryOffender.actionImage (ρ.prod σ))) := by
  let μ := ρ.prod σ
  let : Finite (U × W) := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) (U × W)) := Finite.of_injective
    (fun z : Module.End (ZMod 2) (U × W) => (z : (U × W) → (U × W))) DFunLike.coe_injective
  apply (primeRank_le_iff_elementary_card_le (BinaryOffender.linearNormalizer μ)).mpr
  intro A hA
  let : IsElementaryAbelian 2 A := hA
  let f := (BinaryOffender.actionImage μ).normalizerMonoidHom.comp A.subtype
  have hi : Function.Injective f := by
    apply (injective_iff_map_eq_one _).mpr
    intro a ha
    let E := LinearMap.GeneralLinearGroup.toLinearEquiv a.val.val
    have hsq : ∀ v, E (E v) = v := by
      intro v
      have h2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) a.val a.property
      exact congrArg (fun z : BinaryOffender.linearNormalizer μ => z.val.val v) h2
    have hE : ∀ g v, E (μ g v) = μ g (E v) := by
      intro g v
      have hh := congrArg (fun β : MulAut (BinaryOffender.actionImage μ) =>
        (β (BinaryOffender.actionHom μ g)).val) ha
      change a.val.val * μ.asGroupHom g * a.val.val⁻¹ = μ.asGroupHom g at hh
      exact congrArg (fun z : (Module.End (ZMod 2) (U × W))ˣ => z.val v)
        ((mul_inv_eq_iff_eq_mul).mp hh)
    have he := irreducible_pair_centralizing_involution ρ σ hne E hsq hE
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro v
    exact LinearEquiv.congr_fun he v
  let : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  exact (Nat.card_congr (MonoidHom.ofInjective hi).toEquiv).le.trans
    ((primeRank_le_iff_elementary_card_le (MulAut (BinaryOffender.actionImage μ))).mp
      le_rfl f.range inferInstance)

end Representation

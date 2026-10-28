module

public import Theory.Representation.OrthogonalFourPlusMatrix.PrimeFieldTwo.FactorNormalizer.Permutations
public import Theory.Representation.OrthogonalFourPlusMatrix.Commutant
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Mathlib.GroupTheory.Coset.Card

/-!
# Order-eight normalizers of the binary determinant action

The two SL₂(2) factors act faithfully on two-by-two matrices by
`X ↦ A * X * B⁻¹`. A linear normalizer induces an automorphism of their
S₃ × S₃ image. Such an automorphism either exchanges the actual factors
or is inner. In the latter case an inner correction centralizes the whole
matrix action, hence is scalar; over F₂ an invertible scalar is one.
Thus every element which does not exchange the factors belongs to the
image of order 36. Lagrange's theorem forces any subgroup of order eight
in the normalizer to contain a factor exchange.

No preservation of the determinant by the normalizing subgroup is assumed.
This is the fixed-model calculation used in Aschbacher–Smith, G.2.6(5),
printed p.336, and its Chapter 15 application, printed pp.1121–1122 and
1146–1147. The literal source-action transport is in the CFSG consumer.
-/

@[expose] public noncomputable section
open Subgroup
namespace ClassicalOrthogonal.FourPlusMatrix.PrimeFieldTwo.FactorNormalizer
abbrev SL := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)
abbrev V := Mat (F := ZMod 2)
abbrev Actor := V ≃ₗ[ZMod 2] V
private abbrev S := Equiv.Perm (Fin 3)

/-- The image of the first factor under the literal determinant action. -/
def left : Subgroup Actor := (matrixHom.comp (MonoidHom.inl SL SL)).range
/-- The image of the second factor under the literal determinant action. -/
def right : Subgroup Actor := (matrixHom.comp (MonoidHom.inr SL SL)).range

private def slEquiv : S ≃* SL :=
  (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three).symm
private def pairEquiv : S × S ≃* PairSL (F := ZMod 2) := slEquiv.prodCongr slEquiv
private def hom : S × S →* Actor := matrixHom.comp pairEquiv.toMonoidHom
private theorem hom_injective : Function.Injective hom :=
  matrixHom_injective.comp pairEquiv.injective
private def model : S × S ≃* hom.range := MonoidHom.ofInjective hom_injective

private theorem hom_range : hom.range = (matrixHom (F := ZMod 2)).range := by
  rw [hom, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr pairEquiv.surjective,
    ← MonoidHom.range_eq_map]

private theorem hom_left : (hom.comp (MonoidHom.inl S S)).range = left := by
  have he : hom.comp (MonoidHom.inl S S) =
      (matrixHom.comp (MonoidHom.inl SL SL)).comp slEquiv.toMonoidHom := by
    ext x : 1
    change matrixHom (slEquiv x, slEquiv 1) = matrixHom (slEquiv x, 1)
    rw [map_one]
  rw [he, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr slEquiv.surjective,
    ← MonoidHom.range_eq_map]
  rfl

private theorem hom_right : (hom.comp (MonoidHom.inr S S)).range = right := by
  have he : hom.comp (MonoidHom.inr S S) =
      (matrixHom.comp (MonoidHom.inr SL SL)).comp slEquiv.toMonoidHom := by
    ext x : 1
    change matrixHom (slEquiv 1, slEquiv x) = matrixHom (1, slEquiv x)
    rw [map_one]
  rw [he, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr slEquiv.surjective,
    ← MonoidHom.range_eq_map]
  rfl

/-- The faithful binary determinant image has order 36. -/
theorem image_card : Nat.card (matrixHom (F := ZMod 2)).range = 36 := by
  rw [← hom_range, ← Nat.card_congr model.toEquiv, Nat.card_prod,
    Nat.card_perm, Nat.card_fin]
  norm_num [Nat.factorial]

/-- An invertible binary linear map commuting with both factors is the identity. -/
theorem centralizer_eq_one (v : Actor)
    (hv : ∀ a : PairSL (F := ZMod 2), v * matrixHom a = matrixHom a * v) : v = 1 := by
  obtain ⟨c, hc⟩ := centralizer_scalar v.toLinearMap.toAddMonoidHom (by
    intro a x
    exact LinearEquiv.congr_fun (hv a) x)
  have hc0 : c ≠ 0 := by
    intro he
    have h : v (1 : V) = v 0 := by simpa [he] using hc (1 : V)
    exact one_ne_zero (v.injective h)
  have hc1 : c = 1 := (show ∀ a : ZMod 2, a ≠ 0 → a = 1 by decide) c hc0
  apply LinearEquiv.ext
  intro x
  change v x = x
  have hx : v x = c • x := hc x
  rw [hc1, one_smul] at hx
  exact hx

/-- Every normalizer lies in the tensor image or exchanges its two actual factors. -/
theorem normalizer_mem_or_exchange (u : Actor)
    (hu : u ∈ normalizer ((matrixHom (F := ZMod 2)).range : Set Actor)) :
    u ∈ (matrixHom (F := ZMod 2)).range ∨
      left.map (MulAut.conj u).toMonoidHom = right := by
  have hu' : u ∈ normalizer (hom.range : Set Actor) := by rwa [hom_range]
  let a : MulAut hom.range := hom.range.normalizerMonoidHom ⟨u, hu'⟩
  let e : MulAut (S × S) := model.trans (a.trans model.symm)
  have he (x : S × S) : hom (e x) = u * hom x * u⁻¹ := by
    change (model (model.symm (a (model x))) : Actor) = _
    rw [model.apply_symm_apply]
    rfl
  rcases Theory.GroupTheory.PermThreeProduct.automorphism_inner_or_exchange e with
    ⟨c, hc⟩ | hs
  · left
    have hconj (x : S × S) :
        u * hom x * u⁻¹ = hom c * hom x * (hom c)⁻¹ := by
      rw [← he, hc, map_mul, map_mul, map_inv]
    have hcomm (x : S × S) :
        ((hom c)⁻¹ * u) * hom x = hom x * ((hom c)⁻¹ * u) := by
      have h := congrArg (fun z : Actor => (hom c)⁻¹ * z * u) (hconj x)
      simpa only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] using h
    have hv : (hom c)⁻¹ * u = 1 := centralizer_eq_one _ (by
      intro b
      obtain ⟨x, rfl⟩ := pairEquiv.surjective b
      exact hcomm x)
    have huc : u = hom c := (inv_mul_eq_one.mp hv).symm
    rw [huc, ← hom_range]
    exact ⟨c, rfl⟩
  · right
    have hcomp : (MulAut.conj u).toMonoidHom.comp (hom.comp (MonoidHom.inl S S)) =
        hom.comp (e.toMonoidHom.comp (MonoidHom.inl S S)) := by
      ext x : 1
      exact (he (x, 1)).symm
    rw [← hom_left, ← MonoidHom.range_comp, hcomp, MonoidHom.range_comp, hs]
    rw [← hom_right, MonoidHom.range_comp]
    congr 1
    ext x
    change (x.1 = 1 ∧ True) ↔ ∃ b, (1, b) = x
    constructor
    · rintro ⟨hx, _⟩; exact ⟨x.2, Prod.ext hx.symm rfl⟩
    · rintro ⟨b, rfl⟩; exact ⟨rfl, trivial⟩

/-- An order-eight subgroup of the linear normalizer exchanges the tensor factors. -/
theorem exists_exchange (P : Subgroup Actor)
    (hP : P ≤ normalizer ((matrixHom (F := ZMod 2)).range : Set Actor))
    (hcard : Nat.card P = 8) :
    ∃ u ∈ P, left.map (MulAut.conj u).toMonoidHom = right := by
  classical
  by_contra! h
  have hle : P ≤ (matrixHom (F := ZMod 2)).range := by
    intro u hu
    exact (normalizer_mem_or_exchange u (hP hu)).resolve_right (h u hu)
  have hd := card_dvd_of_le hle
  rw [hcard, image_card] at hd
  norm_num at hd

end ClassicalOrthogonal.FourPlusMatrix.PrimeFieldTwo.FactorNormalizer

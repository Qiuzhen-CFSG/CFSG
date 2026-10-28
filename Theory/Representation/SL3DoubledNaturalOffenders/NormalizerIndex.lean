module
public import Theory.Representation.SL3DoubledNaturalOffenders.NormalizerCoverage.Factorization
public import Theory.Representation.SymplecticConjugatePair.Ambient.TwoGeometry.Coefficients
public import Theory.Representation.GeneralLinearNatural
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The index of a full doubled natural SL₃ layer

The binary normalizer recovers the coefficient field from the center of the
multiplicity commutant. Its linear kernel lies in the image of GL₃ × GL₂.
Canceling the full SL₃ order and then adjoining the coefficient action gives
an index dividing (q−1)|GL₂(q)|n. The layer and its center are retained.

Source: Aschbacher–Smith, 11.2.1, printed pp.766–767; the tensor commutant
calculation is the doubled-natural geometry of B.5.9–10.
-/

public noncomputable section
namespace Representation.SL3DoubledNaturalOffenders
open Matrix Subgroup
variable (F : Type*) [Field F] [Algebra (ZMod 2) F]

private def repeatedGL : Representation (ZMod 2) (GL (Fin 3) F) (Space F) where
  toFun g :=
    { toFun := fun v i => g.val.mulVec (v i)
      map_add' v w := by funext i; exact Matrix.mulVec_add _ _ _
      map_smul' a v := by funext i; exact Matrix.mulVec_smul g.val a (v i) }
  map_one' := by apply LinearMap.ext; intro v; funext i; exact Matrix.one_mulVec _
  map_mul' g h := by apply LinearMap.ext; intro v; funext i; exact (Matrix.mulVec_mulVec (v i) g.val h.val).symm

/-- The full general-linear tensor action, with its actual multiplicity matrices. -/
def generalTensor : Representation (ZMod 2)
    (GL (Fin 3) F × GL (Fin 2) F) (Space F) where
  toFun p := repeatedGL F p.1 * multiplicity F p.2.val
  map_one' := by simp [multiplicity_one]
  map_mul' p q := by
    have hc : multiplicity F p.2.val * repeatedGL F q.1 =
        repeatedGL F q.1 * multiplicity F p.2.val := by
      apply LinearMap.ext
      intro v
      funext i
      change p.2.val i 0 • q.1.val.mulVec (v 0) + p.2.val i 1 • q.1.val.mulVec (v 1) =
        q.1.val.mulVec (p.2.val i 0 • v 0 + p.2.val i 1 • v 1)
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    change repeatedGL F (p.1*q.1) * multiplicity F (p.2.val*q.2.val) = _
    rw [map_mul,multiplicity_mul]
    simp only [mul_assoc]
    rw [←mul_assoc (multiplicity F p.2.val),hc,mul_assoc]

variable [Finite F]

/-- The linear kernel of any doubled normalizer embeds in the full tensor image. -/
theorem linear_normalizer_mem_generalTensor (b : Ambient F) (hb : b ∈ normalizer F)
    (hlin : ∀ (c : F) (v : Space F), (b : Module.End (ZMod 2) (Space F)) (c • v) =
      c • (b : Module.End (ZMod 2) (Space F)) v) :
    b ∈ (generalTensor F).asGroupHom.range := by
  obtain ⟨g,c,h⟩ := normalizer_linear_tensor_factors b hb hlin
  refine ⟨(g,c),Units.ext (LinearMap.ext fun v => ?_)⟩
  funext i
  exact (h v i).symm

omit [Algebra (ZMod 2) F] [Finite F] in
private theorem gl_card_eq_sl_mul_units :
    Nat.card (GL (Fin 3) F) = Nat.card (SL F) * (Nat.card F - 1) := by
  let δ : GL (Fin 3) F →* Fˣ := GeneralLinearGroup.det
  let e : SL F ≃* δ.ker :=
    MulEquiv.ofBijective (SpecialLinearGroup.toGL.codRestrict δ.ker (by
      intro g
      apply Units.ext
      exact g.property)) (by
        constructor
        · intro a b h
          exact SpecialLinearGroup.toGL_injective (congrArg Subtype.val h)
        · intro g
          refine ⟨⟨g.val.val,congrArg Units.val g.property⟩,?_⟩
          apply Subtype.ext
          exact Units.ext rfl)
  have h := card_eq_card_quotient_mul_card_subgroup δ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective δ
    GeneralLinearGroup.det_surjective).toEquiv,←Nat.card_congr e.toEquiv,Nat.card_units] at h
  exact h.trans (Nat.mul_comm _ _)

/-- A faithful doubled layer has index dividing |GL₂(q)|(q−1)n. Full SL₃ is retained. -/
theorem doubled_layer_index_dvd {H : Type*} [Group H] [Finite H] {n : ℕ}
    (hc : Nat.card F = 2^n) (K : Subgroup H) [K.Normal]
    (e : K ≃* SL F) (ρ : Representation (ZMod 2) H (Space F))
    (hfaith : Function.Injective ρ)
    (hnat : ∀ (g : K) (v : Space F), ρ g v = representation F (e g) v) :
    K.index ∣ ((2^n-1) * Nat.card (GL (Fin 2) F)) * n := by
  have him : K.map ρ.asGroupHom = component F := by
    ext b
    constructor
    · rintro ⟨g,hg,rfl⟩
      exact ⟨e ⟨g,hg⟩,Units.ext (LinearMap.ext (hnat ⟨g,hg⟩)).symm⟩
    · rintro ⟨g,rfl⟩
      obtain ⟨g,rfl⟩ := e.surjective g
      exact ⟨g,g.property,Units.ext (LinearMap.ext (hnat g))⟩
  have hn (h : H) : ρ.asGroupHom h ∈ normalizer F := by
    change ρ.asGroupHom h ∈ Subgroup.normalizer (component F : Set _)
    rw [←him]
    exact K.le_normalizer_map ρ.asGroupHom
      (mem_map_of_mem _ (le_normalizer_of_normal (mem_top h)))
  have hsemi (h : H) : ∃ σ : F ≃+* F, ∀ (c : F) (v : Space F),
      ρ h (c • v) = σ c • ρ h v := normalizer_semilinear (ρ.asGroupHom h) (hn h)
  let φ := SymplecticConjugatePair.Ambient.SemilinearCoefficients.coefficientHom ρ hsemi
  have hlin (g : H) : φ g = 1 ↔ ∀ (c : F) (v : Space F), ρ g (c • v) = c • ρ g v :=
    SymplecticConjugatePair.Ambient.SemilinearCoefficients.coefficient_eq_one_iff ρ φ
      (SymplecticConjugatePair.Ambient.SemilinearCoefficients.coefficientHom_smul ρ hsemi) g
  have hK : K ≤ φ.ker := by
    intro g hg
    apply (hlin g).mpr
    intro c v
    rw [show ρ g (c • v) = representation F (e ⟨g,hg⟩) (c • v) from hnat ⟨g,hg⟩ _,
      hnat ⟨g,hg⟩]
    funext i
    exact Matrix.mulVec_smul (e ⟨g,hg⟩).val c (v i)
  have hker : Nat.card φ.ker ∣ Nat.card (GL (Fin 3) F × GL (Fin 2) F) := by
    have hm : φ.ker.map ρ.asGroupHom ≤ (generalTensor F).asGroupHom.range := by
      rintro b ⟨g,hg,rfl⟩
      exact linear_normalizer_mem_generalTensor F _ (hn g) ((hlin g).mp hg)
    have hd := (card_dvd_of_le hm).trans (card_range_dvd (generalTensor F).asGroupHom)
    rwa [card_map_of_injective (show Function.Injective ρ.asGroupHom from
      fun a b h => hfaith (congrArg Units.val h))] at hd
  have hi : (K.subgroupOf φ.ker).index ∣ (2^n-1) * Nat.card (GL (Fin 2) F) := by
    rw [Nat.card_prod,gl_card_eq_sl_mul_units F, hc] at hker
    have he : Nat.card (K.subgroupOf φ.ker) = Nat.card (SL F) :=
      (Nat.card_congr (subgroupOfEquivOfLe hK).toEquiv).trans (Nat.card_congr e.toEquiv)
    rw [←(K.subgroupOf φ.ker).card_mul_index,he,mul_assoc] at hker
    exact Nat.dvd_of_mul_dvd_mul_left Nat.card_pos hker
  rw [←K.relIndex_mul_index hK]
  apply Nat.mul_dvd_mul hi
  rw [index_ker]
  exact φ.range.card_subgroup_dvd_card.trans
    (dvd_of_eq (SL3OddNaturalNormalizer.binaryFieldAut_card hc))
end Representation.SL3DoubledNaturalOffenders

module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenNormalization.MatrixCalculation.ScalarRigidity
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenNormalization.MatrixCalculation.NormalizerBasis
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenNormalization.ElementOrders

/-!
# The matrix calculation in the supplied representation

For a supplied `BruhatFrame` and faithful seven-dimensional representation,
`NormalizerBasis` constructs coordinates in which x,u and either y or y⁻¹
have images `normalX`, `normalU`, `sourceY`. The actual group relations for w
then force xw to be represented by the literal `sourceV`. The proof passes
through the conjugated matrix-valued homomorphism and applies the linear and
scalar calculations in `ScalarRigidity`.

The final theorem constructs the simultaneous change of basis and source pair;
the intermediate theorem with an explicit change of basis remains available.
Allowing either orientation of y avoids imposing an unnecessary marking on its
Singer action. No irreducibility, model isomorphism, or generation assertion is
assumed. The supplied frame suffices without additional simplicity, ambient
order, or fusion hypotheses. Constructing this frame from the source hypotheses
remains the obligation of the parent normalization theorem.

Source: Gorenstein, *Finite Groups*, §16.6, (6.1)–(6.2), pp.482–483,
describing Z. Janko, J. Algebra 3 (1966), 147–186,
DOI 10.1016/0021-8693(66)90010-X.
-/

namespace CFSG.Quasithin.Janko1RelatorPair.SevenNormalization.MatrixCalculation

private abbrev Mat := Matrix (Fin 7) (Fin 7) (ZMod 11)

private theorem sourceY_mul_transpose : sourceY * sourceY.transpose = 1 := by decide +kernel

private theorem matrix_product_of_images {G : Type*} [Group G]
    (f : G →* Mat) (x y u w : G)
    (hx : f x = normalX) (hy : f y = sourceY) (hu : f u = normalU)
    (h2 : w ^ 2 = 1) (hU : Commute w u)
    (hY : w * y * w⁻¹ = y⁻¹) (h5 : (x * w) ^ 5 = 1) :
    f (x * w) = sourceV := by
  have hi : f y⁻¹ = sourceY.transpose := by
    calc
      f y⁻¹ = f y⁻¹ * (sourceY * sourceY.transpose) := by
        rw [sourceY_mul_transpose, mul_one]
      _ = (f y⁻¹ * f y) * sourceY.transpose := by rw [hy, mul_assoc]
      _ = sourceY.transpose := by rw [← map_mul, inv_mul_cancel, map_one, one_mul]
  have hY' : w * y = y⁻¹ * w := mul_inv_eq_iff_eq_mul.mp hY
  have hwY : f w * sourceY = sourceY.transpose * f w := by
    simpa only [map_mul, hy, hi] using congrArg f hY'
  have hwU : f w * normalU = normalU * f w := by
    simpa only [map_mul, hu] using congrArg f hU.eq
  have hw2 : f w ^ 2 = 1 := by
    simpa only [map_pow, map_one] using congrArg f h2
  have hw5 : (normalX * f w) ^ 5 = 1 := by
    simpa only [map_pow, map_mul, map_one, hx] using congrArg f h5
  rw [map_mul, hx]
  exact matrix_eq_sourceV (f w) hwY hwU hw2 hw5

/-- Application to the literal supplied representation and frame. Either
orientation of the marked seven-generator is permitted. -/
public theorem exists_source_pair_of_normalizer_images
    {G : Type*} [Group G] [Finite G] {h : Janko1CentralizerData G}
    (D : BruhatFrame h) (ρ : G →* Janko1.Ambient) (c : Janko1.Ambient)
    (hx : (c * ρ D.x * c⁻¹ : Matrix (Fin 7) (Fin 7) (ZMod 11)) = normalX)
    (hu : (c * ρ D.u * c⁻¹ : Matrix (Fin 7) (Fin 7) (ZMod 11)) = normalU)
    (hy : (c * ρ D.y * c⁻¹ : Matrix (Fin 7) (Fin 7) (ZMod 11)) = sourceY ∨
      (c * ρ D.y⁻¹ * c⁻¹ : Matrix (Fin 7) (Fin 7) (ZMod 11)) = sourceY) :
    ∃ y v : G,
      (c * ρ y * c⁻¹ : Matrix (Fin 7) (Fin 7) (ZMod 11)) = sourceY ∧
      (c * ρ v * c⁻¹ : Matrix (Fin 7) (Fin 7) (ZMod 11)) = sourceV := by
  let f : G →* Mat := (Units.coeHom _).comp ((MulAut.conj c).toMonoidHom.comp ρ)
  have hfx : f D.x = normalX := hx
  have hfu : f D.u = normalU := hu
  have hw2 : D.w ^ 2 = 1 := by rw [← D.order_w]; exact pow_orderOf_eq_one _
  rcases hy with hy | hy
  · exact ⟨D.y, D.x * D.w, hy,
      matrix_product_of_images f D.x D.y D.u D.w hfx hy hfu hw2
        D.w_centralizes D.w_inverts D.product_fifth⟩
  · have hwi : D.w * D.y⁻¹ * D.w⁻¹ = (D.y⁻¹)⁻¹ := by
      simpa only [mul_inv_rev, inv_inv, mul_assoc] using congrArg (fun g : G => g⁻¹) D.w_inverts
    exact ⟨D.y⁻¹, D.x * D.w, hy,
      matrix_product_of_images f D.x D.y⁻¹ D.u D.w hfx hy hfu hw2
        D.w_centralizes hwi D.product_fifth⟩

/-- The supplied source configuration and faithful representation admit one
change of basis containing both literal matrices from (6.1). The normalizer
basis and all matrix relations are derived from these inputs. -/
public theorem exists_conjugated_source_matrix_images
    {G : Type*} [Group G] [Finite G] {h : Janko1CentralizerData G}
    (D : BruhatFrame h) (ρ : G →* Janko1.Ambient) (hρ : Function.Injective ρ) :
    ∃ c : Janko1.Ambient, ∃ y v : G,
      (c * ρ y * c⁻¹ : Matrix (Fin 7) (Fin 7) (ZMod 11)) = sourceY ∧
      (c * ρ v * c⁻¹ : Matrix (Fin 7) (Fin 7) (ZMod 11)) = sourceV := by
  obtain ⟨c, hx, hu, hy⟩ := exists_normalizer_images D ρ hρ
  exact ⟨c, exists_source_pair_of_normalizer_images D ρ c hx hu hy⟩

end CFSG.Quasithin.Janko1RelatorPair.SevenNormalization.MatrixCalculation

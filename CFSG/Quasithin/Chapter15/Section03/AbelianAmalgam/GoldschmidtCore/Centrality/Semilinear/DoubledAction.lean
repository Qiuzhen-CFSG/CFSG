module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.ActualAction
public import Theory.Representation.PSL3Two.SmallModules
public import Theory.Representation.RepEquiv

/-!
# Literal doubled natural action on the cubic splitting

The map (w,v) ↦ w+bvb⁻¹ intertwines conjugation by every element of the
character kernel: these elements commute with the cubic operator on U.
A natural representation equivalence on W therefore induces an explicit
equivalence on U with two natural binary summands. The equivariance
formula retains the actual quotient map and ambient conjugation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.68 and the terminal module argument, printed pp.1154–1155.
-/

@[expose] public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear
variable {G J : Type*} [Group G] [Group J]

private noncomputable abbrev binaryInclusion (W U : Subgroup G)
    [IsElementaryAbelian 2 W] [IsElementaryAbelian 2 U] (hWU : W ≤ U) :
    Additive W →ₗ[ZMod 2] Additive U :=
  (Subgroup.inclusion hWU).toAdditive.toZModLinearMap 2

/-- The explicit cubic splitting is equivariant for the actual character kernel. -/
theorem cubic_pair_equivariant
    (H B U W : Subgroup G) [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 W]
    (hHB : H ≤ normalizer (B : Set G)) (hHU : H ≤ normalizer (U : Set G))
    (hBU : B ≤ normalizer (U : Set G))
    (h0U : ambientTwoCore B ≤ centralizer (U : Set G)) (hWU : W ≤ U)
    (q : H →* J) (ρ : Representation (ZMod 2) J (Additive W))
    (hconj : ∀ (h : H) (w : Additive W),
      ((ρ (q h) w).toMul : G) = (h : G) * (w.toMul : G) * (h : G)⁻¹)
    (b : B) (P : (Additive W × Additive W) ≃ₗ[ZMod 2] Additive U)
    (hP : ∀ w v, ((P (w,v)).toMul : G) =
      (w.toMul : G) * ((b : G) * (v.toMul : G) * (b : G)⁻¹))
    (h : H) (hχ : quotientAction H B hHB h = 1) (w v : Additive W) :
    P (ρ (q h) w,ρ (q h) v) = spanAction H U hHU h (P (w,v)) := by
  let ι := binaryInclusion W U hWU
  let β := externalCubicAction B U hBU h0U (QuotientGroup.mk' _ b)
  have hP' (w v : Additive W) : P (w,v) = ι w + β (ι v) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact hP w v
  have hi (w : Additive W) : ι (ρ (q h) w) = spanAction H U hHU h (ι w) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact hconj h w
  have hc : spanAction H U hHU h * β = β * spanAction H U hHU h := by
    simpa only [hχ,MulAut.one_apply] using
      externalCubicAction_intertwining H B U hHB hHU hBU h0U h (QuotientGroup.mk' _ b)
  rw [hP',hP',map_add,hi,hi]
  congr 1
  exact (LinearMap.congr_fun hc (ι v)).symm

/-- A natural identification of the actual W yields two natural summands on U,
with literal ambient conjugation for every element of the character kernel. -/
theorem doubled_natural_of_cubic_pair
    (H B U W : Subgroup G) [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 W]
    (hHB : H ≤ normalizer (B : Set G)) (hHU : H ≤ normalizer (U : Set G))
    (hBU : B ≤ normalizer (U : Set G))
    (h0U : ambientTwoCore B ≤ centralizer (U : Set G)) (hWU : W ≤ U)
    (q : H →* J) (ρ : Representation (ZMod 2) J (Additive W))
    (hconj : ∀ (h : H) (w : Additive W),
      ((ρ (q h) w).toMul : G) = (h : G) * (w.toMul : G) * (h : G)⁻¹)
    (b : B) (P : (Additive W × Additive W) ≃ₗ[ZMod 2] Additive U)
    (hP : ∀ w v, ((P (w,v)).toMul : G) =
      (w.toMul : G) * ((b : G) * (v.toMul : G) * (b : G)⁻¹))
    (m : J ≃* BinaryLinearThree.Group)
    (e : ρ.Equiv (BinaryLinearThree.W.comp m.toMonoidHom)) :
    ∃ Φ : Additive U ≃ₗ[ZMod 2] (BinaryLinearThree.Vector × BinaryLinearThree.Vector),
      ∀ (h : H), quotientAction H B hHB h = 1 → ∀ u : Additive U,
        Φ (spanAction H U hHU h u) =
          (BinaryLinearThree.W (m (q h)) (Φ u).1,
           BinaryLinearThree.W (m (q h)) (Φ u).2) := by
  let Φ := P.symm.trans (e.toLinearEquiv.prodCongr e.toLinearEquiv)
  have hΦ (w v : Additive W) : Φ (P (w,v)) = (e w,e v) := by
    simp only [Φ,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply]
    rfl
  refine ⟨Φ,?_⟩
  intro h hχ u
  obtain ⟨⟨w,v⟩,rfl⟩ := P.surjective u
  rw [← cubic_pair_equivariant H B U W hHB hHU hBU h0U hWU q ρ hconj b P hP h hχ]
  have he (w : Additive W) : e (ρ (q h) w) = BinaryLinearThree.W (m (q h)) (e w) :=
    Representation.IntertwiningMap.isIntertwining ρ (BinaryLinearThree.W.comp m.toMonoidHom)
      e.toIntertwiningMap (q h) w
  rw [hΦ,hΦ]
  exact Prod.ext (he w) (he v)


end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear

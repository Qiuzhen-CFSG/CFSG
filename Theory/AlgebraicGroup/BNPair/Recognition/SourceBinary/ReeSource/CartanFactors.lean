module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.RankOneOrders

/-!
# Actual Cartan product coordinates at each source endpoint

The fixed-kernel theorem turns the odd reflection decomposition into
H = (H ∩ K_i) × H_i⁻. Restriction of the actual faithful-panel projection
identifies H_i⁻ with the entire Cartan image, preserving representatives.
Thus its order is exactly the appropriate field-unit order for the linear
or Suzuki marking, including the binary parameters.

These are the individual reflection factorizations in Fong–Seitz I,
proof of (6H)(a), p.51. They do not identify the two endpoint kernels as
each other's inverted factors: that still needs the cross-root scalar
action and common-field argument. OriginalCartan supplies the literal
original/geometric application with both whole-Borel markings retained.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)

def kernelReflectionEquiv
    (hfix : reflectionFixed Q split i = (cartanPanelMap Q i).ker) :
    (cartanPanelMap Q i).ker × reflectionInverted Q split i ≃*
      (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) :=
  ((MulEquiv.subgroupCongr hfix.symm).prodCongr (MulEquiv.refl _)).trans
    (cartanReflectionEquiv Q split i)

@[simp] theorem kernelReflectionEquiv_apply
    (hfix : reflectionFixed Q split i = (cartanPanelMap Q i).ker)
    (a : (cartanPanelMap Q i).ker) (b : reflectionInverted Q split i) :
    (kernelReflectionEquiv Q split i hfix (a,b) : X ⧸ Q.D) =
      (a.val : X ⧸ Q.D) * b.val := rfl

/-- The inverted factor projects onto precisely the whole actual Cartan image. -/
def invertedImageMap : reflectionInverted Q split i →* (cartanPanelMap Q i).range :=
  (cartanPanelMap Q i).rangeRestrict.comp (reflectionInverted Q split i).subtype

theorem invertedImageMap_bijective
    (hfix : reflectionFixed Q split i = (cartanPanelMap Q i).ker) :
    Function.Bijective (invertedImageMap Q split i) := by
  let := split.abelian
  constructor
  · apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro x hx
    have hxK : x.val ∈ (cartanPanelMap Q i).ker := congrArg Subtype.val hx
    rw [← hfix] at hxK
    apply Subtype.ext
    exact (OddReflection.fixed_disjoint_inverted (simpleCartanAction Q split i) split.odd).le_bot
      ⟨hxK,x.property⟩
  · rintro ⟨h,a,rfl⟩
    obtain ⟨⟨c,d⟩,hcd⟩ := (kernelReflectionEquiv Q split i hfix).surjective a
    refine ⟨d,?_⟩
    apply Subtype.ext
    change cartanPanelMap Q i d.val = cartanPanelMap Q i a
    have he : c.val*d.val = a := hcd
    rw [← he, map_mul, show cartanPanelMap Q i c.val = 1 from c.property, one_mul]

def invertedImageEquiv
    (hfix : reflectionFixed Q split i = (cartanPanelMap Q i).ker) :
    reflectionInverted Q split i ≃* (cartanPanelMap Q i).range :=
  MulEquiv.ofBijective (invertedImageMap Q split i) (invertedImageMap_bijective Q split i hfix)

@[simp] theorem invertedImageEquiv_apply
    (hfix : reflectionFixed Q split i = (cartanPanelMap Q i).ker)
    (b : reflectionInverted Q split i) :
    (invertedImageEquiv Q split i hfix b : Endpoint Q i ⧸ panelKernel Q i) =
      cartanPanelMap Q i b.val := rfl

open BenderSuzuki.MatrixGroups

def linearCartanEquiv (n : ℕ)
    (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hB : (quotientBorel Q i).map μ.toMonoidHom = normalizer (T : Set _))
    (s : RootReflection Q split i) :
    (cartanPanelMap Q i).ker × reflectionInverted Q split i ≃*
      (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) :=
  kernelReflectionEquiv Q split i (linear_reflectionFixed_eq_kernel Q split i n μ T hB s)

def suzukiCartanEquiv (m : ℕ)
    (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
    (hB : (quotientBorel Q i).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
    (s : RootReflection Q split i) :
    (cartanPanelMap Q i).ker × reflectionInverted Q split i ≃*
      (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) :=
  kernelReflectionEquiv Q split i (suzuki_reflectionFixed_eq_kernel Q split i m μ hB s)

theorem linear_inverted_card (n : ℕ) (hn : 0 < n)
    (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hB : (quotientBorel Q i).map μ.toMonoidHom = normalizer (T : Set _))
    (s : RootReflection Q split i) : Nat.card (reflectionInverted Q split i) = 2^n-1 := by
  rw [Nat.card_congr (invertedImageEquiv Q split i
    (linear_reflectionFixed_eq_kernel Q split i n μ T hB s)).toEquiv]
  exact linear_cartanImage_card Q split i n hn μ T hB s

theorem suzuki_inverted_card (m : ℕ)
    (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
    (hB : (quotientBorel Q i).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
    (s : RootReflection Q split i) : Nat.card (reflectionInverted Q split i) = 2^(2*m+1)-1 := by
  rw [Nat.card_congr (invertedImageEquiv Q split i
    (suzuki_reflectionFixed_eq_kernel Q split i m μ hB s)).toEquiv]
  exact suzuki_cartanImage_card Q split i m μ hB s

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource

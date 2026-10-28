module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureCore
public import Theory.Representation.SL3DoubledNaturalOffenders.BinaryOrbits
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureFactors

/-!
# The natural quotient at a pure line

The binary point stabilizer is transitive on the six vectors outside its
fixed line. An invariant subgroup containing the line and one further
natural vector therefore contains the entire natural factor. This is the
irreducibility step for V₁/Z₁ in the terminal binary doubled argument.
The application in NonFFSourceDoubledBinaryPureCore uses the actual local
Sylow fixed-vector lift, literal centralizer core and marked component map.
Source: Aschbacher–Smith, 7.6.1, printed p.702, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureNatural
open BinaryLinearThree NaturalDual ChapterE DoubledBinaryPureCore
variable {G : Type*} [_root_.Group G]

/-- The point stabilizer is transitive on the six vectors outside its
fixed line. Thus an invariant subgroup containing that line and one more
natural vector contains the entire original natural factor. -/
theorem natural_factor_le_of_fixed_seed
    (W₀ L A Z N : Subgroup G) [IsElementaryAbelian 2 W₀]
    (hLN : L ≤ normalizer (W₀ : Set G)) (hAW : A ≤ W₀)
    (q : L →* Group) (hq : Function.Surjective q)
    (E : Additive W₀ ≃ₗ[ZMod 2] Space)
    (hE : ∀ l w, E (automizerRepresentation W₀
      (W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) w) = action (q l) (E w))
    (hA : ∀ w, (E w).2 = 0 ↔ (w.toMul : G) ∈ A)
    (hZ : Nat.card Z = 2) (hZA : Z ≤ A) (hZN : Z ≤ N)
    (hN : L ⊓ centralizer (Z : Set G) ≤ normalizer (N : Set G))
    (x : G) (hx : x ∈ A) (hxN : x ∈ N) (hxZ : x ∉ Z) : A ≤ N := by
  obtain ⟨z,hz,hunique⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hZ
  let u : Additive W₀ := Additive.ofMul ⟨z,hAW (hZA z.property)⟩
  let v : Additive W₀ := Additive.ofMul ⟨x,hAW hx⟩
  have hu : (E u).2 = 0 := (hA u).mpr (hZA z.property)
  have hv : (E v).2 = 0 := (hA v).mpr hx
  have hu0 : (E u).1 ≠ 0 := by
    intro he
    have hh := E.map_eq_zero_iff.mp (Prod.ext he hu)
    apply hz
    exact Subtype.ext (congrArg (fun w : Additive W₀ => (w.toMul : G)) hh)
  have hv0 : (E v).1 ≠ 0 := by
    intro he
    have hh := E.map_eq_zero_iff.mp (Prod.ext he hv)
    have heq : x = 1 := congrArg (fun w : Additive W₀ => (w.toMul : G)) hh
    exact hxZ (heq.symm ▸ Z.one_mem)
  have huv : (E u).1 ≠ (E v).1 := by
    intro he
    have hh := E.injective (Prod.ext he (hu.trans hv.symm))
    have heq : (z : G) = x := congrArg (fun w : Additive W₀ => (w.toMul : G)) hh
    exact hxZ (heq ▸ z.property)
  intro y hy
  by_cases hyZ : y ∈ Z
  · exact hZN hyZ
  let w : Additive W₀ := Additive.ofMul ⟨y,hAW hy⟩
  have hw : (E w).2 = 0 := (hA w).mpr hy
  have hw0 : (E w).1 ≠ 0 := by
    intro he
    have hh := E.map_eq_zero_iff.mp (Prod.ext he hw)
    have heq : y = 1 := congrArg (fun w : Additive W₀ => (w.toMul : G)) hh
    exact hyZ (heq.symm ▸ Z.one_mem)
  have huw : (E u).1 ≠ (E w).1 := by
    intro he
    have hh := E.injective (Prod.ext he (hu.trans hw.symm))
    have heq : (z : G) = y := congrArg (fun w : Additive W₀ => (w.toMul : G)) hh
    exact hyZ (heq ▸ z.property)
  obtain ⟨g,hgu,hgv⟩ := SL3DoubledNaturalOffenders.BinaryOrbits.pair_transitive
    (E u).1 (E v).1 (E u).1 (E w).1 hu0 hv0 huv hu0 hw0 huw
  obtain ⟨l,hl⟩ := hq g
  have hfix : automizerRepresentation W₀
      (W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) u = u := by
    apply E.injective
    rw [hE,hl]
    apply Prod.ext hgu
    change W.dual g (E u).2 = (E u).2
    rw [hu,map_zero]
  have hlz : (l : G) * (z : G) * (l : G)⁻¹ = z :=
    congrArg (fun w : Additive W₀ => (w.toMul : G)) hfix
  have hlC : (l : G) ∈ centralizer (Z : Set G) := by
    intro b hb
    by_cases hb1 : (⟨b,hb⟩ : Z) = 1
    · have hb' : b = 1 := congrArg Subtype.val hb1
      simp only [hb',one_mul,mul_one]
    · have hb' : b = z := congrArg Subtype.val (hunique ⟨b,hb⟩ hb1)
      rw [hb']
      exact (mul_inv_eq_iff_eq_mul.mp hlz).symm
  have hmove : automizerRepresentation W₀
      (W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) v = w := by
    apply E.injective
    rw [hE,hl]
    apply Prod.ext hgv
    change W.dual g (E v).2 = (E w).2
    rw [hv,hw,map_zero]
  have hxy : (l : G) * x * (l : G)⁻¹ = y :=
    congrArg (fun w : Additive W₀ => (w.toMul : G)) hmove
  rw [←hxy]
  exact (mem_normalizer_iff.mp (hN ⟨l.property,hlC⟩) x).mp hxN

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureNatural

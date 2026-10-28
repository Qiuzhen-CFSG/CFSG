module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoShearCorrection
public import Theory.Representation.BinaryConjugationSection.QuadraticPair
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.Tactic.Group

/-!
# Correcting a section stabilizer in the original group

Surjective actual commutator rows realize every shear of the original
numerator over the specified quotient coordinates. A lift centralizing the
denominator and preserving a subgroup's quotient image can therefore be
corrected to normalize that literal subgroup. No containment of the
denominator in the corrected subgroup is required.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.DecomposableQuinticControl

/-- Full actual kernel rows lift a quotient-subspace stabilizer to the
normalizer of the original subgroup, without changing its section action. -/
theorem exists_row_correction_normalizing_subgroup
    {G : Type*} [Group G] (H F D E B : Subgroup G)
    [Finite F] [IsElementaryAbelian 2 F] [IsMulCommutative D]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) (dF : BinaryConjugationSection H F D ρ)
    (hEF : E ≤ F) (hBH : B ≤ H)
    (row : B →* (Multiplicative W →* D)) (hrow : Function.Surjective row)
    (heval : ∀ (b : B) (f : F),
      (row b (dF.coordinates f) : G) = ⁅(b : G),(f : G)⁆)
    (l : H) (hlD : (l : G) ∈ centralizer (D : Set G))
    (himage : (dF.imageSpace E).map (ρ l) = dF.imageSpace E) :
    ∃ b : B, (b : G) * (l : G) ∈ normalizer (E : Set G) ∧
      ρ (inclusion hBH b * l) = ρ l := by
  classical
  let p : Additive F →ₗ[ZMod 2] W := dF.coordinates.toAdditiveLeft.toZModLinearMap 2
  let ES : Submodule (ZMod 2) (Additive F) :=
    AddSubgroup.toZModSubmodule 2 (E.subgroupOf F).toAddSubgroup
  let α := F.normalizerMonoidHom (inclusion dF.normalized l)
  let g : Additive F ≃ₗ[ZMod 2] Additive F :=
    α.toAdditive.toLinearEquiv (fun t v => ZMod.map_smul α.toAdditive.toAddMonoidHom t v)
  have hpker (x : Additive F) : x ∈ p.ker ↔ (x.toMul : G) ∈ D := by
    change (dF.coordinates x.toMul).toAdd = 0 ↔ _
    exact dF.coordinates_eq_one_iff x.toMul
  have hfix : ∀ x ∈ p.ker, g x = x := by
    intro x hx
    apply Additive.toMul.injective
    apply Subtype.ext
    change (l : G) * (x.toMul : G) * (l : G)⁻¹ = (x.toMul : G)
    rw [(hlD _ ((hpker x).mp hx)).symm, mul_inv_cancel_right]
  have hpe : ES.map p = dF.imageSpace E := by
    ext w
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact (dF.mem_imageSpace_iff E _).mpr ⟨x.toMul,hx,rfl⟩
    · intro hw
      obtain ⟨x,hx,he⟩ := (dF.mem_imageSpace_iff E w).mp hw
      exact ⟨Additive.ofMul x,hx,he⟩
  have hpg : p.comp g.toLinearMap = (ρ l).comp p := by
    ext x
    exact dF.equivariant l x.toMul
  have hi : ES.map (p.comp g.toLinearMap) = ES.map p := by
    rw [hpg, Submodule.map_comp, hpe, himage]
  obtain ⟨f,hf⟩ := exists_shear_correcting_subspace p ES g hfix hi
  let k : Multiplicative p.ker →* D := {
    toFun x := ⟨(x.toAdd.val.toMul : G),(hpker x.toAdd.val).mp x.toAdd.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  let r : Multiplicative W →* D := k.comp f.toAddMonoidHom.toMultiplicative
  obtain ⟨b,hb⟩ := hrow r
  let bl : H := inclusion hBH b * l
  let β := F.normalizerMonoidHom (inclusion dF.normalized bl)
  let φ := g.toLinearMap + p.ker.subtype.comp (f.comp (p.comp g.toLinearMap))
  have hφ (x : Additive F) : φ x = Additive.ofMul (β x.toMul) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    let y : F := α x.toMul
    have hr : ((f (p (g x))).val.toMul : G) = ⁅(b : G),(y : G)⁆ := by
      have hh := heval b y
      rw [hb] at hh
      exact hh
    change (y : G) * ((f (p (g x))).val.toMul : G) =
      ((b : G) * (l : G)) * (x.toMul : G) * ((b : G) * (l : G))⁻¹
    rw [hr]
    have hc : (y : G) * ⁅(b : G),(y : G)⁆ = ⁅(b : G),(y : G)⁆ * (y : G) := by
      have hd : ⁅(b : G),(y : G)⁆ ∈ F := by
        rw [←heval b y]
        exact dF.kernel_le (row b (dF.coordinates y)).property
      exact congrArg Subtype.val (mul_comm y (⟨_,hd⟩ : F))
    rw [hc]
    dsimp [y,α]
    simp only [normalizerMonoidHom_apply_apply_coe, coe_inclusion]
    group
  have hnormal : (bl : G) ∈ normalizer (E : Set G) := by
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · intro hx
      have hm : φ (Additive.ofMul (⟨x,hEF hx⟩ : F)) ∈ ES := by
        rw [←hf]
        exact ⟨Additive.ofMul (⟨x,hEF hx⟩ : F),hx,rfl⟩
      rw [hφ] at hm
      exact hm
    · intro hx
      have hfx : (bl : G) * x * (bl : G)⁻¹ ∈ F := hEF hx
      have hxF : x ∈ F := (mem_normalizer_iff.mp (dF.normalized bl.property) x).mpr hfx
      have hm : Additive.ofMul (β (⟨x,hxF⟩ : F)) ∈ ES.map φ := by
        rw [hf]
        exact hx
      obtain ⟨z,hz,hzφ⟩ := hm
      rw [hφ] at hzφ
      have hz' : z.toMul = (⟨x,hxF⟩ : F) := β.injective (Additive.ofMul.injective hzφ)
      change (z.toMul : G) ∈ E at hz
      simpa only [hz'] using hz
  have hbact : ρ (inclusion hBH b) = 1 := by
    apply LinearMap.ext
    intro w
    obtain ⟨x,hx⟩ := dF.onto (Multiplicative.ofAdd w)
    have hm : ⁅(b : G),(x : G)⁆ ∈ D := by
      rw [←heval b x]
      exact (row b (dF.coordinates x)).property
    let c : F := (F.normalizerMonoidHom (inclusion dF.normalized (inclusion hBH b)) x) * x⁻¹
    have hzero : dF.coordinates c = 1 := (dF.coordinates_eq_one_iff c).mpr hm
    have he := dF.equivariant (inclusion hBH b) x
    have hc : dF.coordinates (F.normalizerMonoidHom
        (inclusion dF.normalized (inclusion hBH b)) x) = dF.coordinates x := by
      have hh := hzero
      change dF.coordinates (_ * x⁻¹) = 1 at hh
      rw [map_mul,map_inv,mul_inv_eq_one] at hh
      exact hh
    change (dF.coordinates (F.normalizerMonoidHom
      (inclusion dF.normalized (inclusion hBH b)) x)).toAdd =
        ρ (inclusion hBH b) (dF.coordinates x).toAdd at he
    rw [hc,hx] at he
    exact he.symm
  refine ⟨b,hnormal,?_⟩
  rw [map_mul,hbact,one_mul]

end CFSG.Quasithin.Chapter15.DecomposableQuinticControl

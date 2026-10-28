module

public import Theory.Representation.PSL3Two.SmallModuleProperties
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.SpecificGroups.PSL3Two.OuterInvolutionSinger

/-!
# Singer displacement on the three small binary modules

The specified Singer matrix has no fixed vector in the natural module, and
contragredience preserves its displacement. On the trace-zero adjoint module,
a fixed vector is a commuting trace-zero matrix. Its first-column entries in
rows one and two determine it; the resulting injection into F₂² bounds the
fixed space by two. Since the adjoint space has dimension eight, its fixed
codimension is at least six.

These are intrinsic calculations on the concrete models of Aschbacher–Smith
H.6.1, printed p.386, used in the paired-module step of 13.8.21(1), printed
p.956 (combined manuscript of 1 March 2004).
-/

public section
open Representation Representation.BinaryOffender
open scoped Matrix
namespace BinaryLinearThree.SingerDisplacement
open Matrix.PSL3Two.OuterInvolutionSinger
private abbrev Mat := Matrix (Fin 3) (Fin 3) (ZMod 2)
private theorem matrix_W (g : Group) : LinearMap.toMatrix' (W g) = g.val := by
  change LinearMap.toMatrix' (Matrix.toLin' g.val) = g.val
  exact LinearMap.toMatrix'_toLin' g.val

private theorem fixed_commutes (f : Steinberg) (hf : S singer f = f) :
    LinearMap.toMatrix' f.val * singer.val = singer.val * LinearMap.toMatrix' f.val := by
  have he := congrArg (fun f : Steinberg => f.val) hf
  change W singer ∘ₗ f.val ∘ₗ W singer⁻¹ = f.val at he
  have hinv : W singer⁻¹ ∘ₗ W singer = LinearMap.id := by
    rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hh := congrArg (fun q : Module.End (ZMod 2) Vector => q ∘ₗ W singer) he
  simp only [LinearMap.comp_assoc, hinv, LinearMap.comp_id] at hh
  have hm := congrArg LinearMap.toMatrix' hh
  simpa only [LinearMap.toMatrix'_comp, matrix_W] using hm.symm

private noncomputable def fixedCoordinates :
    fixedSpace S (Subgroup.zpowers singer) →ₗ[ZMod 2] (ZMod 2 × ZMod 2) where
  toFun f := (f.val.val (Pi.single 0 1) 1, f.val.val (Pi.single 0 1) 2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem fixedCoordinates_injective : Function.Injective fixedCoordinates := by
  apply (LinearMap.ker_eq_bot).mp
  apply _root_.eq_bot_iff.mpr
  intro f hf
  change fixedCoordinates f = 0 at hf
  have h1 : LinearMap.toMatrix' f.val.val 1 0 = 0 := congrArg Prod.fst hf
  have h2 : LinearMap.toMatrix' f.val.val 2 0 = 0 := congrArg Prod.snd hf
  have hc := fixed_commutes f.val (f.property ⟨singer, Subgroup.mem_zpowers singer⟩)
  have ht : Matrix.trace (LinearMap.toMatrix' f.val.val) = 0 := by
    have htrace : LinearMap.trace (ZMod 2) Vector f.val.val =
        Matrix.trace (LinearMap.toMatrix' f.val.val) := by
      simpa only [LinearMap.toMatrix_eq_toMatrix'] using
        LinearMap.trace_eq_matrix_trace (ZMod 2) (Pi.basisFun (ZMod 2) (Fin 3)) f.val.val
    rw [← htrace]
    exact f.val.property
  have hm : ∀ f : Mat, f * singer.val = singer.val * f → Matrix.trace f = 0 →
      f 1 0 = 0 → f 2 0 = 0 → f = 0 := by decide +kernel
  have hz := hm _ hc ht h1 h2
  apply Subtype.ext
  apply Subtype.ext
  exact LinearMap.toMatrix'.injective (by simpa using hz)

/-- The trace-zero adjoint action of the Singer element displaces at least six dimensions. -/
theorem six_le_fixedCodim_singer_steinberg : 6 ≤ fixedCodim S (Subgroup.zpowers singer) := by
  have hle := LinearMap.finrank_le_finrank_of_injective fixedCoordinates_injective
  have hd : Module.finrank (ZMod 2) (ZMod 2 × ZMod 2) = 2 := by simp
  rw [hd] at hle
  have hcod := fixedCodim_add_finrank S (Subgroup.zpowers singer)
  rw [finrank_steinberg] at hcod
  omega

/-- The Singer element fixes no nonzero vector on the natural module. -/
theorem fixedCodim_singer_natural : fixedCodim W (Subgroup.zpowers singer) = 3 := by
  have hb : fixedSpace W (Subgroup.zpowers singer) = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro v hv
    have hf : W singer v = v := hv ⟨singer, Subgroup.mem_zpowers singer⟩
    have hc : ∀ v : Vector, singer.val *ᵥ v = v → v = 0 := by decide
    exact hc v hf
  have hcod := fixedCodim_add_finrank W (Subgroup.zpowers singer)
  rw [hb, finrank_bot, add_zero] at hcod
  simpa [BinaryLinearThree.Vector, Matrix.PSL3Two.Fano.Vector] using hcod

/-- The Singer element fixes no nonzero vector on the contragredient natural module. -/
theorem fixedCodim_singer_dual : fixedCodim W.dual (Subgroup.zpowers singer) = 3 := by
  rw [fixedCodim_zpowers_dual, fixedCodim_singer_natural]
end BinaryLinearThree.SingerDisplacement

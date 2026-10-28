module

public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.DoubleCover.NontrivialDisplacement.RootPairs
public import Theory.SpecificGroups.PSL3Four.SylowModel

/-!
# Source lifting input and unitary Sylow coordinates

I.2.2(3b) says that projective involutions lift to involutions when the
covering center is elementary. For a center of order two, all lifts then
have square one: two lifts differ by a central involution. Consequently the
full preimage of an elementary two-subgroup is elementary abelian.

The separate `UnitarySylowModel` contract specifies an actual embedding of
UT₃(F₄) as a graph-field-invariant Sylow subgroup, with the graph-field action
in a hyperbolic basis. The existence of these coordinates and their lifted
root presentation remain separate obligations; neither is asserted here.
This allows the matrix calculation and the central-cover lifting argument
to proceed independently, with final assembly in the parent module.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
I.2.2(3b), printed pp.409–410, and 16.4.9(2), printed p.1191.
-/

@[expose] public section
open Subgroup
namespace Matrix.PSL3Four.InnerFamilyNormalizer.DoubleCover.NontrivialDisplacement
variable {H : Type*} [Group H]

/-- The involution-lifting clause of I.2.2(3b), for the specified covering map. -/
def InvolutionLifting (c : PerfectCentralCovering.Cover H PSL) : Prop :=
  ∀ v : PSL, orderOf v = 2 → ∃ x : H, c.toMonoidHom x = v ∧ orderOf x = 2

/-- Every lift, not just a chosen lift, of an involution has square one. -/
theorem square_eq_one_of_projective_square
    (c : PerfectCentralCovering.Cover H PSL)
    (hk : c.toMonoidHom.ker = center H) (hZ : Nat.card (center H) = 2)
    (hlift : InvolutionLifting c) (x : H) (hx : (c.toMonoidHom x) ^ 2 = 1) :
    x ^ 2 = 1 := by
  have hzsq (z : H) (hz : z ∈ center H) : z ^ 2 = 1 := by
    have h := pow_card_eq_one' (x := (⟨z, hz⟩ : center H))
    rw [hZ] at h
    exact congrArg Subtype.val h
  by_cases he : c.toMonoidHom x = 1
  · exact hzsq x (hk ▸ (show x ∈ c.toMonoidHom.ker from he))
  · obtain ⟨y, hy, hy2⟩ := hlift (c.toMonoidHom x) (orderOf_eq_prime hx he)
    have hySq : y ^ 2 = 1 := by simpa only [hy2] using pow_orderOf_eq_one y
    have hxy : x * y⁻¹ ∈ center H := by
      rw [← hk, MonoidHom.mem_ker, map_mul, map_inv, hy, mul_inv_cancel]
    have hc : Commute (x * y⁻¹) y := (mem_center_iff.mp hxy y).symm
    calc
      x ^ 2 = ((x * y⁻¹) * y) ^ 2 := by rw [inv_mul_cancel_right]
      _ = (x * y⁻¹) ^ 2 * y ^ 2 := hc.mul_pow 2
      _ = 1 := by rw [hzsq _ hxy, hySq, one_mul]

/-- The preimage of any elementary two-subgroup is elementary. This uses the
 source involution-lifting clause and the actual center-C₂ kernel. -/
theorem elementary_preimage
    (c : PerfectCentralCovering.Cover H PSL)
    (hk : c.toMonoidHom.ker = center H) (hZ : Nat.card (center H) = 2)
    (hlift : InvolutionLifting c) (V : Subgroup PSL) [IsElementaryAbelian 2 V] :
    IsElementaryAbelian 2 (V.comap c.toMonoidHom) := by
  have hs (x : V.comap c.toMonoidHom) : x ^ 2 = 1 := by
    apply Subtype.ext
    exact square_eq_one_of_projective_square c hk hZ hlift x (by
      have he := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 V) (⟨c.toMonoidHom x, x.property⟩ : V)
      exact congrArg Subtype.val he)
  have hi (x : V.comap c.toMonoidHom) : x⁻¹ = x :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hs x)
  refine {
    toIsMulCommutative := ⟨⟨?_⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }
  intro x y
  calc
    x * y = (x * y)⁻¹ := (hi _).symm
    _ = y * x := by rw [_root_.mul_inv_rev, hi, hi]

/-- Unitary coordinates on an actual graph-field-invariant projective Sylow
 subgroup. The formula is inverse transpose followed by Frobenius in a
 hyperbolic basis; the embedding must be constructed in the concrete PSL. -/
structure UnitarySylowModel where
  embedding : SylowModel.U →* PSL
  injective : Function.Injective embedding
  sylow : Sylow 2 PSL
  range_eq : embedding.range = (sylow : Subgroup PSL)
  compatible : ∀ u : SylowModel.U,
    ExtendedCentralizer.ProjectiveFixer.graphField (embedding u) =
      embedding ⟨u.y ^ 2, u.x ^ 2, u.c ^ 2 + (u.x * u.y) ^ 2⟩

end Matrix.PSL3Four.InnerFamilyNormalizer.DoubleCover.NontrivialDisplacement

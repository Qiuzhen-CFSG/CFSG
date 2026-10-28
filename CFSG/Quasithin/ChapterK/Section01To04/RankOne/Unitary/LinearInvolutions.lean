module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Unitary.Model
public import Theory.SpecificGroups.SU3.LinearNormalizerInvolutions
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Field

/-!
# Linear involutions in the natural SU₃ extension

The F-linearity of one ambient involution gives a square-one matrix on the
marked column module. Normality of the original layer makes that matrix
normalize the literal special unitary subgroup. The linear normalizer theorem
then places the matrix in SU₃, and faithfulness identifies the original element
with its preimage in the layer, retaining the possible cubic center.

The final theorem supplies the linear-involution clause of the K.3.3 normalizer
argument. It assumes no coefficient homomorphism or global semilinearity.
Source: Aschbacher–Smith, K.3.3, printed p.456 (1 March 2004 manuscript).
-/

public section
open BenderSuzuki.MatrixGroups Matrix
namespace CFSG.Quasithin.ChapterK.RankOne.UnitaryModel
variable {G V F : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [Field F] [Algebra (ZMod 2) F]
  {J : HermitianForm 3 F} {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
  (M : UnitaryModel J ρ L)

/-- A linear involution in a faithful extension of the marked natural SU₃
module belongs to the actual special-unitary layer. -/
theorem linear_involution_mem_of_normal [L.Normal]
    (hfaith : Function.Injective ρ)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hconj : ∃ z : F, J.conj z ≠ z) {t : G} (ht : t ^ 2 = 1)
    (hlinear : ∀ (c : F) (v : Fin 3 → F),
      M.coordinateAction t (c • v) = c • M.coordinateAction t v) : t ∈ L := by
  classical
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  have htt : t * t = 1 := by simpa [pow_two] using ht
  have htact (v : Fin 3 → F) : M.coordinateAction t (M.coordinateAction t v) = v := by
    change (M.coordinateAction t * M.coordinateAction t) v = v
    rw [← map_mul, htt, map_one]
    rfl
  let f : (Fin 3 → F) →ₗ[F] (Fin 3 → F) :=
    { toFun := M.coordinateAction t
      map_add' := (M.coordinateAction t).map_add
      map_smul' := hlinear }
  let A := LinearMap.toMatrix' f
  have hA (v : Fin 3 → F) : A *ᵥ v = M.coordinateAction t v :=
    LinearMap.toMatrix'_mulVec f v
  have hAA : A * A = 1 := by
    apply Matrix.mulVec_injective
    funext v
    rw [← Matrix.mulVec_mulVec, hA, hA, htact, Matrix.one_mulVec]
  let S : GL (Fin 3) F := ⟨A, A, hAA, hAA⟩
  have hS : S * S = 1 := Units.ext hAA
  have hSact (v : Fin 3 → F) : S.val *ᵥ v = M.coordinateAction t v := hA v
  have hN (X : J.specialSubgroup) : S * X.val * S ∈ J.specialSubgroup := by
    let l := M.groupEquiv.symm X
    have hn : t * (l : G) * t ∈ L := by
      have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
      simpa only [htinv] using (inferInstance : L.Normal).conj_mem (l : G) l.property t
    let y : L := ⟨t * (l : G) * t, hn⟩
    have he : S * X.val * S = (M.groupEquiv y).val := by
      apply Units.ext
      apply Matrix.mulVec_injective
      funext v
      change (S.val * X.val.val * S.val) *ᵥ v = _
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hSact]
      have hX (w : Fin 3 → F) : X.val.val *ᵥ w = M.coordinateAction (l : G) w := by
        rw [M.coordinateAction_natural]
        simp [l]
      rw [hX, hSact, ← M.coordinateAction_natural]
      change _ = M.coordinateAction (t * (l : G) * t) v
      rw [map_mul, map_mul]
      rfl
    rw [he]
    exact (M.groupEquiv y).property
  have hSU := HermitianForm.LinearNormalizerInvolutions.mem_special_of_square_one
    J hJ hconj S hS hN
  let l := M.groupEquiv.symm ⟨S, hSU⟩
  have he : t = (l : G) := by
    apply M.coordinateAction_injective hfaith
    apply LinearMap.ext
    intro v
    rw [M.coordinateAction_natural]
    simpa [l] using (hSact v).symm
  exact he ▸ l.property

variable [Finite G] [Finite F]

/-- The linear-involution clause used in K.3.3. Its only semilinearity input
is F-linearity of this single element. -/
theorem linear_involution_mem (h : SourceHypotheses ρ L)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) {s : ℕ} (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hconj : ∀ x : F, J.conj x = x ^ (2 ^ s))
    {t : G} (ht : t ^ 2 = 1)
    (hlinear : ∀ (c : F) (v : Fin 3 → F),
      M.coordinateAction t (c • v) = c • M.coordinateAction t v) : t ∈ L := by
  let : L.Normal := h.layer_normal
  apply M.linear_involution_mem_of_normal h.faithful hJ ?_ ht hlinear
  have hfixed : Nat.card {z : F // J.conj z = z} = 2 ^ s :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 s (by omega) hcard hconj
  have hne := J.conj_ne_one_of_card s hs hcard hfixed
  by_contra! he
  apply hne
  exact RingEquiv.ext he

end CFSG.Quasithin.ChapterK.RankOne.UnitaryModel

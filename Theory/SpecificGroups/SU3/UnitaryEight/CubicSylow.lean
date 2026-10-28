module

public import Theory.GroupTheory.ExternalCubicSylow
public import Theory.SpecificGroups.SU3.UnitaryEight.MatrixCentralizer
public import BenderSuzuki.External.Huppert.II.theorem_10_12

/-!
# Outside diagonal cubics and Sylow two-subgroups of PSU₃(8)

The genuine matrix model has Sylow two-subgroups of order 512. If an
outside diagonal cubic permutes with a two-subgroup meeting the component
in a Sylow subgroup, it normalizes that intersection. Its faithful action
then normalizes a two-subgroup of order 512 in the automorphism group.
The odd-centralizer calculation and the orbit congruence modulo three
contradict 512 ≡ 2 (mod 3).

Only full semilinear coverage and faithfulness of the field parameter are
left explicit as universal automorphism inputs. The linear centralizer
bound, the exact Sylow order, and the obstruction to permutability are proved.
The caller must place its actual outside cubic in the diagonal image; this
module does not claim that every outside cubic is diagonal.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.8.20,
printed p.955; A.3.18(2), pp.51–52. The projective clause (2) must be used
here, separately from the special-unitary clause (3b).
-/

public section
open BenderSuzuki.MatrixGroups Matrix Subgroup
open scoped Pointwise
namespace BenderSuzuki.MatrixGroups.HermitianForm.UnitaryEight
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)

/-- The actual Sylow two-order, with fixed-field order eight and matrix-field
order sixty-four. No simplicity assumption is needed. -/
theorem sylow_card
    (hJ : J.form = !![0,0,1; 0,1,0; 1,0,0])
    (hcard : Nat.card E = 64) (hfixed : Nat.card {z : E // J.conj z = z} = 8)
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) : Nat.card S = 512 := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  obtain ⟨_, _, _, _, _, _, _, _, horder, _⟩ :=
    BenderSuzuki.External.huppert_II_10_12 J 8 (by simpa using hcard) hfixed hJ
  rw [S.card_eq_multiplicity, horder]
  decide +kernel

/-- An actual faithful action of an overgroup with a PSU₃(8) component cannot
have an outside diagonal cubic permuting with its specified Sylow arrangement. -/
theorem external_diagonal_cubic_not_permuting
    (hJ : J.form = !![0,0,1; 0,1,0; 1,0,0])
    (hcard : Nat.card E = 64) (hfixed : Nat.card {z : E // J.conj z = z} = 8)
    (hcoverage : ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
      ∃ σ : E ≃+* E, J.HasUnitarySemilinearForm a σ)
    (hfaithful : ∀ σ : E ≃+* E, J.HasUnitarySemilinearForm 1 σ → σ = 1)
    {G : Type*} [Group G] [Finite G]
    (K T : Subgroup G) [K.Normal] (e : K ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (S : Sylow 2 K) (hS : (S : Subgroup K).map K.subtype = T ⊓ K)
    (hT : IsPGroup 2 T)
    (f : G →* MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (hf : Function.Injective f)
    (x : G) (hx : orderOf x = 3) (hxK : x ∉ K)
    (hdiag : f x ∈ J.unitaryConjHom.range)
    (houter : f x ∉ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ((zpowers x ⊔ T : Subgroup G) : Set G) ≠ (zpowers x : Set G) * T := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let : Finite (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    Finite.of_injective
      (fun a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J) =>
        (a : ProjectiveSpecialUnitaryMatrixGroup J → ProjectiveSpecialUnitaryMatrixGroup J))
      DFunLike.coe_injective
  have hx' : orderOf (f x) = 3 := (orderOf_injective f hf x).trans hx
  have hodd := odd_centralizer_of_matrix_bound J hJ hcard hfixed hcoverage hfaithful
    (linearCentralizerBound J hcard hfixed) (f x) hdiag hx' houter
  let R := (T ⊓ K).map f
  have hR : IsPGroup 2 R := (hT.of_injective
    (inclusion (show T ⊓ K ≤ T from inf_le_left))
    (inclusion_injective _)).map f
  have hScard : Nat.card S = 512 := by
    let P := S.mapSurjective (f := e.toMonoidHom) e.surjective
    have hc := sylow_card J hJ hcard hfixed P
    change Nat.card ((S : Subgroup K).map e.toMonoidHom) = 512 at hc
    rwa [card_map_of_injective e.injective] at hc
  have hRcard : Nat.card R = 512 := by
    change Nat.card ((T ⊓ K).map f) = 512
    rw [card_map_of_injective hf, ← hS, card_map_of_injective K.subtype_injective]
    exact hScard
  intro hprod
  have hn := external_cubic_normalizes_intersection K T hT x hx hxK hprod
  have hn' : f x ∈ normalizer (R : Set (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))) :=
    (T ⊓ K).le_normalizer_map f (mem_map_of_mem f hn)
  exact not_normalizes_two_subgroup_of_odd_centralizer R hR (f x) hx' hodd
    (by rw [hRcard]; decide) hn'

end BenderSuzuki.MatrixGroups.HermitianForm.UnitaryEight

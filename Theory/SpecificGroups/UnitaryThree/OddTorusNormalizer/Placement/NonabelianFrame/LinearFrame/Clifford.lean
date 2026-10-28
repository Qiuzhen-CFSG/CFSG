module

public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.NonabelianFrame.Basic
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.NonabelianFrame.SingerExclusion
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.NonabelianFrame.LinearFrame.Irreducible
public import Theory.SpecificGroups.SL3.SplitMonomial.AbelianBasis.Clifford

/-!
# From a normal abelian restriction to an invariant unitary linear frame

Irreducibility of the odd nonabelian subgroup passes to its join with the
given involution. Singer exclusion makes every abelian normal restriction
reducible. If that restriction is nonscalar, the degree-three Clifford
argument gives three distinct lines over E permuted by the whole join.
The basis matrix below turns these spans into the literal projective column
lines used by `PreservesLines`, retaining the original involution.

Source: GLS4, Chapter 4, Lemma 3.11(a),
`refs/KGroup/GLS4/Chapter4.tex`, lines 585–603; Isaacs, Theorem 6.5.
This proves the abelian normal branch, not existence of such a subgroup.
-/

public section
open Matrix BenderSuzuki.MatrixGroups Representation
open scoped Pointwise LinearAlgebra.Projectivization
namespace UnitaryThree.OddTorusNormalizer.NonabelianFrame
variable {E : Type*} [Field E]

/-- The matrix carrying coordinate vectors to the chosen basis vectors. -/
@[expose] noncomputable def basisMatrix (b : Module.Basis (Fin 3) E (Fin 3 → E)) : GL (Fin 3) E :=
  GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv b.equivFun.symm)

/-- The change of basis acts by the inverse coordinate equivalence. -/
theorem basisMatrix_smul (b : Module.Basis (Fin 3) E (Fin 3 → E)) (v : Fin 3 → E) :
    basisMatrix b • v = b.equivFun.symm v := by
  have h := GeneralLinearGroup.toLin.apply_symm_apply
    (LinearMap.GeneralLinearGroup.ofLinearEquiv b.equivFun.symm)
  exact congrArg (fun u : LinearMap.GeneralLinearGroup E (Fin 3 → E) => u.val v) h

/-- The columns of the change of basis give the actual projective basis lines. -/
theorem basisMatrix_coordinateLine (b : Module.Basis (Fin 3) E (Fin 3 → E)) (i : Fin 3) :
    basisMatrix b • coordinateLine (E := E) i =
      Projectivization.mk E (b i) (b.ne_zero i) := by
  rw [coordinateLine, Projectivization.smul_mk]
  have h : basisMatrix b • Pi.single i (1 : E) = b i := by
    rw [basisMatrix_smul]
    apply b.equivFun.injective
    ext j
    simp [Module.Basis.equivFun_self, Pi.single_apply, eq_comm]
  apply Projectivization.submodule_injective
  simp only [Projectivization.submodule_mk, h]

/-- Permutation of basis spans gives literal setwise preservation of the
projective column lines. -/
theorem preservesLines_of_permuted_basis
    (J : HermitianForm 3 E) (K : Subgroup J.specialSubgroup)
    (b : Module.Basis (Fin 3) E (Fin 3 → E))
    (hb : ∀ g : K, ∀ i : Fin 3, ∃ j,
      (Submodule.span E {b i}).map (naturalRepresentation J g.val) =
        Submodule.span E {b j}) :
    PreservesLines J K (basisMatrix b) := by
  have hm (g : K) :
      g.val.val • (basisMatrix b • Set.range (coordinateLine (E := E))) ⊆
        basisMatrix b • Set.range (coordinateLine (E := E)) := by
    rintro _ ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, rfl⟩
    obtain ⟨j, hj⟩ := hb g i
    refine ⟨coordinateLine j, Set.mem_range_self j, ?_⟩
    change basisMatrix b • coordinateLine j =
      g.val.val • (basisMatrix b • coordinateLine i)
    rw [basisMatrix_coordinateLine, basisMatrix_coordinateLine, Projectivization.smul_mk]
    apply Projectivization.submodule_injective
    simp only [Projectivization.submodule_mk]
    rw [Submodule.map_span, Set.image_singleton] at hj
    exact hj.symm
  intro g hg
  apply Set.Subset.antisymm (hm ⟨g, hg⟩)
  rw [Set.subset_smul_set_iff]
  exact hm ⟨g⁻¹, K.inv_mem hg⟩

/-- A nonscalar abelian subgroup normal in the actual join supplies an invariant
linear frame. Singer exclusion and Clifford theory are applied over E. The
existence of the abelian normal subgroup remains an explicit premise. -/
theorem exists_preserved_linear_frame_of_abelian_normal [Finite E]
    (J : HermitianForm 3 E) (n : ℕ) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (H : Subgroup J.specialSubgroup) (hodd : Odd (Nat.card H))
    (hna : ¬ IsMulCommutative H) (t : J.specialSubgroup) (ht : orderOf t = 2)
    (A : Subgroup J.specialSubgroup) (hA : A ≤ H ⊔ Subgroup.zpowers t)
    (hAn : (A.subgroupOf (H ⊔ Subgroup.zpowers t)).Normal)
    (hAc : IsMulCommutative A)
    (hAs : ¬ ∀ a : A, ∃ c : E, naturalRepresentation J a.val = c • LinearMap.id) :
    ∃ C : GL (Fin 3) E, PreservesLines J (H ⊔ Subgroup.zpowers t) C := by
  let : CharP E 2 := charTwo_of_card n hcard
  let : IsMulCommutative A := hAc
  let K := H ⊔ Subgroup.zpowers t
  let ρ := (naturalRepresentation J).comp K.subtype
  let N := A.subgroupOf K
  let : N.Normal := hAn
  have hi : IsIrreducible ρ :=
    natural_isIrreducible_of_odd_nonabelian_le J H K hodd hna le_sup_left
  have hred : ¬ IsIrreducible (ρ.comp N.subtype) := by
    intro hirr
    have hiA : IsIrreducible ((naturalRepresentation J).comp A.subtype) :=
      (RepEquiv.irreducible_iff_group_iso
      (Subgroup.subgroupOfEquivOfLe hA) (fun _ _ => rfl)).mp hirr
    exact not_irreducible_abelian_normal_in_join J H A t ht hA hAn hiA
  have hscalar : ¬ ∀ a : N, ∃ c : E, ρ a.val = c • LinearMap.id := by
    intro hs
    apply hAs
    intro a
    exact hs ⟨⟨a.val, hA a.property⟩, a.property⟩
  obtain ⟨b, hb⟩ :=
    Matrix.SL3.SplitMonomial.AbelianBasis.exists_permuted_basis_of_reducible_normal
      ρ N hi (by simp) hred hscalar
  exact ⟨basisMatrix b, preservesLines_of_permuted_basis J K b hb⟩
end UnitaryThree.OddTorusNormalizer.NonabelianFrame

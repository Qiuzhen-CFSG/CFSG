module

public import Theory.Representation.AbelianAllWeights
public import Theory.Representation.AffineNine.BinaryWeights
public import Theory.Representation.AffineNine.Orbit
public import Theory.Representation.BinaryOffender.CubicRatio
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The strict binary cubic-ratio bound for the affine-nine groups

Every faithful finite-dimensional binary representation of the actual natural
semidirect products E₉ ⋊ SL₂(3) and E₉ ⋊ GL₂(3) has cubic ratio strictly above
two. Extend scalars to the algebraic closure of F₂. The eight nonzero translation
weights have a common positive dimension m, while the zero weight has dimension
d₀. An elementary two-subgroup projects injectively to GL₂(3), preserving rank,
and its dual-weight orbit cover S satisfies |S| + 2 rank(A) < 9.

An invariant vector is determined by its coordinates at orbit representatives,
so the fixed dimension is at most d₀ + (|S| - 1)m, against total dimension
d₀ + 8m. This proves fixed codimension greater than twice the rank for every
nontrivial elementary actor. The coordinate injection uses permuted subspaces;
it requires neither a permuted basis nor an irreducible constituent.

Source: Aschbacher--Smith, Lemma 15.4.10, printed p.1159. This direct proof
replaces the source's intermediate assertion of an eight-dimensional constituent.
-/

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

public section

namespace Representation.AffineNine

variable {E G V I : Type*} [Field E] [Group G]
  [AddCommGroup V] [Module E V] [Fintype I]

noncomputable def sumEquiv (U : I → Submodule E V)
    (hi : iSupIndep U) (ht : iSup U = ⊤) : (∀ i, U i) ≃ₗ[E] V := by
  classical
  exact (DirectSum.linearEquivFunOnFintype E I (fun i => U i)).symm.trans
    (hi.linearEquiv ht)

theorem sumEquiv_apply (U : I → Submodule E V)
    (hi : iSupIndep U) (ht : iSup U = ⊤) (v : ∀ i, U i) :
    sumEquiv U hi ht v = ∑ i, (v i : V) := by
  classical
  simp only [sumEquiv, LinearEquiv.trans_apply]
  exact (iSupIndep.linearEquiv_apply hi ht _).trans (by
    rw [DFinsupp.sumAddHom_apply]
    exact DFinsupp.sum_eq_sum_fintype
      ((DirectSum.linearEquivFunOnFintype E I (fun i => U i)).symm v)
      (f := fun i => (U i).subtype.toAddMonoidHom) (fun i => map_zero _))

theorem coordinate_transport (rho : Representation E G V)
    (U : I → Submodule E V) (hi : iSupIndep U) (ht : iSup U = ⊤)
    (p : G → Equiv.Perm I)
    (hm : ∀ g i v, v ∈ U i → rho g v ∈ U (p g i)) (g : G) (v : V) (i : I) :
    (((sumEquiv U hi ht).symm (rho g v)) (p g i) : V) =
      rho g (((sumEquiv U hi ht).symm v) i : V) := by
  classical
  let c := (sumEquiv U hi ht).symm
  let w : ∀ j, U j := fun j => ⟨rho g (c v ((p g).symm j)), by
    simpa using hm g ((p g).symm j) (c v ((p g).symm j)) (c v ((p g).symm j)).property⟩
  have hw : sumEquiv U hi ht w = rho g v := by
    rw [sumEquiv_apply]
    change (∑ j, rho g (c v ((p g).symm j))) = rho g v
    rw [(p g).symm.sum_comp (fun j => rho g (c v j : V)),
      ← map_sum, ← sumEquiv_apply U hi ht]
    simp [c]
  have he : c (rho g v) = w := (LinearEquiv.symm_apply_eq (sumEquiv U hi ht)).mpr hw.symm
  have hei := congrArg (fun z : ∀ j, U j => (z (p g i) : V)) he
  exact hei.trans (congrArg (fun j => rho g (c v j : V)) ((p g).symm_apply_apply i))

theorem finrank_invariants_le_representatives [FiniteDimensional E V]
    (rho : Representation E G V)
    (U : I → Submodule E V) (hi : iSupIndep U) (ht : iSup U = ⊤)
    (p : G → Equiv.Perm I)
    (hm : ∀ g i v, v ∈ U i → rho g v ∈ U (p g i))
    (S : Finset I) (hS : ∀ i, ∃ r ∈ S, ∃ g, p g r = i) :
    Module.finrank E rho.invariants ≤ ∑ r : S, Module.finrank E (U r.val) := by
  classical
  let c := (sumEquiv U hi ht).symm
  let f : rho.invariants →ₗ[E] (∀ r : S, U r.val) :=
    LinearMap.pi fun r => ((LinearMap.proj r.val).comp c.toLinearMap).comp rho.invariants.subtype
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply c.injective
    funext i
    obtain ⟨r, hr, g, hgr⟩ := hS i
    have he : (c x r : V) = (c y r : V) :=
      congrArg (fun z : ∀ r : S, U r.val => (z ⟨r, hr⟩ : V)) hxy
    apply Subtype.ext
    have hx := coordinate_transport rho U hi ht p hm g x r
    have hy := coordinate_transport rho U hi ht p hm g y r
    rw [(mem_invariants rho x).mp x.property g, hgr] at hx
    rw [(mem_invariants rho y).mp y.property g, hgr] at hy
    exact hx.trans ((congrArg (rho g) he).trans hy.symm)
  simpa only [Module.finrank_pi_fintype] using LinearMap.finrank_le_finrank_of_injective hf


theorem finrank_eq_sum [FiniteDimensional E V]
    (U : I → Submodule E V) (hi : iSupIndep U) (ht : iSup U = ⊤) :
    Module.finrank E V = ∑ i, Module.finrank E (U i) := by
  rw [← (sumEquiv U hi ht).finrank_eq, Module.finrank_pi_fintype]


end Representation.AffineNine

open scoped TensorProduct ENNReal

namespace Representation.AffineNine
open BinaryOffender

private theorem sum_plane_weights (d : Plane → ℕ) (m : ℕ)
    (hd : ∀ w, w ≠ 0 → d w = m) (S : Finset Plane) (h0 : 0 ∈ S) :
    ∑ w ∈ S, d w = d 0 + (S.card - 1) * m := by
  classical
  have hs : ∑ w ∈ S.erase 0, d w = (S.erase 0).card * m := by
    calc
      _ = ∑ _w ∈ S.erase 0, m := Finset.sum_congr rfl (fun w hw => hd w (Finset.mem_erase.mp hw).1)
      _ = _ := by simp
  have he := Finset.sum_erase_add S d h0
  rw [hs, Finset.card_erase_of_mem h0] at he
  omega

variable {L V : Type*} [Group L] [Finite L] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- Uniform positive nonzero weights and the actual dual orbit geometry force
strict fixed codimension. The zero weight is retained and cancels in the
comparison after descending invariant dimensions to the binary field. -/
theorem strict_fixedCodim_of_geometry (j : L →* LinearGroup)
    (hj : Function.Injective j) (rho : Representation (ZMod 2) (Affine j) V)
    (u : UniformWeights j (rho.extendScalars algebraicClosureE9))
    (A : Subgroup (Affine j)) (hA : IsElementaryTwo A) :
    2 * rank A < fixedCodim rho A := by
  classical
  let : IsElementaryAbelian 2 A := hA.2
  let σ := rho.extendScalars algebraicClosureE9
  let U := planeWeightSpace j σ
  let d := fun w => Module.finrank algebraicClosureE9 (U w)
  let m := u.nontrivialDim
  have hm : 0 < m := u.positive
  have hd : ∀ w, w ≠ 0 → d w = m := planeWeightSpace_finrank_nonzero j σ u
  let B := A.map (linearPart j)
  obtain ⟨S, h0, hcover, _, _, hcard⟩ :=
    exists_dual_orbit_cover_strict B (elementary_linearPart j hj hA)
  have hrank : rank B = rank A := rank_linearPart j hj A
  rw [hrank] at hcard
  let p : A → Equiv.Perm Plane := fun a => dualPerm (linearPart j a)
  have hS : ∀ w, ∃ r ∈ S, ∃ a : A, p a r = w := by
    intro w
    obtain ⟨b, hb⟩ := hcover w
    obtain ⟨a, ha, hab⟩ := Subgroup.mem_map.mp b.property
    refine ⟨dualPerm b w, hb, ⟨a⁻¹, A.inv_mem ha⟩, ?_⟩
    change dualPerm (linearPart j a⁻¹) (dualPerm b w) = w
    rw [map_inv, hab]
    simp only [dualPerm_apply, inv_inv]
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul]
    simp
  have hfixed := finrank_invariants_le_representatives (σ.comp A.subtype) U
    (planeWeightSpace_independent j σ) (iSup_planeWeightSpace_eq_top j σ) p
    (fun a w v hv => mem_planeWeightSpace_apply j σ a w v hv) S hS
  have hfixed' : Module.finrank algebraicClosureE9 (Representation.invariants (σ.comp A.subtype)) ≤
      d 0 + (S.card - 1) * m := by
    calc
      _ ≤ ∑ r : S, d r := hfixed
      _ = ∑ r ∈ S, d r := Finset.sum_coe_sort S d
      _ = _ := sum_plane_weights d m hd S h0
  have htotal : Module.finrank algebraicClosureE9 (algebraicClosureE9 ⊗[ZMod 2] V) =
      d 0 + 8 * m := by
    have ht := finrank_eq_sum U (planeWeightSpace_independent j σ)
      (iSup_planeWeightSpace_eq_top j σ)
    rw [sum_plane_weights d m hd Finset.univ (Finset.mem_univ _)] at ht
    simpa only [Finset.card_univ, card_plane] using ht
  have hbase : Module.finrank algebraicClosureE9 (Representation.invariants (σ.comp A.subtype)) =
      Module.finrank (ZMod 2) (fixedSpace rho A) :=
    finrank_invariants_extendScalars_eq_of_finite (rho.comp A.subtype)
  have htotalbase : Module.finrank algebraicClosureE9 (algebraicClosureE9 ⊗[ZMod 2] V) =
      Module.finrank (ZMod 2) V := Module.finrank_baseChange
  rw [hbase] at hfixed'
  rw [htotalbase] at htotal
  have hdim := fixedCodim_add_finrank rho A
  have hSpos : 0 < S.card := Finset.card_pos.mpr ⟨0, h0⟩
  have hn : (S.card - 1) + 2 * rank A < 8 := by omega
  have hmul := Nat.mul_le_mul_right m (show (S.card - 1) + 2 * rank A + 1 ≤ 8 by omega)
  have hrankmul : 2 * rank A ≤ 2 * rank A * m := Nat.le_mul_of_pos_right _ hm
  nlinarith

/-- Every faithful binary representation of the full natural affine group has
strict fixed codimension for every nontrivial elementary two-subgroup. -/
theorem full_strict_fixedCodim
    (rho : Representation (ZMod 2) Full V) (hfaith : Function.Injective rho)
    (A : Subgroup Full) (hA : IsElementaryTwo A) :
    2 * rank A < fixedCodim rho A :=
  strict_fixedCodim_of_geometry (MonoidHom.id LinearGroup) Function.injective_id
    rho (full_binary_uniformWeights rho hfaith) A hA

/-- The same bound for the determinant-one natural affine group. -/
theorem special_strict_fixedCodim
    (rho : Representation (ZMod 2) Special V) (hfaith : Function.Injective rho)
    (A : Subgroup Special) (hA : IsElementaryTwo A) :
    2 * rank A < fixedCodim rho A :=
  strict_fixedCodim_of_geometry Matrix.SpecialLinearGroup.toGL
    Matrix.SpecialLinearGroup.toGL_injective rho
    (special_binary_uniformWeights rho hfaith) A hA

/-- The strict cubic-ratio estimate for the full affine-nine model. -/
theorem full_cubicRatio_not_le_two
    (rho : Representation (ZMod 2) Full V) (hfaith : Function.Injective rho) :
    ¬ cubicRatio rho ≤ 2 := by
  intro h
  obtain ⟨A, hA, _, hcodim⟩ := (cubicRatio_le_nat_iff rho 2).mp h
  exact (Nat.not_le_of_lt (full_strict_fixedCodim rho hfaith A hA)) hcodim

/-- The strict cubic-ratio estimate for the special affine-nine model. -/
theorem special_cubicRatio_not_le_two
    (rho : Representation (ZMod 2) Special V) (hfaith : Function.Injective rho) :
    ¬ cubicRatio rho ≤ 2 := by
  intro h
  obtain ⟨A, hA, _, hcodim⟩ := (cubicRatio_le_nat_iff rho 2).mp h
  exact (Nat.not_le_of_lt (special_strict_fixedCodim rho hfaith A hA)) hcodim

end Representation.AffineNine

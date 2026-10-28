module

public import Theory.SpecificGroups.OrthogonalFourBinary.NaturalAction
public import Mathlib.GroupTheory.Sylow

/-!
# Stabilizers of singular vectors in the binary orthogonal four-space

The stabilizer of a nonzero singular vector has order eight. The common
stabilizer of two distinct such vectors has order at most two. At the vector
`((1,1),(1,1))`, all eight isometries are obtained by interchanging the two
coordinates in either definite plane and interchanging the planes. A kernel
checked calculation on the images of the four basis vectors proves that this
list is exhaustive; another counts its elements fixing a second singular
vector. Singular-vector transitivity transports the counts to any vector.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the orthogonal
space on printed pp.1121–1122; used in the Sylow argument on p.1154.
-/

@[expose] public section

set_option synthInstance.maxSize 10000

open Subgroup Theory.AlgebraicGroup

namespace OrthogonalFourBinary.IndexTwoNormalizer
public abbrev IsometryGroup := quadraticIsometrySubgroup (k := F) (V := Space) form

public instance finiteIsometryGroup : Finite IsometryGroup := Finite.of_injective (fun g : IsometryGroup => (g.val : Space → Space))
  (fun _ _ hgh => Subtype.ext (LinearEquiv.ext (fun w => congrFun hgh w)))

private def planeFlip : Plane ≃ₗ[F] Plane := LinearEquiv.prodComm F F F
private def swap : Space ≃ₗ[F] Space := LinearEquiv.prodComm F Plane Plane
private abbrev Code := Fin 2 × Fin 2 × Fin 2
private def candidate (i : Code) : Space ≃ₗ[F] Space :=
  ((planeFlip ^ (i.1 : ℕ)).prodCongr (planeFlip ^ (i.2.1 : ℕ))) * swap ^ (i.2.2 : ℕ)
private def v : Space := ((1,1),(1,1))
private def basis0 : Space := ((1,0),(0,0))
private def basis1 : Space := ((0,1),(0,0))
private def basis2 : Space := ((0,0),(1,0))
private def basis3 : Space := ((0,0),(0,1))

private theorem candidate_fix : ∀ i : Code, candidate i v = v := by decide +kernel
private theorem candidate_form : ∀ i : Code, ∀ w : Space, form (candidate i w) = form w := by decide +kernel
private theorem candidate_inj : ∀ i j : Code,
    (candidate i basis0, candidate i basis1, candidate i basis2, candidate i basis3) =
    (candidate j basis0, candidate j basis1, candidate j basis2, candidate j basis3) → i = j := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem exhaustive : ∀ a b c d : Space,
    form a = 1 ∧ form b = 1 ∧ form c = 1 ∧ form d = 1 ∧
    form (a+b) = 1 ∧ form (c+d) = 1 ∧
    form (a+c) = 0 ∧ form (a+d) = 0 ∧ form (b+c) = 0 ∧ form (b+d) = 0 ∧
    a+b+c+d = v → ∃ i : Code,
      a = candidate i basis0 ∧ b = candidate i basis1 ∧
      c = candidate i basis2 ∧ d = candidate i basis3 := by decide +kernel

private theorem space_expand (w : Space) :
    w = w.1.1 • basis0 + w.1.2 • basis1 + w.2.1 • basis2 + w.2.2 • basis3 := by
  have h : ∀ w : Space,
      w = w.1.1 • basis0 + w.1.2 • basis1 + w.2.1 • basis2 + w.2.2 • basis3 := by
    decide +kernel
  exact h w

private theorem basis_ext (e f : Space ≃ₗ[F] Space)
    (h0 : e basis0 = f basis0) (h1 : e basis1 = f basis1)
    (h2 : e basis2 = f basis2) (h3 : e basis3 = f basis3) : e = f := by
  apply LinearEquiv.ext
  intro w
  rw [space_expand w]
  simp only [map_add, map_smul, h0, h1, h2, h3]

private def codeMap (i : Code) : MulAction.stabilizer IsometryGroup v :=
  ⟨⟨candidate i, (mem_quadraticIsometrySubgroup form _).mpr (candidate_form i)⟩,
    candidate_fix i⟩

private theorem codeMap_bijective : Function.Bijective codeMap := by
  constructor
  · intro i j h
    apply candidate_inj i j
    have he : candidate i = candidate j := congrArg (fun g => g.val.val) h
    rw [he]
  · intro e
    have hq := (mem_quadraticIsometrySubgroup form _).mp e.val.property
    have hv : e.val.val v = v := e.property
    obtain ⟨i, h0, h1, h2, h3⟩ := exhaustive
      (e.val.val basis0) (e.val.val basis1) (e.val.val basis2) (e.val.val basis3) (by
        simp only [← map_add, hq]
        refine ⟨by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, ?_⟩
        have he : basis0 + basis1 + basis2 + basis3 = v := by decide +kernel
        rw [he, hv])
    refine ⟨i, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact (basis_ext _ _ h0 h1 h2 h3).symm

private noncomputable def codeEquiv : Code ≃ MulAction.stabilizer IsometryGroup v :=
  Equiv.ofBijective codeMap codeMap_bijective

private theorem stabilizer_card : Nat.card (MulAction.stabilizer IsometryGroup v) = 8 := by
  rw [← Nat.card_congr codeEquiv]
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem fixed_codes_card : ∀ w : Space, w ≠ 0 → form w = 0 → w ≠ v →
    Fintype.card {i : Code // candidate i w = w} = 2 := by decide +kernel

private theorem two_stabilizer_card (w : Space) (hw : w ≠ 0) (hqw : form w = 0) (hvw : w ≠ v) :
    Nat.card (MulAction.stabilizer IsometryGroup v ⊓ MulAction.stabilizer IsometryGroup w : Subgroup IsometryGroup) ≤ 2 := by
  let f : (MulAction.stabilizer IsometryGroup v ⊓ MulAction.stabilizer IsometryGroup w : Subgroup IsometryGroup) →
      {i : Code // candidate i w = w} := fun g =>
    ⟨codeEquiv.symm ⟨g.val,g.property.1⟩, by
      have he := codeEquiv.apply_symm_apply ⟨g.val,g.property.1⟩
      have hh := congrArg (fun k : MulAction.stabilizer IsometryGroup v => k.val.val w) he
      exact hh.trans g.property.2⟩
  have hf : Function.Injective f := by
    intro g h hh
    have hh' : codeEquiv.symm ⟨g.val,g.property.1⟩ =
        codeEquiv.symm ⟨h.val,h.property.1⟩ := congrArg
      (fun i : {i : Code // candidate i w = w} => i.val) hh
    have he := codeEquiv.symm.injective hh'
    exact Subtype.ext (congrArg (fun k : MulAction.stabilizer IsometryGroup v => k.val) he)
  have hc := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card (α := {i : Code // candidate i w = w}),
    fixed_codes_card w hw hqw hvw] at hc
  exact hc


private theorem exists_to_standard (x : Space) (hx : x ≠ 0) (hqx : form x = 0) :
    ∃ e : IsometryGroup, e • x = v := by
  obtain ⟨e, he⟩ := exists_isometry_of_singular x v hx
    (by decide +kernel) hqx (by decide +kernel)
  exact ⟨⟨e.toLinearEquiv,(mem_quadraticIsometrySubgroup form _).mpr e.map_app'⟩,he⟩

public theorem singular_stabilizer_card (x : Space) (hx : x ≠ 0) (hqx : form x = 0) :
    Nat.card (MulAction.stabilizer IsometryGroup x) = 8 := by
  obtain ⟨e,he⟩ := exists_to_standard x hx hqx
  exact (Nat.card_congr (MulAction.stabilizerEquivStabilizer he.symm).toEquiv).trans
    stabilizer_card

public theorem two_singular_stabilizer_card (x y : Space)
    (hx : x ≠ 0) (hqx : form x = 0) (hy : y ≠ 0) (hqy : form y = 0) (hxy : y ≠ x) :
    Nat.card (MulAction.stabilizer IsometryGroup x ⊓ MulAction.stabilizer IsometryGroup y : Subgroup IsometryGroup) ≤ 2 := by
  obtain ⟨e,he⟩ := exists_to_standard x hx hqx
  have heq : (MulAction.stabilizer IsometryGroup x ⊓ MulAction.stabilizer IsometryGroup y : Subgroup IsometryGroup).map
      (MulAut.conj e).toMonoidHom =
      MulAction.stabilizer IsometryGroup v ⊓ MulAction.stabilizer IsometryGroup (e • y) := by
    rw [map_inf _ _ _ (MulAut.conj e).injective,
      ← MulAction.stabilizer_smul_eq_stabilizer_map_conj,
      ← MulAction.stabilizer_smul_eq_stabilizer_map_conj, he]
  rw [← card_map_of_injective (K := MulAction.stabilizer IsometryGroup x ⊓ MulAction.stabilizer IsometryGroup y)
    (f := (MulAut.conj e).toMonoidHom) (MulAut.conj e).injective, heq]
  apply two_stabilizer_card
  · change e.val y ≠ 0
    intro h
    exact hy (e.val.injective (h.trans (map_zero e.val).symm))
  · exact ((mem_quadraticIsometrySubgroup form _).mp e.property y).trans hqy
  · rw [← he]
    exact fun h => hxy (e.val.injective h)

end OrthogonalFourBinary.IndexTwoNormalizer

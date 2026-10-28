module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.AsymmetricPair.CoverSymplecticGeometry.Form
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.AsymmetricPair.Actions

/-!
# Transport of the actual natural action and its displacement

The natural action is recorded by a multiplicative equivalence from the
ambient subgroup and a permutation action compatible with actual conjugation.
The coordinate pairing is proved alternating, nondegenerate, additive in each
argument and invariant under that conjugation. Every subgroup marking and the
whole action are transported by the explicit inverse-conjugation equivalence.

The earlier T-invariant rank-one and rank-three flag, with actual Borel lifts,
then gives the perpendicular marking. A commutator bound gives a coordinate
displacement bound. If all displacement were in the marked line, preservation
of the alternating form would force the orthogonal hyperplane to be fixed,
contrary to the noncommuting seed. Thus the full displacement is strictly larger.

Source: Aschbacher–Smith, Notation 13.2.1, Remark 13.5.3 and the geometric
paragraph of 13.8.7, printed p.949. The final assembly in the parent module
constructs the seed and discharges the marking and placement premises here.
-/

@[expose] public section
open Subgroup
open BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair.CoverGeometry
variable {G : Type*} [Group G]
abbrev N := natural (Fin 6)

/-- The literal image of an ambient subgroup in natural-module coordinates. -/
noncomputable def subspace {V : Subgroup G} (e : V ≃* Multiplicative N)
    (X : Subgroup G) : Submodule (ZMod 2) N :=
  AddSubgroup.toZModSubmodule 2 (((X.subgroupOf V).map e.toMonoidHom).toAddSubgroup)

theorem mem_subspace {V : Subgroup G} (e : V ≃* Multiplicative N)
    (X : Subgroup G) (x : N) :
    x ∈ subspace e X ↔ (e.symm (Multiplicative.ofAdd x) : G) ∈ X := by
  change Multiplicative.ofAdd x ∈ (X.subgroupOf V).map e.toMonoidHom ↔ _
  rw [mem_map_equiv]
  rfl

theorem coordinate_mem_subspace {V : Subgroup G} (e : V ≃* Multiplicative N)
    (X : Subgroup G) (x : V) : (e x).toAdd ∈ subspace e X ↔ (x : G) ∈ X := by
  rw [mem_subspace]
  change (e.symm (e x) : G) ∈ X ↔ (x : G) ∈ X
  rw [e.symm_apply_apply]

/-- The exact earlier natural action, with its actual conjugation compatibility.
There is no invariant-form or orthogonal-marking field. -/
structure NaturalAction (M V : Subgroup G) where
  normalizes : M ≤ normalizer V
  perm : M →* Equiv.Perm (Fin 6)
  coordinate : V ≃* Multiplicative N
  equivariant : ∀ (m : M) (v : V),
    (coordinate ⟨(m : G) * v * (m : G)⁻¹,
      (mem_normalizer_iff.mp (normalizes m.property) v).mp v.property⟩).toAdd =
      naturalRepresentation (Fin 6) (perm m) (coordinate v).toAdd

/-- The invariant form evaluated on elements of the actual group carrier. -/
noncomputable def NaturalAction.coordinateForm {M V : Subgroup G}
    (a : NaturalAction M V) (v w : V) : ZMod 2 :=
  form (a.coordinate v).toAdd (a.coordinate w).toAdd

theorem NaturalAction.coordinateForm_mul_left {M V : Subgroup G}
    (a : NaturalAction M V) (u v w : V) :
    a.coordinateForm (u * v) w = a.coordinateForm u w + a.coordinateForm v w := by
  simp only [NaturalAction.coordinateForm, map_mul, toAdd_mul, map_add, LinearMap.add_apply]

theorem NaturalAction.coordinateForm_mul_right {M V : Subgroup G}
    (a : NaturalAction M V) (u v w : V) :
    a.coordinateForm u (v * w) = a.coordinateForm u v + a.coordinateForm u w := by
  simp only [NaturalAction.coordinateForm, map_mul, toAdd_mul, map_add]

theorem NaturalAction.coordinateForm_alternating {M V : Subgroup G}
    (a : NaturalAction M V) (v : V) : a.coordinateForm v v = 0 :=
  form_alt (a.coordinate v).toAdd

/-- Nondegeneracy on the genuine elementary abelian carrier, whose zero is 1. -/
theorem NaturalAction.coordinateForm_nondegenerate {M V : Subgroup G}
    (a : NaturalAction M V) (v : V)
    (hv : ∀ w, a.coordinateForm v w = 0) : v = 1 := by
  have hz : (a.coordinate v).toAdd = 0 := by
    apply form_nondegenerate.1
    intro y
    simpa [NaturalAction.coordinateForm] using
      hv (a.coordinate.symm (Multiplicative.ofAdd y))
  apply a.coordinate.injective
  rw [map_one]
  exact hz

/-- Form preservation is deduced from coordinate permutations and actual
conjugation compatibility, not postulated in the natural action. -/
theorem NaturalAction.coordinateForm_invariant {M V : Subgroup G}
    (a : NaturalAction M V) (m : M) (v w : V) :
    a.coordinateForm
      ⟨(m : G) * v * (m : G)⁻¹,
        (mem_normalizer_iff.mp (a.normalizes m.property) v).mp v.property⟩
      ⟨(m : G) * w * (m : G)⁻¹,
        (mem_normalizer_iff.mp (a.normalizes m.property) w).mp w.property⟩ =
      a.coordinateForm v w := by
  unfold NaturalAction.coordinateForm
  rw [a.equivariant, a.equivariant, form_invariant]

/-- A normalized subgroup acts in the asserted coordinates by genuine conjugation. -/
theorem NaturalAction.subspace_invariant {M V X : Subgroup G}
    (a : NaturalAction M V) (m : M) (hn : (m : G) ∈ normalizer X) :
    Submodule.map (naturalRepresentation (Fin 6) (a.perm m)) (subspace a.coordinate X) =
      subspace a.coordinate X := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨v, hv, rfl⟩
    let x : V := a.coordinate.symm (Multiplicative.ofAdd v)
    have hx : (x : G) ∈ X := (mem_subspace _ _ _).mp hv
    have he := a.equivariant m x
    have he' : (a.coordinate x).toAdd = v := by simp [x]
    rw [he'] at he
    rw [← he, coordinate_mem_subspace]
    exact (mem_normalizer_iff.mp hn (x : G)).mp hx
  · exact (LinearMap.GeneralLinearGroup.toLinearEquiv
      ((naturalRepresentation (Fin 6)).asGroupHom (a.perm m))).finrank_map_eq _

/-- Natural coordinates after conjugation are explicitly obtained by undoing g. -/
noncomputable def conjugateCoordinate {V : Subgroup G}
    (e : V ≃* Multiplicative N) (g : G) : V.conjBy g ≃* Multiplicative N :=
  ((MulAut.conj g).subgroupMap V).symm.trans e

theorem conjugateCoordinate_apply {V : Subgroup G}
    (e : V ≃* Multiplicative N) (g : G) (v : V) :
    conjugateCoordinate e g ((MulAut.conj g).subgroupMap V v) = e v := by
  change e (((MulAut.conj g).subgroupMap V).symm (((MulAut.conj g).subgroupMap V) v)) = e v
  rw [MulEquiv.symm_apply_apply]

/-- Every subgroup marking is transported by the same coordinate equivalence. -/
theorem subspace_conjugate {V : Subgroup G}
    (e : V ≃* Multiplicative N) (X : Subgroup G) (g : G) :
    subspace (conjugateCoordinate e g) (X.conjBy g) = subspace e X := by
  ext v
  rw [mem_subspace, mem_subspace]
  change (MulAut.conj g (e.symm (Multiplicative.ofAdd v)) : G) ∈ X.map _ ↔ _
  rw [mem_map_equiv]
  simp [mul_assoc]

/-- Conjugation transports the genuine action, as well as its carrier. -/
noncomputable def NaturalAction.conjugate {M V : Subgroup G}
    (a : NaturalAction M V) (g : G) : NaturalAction (M.conjBy g) (V.conjBy g) where
  normalizes := by
    have hi := map_mono (f := (MulAut.conj g).toMonoidHom) a.normalizes
    rw [map_equiv_normalizer_eq] at hi
    exact hi
  perm := a.perm.comp ((MulAut.conj g).subgroupMap M).symm.toMonoidHom
  coordinate := conjugateCoordinate a.coordinate g
  equivariant := by
    intro m v
    let m0 := ((MulAut.conj g).subgroupMap M).symm m
    let v0 := ((MulAut.conj g).subgroupMap V).symm v
    have he := a.equivariant m0 v0
    change (a.coordinate _).toAdd = naturalRepresentation (Fin 6) (a.perm m0)
      (a.coordinate v0).toAdd
    convert he using 2
    apply congrArg a.coordinate
    apply Subtype.ext
    change g⁻¹ * ((m : G) * (v : G) * (m : G)⁻¹) * g =
      (g⁻¹ * (m : G) * g) * (g⁻¹ * (v : G) * g) * (g⁻¹ * (m : G) * g)⁻¹
    group

/-- The invariant line and hyperplane of Notation 13.2.1, before any orthogonal
identification. The Borel is realized by actual elements of the marked T. -/
structure NaturalFlag {M V : Subgroup G} (a : NaturalAction M V)
    (T Z C : Subgroup G) : Prop where
  line_le : Z ≤ V
  hyperplane_le : C ≤ V
  line_rank : Module.finrank (ZMod 2) (subspace a.coordinate Z) = 1
  hyperplane_rank : Module.finrank (ZMod 2) (subspace a.coordinate C) = 3
  normalizes_line : T ≤ normalizer Z
  normalizes_hyperplane : T ≤ normalizer C
  borel_lifts : ∀ t ∈ T0, ∃ m : M, a.perm m = t ∧ (m : G) ∈ T

/-- The source flag's orthogonal marking is derived in the literal natural model. -/
theorem NaturalFlag.orthogonal {M V T Z C : Subgroup G}
    {a : NaturalAction M V} (f : NaturalFlag a T Z C) :
    subspace a.coordinate C = form.orthogonal (subspace a.coordinate Z) := by
  apply invariant_hyperplane_eq_orthogonal _ _ f.line_rank f.hyperplane_rank
  · intro t ht
    obtain ⟨m, rfl, hm⟩ := f.borel_lifts t ht
    exact a.subspace_invariant m (f.normalizes_line hm)
  · intro t ht
    obtain ⟨m, rfl, hm⟩ := f.borel_lifts t ht
    exact a.subspace_invariant m (f.normalizes_hyperplane hm)

/-- A commutator bound is exactly the corresponding coordinate-displacement bound. -/
theorem NaturalAction.displacement_mem {M W C A : Subgroup G}
    (a : NaturalAction M W) (hCM : C ≤ M) (hc : ⁅W, C⁆ ≤ A)
    (c : C) (v : N) :
    naturalRepresentation (Fin 6) (a.perm ⟨c, hCM c.property⟩) v - v ∈
      subspace a.coordinate A := by
  let w : W := a.coordinate.symm (Multiplicative.ofAdd v)
  let m : M := ⟨c, hCM c.property⟩
  let w' : W := ⟨(c : G) * w * (c : G)⁻¹,
    (mem_normalizer_iff.mp (a.normalizes m.property) w).mp w.property⟩
  have he : (a.coordinate w').toAdd =
      naturalRepresentation (Fin 6) (a.perm m) v := by
    simpa [w, w', m] using a.equivariant m w
  have hw : (a.coordinate w).toAdd = v := by simp [w]
  have hd : (a.coordinate (w' * w⁻¹)).toAdd =
      naturalRepresentation (Fin 6) (a.perm m) v - v := by
    rw [map_mul, map_inv]
    change (a.coordinate w').toAdd + -(a.coordinate w).toAdd = _
    rw [he, hw, sub_eq_add_neg]
  rw [← hd, coordinate_mem_subspace]
  apply hc
  rw [commutator_comm]
  exact commutator_mem_commutator c.property w.property

/-- The actual natural-module action cannot have only line displacement when it
moves the orthogonal hyperplane. No abstract symplectic-family label is used. -/
theorem strict_displacement {M W B C A : Subgroup G}
    (a : NaturalAction M W) (hCM : C ≤ M) (hBW : B ≤ W)
    (hline : Module.finrank (ZMod 2) (subspace a.coordinate A) = 1)
    (horth : subspace a.coordinate B = form.orthogonal (subspace a.coordinate A))
    (hn : ⁅B, C⁆ ≠ ⊥) (hc : ⁅B, C⁆ = A) : A < ⁅W, C⁆ := by
  refine lt_iff_le_not_ge.mpr ⟨?_, ?_⟩
  · rw [← hc]
    exact commutator_mono hBW le_rfl
  intro hle
  have hne : subspace a.coordinate A ≠ ⊥ := by
    intro hz
    rw [hz, finrank_bot] at hline
    exact Nat.zero_ne_one hline
  obtain ⟨z, hz, hz0⟩ := (Submodule.exists_mem_ne_zero_of_ne_bot hne)
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hline hz hz0
  have hnr : ∃ y, form z y ≠ 0 := by
    by_contra! hh
    exact hz0 (form_nondegenerate.1 z hh)
  apply hn
  rw [commutator_comm, commutator_eq_bot_iff_le_centralizer]
  intro c hcC
  apply mem_centralizer_iff.mpr
  intro b hb
  let m : M := ⟨c, hCM hcC⟩
  let w : W := ⟨b, hBW hb⟩
  let E := LinearMap.GeneralLinearGroup.toLinearEquiv
    ((naturalRepresentation (Fin 6)).asGroupHom (a.perm m))
  have hfix := fixes_orthogonal_of_displacement_line form form_alt z hnr E
    (fun x y => form_invariant (a.perm m) x y)
    (fun x => hspan ▸ a.displacement_mem hCM hle ⟨c, hcC⟩ x)
  have hw : (a.coordinate w).toAdd ∈ form.orthogonal (subspace a.coordinate A) := by
    rw [← horth, coordinate_mem_subspace]
    exact hb
  have heq := hfix (a.coordinate w).toAdd (hw z hz)
  have he := a.equivariant m w
  have hconj : c * b * c⁻¹ = b := by
    have hi : a.coordinate ⟨c * b * c⁻¹,
        (mem_normalizer_iff.mp (a.normalizes m.property) b).mp (hBW hb)⟩ =
        a.coordinate w := by
      exact he.trans heq
    exact congrArg Subtype.val (a.coordinate.injective hi)
  exact (mul_inv_eq_iff_eq_mul.mp hconj).symm

end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair.CoverGeometry
end

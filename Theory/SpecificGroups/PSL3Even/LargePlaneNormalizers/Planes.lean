module

public import Theory.SpecificGroups.PSL3Even.LargePlaneNormalizers.SquareCore

/-!
# Centralizers of large subgroups of a root plane in PSL₃

A subgroup of either coordinate plane with more than |F| elements contains both
a nonidentity central element and a noncentral element: project to the simple
root coordinate and compare cardinalities. The former places its centralizer
inside the highest-root centralizer. The latter kills the torus factor and
forces the remaining unitriangular element into the same plane. Thus the full
PSL₃ centralizer is exactly that plane.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
§5.3.5–7, printed p.660; the geometric input to E.1.14(1), p.214.
-/

@[expose] public section

open scoped MatrixGroups
open Subgroup Matrix.PSL3 Matrix.PSL3.LinearThree
open Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3Even.LargePlaneNormalizers
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

omit [CharP F 2] in
private theorem large_plane_witnesses (A : Subgroup (U F)) (b : Bool)
    (hA : A ≤ if b then V₁ F else V₂ F) (hc : Nat.card F < Nat.card A) :
    (∃ z ∈ A, z ∈ Z F ∧ z ≠ 1) ∧ (∃ u ∈ A, u ∉ Z F) := by
  have hn : ¬ A ≤ Z F := by
    intro h
    have hh := Subgroup.card_le_of_le h
    rw [card_Z] at hh
    exact (not_le_of_gt hc) hh
  refine ⟨?_, SetLike.not_le_iff_exists.mp hn⟩
  let coord : A → F := fun a => if b then a.val.x else a.val.y
  have hni : ¬ Function.Injective coord := fun hi =>
    (not_le_of_gt hc) (Nat.card_le_card_of_injective coord hi)
  obtain ⟨a,d,had,hne⟩ := Function.not_injective_iff.mp hni
  refine ⟨a.val * d.val⁻¹, A.mul_mem a.property (A.inv_mem d.property), ?_, ?_⟩
  · rw [mem_Z]
    have ha := hA a.property
    have hd := hA d.property
    cases b
    · have ha : a.val.x = 0 := (mem_V₂ F _).mp ha
      have hd : d.val.x = 0 := (mem_V₂ F _).mp hd
      have had : a.val.y = d.val.y := had
      change a.val.x + -d.val.x = 0 ∧ a.val.y + -d.val.y = 0
      simp [ha,hd,had]
    · have ha : a.val.y = 0 := (mem_V₁ F _).mp ha
      have hd : d.val.y = 0 := (mem_V₁ F _).mp hd
      have had : a.val.x = d.val.x := had
      change a.val.x + -d.val.x = 0 ∧ a.val.y + -d.val.y = 0
      simp [ha,hd,had]
  · intro h
    exact hne (Subtype.ext (mul_inv_eq_one.mp h))

omit [Finite F] [CharP F 2] in
private theorem torus_eq_one_of_commutes (a : Fˣ) (v u : U F)
    (hu : u ∉ Z F)
    (h : (EvenInnerCentralizers.torus F a * EvenInnerCentralizers.unipotentInCentralizer F v) *
        EvenInnerCentralizers.unipotentInCentralizer F u =
      EvenInnerCentralizers.unipotentInCentralizer F u *
        (EvenInnerCentralizers.torus F a * EvenInnerCentralizers.unipotentInCentralizer F v)) :
    EvenInnerCentralizers.torus F a = 1 := by
  let j := EvenInnerCentralizers.unipotentInCentralizer F
  have he : EvenInnerCentralizers.torus F a * j (v*u*v⁻¹) *
      (EvenInnerCentralizers.torus F a)⁻¹ = j u := by
    change EvenInnerCentralizers.torus F a *
      EvenInnerCentralizers.unipotentInCentralizer F (v*u*v⁻¹) * _ = _
    rw [map_mul, map_mul, map_inv]
    calc
      _ = (EvenInnerCentralizers.torus F a * j v) * j u *
          (EvenInnerCentralizers.torus F a * j v)⁻¹ := by dsimp [j]; group
      _ = j u := by rw [h, mul_inv_cancel_right]
  rw [EvenInnerCentralizers.torus_conjugate] at he
  have he := EvenInnerCentralizers.unipotentInCentralizer_injective F he
  have hx := congrArg U.x he
  have hy := congrArg U.y he
  have hx : (a : F)^3 * u.x = u.x := by
    simpa only [mul_x, show (v⁻¹).x = -v.x from rfl,
      add_comm v.x u.x, add_neg_cancel_right] using hx
  have hy : (↑a⁻¹ : F)^3 * u.y = u.y := by
    simpa only [mul_y, show (v⁻¹).y = -v.y from rfl,
      add_comm v.y u.y, add_neg_cancel_right] using hy
  by_cases hux : u.x = 0
  · have huy : u.y ≠ 0 := fun h => hu ((mem_Z F u).mpr ⟨hux,h⟩)
    have hi : a⁻¹ ^ 3 = 1 := Units.ext ((mul_eq_right₀ huy).mp hy)
    have ht : EvenInnerCentralizers.torus F a⁻¹ = 1 :=
      (EvenInnerCentralizers.torus_eq_one_iff F _).mpr hi
    simpa only [map_inv, inv_eq_one] using ht
  · exact (EvenInnerCentralizers.torus_eq_one_iff F a).mpr
      (Units.ext ((mul_eq_right₀ hux).mp hx))

/-- More than |F| elements in one coordinate plane determine its full PSL₃ centralizer. -/
theorem centralizer_large_plane (A : Subgroup (U F)) (b : Bool)
    (hA : A ≤ if b then V₁ F else V₂ F) (hc : Nat.card F < Nat.card A) :
    centralizer (A.map (projective F) : Set PSL(3,F)) =
      (if b then V₁ F else V₂ F).map (projective F) := by
  obtain ⟨⟨z,hzA,hzZ,hnz⟩,u,huA,huZ⟩ := large_plane_witnesses F A b hA hc
  apply le_antisymm
  · intro g hg
    have hgz : g ∈ centralizer ({projective F z} : Set PSL(3,F)) :=
      centralizer_le (Set.singleton_subset_iff.mpr (mem_map_of_mem _ hzA)) hg
    have hnz' : projective F z ≠ 1 := by
      intro h
      exact hnz ((projective_injective F) (h.trans (map_one _).symm))
    rw [centralizer_singleton_eq_of_mem_center F _ (mem_map_of_mem _ hzZ) hnz'] at hgz
    let c : EvenInnerCentralizers.centralizer F := ⟨g,hgz⟩
    obtain ⟨a,v,hc⟩ := EvenInnerCentralizers.centralizer_factorization F c
    have hcomm : c * EvenInnerCentralizers.unipotentInCentralizer F u =
        EvenInnerCentralizers.unipotentInCentralizer F u * c := by
      apply Subtype.ext
      exact (hg _ (mem_map_of_mem _ huA)).symm
    rw [hc] at hcomm
    have ht := torus_eq_one_of_commutes F a v u huZ hcomm
    rw [ht, one_mul] at hc hcomm
    have hgval : g = projective F v := congrArg Subtype.val hc
    rw [hgval]
    apply mem_map_of_mem
    have huv : v*u = u*v := EvenInnerCentralizers.unipotentInCentralizer_injective F
      (by simpa only [map_mul] using hcomm)
    have he := (mul_comm_iff F v u).mp huv
    have hpu := hA huA
    cases b
    · have hux : u.x = 0 := (mem_V₂ F u).mp hpu
      have huy : u.y ≠ 0 := fun h => huZ ((mem_Z F u).mpr ⟨hux,h⟩)
      exact (mem_V₂ F v).mpr ((mul_eq_zero.mp (by simpa [hux] using he)).resolve_right huy)
    · have huy : u.y = 0 := (mem_V₁ F u).mp hpu
      have hux : u.x ≠ 0 := fun h => huZ ((mem_Z F u).mpr ⟨h,huy⟩)
      exact (mem_V₁ F v).mpr ((mul_eq_zero.mp (by simpa [huy] using he.symm)).resolve_left hux)
  · rintro _ ⟨v,hv,rfl⟩ _ ⟨u,hu,rfl⟩
    rw [← map_mul, ← map_mul]
    apply congrArg (projective F)
    apply (mul_comm_iff F u v).mpr
    have hu := hA hu
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, mem_V₂] at hu hv
      have hv : v.x = 0 := (mem_V₂ F v).mp hv
      simp [hu,hv]
    · simp only [↓reduceIte, mem_V₁] at hu hv
      have hv : v.y = 0 := (mem_V₁ F v).mp hv
      simp [hu,hv]

end Matrix.PSL3Even.LargePlaneNormalizers

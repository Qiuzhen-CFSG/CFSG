module
public import Theory.SpecificGroups.SymplecticFour.FlagPaths.Counts
public import Theory.SpecificGroups.SymplecticFour.Sylow.OddSubgroups
import Mathlib.Tactic.FinCases
set_option backward.isDefEq.respectTransparency false
/-!
# Five-path transitivity of the symplectic flag graph

A quarter-turn of the standard symplectic frame gives a five-edge apartment
path. Its fixer lies in two opposite Borels. The unipotent intersection with
the opposite Borel is trivial by the four matrix coordinates, so the two
determinant characters embed the fixer in the rank-two torus. Orbit–stabilizer
and the native path census prove transitivity. Reversing the path treats the
plane root; translations then treat every vertex.

Source: Aschbacher–Smith F.4.5(7), printed p.275 of `refs/quasithin.pdf`.
This is a direct matrix proof of the native action, with no polygon
classification or completion-recognition premise.
-/

@[expose] public noncomputable section
open Matrix Subgroup SimpleGraph
open Subgroup.CosetGeometry.RankTwo
open Subgroup.CosetGeometry (translationGraphIso incident_base incident_base_iff)
namespace Theory.SpecificGroups.SymplecticFour.FlagPaths
variable {F : Type*} [Field F] [CharP F 2]

private def rotation : Sp F := ⟨fromBlocks !![0,0;1,0] !![0,1;0,0]
    !![0,1;0,0] !![0,0;1,0], by
  rw [SymplecticGroup.mem_iff]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [CharTwo.neg_eq, Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]⟩

private def swap : Sp F := ⟨fromBlocks !![0,1;1,0] 0 0 !![0,1;1,0], by
  rw [SymplecticGroup.mem_iff]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [CharTwo.neg_eq, Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]⟩

private theorem swap_mem : swap (F := F) ∈ planeParabolic := by
  rw [mem_planeParabolic_iff]
  intro i j
  rfl

private theorem swap_inv : (swap (F := F))⁻¹ = swap := by
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  change (swap (F := F)).val * swap.val = (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
  simp only [swap, fromBlocks_multiply, mul_zero, zero_mul, add_zero, zero_add]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;> simp

private theorem swap_inv_mul_rotation_mem : (swap (F := F))⁻¹ * rotation ∈ pointParabolic := by
  rw [swap_inv, mem_pointParabolic_iff]
  constructor
  · simp [swap, rotation, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]
  · intro i
    fin_cases i <;> simp [swap, rotation, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]

private theorem rotation_not_mem (i : Bool) : rotation (F := F) ∉ family i := by
  cases i
  · intro h
    have hz := (mem_pointParabolic_iff _).mp h
    have he : (1 : F) = 0 := hz.1
    exact one_ne_zero he
  · intro h
    have hz := (mem_planeParabolic_iff _).mp h
    have he : (1 : F) = 0 := hz 0 1
    exact one_ne_zero he

private def apartmentVertex (k : ℕ) (i : Bool) : Vertex (family (F := F)) :=
  (rotation (F := F)) ^ k • base family i

private theorem edge (k : ℕ) :
    (graph (family (F := F))).Adj (apartmentVertex k false) (apartmentVertex k true) :=
  (translationGraphIso family (rotation^k)).toHom.map_adj
    ⟨Bool.false_ne_true, incident_base family false true⟩

private theorem crossing_zero :
    (graph (family (F := F))).Adj (base family true) ((rotation (F := F)) • base family false) := by
  have he : rotation (F := F) • base family false = mkVertex family false (swap (F := F)) := by
    change mkVertex family false (rotation * 1) = mkVertex family false (swap (F := F))
    rw [mul_one, mkVertex_eq]
    have hm := (pointParabolic (F := F)).inv_mem (swap_inv_mul_rotation_mem (F := F))
    simpa only [_root_.mul_inv_rev, inv_inv, family, Bool.false_eq_true, ite_false] using hm
  rw [he]
  refine ⟨show true ≠ false from Bool.false_ne_true.symm, ?_⟩
  apply (incident_base_iff family true _).mpr
  exact ⟨swap, swap_mem, rfl⟩

private theorem crossing (k : ℕ) :
    (graph (family (F := F))).Adj (apartmentVertex k true) (apartmentVertex (k+1) false) := by
  have h := (translationGraphIso family (rotation^k)).toHom.map_adj (crossing_zero (F := F))
  change (graph (family (F := F))).Adj
    ((rotation (F := F))^k • base family true) ((rotation (F := F))^k • (rotation • base family false)) at h
  simpa only [apartmentVertex, pow_succ, mul_smul] using h

private theorem different (k : ℕ) (i : Bool) :
    apartmentVertex (F := F) (k+1) i ≠ apartmentVertex k i := by
  intro he
  have hh : rotation (F := F) • base family i = base family i :=
    (MulAction.injective (rotation (F := F)^k)) (by simpa only [apartmentVertex, pow_succ, mul_smul] using he)
  apply rotation_not_mem (F := F) i
  have hm : rotation (F := F) ∈ MulAction.stabilizer (Sp F) (base family i) := hh
  simpa only [base, CosetGeometry.stabilizer_base] using hm

private def fivePath : BasedWalk (graph (family (F := F))) 5 (apartmentVertex 0 false) := by
  exact   ⟨⟨apartmentVertex 0 true,edge 0⟩, ⟨⟨apartmentVertex 1 false,crossing 0⟩,
    ⟨⟨apartmentVertex 1 true,edge 1⟩, ⟨⟨apartmentVertex 2 false,crossing 1⟩,
      ⟨⟨apartmentVertex 2 true,edge 2⟩, PUnit.unit⟩⟩⟩⟩⟩

private def reverseFivePath : BasedWalk (graph (family (F := F))) 5 (apartmentVertex 2 true) := by
  exact   ⟨⟨apartmentVertex 2 false,(edge 2).symm⟩, ⟨⟨apartmentVertex 1 true,(crossing 1).symm⟩,
    ⟨⟨apartmentVertex 1 false,(edge 1).symm⟩, ⟨⟨apartmentVertex 0 true,(crossing 0).symm⟩,
      ⟨⟨apartmentVertex 0 false,(edge 0).symm⟩, PUnit.unit⟩⟩⟩⟩⟩

private theorem fivePath_nonbacktracking : (fivePath (F := F)).Nonbacktracking :=
  ⟨different 0 false, different 0 true, different 1 false, different 1 true, trivial⟩

private theorem reverseFivePath_nonbacktracking : (reverseFivePath (F := F)).Nonbacktracking :=
  ⟨(different 1 true).symm, (different 1 false).symm,
    (different 0 true).symm, (different 0 false).symm, trivial⟩

private theorem rotation_sq : (rotation (F := F)^2).val = fromBlocks 0 1 1 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [pow_two, rotation, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]

private theorem rotation_sq_inv : ((rotation (F := F))^2)⁻¹ = rotation^2 := by
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  change (rotation (F := F)^2).val * (rotation^2).val = (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
  rw [rotation_sq]
  simp [fromBlocks_multiply]

private theorem opposite_conjugate (g : Sp F) (i j : Fin 2 ⊕ Fin 2) :
    ((rotation^2)⁻¹ * g * rotation^2).val i j = g.val (i.swap) (j.swap) := by
  rw [rotation_sq_inv]
  simp only [Submonoid.coe_mul, rotation_sq]
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]


private theorem opposite_unipotent [Finite F] (g : Sp F) (hg : g ∈ unipotent)
    (ho : (rotation^2)⁻¹ * g * rotation^2 ∈ borel) : g = 1 := by
  obtain ⟨⟨b,u,w,v⟩,he⟩ := CentralRootGeometry.element_surjective (⟨g,hg⟩ : unipotent (F := F))
  have hm : g.val = (CentralRootGeometry.element b u w v).val.val :=
    (congrArg (fun x : unipotent (F := F) => x.val.val) he).symm
  have h := (mem_borel_iff _).mp ho
  simp only [opposite_conjugate] at h
  have hb : b = 0 := by simpa [hm, CentralRootGeometry.element_matrix] using h.1
  have hu : u = 0 := by simpa [hm, CentralRootGeometry.element_matrix] using h.2 0 0
  have hw : w = 0 := by simpa [hm, CentralRootGeometry.element_matrix] using h.2 1 0
  have hv : v = 0 := by simpa [hm, CentralRootGeometry.element_matrix] using h.2 1 1
  have hh : (⟨g,hg⟩ : unipotent (F := F)) = 1 := by
    rw [←he,hb,hu,hw,hv]
    exact CentralRootGeometry.element_zero
  exact congrArg Subtype.val hh

private theorem mem_stabilizer_apartment (g : Sp F) (k : ℕ) (i : Bool) :
    g • apartmentVertex (F := F) k i = apartmentVertex k i ↔
      (rotation^k)⁻¹ * g * rotation^k ∈ family i := by
  change g ∈ MulAction.stabilizer (Sp F) (rotation^k • base family i) ↔ _
  have hv : rotation (F := F)^k • base family i = mkVertex family i ((rotation (F := F))^k) := by
    change mkVertex family i (rotation^k * 1) = _
    rw [mul_one]
  rw [hv]
  exact CoverData.mem_stabilizer_mk i _ g

private theorem fivePath_fixer_le_borel : pathStabilizer (family (F := F)) fivePath ≤ borel := by
  intro g hg
  have hp := (mem_stabilizer_apartment g 0 false).mp (hg (apartmentVertex 0 false) (by simp [fivePath, BasedWalk.vertices]))
  have hl := (mem_stabilizer_apartment g 0 true).mp (hg (apartmentVertex 0 true) (by simp [fivePath, BasedWalk.vertices]))
  change (g ∈ pointParabolic) ∧ (g ∈ planeParabolic)
  exact ⟨by simpa only [pow_zero, inv_one, one_mul, mul_one, family, Bool.false_eq_true, ite_false] using hp,
    by simpa only [pow_zero, inv_one, one_mul, mul_one, family, ite_true] using hl⟩

private theorem fivePath_opposite {g : Sp F} (hg : g ∈ pathStabilizer family fivePath) :
    (rotation^2)⁻¹ * g * rotation^2 ∈ borel := by
  exact ⟨(mem_stabilizer_apartment g 2 false).mp (hg (apartmentVertex 2 false) (by simp [fivePath, BasedWalk.vertices])),
    (mem_stabilizer_apartment g 2 true).mp (hg (apartmentVertex 2 true) (by simp [fivePath, BasedWalk.vertices]))⟩

private theorem fivePath_characters_injective [Finite F] :
    Function.Injective ((borelCharacters (F := F)).comp (inclusion fivePath_fixer_le_borel)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro g hg
  apply Subtype.ext
  change g.val = 1
  exact opposite_unipotent g.val
    ((borelCharacters_eq_one (inclusion fivePath_fixer_le_borel g)).mp hg)
    (fivePath_opposite g.property)

private theorem fivePath_fixer_card [Finite F] :
    Nat.card (pathStabilizer (family (F := F)) fivePath) ≤ (Nat.card F - 1)^2 := by
  have h := Nat.card_le_card_of_injective _ (fivePath_characters_injective (F := F))
  simpa only [Nat.card_prod, Nat.card_units, pow_two] using h

private theorem reverseFivePath_fixer : pathStabilizer (family (F := F)) reverseFivePath =
    pathStabilizer family fivePath := by
  ext g
  change (∀ w ∈ (reverseFivePath (F := F)).vertices, g • w = w) ↔
    (∀ w ∈ (fivePath (F := F)).vertices, g • w = w)
  simp only [fivePath, reverseFivePath,
    BasedWalk.vertices, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  tauto

variable [Finite F]
open SimpleGraph.PathTransitivePolygon

theorem card_vertex_stabilizer (v : Vertex (family (F := F))) :
    Nat.card (MulAction.stabilizer (Sp F) v) =
      Nat.card F ^ 4 * (Nat.card F - 1)^2 * (Nat.card F + 1) := by
  obtain ⟨a,ha⟩ := CosetGeometry.exists_smul_base family v
  rw [←ha, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  rw [Subgroup.card_map_of_injective (MulAut.conj a).injective,
    CosetGeometry.stabilizer_base, card_endpoint]

private theorem transitive_of_fixer_bound {v : Vertex (family (F := F))}
    (p : BasedWalk (graph family) 5 v) (hp : p.Nonbacktracking)
    (hc : Nat.card (pathStabilizer family p) ≤ (Nat.card F - 1)^2) :
    RootPathTransitive (graph family) (Sp F) v 5 := by
  have hq := Finite.one_lt_card (α := F)
  have hq0 : 0 < Nat.card F := by omega
  have hqm : 0 < Nat.card F - 1 := by omega
  have : Finite {p : BasedWalk (graph family) 5 v // p.Nonbacktracking} :=
    Nat.finite_of_card_ne_zero (by rw [card_paths 4]; positivity)
  apply rootPathTransitive_of_pathStabilizer_card_le family p hp (by positivity) hc
  rw [card_vertex_stabilizer, card_paths 4]
  ring

/-- Both native vertex groups are transitive on all nonbacktracking five-paths. -/
theorem rootPathTransitive_five (i : Bool) :
    RootPathTransitive (graph (family (F := F))) (Sp F) (base family i) 5 := by
  cases i
  · simpa only [apartmentVertex, pow_zero, one_smul] using
      transitive_of_fixer_bound fivePath fivePath_nonbacktracking fivePath_fixer_card
  · have ht := transitive_of_fixer_bound (reverseFivePath (F := F)) reverseFivePath_nonbacktracking
      (by rw [reverseFivePath_fixer]; exact fivePath_fixer_card (F := F))
    have hact : GraphAction (graph (family (F := F))) (Sp F) :=
      ⟨fun g _ _ h => (translationGraphIso family g).toHom.map_adj h⟩
    have hh := RootPathTransitive.smul hact ht ((rotation (F := F)^2)⁻¹)
    simpa only [apartmentVertex, inv_smul_smul] using hh

/-- Native five-path transitivity at every vertex, with its literal point or plane type. -/
theorem all_rootPathTransitive_five (v : Vertex (family (F := F))) :
    RootPathTransitive (graph family) (Sp F) v 5 := by
  obtain ⟨a,ha⟩ := CosetGeometry.exists_smul_base family v
  rw [←ha]
  exact RootPathTransitive.smul
    (⟨fun g _ _ h => (translationGraphIso family g).toHom.map_adj h⟩ : GraphAction (graph family) (Sp F))
    (rootPathTransitive_five v.type) a
end Theory.SpecificGroups.SymplecticFour.FlagPaths

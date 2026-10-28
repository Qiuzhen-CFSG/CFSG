module
public import Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FourPaths.Counts

/-!
# Five-path transitivity of the Hermitian four-space flag graph

A product of the two native coordinate reflections gives a five-edge
apartment path. Its fixer lies in opposite flag stabilizers, so its
unitriangular intersection is trivial. The native diagonal character
therefore embeds it in Fˣ × (F^σ)ˣ. The exact endpoint and five-path
counts prove transitivity by orbit–stabilizer. Reversing the same path
treats the other vertex type and its different valence.

Source: Aschbacher–Smith F.4.5(7), p.275 of `refs/quasithin.pdf`.
The proof follows the orbit-count method of the symplectic `FlagPaths`
module, with the actual unitary involution and fixed-field torus retained.
-/

@[expose] public noncomputable section
open Matrix Subgroup SimpleGraph BenderSuzuki.MatrixGroups
open Subgroup.CosetGeometry.RankTwo
open Subgroup.CosetGeometry (translationGraphIso incident_base incident_base_iff)
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourGeneration UnitaryFourSylow
namespace Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FourPaths
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {σ : F ≃+* F} {hσ : Function.Involutive σ}
local notation "J" => form F σ hσ
local notation "Pₛ" => family F σ hσ
local notation "B" => borelSU F J
local notation "K" => FixedField F σ

private def rotation : SU F J := pairSwap F σ hσ * middleSwap F σ hσ
local notation "r" => rotation (F := F) (σ := σ) (hσ := hσ)

private theorem rotation_sq : (r^2).val.val = gram F := by
  have he : r^2 = UnitaryFourGeneration.reverse F σ hσ := by
    simp only [rotation, UnitaryFourGeneration.reverse, pow_two, mul_assoc]
  rw [he, reverse_val]

private theorem rotation_not_mem (i : Bool) : r ∉ Pₛ i := by
  cases i
  · intro h
    have he := (mem_pointParabolicSU F J r).mp h
    have hz : (1 : F) = 0 := by
      simpa [rotation, pairSwap, middleSwap, involutionElement, pairSwapMatrix,
        middleSwapMatrix, Matrix.mul_apply, Fin.sum_univ_succ] using he.1
    exact one_ne_zero hz
  · intro h
    have he := (mem_planeParabolicSU F J r).mp h
    have hz : (1 : F) = 0 := by
      simpa [rotation, pairSwap, middleSwap, involutionElement, pairSwapMatrix,
        middleSwapMatrix, Matrix.mul_apply, Fin.sum_univ_succ] using he.2.2.2
    exact one_ne_zero hz

private def apartmentVertex (k : ℕ) (i : Bool) : Vertex Pₛ := r ^ k • base Pₛ i
local notation "a" => apartmentVertex (F := F) (σ := σ) (hσ := hσ)

private theorem edge (k : ℕ) : (graph Pₛ).Adj (a k false) (a k true) :=
  (translationGraphIso Pₛ (r^k)).toHom.map_adj
    ⟨Bool.false_ne_true, incident_base Pₛ false true⟩

private theorem crossing_zero : (graph Pₛ).Adj (base Pₛ true) (r • base Pₛ false) := by
  have he : r • base Pₛ false = mkVertex Pₛ false (pairSwap F σ hσ) := by
    change mkVertex Pₛ false (r * 1) = _
    rw [mul_one, mkVertex_eq]
    change r⁻¹ * pairSwap F σ hσ ∈ pointParabolicSU F J
    have hh : r⁻¹ * pairSwap F σ hσ = (middleSwap F σ hσ)⁻¹ := by
      dsimp [rotation]
      group
    rw [hh]
    exact (pointParabolicSU F J).inv_mem (middleSwap_mem_point F σ hσ)
  rw [he]
  refine ⟨show true ≠ false from Bool.false_ne_true.symm, ?_⟩
  exact (incident_base_iff Pₛ true _).mpr
    ⟨pairSwap F σ hσ, pairSwap_mem_plane F σ hσ, rfl⟩

private theorem crossing (k : ℕ) : (graph Pₛ).Adj (a k true) (a (k+1) false) := by
  have h := (translationGraphIso Pₛ (r^k)).toHom.map_adj (crossing_zero (σ := σ) (hσ := hσ))
  change (graph Pₛ).Adj (r^k • base Pₛ true) (r^k • (r • base Pₛ false)) at h
  simpa only [apartmentVertex, pow_succ, mul_smul] using h

private theorem different (k : ℕ) (i : Bool) : a (k+1) i ≠ a k i := by
  intro he
  have hh : r • base Pₛ i = base Pₛ i :=
    (MulAction.injective (r^k)) (by simpa only [apartmentVertex, pow_succ, mul_smul] using he)
  apply rotation_not_mem (σ := σ) (hσ := hσ) i
  have hm : r ∈ MulAction.stabilizer (SU F J) (base Pₛ i) := hh
  simpa only [base, CosetGeometry.stabilizer_base] using hm

private def fivePath : BasedWalk (graph Pₛ) 5 (a 0 false) :=
  ⟨⟨a 0 true,edge 0⟩, ⟨⟨a 1 false,crossing 0⟩,
    ⟨⟨a 1 true,edge 1⟩, ⟨⟨a 2 false,crossing 1⟩,
      ⟨⟨a 2 true,edge 2⟩, PUnit.unit⟩⟩⟩⟩⟩

private def reverseFivePath : BasedWalk (graph Pₛ) 5 (a 2 true) :=
  ⟨⟨a 2 false,(edge 2).symm⟩, ⟨⟨a 1 true,(crossing 1).symm⟩,
    ⟨⟨a 1 false,(edge 1).symm⟩, ⟨⟨a 0 true,(crossing 0).symm⟩,
      ⟨⟨a 0 false,(edge 0).symm⟩, PUnit.unit⟩⟩⟩⟩⟩

private theorem fivePath_nonbacktracking :
    (fivePath (σ := σ) (hσ := hσ)).Nonbacktracking :=
  ⟨different 0 false, different 0 true, different 1 false, different 1 true, trivial⟩

private theorem reverseFivePath_nonbacktracking :
    (reverseFivePath (σ := σ) (hσ := hσ)).Nonbacktracking :=
  ⟨(different 1 true).symm, (different 1 false).symm,
    (different 0 true).symm, (different 0 false).symm, trivial⟩

private theorem rotation_sq_inv : (r^2)⁻¹ = r^2 := by
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  apply Units.ext
  change (r^2).val.val * (r^2).val.val = 1
  rw [rotation_sq, gram_sq]

private theorem opposite_upper (g : SU F J) (hg : g ∈ upper F σ hσ)
    (ho : (r^2)⁻¹ * g * r^2 ∈ B) : g = 1 := by
  obtain ⟨ht,hd⟩ := (mem_upper_iff_entries F σ hσ g).mp hg
  have ht' := (mem_borel_iff_triangular F σ hσ _).mp ho
  rw [rotation_sq_inv] at ht'
  have h23 := ht' (by decide : (0 : Fin 4) < 1)
  have h13 := ht' (by decide : (0 : Fin 4) < 2)
  have h03 := ht' (by decide : (0 : Fin 4) < 3)
  have h12 := ht' (by decide : (1 : Fin 4) < 2)
  have h02 := ht' (by decide : (1 : Fin 4) < 3)
  have h01 := ht' (by decide : (2 : Fin 4) < 3)
  change ((r^2).val.val * g.val.val * (r^2).val.val) 1 0 = 0 at h23
  change ((r^2).val.val * g.val.val * (r^2).val.val) 2 0 = 0 at h13
  change ((r^2).val.val * g.val.val * (r^2).val.val) 3 0 = 0 at h03
  change ((r^2).val.val * g.val.val * (r^2).val.val) 2 1 = 0 at h12
  change ((r^2).val.val * g.val.val * (r^2).val.val) 3 1 = 0 at h02
  change ((r^2).val.val * g.val.val * (r^2).val.val) 3 2 = 0 at h01
  rw [rotation_sq] at h23 h13 h03 h12 h02 h01
  simp [gram, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ] at h23 h13 h03 h12 h02 h01
  apply Subtype.ext
  apply Units.ext
  change g.val.val = (1 : Matrix (Fin 4) (Fin 4) F)
  ext i j
  by_cases hij : i = j
  · subst j
    simpa using hd i
  · rw [Matrix.one_apply_ne hij]
    rcases lt_or_gt_of_ne hij with h | h
    · fin_cases i <;> fin_cases j <;> simp_all
    · exact ht _ _ h

private theorem mem_stabilizer_apartment (g : SU F J) (k : ℕ) (i : Bool) :
    g • a k i = a k i ↔ (r^k)⁻¹ * g * r^k ∈ Pₛ i := by
  change g ∈ MulAction.stabilizer (SU F J) (r^k • base Pₛ i) ↔ _
  have hv : r^k • base Pₛ i = mkVertex Pₛ i (r^k) := by
    change mkVertex Pₛ i (r^k * 1) = _
    rw [mul_one]
  rw [hv]
  exact CoverData.mem_stabilizer_mk i _ g

private theorem fivePath_fixer_le_borel :
    pathStabilizer Pₛ (fivePath (σ := σ) (hσ := hσ)) ≤ B := by
  intro g hg
  have hp := (mem_stabilizer_apartment g 0 false).mp (hg (a 0 false) (by simp [fivePath, BasedWalk.vertices]))
  have hl := (mem_stabilizer_apartment g 0 true).mp (hg (a 0 true) (by simp [fivePath, BasedWalk.vertices]))
  change g ∈ pointParabolicSU F J ∧ g ∈ planeParabolicSU F J
  exact ⟨by simpa only [pow_zero, inv_one, one_mul, mul_one, family, Bool.false_eq_true, ite_false] using hp,
    by simpa only [pow_zero, inv_one, one_mul, mul_one, family, ite_true] using hl⟩

private theorem fivePath_opposite {g : SU F J}
    (hg : g ∈ pathStabilizer Pₛ (fivePath (σ := σ) (hσ := hσ))) :
    (r^2)⁻¹ * g * r^2 ∈ B :=
  ⟨(mem_stabilizer_apartment g 2 false).mp (hg (a 2 false) (by simp [fivePath, BasedWalk.vertices])),
    (mem_stabilizer_apartment g 2 true).mp (hg (a 2 true) (by simp [fivePath, BasedWalk.vertices]))⟩

private theorem fivePath_characters_injective :
    Function.Injective ((torusCharacter F σ hσ).comp (inclusion fivePath_fixer_le_borel)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro g hg
  apply Subtype.ext
  change g.val = 1
  apply opposite_upper g.val _ (fivePath_opposite g.property)
  have hh : inclusion fivePath_fixer_le_borel g ∈ (torusCharacter F σ hσ).ker := hg
  rw [torusCharacter_ker] at hh
  exact hh

private theorem fivePath_fixer_card :
    Nat.card (pathStabilizer Pₛ (fivePath (σ := σ) (hσ := hσ))) ≤
      (Nat.card F - 1)*(Nat.card K - 1) := by
  have h := Nat.card_le_card_of_injective _ (fivePath_characters_injective (σ := σ) (hσ := hσ))
  simpa only [Nat.card_prod, Nat.card_units] using h

private theorem reverseFivePath_fixer :
    pathStabilizer Pₛ (reverseFivePath (σ := σ) (hσ := hσ)) = pathStabilizer Pₛ fivePath := by
  ext g
  change (∀ w ∈ (reverseFivePath (σ := σ) (hσ := hσ)).vertices, g • w = w) ↔
    (∀ w ∈ (fivePath (σ := σ) (hσ := hσ)).vertices, g • w = w)
  simp only [fivePath, reverseFivePath,
    BasedWalk.vertices, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  tauto

open SimpleGraph.PathTransitivePolygon

theorem card_vertex_stabilizer (v : Vertex Pₛ) :
    Nat.card (MulAction.stabilizer (SU F J) v) =
      degree F σ v.type * (Nat.card F ^ 2 * Nat.card K ^ 2) *
        ((Nat.card F - 1) * (Nat.card K - 1)) := by
  obtain ⟨g,hg⟩ := CosetGeometry.exists_smul_base Pₛ v
  rw [←hg, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
    CosetGeometry.stabilizer_base, card_endpoint]
  rfl

private theorem transitive_of_fixer_bound {v : Vertex Pₛ}
    (p : BasedWalk (graph Pₛ) 5 v) (hp : p.Nonbacktracking)
    (hc : Nat.card (pathStabilizer Pₛ p) ≤ (Nat.card F - 1)*(Nat.card K - 1)) :
    RootPathTransitive (graph Pₛ) (SU F J) v 5 := by
  have hF := Finite.one_lt_card (α := F)
  have hK := Finite.one_lt_card (α := K)
  have hF0 : 0 < Nat.card F := by omega
  have hK0 : 0 < Nat.card K := by omega
  have hFm : 0 < Nat.card F - 1 := by omega
  have hKm : 0 < Nat.card K - 1 := by omega
  have : Finite {p : BasedWalk (graph Pₛ) 5 v // p.Nonbacktracking} :=
    Nat.finite_of_card_ne_zero (by
      rw [card_five_paths]
      apply Nat.ne_of_gt
      cases v.type <;> dsimp [degree] <;> positivity)
  apply rootPathTransitive_of_pathStabilizer_card_le Pₛ p hp (Nat.mul_pos hFm hKm) hc
  rw [card_vertex_stabilizer, card_five_paths]

theorem rootPathTransitive_five (i : Bool) :
    RootPathTransitive (graph Pₛ) (SU F J) (base Pₛ i) 5 := by
  cases i
  · simpa only [apartmentVertex, pow_zero, one_smul] using
      transitive_of_fixer_bound fivePath fivePath_nonbacktracking
        (fivePath_fixer_card (σ := σ) (hσ := hσ))
  · have ht := transitive_of_fixer_bound (reverseFivePath (σ := σ) (hσ := hσ))
      reverseFivePath_nonbacktracking
      (by rw [reverseFivePath_fixer]; exact fivePath_fixer_card)
    have hact : GraphAction (graph Pₛ) (SU F J) :=
      ⟨fun g _ _ h => (translationGraphIso Pₛ g).toHom.map_adj h⟩
    have hh := RootPathTransitive.smul hact ht ((r^2)⁻¹)
    simpa only [apartmentVertex, inv_smul_smul] using hh

end Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FourPaths

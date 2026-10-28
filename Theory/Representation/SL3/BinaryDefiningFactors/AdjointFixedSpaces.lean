module

public import Theory.Representation.SL3.BinaryDefiningFactors.AdjointFixedSpaces.RootPlanes
public import Theory.Representation.SL3.BinaryDefiningFactors.AdjointFixedSpaces.MatrixCentralizers

/-!
# The strict common-fixed-space obstruction for the SL₃ adjoint module

An elementary two-subgroup is conjugate into a root plane of order q².
Its nontriviality gives adjoint fixed codimension at least four. If its rank
is less than 2r this is already strict against twice the rank. At rank 2r
the subgroup is the entire plane, whose fixed codimension is at least six.
Conjugation transports the actual invariant subspace back to the original
subgroup. This includes q = 2, arbitrary coefficient embeddings, and the
possibly nonfaithful adjoint action of SL₃.

The carrier and action are the literal `AdjointSpace` and `factorRep`.
Fixed endomorphisms are sent injectively to their coordinate matrices;
conjugation invariance becomes matrix commutation. No representation
classification or irreducibility hypothesis is used.

Source: Guralnick–Malle, Classification of 2F-modules II, author manuscript
Lemma 4.5, pp.23–24, paragraph 2; Aschbacher–Smith K.3.2, pp.454–456.
-/

public section
open scoped MatrixGroups
open Matrix.PSL3Even.UnipotentGeometry Matrix.PSL3.RootPlaneGeometry
namespace Representation.SL3.BinaryDefiningFactors.AdjointFixedSpaces
set_option backward.isDefEq.respectTransparency false
variable {F K : Type*} [Field F] [Field K]

private noncomputable def fixedMatrix (ι : F →+* K) (E : Subgroup SL(3,F)) :
    invariants ((factorRep ι .adjoint).comp E.subtype) →ₗ[K] Matrix (Fin 3) (Fin 3) K :=
  LinearMap.toMatrix'.toLinearMap.comp
    ((LinearMap.ker (LinearMap.trace K (Fin 3 → K))).subtype.comp
      (invariants ((factorRep ι .adjoint).comp E.subtype)).subtype)

private theorem fixedMatrix_injective (ι : F →+* K) (E : Subgroup SL(3,F)) :
    Function.Injective (fixedMatrix ι E) :=
  LinearMap.toMatrix'.injective.comp (Subtype.val_injective.comp Subtype.val_injective)

private theorem fixedMatrix_trace (ι : F →+* K) (E : Subgroup SL(3,F))
    (v : invariants ((factorRep ι .adjoint).comp E.subtype)) :
    Matrix.trace (fixedMatrix ι E v) = 0 := by
  have htrace := LinearMap.trace_eq_matrix_trace K (Pi.basisFun K (Fin 3)) v.val.val
  rw [LinearMap.toMatrix_eq_toMatrix'] at htrace
  exact htrace.symm.trans v.val.property

private theorem matrix_natural (ι : F →+* K) (g : SL(3,F)) :
    LinearMap.toMatrix' (natural ι g) = g.val.map ι := by
  change LinearMap.toMatrix' (Matrix.toLin' (g.val.map ι)) = _
  exact LinearMap.toMatrix'_toLin' _

private theorem fixedMatrix_commutes (ι : F →+* K) (E : Subgroup SL(3,F))
    (v : invariants ((factorRep ι .adjoint).comp E.subtype)) (g : SL(3,F)) (hg : g ∈ E) :
    fixedMatrix ι E v * g.val.map ι = g.val.map ι * fixedMatrix ι E v := by
  have he := congrArg (fun f : AdjointSpace K => f.val) (v.property ⟨g,hg⟩)
  change natural ι g ∘ₗ v.val.val ∘ₗ natural ι g⁻¹ = v.val.val at he
  have hinv : natural ι g⁻¹ ∘ₗ natural ι g = LinearMap.id := by
    rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hh := congrArg (fun q : Module.End K (Fin 3 → K) => q ∘ₗ natural ι g) he
  simp only [LinearMap.comp_assoc, hinv, LinearMap.comp_id] at hh
  have hm := congrArg LinearMap.toMatrix' hh
  change LinearMap.toMatrix' v.val.val * _ = _ * LinearMap.toMatrix' v.val.val
  simpa only [LinearMap.toMatrix'_comp, matrix_natural] using hm.symm

private theorem matrix_map (ι : F →+* K) (a b c : F) :
    (specialLinear F ⟨a,b,c⟩).val.map ι = matrix K ⟨ι a,ι b,ι c⟩ := by
  change (matrix F ⟨a,b,c⟩).map ι = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix, Matrix.map_apply]

theorem finrank_invariants_le_four_of_rootPlane (ι : F →+* K)
    (E : Subgroup SL(3,F)) (hE : E ≠ ⊥) (point : Bool)
    (hle : E ≤ rootPlaneSL F point) :
    Module.finrank K (invariants ((factorRep ι .adjoint).comp E.subtype)) ≤ 4 := by
  obtain ⟨g,hg,hg1⟩ := E.bot_or_exists_ne_one.resolve_left hE
  cases point
  · obtain ⟨b,c,rfl⟩ := (mem_rootPlaneSL_line F g).mp (hle hg)
    have hb : ι b ≠ 0 ∨ ι c ≠ 0 := by
      by_contra h
      push Not at h
      have hb : b = 0 := ι.injective (h.1.trans (map_zero ι).symm)
      have hc : c = 0 := ι.injective (h.2.trans (map_zero ι).symm)
      apply hg1
      rw [hb,hc]
      exact map_one (specialLinear F)
    apply finrank_le_four_of_line_commutes (fixedMatrix ι E)
      (fixedMatrix_injective ι E) (ι b) (ι c) hb (fixedMatrix_trace ι E)
    intro v
    simpa only [matrix_map, map_zero] using fixedMatrix_commutes ι E v _ hg
  · obtain ⟨a,c,rfl⟩ := (mem_rootPlaneSL_point F g).mp (hle hg)
    have ha : ι a ≠ 0 ∨ ι c ≠ 0 := by
      by_contra h
      push Not at h
      have ha : a = 0 := ι.injective (h.1.trans (map_zero ι).symm)
      have hc : c = 0 := ι.injective (h.2.trans (map_zero ι).symm)
      apply hg1
      rw [ha,hc]
      exact map_one (specialLinear F)
    apply finrank_le_four_of_point_commutes (fixedMatrix ι E)
      (fixedMatrix_injective ι E) (ι a) (ι c) ha (fixedMatrix_trace ι E)
    intro v
    simpa only [matrix_map, map_zero] using fixedMatrix_commutes ι E v _ hg

theorem finrank_invariants_rootPlane_le_two [CharP K 2] (ι : F →+* K) (point : Bool) :
    Module.finrank K
      (invariants ((factorRep ι .adjoint).comp (rootPlaneSL F point).subtype)) ≤ 2 := by
  cases point
  · apply finrank_le_two_of_line_plane_commutes (fixedMatrix ι _)
      (fixedMatrix_injective ι _) (fixedMatrix_trace ι _)
    · intro v
      have h := fixedMatrix_commutes ι _ v (specialLinear F ⟨0,1,0⟩)
        ((mem_rootPlaneSL_line F _).mpr ⟨1,0,rfl⟩)
      simpa only [matrix_map, map_zero, map_one] using h
    · intro v
      have h := fixedMatrix_commutes ι _ v (specialLinear F ⟨0,0,1⟩)
        ((mem_rootPlaneSL_line F _).mpr ⟨0,1,rfl⟩)
      simpa only [matrix_map, map_zero, map_one] using h
  · apply finrank_le_two_of_point_plane_commutes (fixedMatrix ι _)
      (fixedMatrix_injective ι _) (fixedMatrix_trace ι _)
    · intro v
      have h := fixedMatrix_commutes ι _ v (specialLinear F ⟨1,0,0⟩)
        ((mem_rootPlaneSL_point F _).mpr ⟨1,0,rfl⟩)
      simpa only [matrix_map, map_zero, map_one] using h
    · intro v
      have h := fixedMatrix_commutes ι _ v (specialLinear F ⟨0,0,1⟩)
        ((mem_rootPlaneSL_point F _).mpr ⟨0,1,rfl⟩)
      simpa only [matrix_map, map_zero, map_one] using h

end Representation.SL3.BinaryDefiningFactors.AdjointFixedSpaces

open scoped MatrixGroups
open Matrix.PSL3.RootPlaneGeometry Representation.BinaryOffender
namespace Representation.SL3.BinaryDefiningFactors.AdjointFixedSpaces
set_option backward.isDefEq.respectTransparency false
section Conjugation
variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]

private theorem finrank_invariants_map_conj (ρ : Representation K G V)
    (P : Subgroup G) (g : G) :
    Module.finrank K (invariants (ρ.comp P.subtype)) =
      Module.finrank K (invariants (ρ.comp (P.map (MulAut.conj g).toMonoidHom).subtype)) := by
  let Q := P.map (MulAut.conj g).toMonoidHom
  have hinv (x : V) : ρ g⁻¹ (ρ g x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hginv (x : V) : ρ g (ρ g⁻¹ x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hforward (v : invariants (ρ.comp P.subtype)) :
      ρ g v ∈ invariants (ρ.comp Q.subtype) := by
    intro q
    obtain ⟨a, ha, hqa⟩ := q.property
    have hv : ρ a v = v := v.property ⟨a, ha⟩
    change ρ (q : G) (ρ g v) = ρ g v
    rw [← hqa]
    change ρ (g * a * g⁻¹) (ρ g v) = _
    rw [map_mul, map_mul]
    simp only [Module.End.mul_apply, hinv, hv]
  have hback (v : invariants (ρ.comp Q.subtype)) :
      ρ g⁻¹ v ∈ invariants (ρ.comp P.subtype) := by
    intro a
    have hmem : g * (a : G) * g⁻¹ ∈ Q := ⟨a, a.property, rfl⟩
    have hv : ρ (g * (a : G) * g⁻¹) v = v := v.property ⟨_, hmem⟩
    change ρ (a : G) (ρ g⁻¹ v) = ρ g⁻¹ v
    have h := congrArg (fun x : V => ρ g⁻¹ x) hv
    rw [map_mul, map_mul] at h
    simpa only [Module.End.mul_apply, hinv] using h
  let e : invariants (ρ.comp P.subtype) ≃ₗ[K] invariants (ρ.comp Q.subtype) :=
    { toFun := fun v => ⟨ρ g v, hforward v⟩
      invFun := fun v => ⟨ρ g⁻¹ v, hback v⟩
      left_inv := fun v => Subtype.ext (hinv v)
      right_inv := fun v => Subtype.ext (hginv v)
      map_add' := fun v w => Subtype.ext (map_add (ρ g) (v : V) (w : V))
      map_smul' := fun c v => Subtype.ext (map_smul (ρ g) c (v : V)) }
  exact e.finrank_eq

end Conjugation

variable {F K : Type*} [Field F] [Finite F] [CharP F 2] [Field K] [CharP K 2]

theorem strict_common_fixedCodim {r : ℕ} (hr : 0 < r) (hF : Nat.card F = 2 ^ r)
    (ι : F →+* K) (E : Subgroup SL(3,F)) (hE : IsElementaryTwo E) :
    2 * rank E < r * Module.finrank K
      (AdjointSpace K ⧸ invariants ((factorRep ι .adjoint).comp E.subtype)) := by
  obtain ⟨g,point,hplane⟩ := elementary_conjugate_le_rootPlane hr hF E hE
  let A := E.map (MulAut.conj g).toMonoidHom
  have hA : IsElementaryTwo A := hE.map_conj g
  have hrA : rank A = rank E := rank_map_conj E g
  have hrank := rank_le_of_le_rootPlane hF A point hplane
  have hd := (invariants ((factorRep ι .adjoint).comp A.subtype)).finrank_quotient_add_finrank
  change Module.finrank K (AdjointSpace K ⧸ invariants ((factorRep ι .adjoint).comp A.subtype)) +
    Module.finrank K (invariants ((factorRep ι .adjoint).comp A.subtype)) =
    Module.finrank K (AdjointSpace K) at hd
  rw [finrank_adjointSpace] at hd
  have hlt : 2 * rank A < r * Module.finrank K
      (AdjointSpace K ⧸ invariants ((factorRep ι .adjoint).comp A.subtype)) := by
    by_cases hsmall : rank A < 2 * r
    · have hfour := finrank_invariants_le_four_of_rootPlane ι A hA.1 point hplane
      have hc : 4 ≤ Module.finrank K
          (AdjointSpace K ⧸ invariants ((factorRep ι .adjoint).comp A.subtype)) := by omega
      have hm := Nat.mul_le_mul_left r hc
      omega
    · have heq : rank A = 2 * r := by omega
      have he := eq_rootPlane_of_rank_eq hF A hA point hplane heq
      have htwo := finrank_invariants_rootPlane_le_two ι point
      rw [← he] at htwo
      have hc : 6 ≤ Module.finrank K
          (AdjointSpace K ⧸ invariants ((factorRep ι .adjoint).comp A.subtype)) := by omega
      have hm := Nat.mul_le_mul_left r hc
      omega
  have hfix := finrank_invariants_map_conj (factorRep ι .adjoint) E g
  have hdE := (invariants ((factorRep ι .adjoint).comp E.subtype)).finrank_quotient_add_finrank
  have hcA : Module.finrank K
      (AdjointSpace K ⧸ invariants ((factorRep ι .adjoint).comp A.subtype)) =
      Module.finrank K
      (AdjointSpace K ⧸ invariants ((factorRep ι .adjoint).comp E.subtype)) := by
    change Module.finrank K (invariants ((factorRep ι .adjoint).comp E.subtype)) =
      Module.finrank K (invariants ((factorRep ι .adjoint).comp A.subtype)) at hfix
    change Module.finrank K (AdjointSpace K ⧸ invariants ((factorRep ι .adjoint).comp E.subtype)) +
      Module.finrank K (invariants ((factorRep ι .adjoint).comp E.subtype)) =
      Module.finrank K (AdjointSpace K) at hdE
    rw [finrank_adjointSpace] at hdE
    omega
  rwa [hrA, hcA] at hlt

end Representation.SL3.BinaryDefiningFactors.AdjointFixedSpaces

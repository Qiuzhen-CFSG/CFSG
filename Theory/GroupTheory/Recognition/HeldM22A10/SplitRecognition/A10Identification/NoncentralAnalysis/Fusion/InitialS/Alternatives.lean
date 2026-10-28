module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.AdditionalFusion.Tables
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.FusionConstraints

/-!
# A noncentral fused representative in Held's local centralizer

Z-star gives a distinct conjugate of pi in the displayed ambient Sylow
subgroup. The concrete local involution table places it in one of the seven
noncentral H-classes. The identity and central pi classes cannot contain it.
This supplies the initial alternative in Held 2.9 without assuming fusion
with any chosen representative.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemmas 2.3 and 2.9, pp.226 and 229.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion.InitialS
open Coordinates

private def classBaseIndex (a : Code) : Fin 16 :=
  ⟨8 * a.1.1.val + 4 * a.1.2.1.val + 2 * a.1.2.2.1.val + a.1.2.2.2.val, by omega⟩
private def classActorIndex (a : Code) : Fin 8 :=
  ⟨4 * a.2.1.val + 2 * a.2.2.1.val + a.2.2.2.2.val, by omega⟩

private def classCertificate : Fin 16 → Fin 8 → Code × Fin 9 :=
  ![![(((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),4), (((0,0,0,0),(0,0,1,1)),3), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),3), (((0,0,0,0),(0,1,0,0)),4), (((0,0,0,0),(0,0,1,0)),3), (((0,0,0,0),(0,0,0,0)),0)],
    ![(((0,0,0,0),(0,0,0,0)),6), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),8), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0)],
    ![(((0,0,0,0),(0,0,1,1)),2), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,1),(0,0,1,1)),3), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0)],
    ![(((0,0,0,0),(0,0,2,0)),6), (((0,0,0,0),(0,1,0,0)),8), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0)],
    ![(((0,0,0,0),(0,0,0,0)),2), (((0,0,0,1),(0,0,0,0)),4), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,1),(0,0,0,0)),3), (((0,0,0,1),(0,1,0,0)),5), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0)],
    ![(((0,0,0,0),(0,0,0,1)),6), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,1)),8), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0)],
    ![(((0,0,0,0),(0,0,1,0)),2), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,1),(0,0,1,0)),3), (((0,0,0,0),(0,0,0,0)),0)],
    ![(((0,0,0,0),(1,1,0,0)),7), (((0,0,1,0),(0,1,0,0)),8), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0)],
    ![(((0,0,0,0),(0,0,0,0)),1), (((0,0,0,0),(0,0,0,0)),5), (((0,0,1,0),(0,0,1,1)),3), (((0,0,0,0),(0,0,0,0)),0), (((0,0,1,0),(0,0,0,0)),3), (((0,0,0,0),(0,1,0,0)),5), (((0,0,1,0),(0,0,1,0)),3), (((0,0,0,0),(0,0,0,0)),0)],
    ![(((0,0,0,0),(0,0,0,0)),7), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,1,0),(0,0,0,1)),8), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0)],
    ![(((0,0,0,0),(0,1,1,1)),2), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,1),(0,1,1,1)),3), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0)],
    ![(((0,0,0,0),(0,0,2,0)),7), (((0,0,1,0),(1,1,0,0)),8), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0)],
    ![(((0,0,0,0),(0,1,0,0)),2), (((0,0,0,1),(0,0,0,0)),5), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,1),(0,1,0,0)),3), (((0,0,0,1),(0,1,0,0)),4), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0)],
    ![(((0,0,0,0),(0,0,0,1)),7), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,1,0),(0,0,0,0)),8), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0)],
    ![(((0,0,0,0),(0,1,1,0)),2), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,1),(0,1,1,0)),3), (((0,0,0,0),(0,0,0,0)),0)],
    ![(((0,0,0,0),(1,1,0,0)),6), (((0,0,0,0),(1,1,0,0)),8), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0), (((0,0,0,0),(0,0,0,0)),0)]]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem local_involution_table : ∀ a : Code, a.2.2.2.1 = 0 → word a ^ 2 = 1 →
    word (classCertificate (classBaseIndex a) (classActorIndex a)).1 * word a *
      (word (classCertificate (classBaseIndex a) (classActorIndex a)).1)⁻¹ =
        localRepresentative (classCertificate (classBaseIndex a) (classActorIndex a)).2 := by
  decide +kernel

private theorem local_involution_representative (x : H) (hD : x ∈ modelD) (hx : x ^ 2 = 1) :
    ∃ i : Fin 9, IsConj x (localRepresentative i) := by
  obtain ⟨a, rfl⟩ := word_bijective.surjective x
  exact ⟨(classCertificate (classBaseIndex a) (classActorIndex a)).2, isConj_iff.mpr
    ⟨word (classCertificate (classBaseIndex a) (classActorIndex a)).1, local_involution_table a ((word_mem_modelD a).mp hD) hx⟩⟩

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

public theorem exists_distinct_coordinate_sylow_conjugate [IsSimpleGroup G] :
    ∃ x : ambientSylow D e, (x : G) ≠ D.z ∧ IsConj D.z (x : G) := by
  have hz : D.z ∈ ambientSylow D e :=
    ambientElementary_le_ambientSylow D e 1 (z_mem_ambientElementary D e 1)
  let z : ambientSylow D e := ⟨D.z, hz⟩
  have hTC : (ambientSylow D e : Subgroup G) ≤ D.centralizer := by
    have hh := map_le_range (f := D.a10ModelEmbedding e) modelD
    rwa [D.a10ModelEmbedding_range e] at hh
  have hcent : z ∈ center (ambientSylow D e) := by
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hTC x.property))
  by_contra! hw
  apply D.z_not_mem_ambient_center
  apply (ambientSylow D e).weakly_closed_involution_mem_center_of_simple z
    ((Subgroup.orderOf_coe z).symm.trans D.z_order) hcent
  intro x hx
  apply Subtype.ext
  by_contra hne
  exact hw x hne hx

/-- The complete noncentral local fusion alternatives, before Held 2.9. -/
public theorem initial_fusion_alternatives [IsSimpleGroup G] :
    IsConj D.z (D.a10NoncentralInvolution e) ∨
    IsConj D.z (D.a10ModelEmbedding e tau) ∨
    IsConj D.z (D.a10ModelEmbedding e lam) ∨
    IsConj D.z (D.a10ModelEmbedding e (pi * lam)) ∨
    IsConj D.z (D.a10ModelEmbedding e xi) ∨
    IsConj D.z (D.a10ModelEmbedding e (pi * xi)) ∨
    IsConj D.z (D.a10ModelEmbedding e (tau * lam * xi)) := by
  obtain ⟨x, hx, hzx⟩ := exists_distinct_coordinate_sylow_conjugate D e
  obtain ⟨y, hyD, hy⟩ := x.property
  have hy2 : y ^ 2 = 1 := by
    apply D.a10ModelEmbedding_injective e
    rw [map_pow, map_one, hy]
    obtain ⟨g, hg⟩ := isConj_iff.mp hzx
    rw [← hg, ← MulAut.conj_apply, ← map_pow,
      show D.z ^ 2 = 1 from D.z_order ▸ pow_orderOf_eq_one D.z, map_one]
  obtain ⟨i, hi⟩ := local_involution_representative y hyD hy2
  have hc := hzx.trans (hy ▸ (D.a10ModelEmbedding e).map_isConj hi)
  fin_cases i
  · exact (D.z_ne_one (isConj_one_left.mp (by simpa [localRepresentative] using hc))).elim
  · have hyz : y = pi := hi.eq_of_right_mem_center modelCentralInvolution_mem_center
    exact (hx (hy.symm.trans ((congrArg (D.a10ModelEmbedding e) hyz).trans
      (D.a10ModelEmbedding_central e)))).elim
  · exact Or.inl hc
  · exact Or.inr (Or.inl hc)
  · exact Or.inr (Or.inr (Or.inl hc))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hc)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hc)))))

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion.InitialS

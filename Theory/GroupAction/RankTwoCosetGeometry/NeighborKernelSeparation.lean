module
public import Theory.GroupAction.RankTwoCosetGeometry.SecondBallKernel

/-!
# Separating ball kernels at neighbors

If the normalizer of a second-type base kernel in the first vertex group
is exactly the common edge group, distinct second-type neighbors have
distinct kernels. Local transitivity and conjugation transport prove the
statement without finiteness of the graph or its vertex stabilizers.

The source quintic application uses radius two to prevent identification
of kernels at the two middle quintic vertices of a six-edge path.
Source: Aschbacher--Smith F.7.3, printed pp.311--312.
-/

public section
namespace Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] (F : Bool → Subgroup G)

/-- Distinct vertices around the first base vertex have distinct transported kernels. -/
theorem neighbor_ballKernel_ne_of_normalizer
    (n : ℕ)
    (hn : F false ⊓ normalizer (ballKernel F (base F true) n : Set G) = F false ⊓ F true)
    {u w v : Vertex F} (hu : u.type = true)
    (huw : (graph F).Adj u w) (hwv : (graph F).Adj w v) (huv : u ≠ v) :
    ballKernel F u n ≠ ballKernel F v n := by
  have hw : w.type = false := by
    have hh := huw.1
    rw [hu] at hh
    cases ht : w.type <;> simp_all
  have hv : v.type = true := by
    have hh := hwv.1
    rw [hw] at hh
    cases ht : v.type <;> simp_all
  obtain ⟨g,hgw,hgu⟩ := incident_common_translate F huw.symm.2
  rw [hw] at hgw
  rw [hu] at hgu
  have hadj : (graph F).Adj (base F false) (g⁻¹ • v) := by
    have hh := (translationGraphIso F g⁻¹).toHom.map_adj hwv
    change (graph F).Adj (g⁻¹ • w) (g⁻¹ • v) at hh
    simpa only [←hgw,inv_smul_smul] using hh
  obtain ⟨a,ha,hav⟩ := locally_transitive F
    (show (graph F).Adj (base F false) (base F true) from
      ⟨by change false ≠ true; decide, incident_base F false true⟩) hadj
  have haF : a ∈ F false := by
    simpa only [stabilizer,stabilizer_base] using ha
  intro heq
  have heq' : ballKernel F (g⁻¹ • v) n = ballKernel F (base F true) n := by
    rw [ballKernel_translate,←heq,←hgu,ballKernel_translate]
    simp only [map_map]
    have hf : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id G := by ext x; simp [mul_assoc]
    rw [hf,map_id]
  have haN : a ∈ normalizer (ballKernel F (base F true) n : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (ballKernel F (base F true) n).map (MulAut.conj a).toMonoidHom = _
    rw [← ballKernel_translate F a (base F true) n, hav, heq']
  have haH : a ∈ F true := (hn ▸ (show a ∈ F false ⊓ normalizer
    (ballKernel F (base F true) n : Set G) from ⟨haF,haN⟩)).2
  have hfix : a • base F true = base F true := by
    change a ∈ stabilizer F (base F true)
    simpa only [stabilizer,stabilizer_base] using haH
  have hvu : v = u := by
    have hh := congrArg (g • ·) (hav.symm.trans hfix)
    simpa only [smul_inv_smul,hgu] using hh
  exact huv hvu.symm
end Subgroup.CosetGeometry.RankTwo

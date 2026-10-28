module
public import Theory.GroupAction.SylowNormalizerKernel
public import Theory.SpecificGroups.SL2.SylowBorelSeparation
public import Theory.SpecificGroups.Suzuki.SmallSylowIntersections
public import Theory.GroupTheory.AmalgamGraph.LinearPathKernel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.LinearResidualLayer
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCenterDenominator
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.CoreGeneration

/-!
# Two-neighbor control of the actual vertex cores

A two-subgroup fixing two distinct neighbors lies in the vertex two-core
on either side of the marked linear/Suzuki pair. First place
the subgroup in the intrinsic Sylow-generated local group, which the
proved enlargement theorems identify with the original star. The literal
quotient map pulls a model Sylow normalizer back to the actual neighbor
stabilizer. Linear Borel separation and Suzuki TI then kill the image.
Conjugation transports the result to every vertex and either orientation.

This is the core-placement step at the beginning of DGS (12.7), printed
p.184. PathCoreControl applies it to the actual path stabilizers. Only
the original quotient markings are assumed; no path bound, core product,
common-Sylow identity or classification output is required. The Suzuki TI argument includes Sz(2); exhaustive Suzuki selection
remains a separate obligation.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction Theory.GroupTheory.AmalgamGraph
open BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem two_neighbor_core_of_separation
    {M : Type*} [Group M] (h : HypothesisF11 L S) (i : Bool)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* M)
    (hloc : graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i) = star L S i)
    (hsep : ∀ T : Sylow 2 M, ∀ t g : M, t ∈ (T : Subgroup M) → t ≠ 1 →
      g * t * g⁻¹ ∈ normalizer (T : Set M) → g ∈ normalizer (T : Set M))
    {x y : Vertex (reducedFamily L S)}
    (hx : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x)
    (hy : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) y)
    (hne : x ≠ y) (D : Subgroup (G₀ L S)) (hp : IsPGroup 2 D)
    (hm : D ≤ stabilizer (reducedFamily L S) (base (reducedFamily L S) i))
    (hDx : D ≤ stabilizer (reducedFamily L S) x)
    (hDy : D ≤ stabilizer (reducedFamily L S) y) :
    D ≤ Q (reducedFamily L S) (base (reducedFamily L S) i) := by
  let F := reducedFamily L S
  let A := star L S i
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite A := Finite.of_injective
    (inclusion (star_le_stabilizer (L := L) (S := S) i)) (inclusion_injective _)
  have hDA : D ≤ A := by
    change D ≤ star L S i
    rw [←hloc]
    exact pGroup_le_sylowGenerated _ D hm hp
  let f := ((originalQuotient h i).symm.trans e).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hf : Function.Surjective f := ((originalQuotient h i).symm.trans e).surjective.comp
    (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 A := by
    ext t
    change e ((originalQuotient h i).symm (QuotientGroup.mk' (pCore 2 A) t)) = 1 ↔ t ∈ pCore 2 A
    rw [map_eq_one_iff _ e.injective, map_eq_one_iff _ (originalQuotient h i).symm.injective]
    exact QuotientGroup.eq_one_iff t
  obtain ⟨T,hT⟩ := base_star_sylow_normalizer h i
  let R : Sylow 2 M := T.mapSurjective (f := f) hf
  have hRT : (R : Subgroup M).comap f = T := by
    apply comap_map_eq_self
    rw [hk]
    exact pCore_isPGroup.le_sylow_of_normal T
  have hmark : (normalizer (R : Set M)).comap f = MulAction.stabilizer A (base F (!i)) := by
    change (normalizer ((R : Subgroup M) : Set M)).comap f = _
    rw [comap_normalizer_eq_of_surjective _ hf, hRT, Sylow.coe_coe, ←hT]
    rfl
  have hadj : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨a,ha,hax⟩ := star_locally_transitive h i hadj hx
  obtain ⟨b,hb,hby⟩ := star_locally_transitive h i hadj hy
  have hDker := Theory.GroupAction.pGroup_le_kernel_of_two_fixed f R (base F (!i))
    hmark (hsep R) (D.subgroupOf A) hp.comap_subtype (⟨a,ha⟩ : A) (⟨b,hb⟩ : A)
    (by change a • base F (!i) ≠ b • base F (!i); rwa [hax,hby])
    (by intro d hd; change (d : G₀ L S) • (a • base F (!i)) = a • base F (!i); rw [hax]; exact hDx hd)
    (by intro d hd; change (d : G₀ L S) • (b • base F (!i)) = b • base F (!i); rw [hby]; exact hDy hd)
  rw [hk] at hDker
  rw [←star_core h i]
  intro d hd
  exact mem_map.mpr ⟨⟨d,hDA hd⟩, hDker hd, rfl⟩

/-- In the linear orbit, a two-subgroup fixing two distinct neighbors lies in Q. -/
theorem source_linear_two_neighbor_core
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    {x y : Vertex (reducedFamily L S)}
    (hx : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x)
    (hy : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) y)
    (hne : x ≠ y) (D : Subgroup (G₀ L S)) (hp : IsPGroup 2 D)
    (hm : D ≤ stabilizer (reducedFamily L S) (base (reducedFamily L S) i))
    (hDx : D ≤ stabilizer (reducedFamily L S) x)
    (hDy : D ≤ stabilizer (reducedFamily L S) y) :
    D ≤ Q (reducedFamily L S) (base (reducedFamily L S) i) :=
  two_neighbor_core_of_separation h i e (source_linear_graphLocalGroup_eq_star h i e)
    Matrix.SpecialLinearGroup.mem_sylow_normalizer_of_conjugate_mem hx hy hne D hp hm hDx hDy

/-- The same core placement for the actual Suzuki orbit, including Sz(2). -/
theorem source_suzuki_two_neighbor_core
    (h : HypothesisF11 L S) (i : Bool) {n : ℕ}
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    {x y : Vertex (reducedFamily L S)}
    (hx : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x)
    (hy : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) y)
    (hne : x ≠ y) (D : Subgroup (G₀ L S)) (hp : IsPGroup 2 D)
    (hm : D ≤ stabilizer (reducedFamily L S) (base (reducedFamily L S) i))
    (hDx : D ≤ stabilizer (reducedFamily L S) x)
    (hDy : D ≤ stabilizer (reducedFamily L S) y) :
    D ≤ Q (reducedFamily L S) (base (reducedFamily L S) i) :=
  two_neighbor_core_of_separation h i e (source_suzuki_graphLocalGroup_eq_star h i e)
    (fun T => T.mem_normalizer_of_conjugate_mem_of_ti (suzuki_sylow_eq_of_inf_ne_bot_all n))
    hx hy hne D hp hm hDx hDy

/-- Both original markings give two-neighbor core control at every vertex. -/
theorem source_mixed_two_neighbor_core
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (eLin : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    {n : ℕ}
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    {m x y : Vertex (reducedFamily L S)}
    (hx : (graph (reducedFamily L S)).Adj m x)
    (hy : (graph (reducedFamily L S)).Adj m y)
    (hne : x ≠ y) (D : Subgroup (G₀ L S)) (hp : IsPGroup 2 D)
    (hm : D ≤ stabilizer (reducedFamily L S) m)
    (hDx : D ≤ stabilizer (reducedFamily L S) x)
    (hDy : D ≤ stabilizer (reducedFamily L S) y) : D ≤ Q (reducedFamily L S) m := by
  let F := reducedFamily L S
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hbase (j : Bool) {u v : Vertex F} (hu : (graph F).Adj (base F j) u)
      (hv : (graph F).Adj (base F j) v) (hne : u ≠ v)
      (E : Subgroup (G₀ L S)) (hE : IsPGroup 2 E)
      (hm : E ≤ stabilizer F (base F j)) (hEu : E ≤ stabilizer F u)
      (hEv : E ≤ stabilizer F v) : E ≤ Q F (base F j) := by
    by_cases hj : j = i
    · subst j
      exact source_linear_two_neighbor_core h i eLin hu hv hne E hE hm hEu hEv
    · have hj' : j = !i := by cases j <;> cases i <;> simp_all
      subst j
      exact source_suzuki_two_neighbor_core h (!i) eSuz hu hv hne E hE hm hEu hEv
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F m
  let c := (MulAut.conj g⁻¹).toMonoidHom
  have hx' : (graph F).Adj (base F m.type) (g⁻¹ • x) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F g⁻¹).map_adj_iff.mpr hx
    change (graph F).Adj (g⁻¹ • m) (g⁻¹ • x) at hh
    rwa [←hg, inv_smul_smul] at hh
  have hy' : (graph F).Adj (base F m.type) (g⁻¹ • y) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F g⁻¹).map_adj_iff.mpr hy
    change (graph F).Adj (g⁻¹ • m) (g⁻¹ • y) at hh
    rwa [←hg, inv_smul_smul] at hh
  have hm' : D.map c ≤ stabilizer F (base F m.type) := by
    have hh := map_mono (f := c) hm
    rw [←stabilizer_translate F, ←hg, inv_smul_smul] at hh
    exact hh
  have hD' : D.map c ≤ Q F (base F m.type) :=
    hbase m.type hx' hy' (fun he => hne ((MulAction.toPerm g⁻¹).injective he))
      (D.map c) (hp.map c) hm'
      (by simpa only [stabilizer_translate] using map_mono (f := c) hDx)
      (by simpa only [stabilizer_translate] using map_mono (f := c) hDy)
  intro d hd
  have hh := mem_map_of_mem (MulAut.conj g).toMonoidHom (hD' (mem_map_of_mem c hd))
  rw [←Q_translate F, hg] at hh
  change g * (g⁻¹ * d * g⁻¹⁻¹) * g⁻¹ ∈ Q F m at hh
  simpa only [inv_inv, mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right,
    mul_inv_cancel, mul_one] using hh

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer

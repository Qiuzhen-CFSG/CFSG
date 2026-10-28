module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSecondKernelUpper
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCenterDenominator
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.NeighborKernels

/-!
# Full second kernels in the nonbinary linear--Suzuki graph

The Suzuki star meets its full first kernel in its two-core. Thus it
commutes with that kernel modulo the two-core. Coprime lifting makes the
centralizer of every odd kernel subgroup transitive on the neighbors.
Together with the nonbinary linear endpoint, source 3.2(c) kills every
common odd subgroup of the two first kernels. Their intersection is
therefore the core intersection, and every full second kernel lies in Q.

The final application identifies the actual span centralizer with the
whole second kernel. Its denominator is the full source denominator in
(12.6), with the original markings and natural center retained.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
3.2(c), 6.2(d), and (12.6), printed pp.73,119,183.
-/

public noncomputable section
open Subgroup
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem kernel_odd_centralizer_transitive_of_commutator
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (_hvw : (graph (family P)).Adj v w)
    (hcomm : ⁅graphLocalGroup (family P) v,ballKernel (family P) v 1⁆ ≤ Q (family P) v)
    (D : Subgroup G)
    (hD : D ≤ ballKernel (family P) v 1) (ho : Odd (Nat.card D))
    (x y : (graph (family P)).neighborSet v) :
    ∃ g ∈ graphLocalGroup (family P) v ⊓ centralizer (D : Set G),
      g • x.val = y.val := by
  let := finite_endpoints h
  let Γ := family P
  let H := graphLocalGroup Γ v
  let N := pCore 2 H
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite D := Finite.of_injective
    (inclusion (hD.trans (ballKernel_le_stabilizer Γ v 1))) (inclusion_injective _)
  have hn : D ≤ normalizer (H : Set G) :=
    (hD.trans (ballKernel_le_stabilizer Γ v 1)).trans (sylowGenerated_normalized _)
  let : MulDistribMulAction D H := conjMulDistribMulActionOfLeNormalizer D H hn
  let : IsInvariant D H N := isInvariant_of_characteristic N
  have hp : IsPGroup 2 N := pCore_isPGroup
  have hcop : Nat.Coprime (Nat.card D) (Nat.card N) := by
    obtain ⟨k,hk⟩ := hp.exists_card_eq
    rw [hk]
    exact ho.coprime_two_right.pow_right k
  have hm : ⁅H,D⁆ ≤ N.map H.subtype := by
    have hcore : N.map H.subtype = Q Γ v := graphLocalGroup_core h v
    rw [hcore]
    exact (commutator_mono le_rfl hD).trans
      hcomm
  have hdis (d : D) (g : H) : g⁻¹ * (d • g) ∈ N := by
    have hh := commutator_le.mp (show ⁅D,H⁆ ≤ N.map H.subtype by
      rw [commutator_comm]; exact hm) d d.property g g.property
    obtain ⟨z,hz,he⟩ := hh
    have hz' : (d • g) * g⁻¹ ∈ N := by
      have he' : z = (d • g) * g⁻¹ := Subtype.ext he
      exact he' ▸ hz
    have heq : QuotientGroup.mk' N (d • g) = QuotientGroup.mk' N g := by
      have he := (QuotientGroup.eq_one_iff (N := N) _).mpr hz'
      change QuotientGroup.mk' N ((d • g) * g⁻¹) = 1 at he
      rw [map_mul,map_inv,mul_inv_eq_one] at he
      exact he
    exact QuotientGroup.eq.mp heq.symm
  obtain ⟨g,hg,hgxy⟩ := graphLocalGroup_transitive h hB hS v x y
  let gH : H := ⟨g,hg⟩
  obtain ⟨n,hnfix⟩ := Theory.GroupAction.exists_fixed_mul_of_solvable_coprime_displacement
    N (@IsNilpotent.to_isSolvable N _ hp.isNilpotent) hcop gH (fun d => hdis d gH)
  have hnQ : ((n : H) : G) ∈ Q Γ v :=
    (graphLocalGroup_core h v).le (mem_map_of_mem H.subtype n.property)
  refine ⟨g * ((n : H) : G),⟨H.mul_mem hg n.val.property,?_⟩,?_⟩
  · intro d hd
    have he := congrArg (fun z : H => (z : G)) (hnfix (⟨d,hd⟩ : D))
    change d * (g * ((n : H) : G)) * d⁻¹ = g * ((n : H) : G) at he
    exact mul_inv_eq_iff_eq_mul.mp he
  · rw [mul_smul]
    have hnK := (source_Z_Q_U h v).2 hnQ
    have hnx : ((n : H) : G) • x.val = x.val :=
      ((ballKernel_one_le_edge Γ x.property) hnK).2
    rw [hnx]
    exact hgxy

namespace ReducedLayer
open Reduction CommutingNontrivial BenderSuzuki.MatrixGroups
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Every common odd subgroup of the two literal base-edge first kernels vanishes. -/
theorem source_suzuki_odd_adjacent_kernels
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) {n : ℕ}
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      SuzukiMatrixGroup n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL(2,k))
    (hk : 4 ≤ Nat.card k) (D : Subgroup (G₀ L S))
    (hD : D ≤ U (reducedFamily L S) (base (reducedFamily L S) i) ⊓
      U (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (ho : Odd (Nat.card D)) : D = ⊥ := by
  let F := reducedFamily L S
  let v := base F i
  let w := base F (!i)
  let ht := reduced_triple h
  let : ∀ j, Finite (F j) := finite_endpoints ht
  have hadj : (graph F).Adj v w :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hcomm : ⁅graphLocalGroup F v,U F v⁆ ≤ Q F v := by
    rw [source_suzuki_graphLocalGroup_eq_star h i eSuz,←source_suzuki_star_kernel h i eSuz]
    exact le_inf
      (le_normalizer_iff_commutator_le_left.mp
        ((ballKernel_le_stabilizer F v 1).trans (by
          rw [←source_suzuki_graphLocalGroup_eq_star h i eSuz]
          exact sylowGenerated_normalized _)))
      (le_normalizer_iff_commutator_le_right.mp
        ((star_le_stabilizer i).trans (stabilizer_le_normalizer_ballKernel F v 1)))
  let eA : (graphLocalGroup F w ⧸ pCore 2 (graphLocalGroup F w)) ≃* SL(2,k) :=
    (QuotientGroup.congr _ _
      (MulEquiv.subgroupCongr (source_linear_graphLocalGroup_eq_star h (!i) eLin))
      (pCore_map_iso 2 _)).trans ((originalQuotient h (!i)).symm.trans eLin)
  apply source_normalized_edge_eq_bot ht hadj D
    (le_inf ((hD.trans inf_le_left).trans (ballKernel_le_stabilizer F v 1))
      ((hD.trans inf_le_right).trans (ballKernel_le_stabilizer F w 1)))
  · intro z hz
    obtain ⟨g,hg,he⟩ := kernel_odd_centralizer_transitive_of_commutator ht
      (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hadj hcomm D
      (hD.trans inf_le_left) ho ⟨w,hadj⟩ ⟨z,hz⟩
    exact ⟨g,Subgroup.centralizer_le_normalizer _ hg.2,he⟩
  · intro z hz
    obtain ⟨g,hg,he⟩ := CommutingTrivial.nonbinary_kernel_odd_centralizer_transitive ht
      (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hadj.symm eA hk D
      (hD.trans inf_le_right) ho ⟨v,hadj.symm⟩ ⟨z,hz⟩
    exact ⟨g,Subgroup.centralizer_le_normalizer _ hg.2,he⟩

/-- The full base-edge first-kernel intersection is exactly the two-core intersection. -/
theorem source_suzuki_adjacent_kernel_intersection
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) {n : ℕ}
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      SuzukiMatrixGroup n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL(2,k))
    (hk : 4 ≤ Nat.card k) :
    U (reducedFamily L S) (base (reducedFamily L S) i) ⊓
      U (reducedFamily L S) (base (reducedFamily L S) (!i)) =
    Q (reducedFamily L S) (base (reducedFamily L S) i) ⊓
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) := by
  let F := reducedFamily L S
  let v := base F i
  let w := base F (!i)
  let E := stabilizer F v ⊓ stabilizer F w
  let W := U F v ⊓ U F w
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hadj : (graph F).Adj v w :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hWE : W ≤ E := inf_le_left.trans (ballKernel_one_le_edge F hadj)
  let : Finite E := Finite.of_injective (inclusion (show E ≤ stabilizer F v from inf_le_left))
    (inclusion_injective _)
  let : Finite W := Finite.of_injective (inclusion hWE) (inclusion_injective _)
  obtain ⟨D,hDW,_,hgen,hcop⟩ := exists_complement_le_of_core_supplement 2 W W le_rfl
    (core_sylow_of_le E W hWE (source_edge_core_sylow (reduced_triple h)
      (reduced_borel_core_sylow h) hadj))
    (sup_eq_left.mpr (pCoreIn_le 2 W))
  have hDb := source_suzuki_odd_adjacent_kernels h i eSuz eLin hk D hDW
    (Nat.coprime_two_left.mp hcop)
  rw [hDb,bot_sup_eq] at hgen
  have hp : IsPGroup 2 W := hgen ▸ isPGroup_pCoreIn 2 W
  exact le_antisymm
    (le_inf (CommutingTrivial.two_subgroup_le_Q F v (reduced_kernel_sylow h v) hp inf_le_left)
      (CommutingTrivial.two_subgroup_le_Q F w (reduced_kernel_sylow h w) hp inf_le_right))
    (inf_le_inf (source_Z_Q_U (reduced_triple h) v).2 (source_Z_Q_U (reduced_triple h) w).2)

/-- Every full second kernel in the mixed source graph is a two-group inside its core. -/
theorem source_suzuki_second_kernel_le_core
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) {n : ℕ}
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      SuzukiMatrixGroup n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL(2,k))
    (hk : 4 ≤ Nat.card k) (v : Vertex (reducedFamily L S)) :
    ballKernel (reducedFamily L S) v 2 ≤ Q (reducedFamily L S) v := by
  let F := reducedFamily L S
  have hbase := source_suzuki_adjacent_kernel_intersection h i eSuz eLin hk
  have hsecond (j : Bool) : ballKernel F (base F j) 2 ≤ Q F (base F j) := by
    have hadj : (graph F).Adj (base F j) (base F (!j)) :=
      ⟨by change j ≠ !j; cases j <;> decide, Subgroup.CosetGeometry.incident_base F j (!j)⟩
    have hle := le_inf (ballKernel_antitone F (base F j) (by decide : 1 ≤ 2))
      (ballKernel_succ_le F hadj 1)
    by_cases hj : j = i
    · subst j
      exact (hle.trans hbase.le).trans inf_le_left
    · have hj' : j = !i := by cases j <;> cases i <;> simp_all
      subst j
      have hh : U F (base F (!i)) ⊓ U F (base F (!(!i))) =
          Q F (base F (!i)) ⊓ Q F (base F (!(!i))) := by
        simpa only [Bool.not_not,inf_comm] using hbase
      exact (hle.trans hh.le).trans inf_le_left
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  have hm := map_mono (f := (MulAut.conj g).toMonoidHom) (hsecond v.type)
  rwa [←ballKernel_translate F,←Q_translate F,hg] at hm

/-- The original span action has the full second kernel as its literal denominator. -/
theorem source_suzuki_second_kernel_centralizer
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) {n : ℕ}
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      SuzukiMatrixGroup n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL(2,k))
    (hk : 4 ≤ Nat.card k)
    (hplace : Q (reducedFamily L S) (base (reducedFamily L S) i) ≤ star L S (!i))
    (hnat : Noncommuting.HasNaturalCenter (star L S (!i))
      (Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
      (Q (reducedFamily L S) (base (reducedFamily L S) (!i)))) :
    let F := reducedFamily L S
    let v := base F i
    Q F v ⊓ centralizer (V F v 1 : Set (G₀ L S)) = ballKernel F v 2 := by
  exact (source_core_span_centralizer_eq_second_kernel h i hplace hnat).trans
    (inf_eq_right.mpr (source_suzuki_second_kernel_le_core h i eSuz eLin hk _))

end ReducedLayer
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile

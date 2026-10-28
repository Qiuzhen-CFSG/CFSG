module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiEightPathBound
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiFullThirdKernel
/-!
# The exact two-core of a linear-centered eight-path fixer

The full third kernel H is elementary of order q³ and fixes the seven
interior vertices of an eight-path centered at the linear vertex. Each
endpoint restriction has index at most q, by the original elementary
local-action bounds. Its intersection with the path fixer therefore has
order at least q. The odd nine-path theorem supplies the matching upper
bound for every two-subgroup of that fixer. Relative normality of H now
identifies the entire path two-core with this intersection and puts every
two-subgroup of the path fixer in H.

This is the order and containment step used by the torus-centralizer
argument in DGS85 (12.9), printed p.189. Torus fixation of a suitable
eight-path remains to be proved. All original earlier-source hypotheses
and the literal completion inclusion are retained.
-/
public noncomputable section
open Subgroup SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
open Theory.GroupTheory.AmalgamGraph BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
/-- The original eight-path two-core is its intersection with the full third kernel. -/
theorem source_suzuki_eight_path_core
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb3 : b (reducedFamily L S) = 3)
    {a x σ : Vertex (reducedFamily L S)}
    (hxadj : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x)
    (hne : x ≠ base (reducedFamily L S) (!i))
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k)
    (hz : center (star L S i) = ⊥)
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzx : Z (reducedFamily L S) x ≤ Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hcommx : ⁅V (reducedFamily L S) x 1, Q (reducedFamily L S) x⁆ ≤ Z (reducedFamily L S) x)
    (hcommy : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ =
        Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcross : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) σ,
      V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥)
    (hsmall : (Q (reducedFamily L S) σ).relIndex
      (V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1) ≤ Nat.card k)
    (hactor : (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex
      (V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (hfield : Nat.card k = 2 ^ (2 * n + 1))
    (Ry : Sylow 2 (star L S (!i)))
    (hRy : (Ry : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) (!i)))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i))
    (hnat : Noncommuting.HasNaturalCenter (star L S i)
      (Z (reducedFamily L S) (base (reducedFamily L S) i))
      (Q (reducedFamily L S) (base (reducedFamily L S) i)))
    (hbranch : ⁅V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥)
    {v₀ : Vertex (reducedFamily L S)}
    (p : BasedWalk (graph (reducedFamily L S)) 8 v₀) (hp : p.Nonbacktracking)
    (hmid : (p.2.2.2.1 : Vertex (reducedFamily L S)) = base (reducedFamily L S) i) :
    let F := reducedFamily L S
    let H := ballKernel F (base F i) 3
    let P := pathStabilizer F p
    P.pCoreIn 2 = H ⊓ P ∧
      Nat.card (P.pCoreIn 2) = Nat.card k ∧
      (P.map (G₀ L S).subtype).pCoreIn 2 = (H ⊓ P).map (G₀ L S).subtype ∧
      ∀ D : Subgroup (G₀ L S), IsPGroup 2 D → D ≤ P → D ≤ H := by
  let F := reducedFamily L S
  let m := base F i
  let H := ballKernel F m 3
  let P := pathStabilizer F p
  change (p.2.2.2.1 : Vertex F) = m at hmid
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hb : 2 < b F := by change 2 < b (reducedFamily L S); omega
  have hthird := source_suzuki_third_kernel_layer h i hb hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat
  have hH := (source_suzuki_full_linear_third_kernel h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch).1
  let : IsElementaryAbelian 2 (V F x 1) := V_elementary F (reduced_triple h).generate
    (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb x
  let : IsElementaryAbelian 2 H := IsElementaryAbelian.of_injective
    (inclusion (hH.le.trans inf_le_left)) (inclusion_injective _)
  let : Finite H := Finite.of_injective (inclusion (ballKernel_le_stabilizer F m 3)) (inclusion_injective _)
  let : Finite P := Finite.of_injective (inclusion (pathStabilizer_le F p)) (inclusion_injective _)
  have hHcard : Nat.card H = Nat.card k ^ 3 := by
    rw [show H = V F x 1 ⊓ V F (base F (!i)) 1 from hH,hfield]
    exact hthird.2.2.2.2.2.2.2.2.1
  have hvi : v₀.type = i := by
    have h₁ := Bool.eq_not_iff.mpr p.1.property.1
    have h₂ := Bool.eq_not_iff.mpr p.2.1.property.1
    have h₃ := Bool.eq_not_iff.mpr p.2.2.1.property.1
    have h₄ := Bool.eq_not_iff.mpr p.2.2.2.1.property.1
    rw [h₁,h₂,h₃,h₄,hmid]
    simp only [Bool.not_not]
    rfl
  have upper (D : Subgroup (G₀ L S)) (hD : IsPGroup 2 D) (hDP : D ≤ P) :
      Nat.card D ≤ Nat.card k :=
    (source_suzuki_eight_path_two_subgroup_bound h i hb3 T hT e hz hcard hcardy
      hzy hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hmin hnat hxadj hne hbranch
      p hp hvi D hD hDP).1
  have step {v w : Vertex F} (hvw : (graph F).Adj v w)
      (D : Subgroup (G₀ L S)) [IsElementaryAbelian 2 D]
      (hDv : D ≤ stabilizer F v) : (stabilizer F w).relIndex D ≤ Nat.card k := by
    let : Finite D := Finite.of_injective (inclusion hDv) (inclusion_injective _)
    have hi := source_linear_suzuki_elementary_local_index h i hn e eSuz hfield v D hDv
    rw [←hfield] at hi
    exact (relIndex_le_of_le_left
      ((source_Z_Q_U (reduced_triple h) v).2.trans
        ((ballKernel_one_le_edge F hvw).trans inf_le_right)) index_ne_zero_of_finite).trans hi
  have hmidP : P ≤ stabilizer F m := by
    intro g hg
    rw [←hmid]
    exact hg _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (origin_mem_vertices F p.2.2.2.2)))))
  have hHPnorm : P ≤ normalizer (H ⊓ P : Set (G₀ L S)) :=
    (le_inf (hmidP.trans (stabilizer_le_normalizer_ballKernel F m 3)) P.le_normalizer).trans
      inf_normalizer_le_normalizer_inf
  let J := H ⊓ P
  let : Finite J := Finite.of_injective (inclusion (show J ≤ P from inf_le_right)) (inclusion_injective _)
  have hpJ : IsPGroup 2 J := (IsElementaryAbelian.isPGroup 2 H).to_le inf_le_left
  have lower : Nat.card k ≤ Nat.card J := by
    have hleft2 : H ≤ ballKernel F (p.2.2.1 : Vertex F) 2 := by
      rw [show H = ballKernel F m 3 from rfl,←hmid]
      exact ballKernel_succ_le F p.2.2.2.1.property.symm 2
    have hleft1 := hleft2.trans (ballKernel_succ_le F p.2.2.1.property.symm 1)
    have hleft0 := hleft1.trans (ballKernel_succ_le F p.2.1.property.symm 0)
    have hright2 : H ≤ ballKernel F (p.2.2.2.2.1 : Vertex F) 2 := by
      rw [show H = ballKernel F m 3 from rfl,←hmid]
      exact ballKernel_succ_le F p.2.2.2.2.1.property 2
    have hright1 := hright2.trans (ballKernel_succ_le F p.2.2.2.2.2.1.property 1)
    have hright0 := hright1.trans (ballKernel_succ_le F p.2.2.2.2.2.2.1.property 0)
    let A := H ⊓ stabilizer F v₀
    let B := A ⊓ stabilizer F p.endpoint
    let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_injective
      (inclusion (show A ≤ H from inf_le_left)) (inclusion_injective _)
    let : Finite A := Finite.of_injective (inclusion (show A ≤ H from inf_le_left)) (inclusion_injective _)
    let : Finite B := Finite.of_injective (inclusion (show B ≤ A from inf_le_left)) (inclusion_injective _)
    have hiA : A.relIndex H ≤ Nat.card k := by
      rw [show A = H ⊓ stabilizer F v₀ from rfl,inf_relIndex_left]
      exact step p.1.property.symm H (hleft0.trans (ballKernel_le_stabilizer F _ 0))
    have hiB : B.relIndex A ≤ Nat.card k := by
      rw [show B = A ⊓ stabilizer F p.endpoint from rfl,inf_relIndex_left]
      exact step p.2.2.2.2.2.2.2.1.property A
        (inf_le_left.trans (hright0.trans (ballKernel_le_stabilizer F _ 0)))
    have hBJ : B = J := by
      ext g
      constructor
      · rintro ⟨⟨hg,hg₀⟩,hg₈⟩
        refine ⟨hg,?_⟩
        intro z hz
        change z ∈ v₀ :: (p.1 : Vertex F) :: (p.2.1 : Vertex F) ::
          (p.2.2.1 : Vertex F) :: (p.2.2.2.1 : Vertex F) ::
          (p.2.2.2.2.1 : Vertex F) :: (p.2.2.2.2.2.1 : Vertex F) ::
          (p.2.2.2.2.2.2.1 : Vertex F) :: [p.endpoint] at hz
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact hg₀
        · exact ballKernel_le_stabilizer F _ 0 (hleft0 hg)
        · exact ballKernel_le_stabilizer F _ 1 (hleft1 hg)
        · exact ballKernel_le_stabilizer F _ 2 (hleft2 hg)
        · rw [hmid]; exact ballKernel_le_stabilizer F m 3 hg
        · exact ballKernel_le_stabilizer F _ 2 (hright2 hg)
        · exact ballKernel_le_stabilizer F _ 1 (hright1 hg)
        · exact ballKernel_le_stabilizer F _ 0 (hright0 hg)
        · exact hg₈
      · rintro ⟨hg,hgp⟩
        exact ⟨⟨hg,pathStabilizer_le F p hgp⟩,
          hgp _ (by rw [←BasedWalk.support_toWalk]; exact p.toWalk.end_mem_support)⟩
    have hmA := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) A H bot_le inf_le_left
    have hmB := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) B A bot_le inf_le_left
    rw [relIndex_bot_left,relIndex_bot_left] at hmA hmB
    have hbound : Nat.card k ^ 3 ≤ Nat.card J * Nat.card k ^ 2 := by
      calc Nat.card k ^ 3 = Nat.card H := hHcard.symm
           _ = (Nat.card B * B.relIndex A) * A.relIndex H := by rw [←hmA,←hmB]
           _ ≤ (Nat.card B * Nat.card k) * Nat.card k := Nat.mul_le_mul (Nat.mul_le_mul_left _ hiB) hiA
           _ = Nat.card J * Nat.card k ^ 2 := by rw [hBJ]; ring
    apply Nat.le_of_mul_le_mul_right (c := Nat.card k ^ 2) _ (pow_pos Nat.card_pos _)
    calc Nat.card k * Nat.card k ^ 2 = Nat.card k ^ 3 := by ring
         _ ≤ Nat.card J * Nat.card k ^ 2 := hbound
  have hJcard : Nat.card J = Nat.card k := le_antisymm (upper J hpJ inf_le_right) lower
  have hJcore : J ≤ P.pCoreIn 2 := le_pCoreIn_of_normalizes hpJ inf_le_right hHPnorm
  let : Finite (P.pCoreIn 2) := Finite.of_injective
    (inclusion (pCoreIn_le 2 P)) (inclusion_injective _)
  have hcore : P.pCoreIn 2 = J :=
    (eq_of_le_of_card_ge hJcore (by rw [hJcard]; exact upper _ (isPGroup_pCoreIn 2 P) (pCoreIn_le 2 P))).symm
  refine ⟨hcore,by rw [hcore]; exact hJcard,?_,?_⟩
  · change (P.map (G₀ L S).subtype).pCoreIn 2 = J.map (G₀ L S).subtype
    rw [Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective
      2 (G₀ L S).subtype (G₀ L S).subtype_injective,hcore]
  · intro D hD hDP
    have hsup : IsPGroup 2 (D ⊔ J : Subgroup (G₀ L S)) :=
      hD.to_sup_of_normal_right' hpJ (hDP.trans hHPnorm)
    let : Finite (D ⊔ J : Subgroup (G₀ L S)) := Finite.of_injective
      (inclusion (sup_le hDP (show J ≤ P from inf_le_right))) (inclusion_injective _)
    have he : J = D ⊔ J := eq_of_le_of_card_ge le_sup_right (by
      rw [hJcard]; exact upper _ hsup (sup_le hDP inf_le_right))
    exact (le_sup_left.trans he.ge).trans inf_le_left
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer

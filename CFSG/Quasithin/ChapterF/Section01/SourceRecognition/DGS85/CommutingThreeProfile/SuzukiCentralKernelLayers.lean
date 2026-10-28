module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiExactCoreOrders
public import Theory.GroupTheory.PResidual.PerfectImage
public import Theory.SpecificGroups.Suzuki.SchurCoverReduction

/-!
# The central quotients of the full kernels

For K = G_beta^(2) and Y = V_beta, the residual calculation already gives
[K,O²(L_beta)] = Y. The derived-core identity kills the action of Q_beta
on K/Y. Since the nonbinary Suzuki quotient is perfect, Q_beta together
with that residual generates L_beta. Thus [K,L_beta] = Y.

The exact orders |K| = q⁶ and |Y| = q⁵ give |K/Y| = q, and the proved
Frattini bound makes this literal quotient elementary abelian. Its
trivial action is identified with original endpoint conjugation, and
the commutator equality is retained after the completion inclusion.

The full linear third kernel is the already identified intersection of
neighboring spans. Its commutator with the linear endpoint is Z_alpha.
This constructs its central elementary quotient of order q with the
same original conjugation formula.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.9)(c2),(c4), printed pp.186,188. All earlier source inputs are retained.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The actual Suzuki second-kernel quotient is the central elementary module of order q. -/
theorem source_suzuki_neighbor_kernel_central
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
    (hnear : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) x,
      V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥) :
    let F := reducedFamily L S
    let y := base F (!i)
    let A := star L S (!i)
    let K := ballKernel F y 2
    let Y := V F y 1
    ∃ hAK : A ≤ normalizer (K : Set (G₀ L S)),
    ∃ hY : (Y.subgroupOf K).Normal,
      let := hY
      ∃ hEl : IsElementaryAbelian 2 (K ⧸ Y.subgroupOf K),
      let := hEl
      Nat.card (K ⧸ Y.subgroupOf K) = Nat.card k ∧
      ⁅K,A⁆ = Y ∧
      ⁅K.map (G₀ L S).subtype,starredParabolic L S (if !i then 1 else 0)⁆ = Y.map (G₀ L S).subtype ∧
      ∃ ρ : Representation (ZMod 2)
        (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0)))
        (Additive (K ⧸ Y.subgroupOf K)),
        ρ = 1 ∧
        ∀ u : L (if !i then 1 else 0), ∀ v : K,
          (ρ (QuotientGroup.mk u) (Additive.ofMul (QuotientGroup.mk v))).toMul =
            QuotientGroup.mk ⟨(originalActor (L := L) (S := S) (!i) u : G₀ L S) * v *
              (originalActor (L := L) (S := S) (!i) u : G₀ L S)⁻¹,
              (mem_normalizer_iff.mp (hAK
                (originalActor (L := L) (S := S) (!i) u).property) v).mp v.property⟩ := by
  let F := reducedFamily L S
  let y := base F (!i)
  let A := star L S (!i)
  let K := ballKernel F y 2
  let Y := V F y 1
  let D := (pResidual 2 A).map A.subtype
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite A := Finite.of_injective (inclusion (star_le_stabilizer (!i))) (inclusion_injective _)
  let : Finite K := Finite.of_injective (inclusion (ballKernel_le_stabilizer F y 2)) (inclusion_injective _)
  have hb : 2 < b F := by change 2 < b (reducedFamily L S); omega
  obtain ⟨hAK,hY,_,hKD,_,_,_⟩ := source_suzuki_neighbor_kernel_residual_action h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch
  let := hY
  have hAY : A ≤ normalizer (Y : Set (G₀ L S)) :=
    (star_le_stabilizer (!i)).trans (stabilizer_normalizes_V F y 1)
  have hQA : Q F y ≤ A := by rw [←star_core h (!i)]; exact map_subtype_le _
  have hk : 4 ≤ Nat.card k := by
    rw [hfield]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : 2 ≤ 2*n+1)
  have hKQ : K ≤ Q F y := source_suzuki_second_kernel_le_core h (!i) eSuz
    (by cases i <;> exact e) hk y
  have hQderived := (source_suzuki_core_derived_eq_span h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear).1
  let eA := (originalQuotient h (!i)).symm.trans eSuz
  let π := eA.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hπ : Function.Surjective π := eA.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = pCore 2 A :=
    (MonoidHom.ker_comp_of_injective _ _ eA.injective).trans (QuotientGroup.ker_mk' _)
  let : Group.IsPerfect (SuzukiMatrixGroup n) := SchurCover.isPerfect n hn
  have him : (pResidual 2 A).map π = ⊤ :=
    (map_pResidual_of_surjective 2 π hπ).trans (pResidual_eq_top_of_isPerfect 2)
  have hs : pResidual 2 A ⊔ pCore 2 A = ⊤ := by
    rw [←hker,←Subgroup.comap_map_eq,him,Subgroup.comap_top]
  have hgen : D ⊔ Q F y = A := by
    have hh := congrArg (Subgroup.map A.subtype) hs
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hh
    change D ⊔ A.pCoreIn 2 = A at hh
    change D ⊔ (star L S (!i)).pCoreIn 2 = A at hh
    rw [star_core h (!i)] at hh
    exact hh
  have hKA : ⁅K,A⁆ = Y := by
    apply le_antisymm
    · rw [commutator_comm,←hgen]
      exact commutator_sup_le_of_relative_normal A D (Q F y) K Y hAY
        (map_subtype_le _) hQA (by rw [commutator_comm]; exact hKD.le)
        ((commutator_mono le_rfl hKQ).trans hQderived.le)
    · exact hKD.ge.trans (commutator_mono le_rfl (map_subtype_le _))
  have hYK : Y ≤ K := V_le_ballKernel F (reduced_triple h).generate y
    (by change 3 ≤ b (reducedFamily L S); omega)
  have hphi : (frattini K).map K.subtype ≤ Y :=
    (source_suzuki_neighbor_kernel_frattini h i hb3 hxadj hne T R hT hR e hz
      hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch).2.trans
        (Z_le_V F y 1)
  have hel : IsElementaryAbelian 2 (K ⧸ Y.subgroupOf K) :=
    elementary_quotient_of_frattini_le ((isPGroup_pCoreIn 2 _).to_le hKQ) _
      (map_le_iff_le_comap.mp hphi)
  have hKcard := (source_suzuki_exact_core_orders h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear).2.2.2.2.1
  have hYcard : Nat.card Y = Nat.card k ^ 5 := by
    simpa only [hfield] using (source_suzuki_center_layer_of_intersection h i hb hxadj hne T R hT hR e hz
      hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat).2.1
  have hcardKY : Nat.card (K ⧸ Y.subgroupOf K) = Nat.card k := by
    have hh := (Y.subgroupOf K).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hYK).toEquiv,hYcard,index_eq_card,hKcard] at hh
    exact Nat.eq_of_mul_eq_mul_left (pow_pos Nat.card_pos 5) (hh.trans (by ring))
  let := hel
  refine ⟨hAK,hY,hel,hcardKY,hKA,?_,1,rfl,?_⟩
  · have hh := congrArg (Subgroup.map (G₀ L S).subtype) hKA
    rw [map_commutator] at hh
    simpa only [A,star,map_subgroupOf_eq_of_le (star_le_completion (if !i then 1 else 0))] using hh
  · intro u v
    change QuotientGroup.mk v = QuotientGroup.mk _
    symm
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (originalActor (L := L) (S := S) (!i) u : G₀ L S) * (v : G₀ L S) *
      (originalActor (L := L) (S := S) (!i) u : G₀ L S)⁻¹ / v ∈ Y
    have hh := (commutator_le.mp (by rw [commutator_comm]; exact hKA.le : ⁅A,K⁆ ≤ Y))
      (originalActor (L := L) (S := S) (!i) u : G₀ L S)
      (originalActor (L := L) (S := S) (!i) u).property v v.property
    simpa only [commutatorElement_def,div_eq_mul_inv] using hh

/-- The full linear third kernel modulo the original center is the central module of order q. -/
theorem source_suzuki_linear_third_kernel_central
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
 :
    let F := reducedFamily L S
    let m := base F i
    let A := star L S i
    let H := ballKernel F m 3
    let Zm := Z F m
    ∃ hAH : A ≤ normalizer (H : Set (G₀ L S)),
    ∃ hZ : (Zm.subgroupOf H).Normal,
      let := hZ
      ∃ hEl : IsElementaryAbelian 2 (H ⧸ Zm.subgroupOf H),
      let := hEl
      Nat.card (H ⧸ Zm.subgroupOf H) = Nat.card k ∧
      ⁅H,A⁆ = Zm ∧
      ⁅H.map (G₀ L S).subtype,starredParabolic L S (if i then 1 else 0)⁆ = Zm.map (G₀ L S).subtype ∧
      ∃ ρ : Representation (ZMod 2)
        (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0)))
        (Additive (H ⧸ Zm.subgroupOf H)),
        ρ = 1 ∧
        ∀ u : L (if i then 1 else 0), ∀ v : H,
          (ρ (QuotientGroup.mk u) (Additive.ofMul (QuotientGroup.mk v))).toMul =
            QuotientGroup.mk ⟨(originalActor (L := L) (S := S) i u : G₀ L S) * v *
              (originalActor (L := L) (S := S) i u : G₀ L S)⁻¹,
              (mem_normalizer_iff.mp (hAH
                (originalActor (L := L) (S := S) i u).property) v).mp v.property⟩ := by
  let F := reducedFamily L S
  let m := base F i
  let H := ballKernel F m 3
  let Zm := Z F m
  let A := star L S i
  have hb : 2 < b F := by change 2 < b (reducedFamily L S); omega
  have hEq := (source_suzuki_full_linear_third_kernel h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch).1
  obtain ⟨_,_,_,_,_,hcomm,_,hindex,_,_,horig⟩ := source_suzuki_third_kernel_layer h i hb hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat
  have hHA : ⁅H,A⁆ = Zm := by change ⁅ballKernel F m 3,A⁆ = Zm; rw [hEq]; exact hcomm
  have hZindex : Zm.relIndex H = Nat.card k := by
    change (Z F m).relIndex (ballKernel F m 3) = Nat.card k
    rw [hEq,hfield]
    exact hindex
  have hAH : A ≤ normalizer (H : Set (G₀ L S)) :=
    (star_le_stabilizer i).trans (stabilizer_le_normalizer_ballKernel F m 3)
  let : IsElementaryAbelian 2 (V F x 1) := V_elementary F (reduced_triple h).generate
    (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb x
  let : IsElementaryAbelian 2 H := IsElementaryAbelian.of_le (show H ≤ V F x 1 from hEq.le.trans inf_le_left)
  let hZ : (Zm.subgroupOf H).Normal := normal_of_isMulCommutative _
  let := hZ
  let hEl : IsElementaryAbelian 2 (H ⧸ Zm.subgroupOf H) :=
    IsElementaryAbelian.of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  let := hEl
  refine ⟨hAH,hZ,hEl,?_,hHA,?_,1,rfl,?_⟩
  · rw [←index_eq_card]
    exact hZindex
  · change ⁅(ballKernel F m 3).map (G₀ L S).subtype,_⁆ = _
    rw [hEq]
    exact horig
  · intro u v
    change QuotientGroup.mk v = QuotientGroup.mk _
    symm
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (originalActor (L := L) (S := S) i u : G₀ L S) * (v : G₀ L S) *
      (originalActor (L := L) (S := S) i u : G₀ L S)⁻¹ / v ∈ Zm
    have hh := (commutator_le.mp (by rw [commutator_comm]; exact hHA.le : ⁅A,H⁆ ≤ Zm))
      (originalActor (L := L) (S := S) i u : G₀ L S)
      (originalActor (L := L) (S := S) i u).property v v.property
    simpa only [commutatorElement_def,div_eq_mul_inv] using hh

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer

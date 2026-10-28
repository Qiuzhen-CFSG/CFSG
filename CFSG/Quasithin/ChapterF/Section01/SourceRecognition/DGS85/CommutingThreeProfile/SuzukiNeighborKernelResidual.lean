module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiFullCoreUpper
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCenterLayer
public import Theory.Representation.Suzuki.SmallTwoGroupAction
public import Theory.GroupTheory.Commutator.ElementaryResidualGeneration
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.Frattini.QuadraticCentralizer

/-!
# Residual action on the full Suzuki second kernel

At the Suzuki vertex y put K = G_y^(2), Y = V_y and A = star_y.
The proved bounds |K| ≤ q⁶ and |Y| = q⁵ give |K/Y| ≤ q. The actual
conjugation action of A on K/Y has trivial two-residual action: a moving
Suzuki residual would require fixed index at least q². Since Y is generated
by A-commutators, binary residual generation gives the exact identity
[K,O²(A)] = Y. Finally K centralizes the elementary Y, so its squares,
and hence its Frattini subgroup, centralize O²(A).

The final statement retains the literal full permutation kernel, the
original endpoint action on quotient representatives, and the completion
inclusion on the commutator equality. All earlier source hypotheses remain
explicit. This supplies the neighboring-kernel action needed before the
source derived-core and C_(Q_alpha)(H)/W analysis; it does not assert those
later conclusions or the second-kernel equality at the linear vertex.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
proof of (12.9), printed pp.188--189, especially the action preceding (3).
-/
public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The literal small quotient is fixed by the Suzuki residual, whose
commutator with the full second kernel is exactly the neighboring span. -/
theorem source_suzuki_neighbor_kernel_residual_action
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
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥) :
    let F := reducedFamily L S
    let y := base F (!i)
    let A := star L S (!i)
    let K := ballKernel F y 2
    let Y := V F y 1
    let R := (pResidual 2 A).map A.subtype
    ∃ hAK : A ≤ normalizer (K : Set (G₀ L S)),
    ∃ hY : (Y.subgroupOf K).Normal,
      let := hY
      Nat.card (K ⧸ Y.subgroupOf K) ≤ Nat.card k ∧
      ⁅K,R⁆ = Y ∧
      (frattini K).map K.subtype ≤ centralizer (R : Set (G₀ L S)) ∧
      ⁅K.map (G₀ L S).subtype,R.map (G₀ L S).subtype⁆ = Y.map (G₀ L S).subtype ∧
      ∃ ρ : A →* MulAut (K ⧸ Y.subgroupOf K),
        pResidual 2 A ≤ ρ.ker ∧
        ∀ u : L (if !i then 1 else 0), ∀ v : K,
          ρ (originalActor (L := L) (S := S) (!i) u) (QuotientGroup.mk v) =
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
  let q := 2^(2*n+1)
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite A := Finite.of_injective (inclusion (star_le_stabilizer (!i)))
    (inclusion_injective _)
  let : Finite K := Finite.of_injective (inclusion (ballKernel_le_stabilizer F y 2))
    (inclusion_injective _)
  have hb : 2 < b F := by change 2 < b (reducedFamily L S); omega
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  let : IsElementaryAbelian 2 Y := V_elementary F (reduced_triple h).generate
    hZ (reduced_kernel_sylow h) hb y
  have hYK : Y ≤ K := V_le_ballKernel F (reduced_triple h).generate y
    (by change 3 ≤ b (reducedFamily L S); omega)
  let : Finite Y := Finite.of_injective (inclusion hYK) (inclusion_injective _)
  have hk : 4 ≤ Nat.card k := by
    rw [hfield]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : 2 ≤ 2*n+1)
  have hKQ : K ≤ Q F y := source_suzuki_second_kernel_le_core h (!i) eSuz
    (by cases i <;> exact e) hk y
  have hpK : IsPGroup 2 K := (isPGroup_pCoreIn 2 _).to_le hKQ
  have hAK : A ≤ normalizer (K : Set (G₀ L S)) :=
    (star_le_stabilizer (!i)).trans (stabilizer_le_normalizer_ballKernel F y 2)
  have hAY : A ≤ normalizer (Y : Set (G₀ L S)) :=
    (star_le_stabilizer (!i)).trans (stabilizer_normalizes_V F y 1)
  have hQyA : Q F y ≤ star L S i := (le_sup_left.trans hT.ge).trans (map_subtype_le _)
  have hKY : K ≤ centralizer (Y : Set (G₀ L S)) :=
    (source_suzuki_second_kernel_centralizer h (!i) eSuz
      (by cases i <;> exact e) hk (by cases i <;> exact hQyA)
      (by cases i <;> exact hnat)).ge.trans inf_le_right
  let hY : (Y.subgroupOf K).Normal := normal_subgroupOf_of_le_normalizer
    (hKY.trans (Subgroup.centralizer_le_normalizer _))
  let := hY
  have hYcard : Nat.card Y = q^5 :=
    (source_suzuki_center_layer_of_intersection h i hb hxadj hne T R hT hR e hz hcard hcardy
      hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat).2.1
  have hfull := (source_suzuki_product_and_intersection_commutator h i hb hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin).2.2.2.1
  have hKcard : Nat.card K ≤ q^6 :=
    (source_suzuki_full_second_kernel_upper h i hb3 T hT e hz hcard hcardy hzy hcommy
      hcross hsmall hactor hn eSuz hfield Ry hRy hmin hnat hxadj hne hbranch hfull).1
  have hindex : Nat.card (K ⧸ Y.subgroupOf K) ≤ q := by
    have hh := (Y.subgroupOf K).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hYK).toEquiv,hYcard,index_eq_card] at hh
    apply Nat.le_of_mul_le_mul_left (c := q^5) _ (by dsimp [q]; positivity)
    calc q^5 * Nat.card (K ⧸ Y.subgroupOf K) = Nat.card K := hh
         _ ≤ q^6 := hKcard
         _ = q^5*q := by ring
  obtain ⟨ρ,hρ⟩ := exists_quotient_conjugation_action A K Y hAK hAY hY
  let eA := (originalQuotient h (!i)).symm.trans eSuz
  let π := eA.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hπ : Function.Surjective π := eA.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = pCore 2 A := by
    exact (MonoidHom.ker_comp_of_injective _ _ eA.injective).trans (QuotientGroup.ker_mk' _)
  have hzero : pResidual 2 A ≤ ρ.ker :=
    Representation.Suzuki.residual_le_action_kernel_of_small_card hn π hπ
      (hker ▸ pCore_isPGroup) (hpK.to_quotient _) (hindex.trans_lt (by
        have hq : 1 < q := Nat.one_lt_pow (by omega) (by decide)
        change q < q^2
        nlinarith)) ρ
  have hcomm : ⁅K,D⁆ ≤ Y := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro r hr v hv
    obtain ⟨u,hu,rfl⟩ := hr
    have hh := DFunLike.congr_fun (hzero hu)
      (QuotientGroup.mk' (Y.subgroupOf K) (⟨v,hv⟩ : K))
    change ρ u (QuotientGroup.mk' (Y.subgroupOf K) ⟨v,hv⟩) =
      QuotientGroup.mk' (Y.subgroupOf K) ⟨v,hv⟩ at hh
    rw [hρ] at hh
    have hc := QuotientGroup.eq_iff_div_mem.mp hh
    change (u : G₀ L S) * v * (u : G₀ L S)⁻¹ / v ∈ Y at hc
    simpa only [commutatorElement_def,div_eq_mul_inv,Subgroup.subtype_apply] using hc
  have hYres : ⁅Y,D⁆ = Y := elementary_commutator_pResidual_eq_self A Y
    ((V_le_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb y).trans (by
      rw [←star_core h (!i)]; exact pCoreIn_le 2 _)) hAY hfull.symm
  have heq : ⁅K,D⁆ = Y := le_antisymm hcomm
    (hYres.ge.trans (commutator_mono hYK le_rfl))
  refine ⟨hAK,hY,?_,heq,
    frattini_image_le_centralizer_of_elementary_commutator K D Y hpK hcomm hKY,?_,ρ,hzero,?_⟩
  · simpa only [hfield] using hindex
  · have hh := congrArg (Subgroup.map (G₀ L S).subtype) heq
    rwa [map_commutator] at hh
  · intro u v
    exact hρ (originalActor (L := L) (S := S) (!i) u) v
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer

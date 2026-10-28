module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiTorusQuotient
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCentralizerGrowth

/-!
# The full linear second kernel and its natural third-kernel quotient

Put N = G_m^(2), H = G_m^(3), C = C_(Q_m)(H), and
W = ⟨(V_y ∩ Q_x)^(G_m)⟩. The proved derived-core identities give
[N,star_m] ≤ W, and N ≤ C. The same selected full-edge torus has
no nonidentity fixed coset in the literal C/W. Therefore N/W is trivial,
so N = W, including after the original completion inclusion.

Apply the established natural coordinates on W/H to this actual full
kernel. Thus N is elementary of order q⁵ and N/H is the natural module
of order q² for the original marked endpoint quotient, with the original
conjugation formula. No naturality or kernel-equality premise is added.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
proof of (12.9), printed pp.188--190. This combines the established
source commutators with the source torus calculation to finish the
second-kernel identification; irreducibility of C/W, the binary cases,
and the remaining earlier-source premise discharge remain separate.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial BenderSuzuki.MatrixGroups
local instance kernelBinaryAlgebra {k : Type*} [Field k] [CharP k 2] : Algebra (ZMod 2) k := ZMod.algebra k 2
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The full second kernel equals the geometric span in both completions. -/
theorem source_suzuki_full_linear_second_kernel
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
    let m := base F i
    let W := conjugateSpanBy (V F (base F (!i)) 1 ⊓ Q F x) (stabilizer F m)
    ballKernel F m 2 = W ∧
    (ballKernel F m 2).map (G₀ L S).subtype = W.map (G₀ L S).subtype := by
  let F := reducedFamily L S
  let m := base F i
  let A := star L S i
  let N := ballKernel F m 2
  let C := Q F m ⊓ centralizer (ballKernel F m 3 : Set (G₀ L S))
  let W := conjugateSpanBy (V F (base F (!i)) 1 ⊓ Q F x) (stabilizer F m)
  have hb : 2 < b F := by change 2 < b (reducedFamily L S); omega
  have hWN : W ≤ N :=
    (source_linear_second_kernel_span h i hb hxadj hne T hT e hcommy.le hnear).2.1
  have hNC : N ≤ C := (source_suzuki_centralizer_second_kernel h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch).2.1
  have hNA : ⁅N,A⁆ ≤ W :=
    (source_suzuki_centralizer_growth_and_fixed_kernel h i hb3 hxadj hne T R hT hR e hz
      hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear).2.2.1
  obtain ⟨K,hK,ho,hKx,hDne,hDo,hJH,hJsize,hAC,hW,hWC,hCE,ρ,hρ,hfixed⟩ :=
    source_suzuki_selected_torus_quotient_fixed h i hb3 hxadj hne T R hT hR e hz
      hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear
  let _ := hW
  have hNW : N = W := le_antisymm (by
    intro z hz
    let c : C := ⟨z,hNC hz⟩
    have hc : (QuotientGroup.mk c : C ⧸ W.subgroupOf C) = 1 := by
      apply hfixed
      intro d
      rw [hρ]
      apply QuotientGroup.eq_iff_div_mem.mpr
      change (d : G₀ L S) * z * (d : G₀ L S)⁻¹ / z ∈ W
      have hh := (commutator_le.mp (by rwa [commutator_comm] : ⁅A,N⁆ ≤ W))
        (d : G₀ L S) d.property.2 z hz
      simpa only [commutatorElement_def,div_eq_mul_inv] using hh
    exact (QuotientGroup.eq_one_iff c).mp hc) hWN
  exact ⟨hNW,congrArg (Subgroup.map (G₀ L S).subtype) hNW⟩


/-- The literal full second-to-third kernel quotient has natural coordinates for the original endpoint action. -/
theorem source_suzuki_linear_kernel_series
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
    let m := base F i
    let y := base F (!i)
    let C := V F y 1 ⊓ Q F x
    let W := ballKernel F m 2
    ∃ hWel : IsElementaryAbelian 2 W,
    ∃ hAW : star L S i ≤ normalizer (W : Set (G₀ L S)),
      let := hWel
      let : ((ballKernel F m 3).subgroupOf W).Normal := normal_of_isMulCommutative _
      ballKernel F m 3 ≤ W ∧
      Nat.card W = Nat.card k ^ 5 ∧
      W = C ⊔ (V F x 1 ⊓ Q F y) ∧
      ballKernel F m 3 = V F x 1 ⊓ V F y 1 ∧
      Nat.card (W ⧸ (ballKernel F m 3).subgroupOf W) = Nat.card k ^ 2 ∧
      ∃ E : Additive (W ⧸ (ballKernel F m 3).subgroupOf W) ≃ₗ[ZMod 2] (Fin 2 → k),
        ∀ u : L (if i then 1 else 0), ∀ w : W,
          E (Additive.ofMul (QuotientGroup.mk
            ⟨(originalActor (L := L) (S := S) i u : G₀ L S) * w *
                (originalActor (L := L) (S := S) i u : G₀ L S)⁻¹,
              (mem_normalizer_iff.mp (hAW
                (originalActor (L := L) (S := S) i u).property) w).mp w.property⟩)) =
            Matrix.mulVec (e (QuotientGroup.mk u)).val
              (E (Additive.ofMul (QuotientGroup.mk w))) := by
  have heq := (source_suzuki_full_linear_second_kernel h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear).1
  have hs := source_suzuki_span_natural h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear
  dsimp only
  rw [heq]
  obtain ⟨hWel,hAW,_,hs⟩ := hs
  exact ⟨hWel,hAW,hs⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer

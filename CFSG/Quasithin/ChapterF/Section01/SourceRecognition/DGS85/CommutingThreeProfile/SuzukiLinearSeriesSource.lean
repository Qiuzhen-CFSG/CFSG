module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiMarkedLayers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiExactPathParameters

/-!
# The nonbinary path and linear-kernel consumer with its center premise discharged

Construct the natural middle center from its literal minimality, Sylow,
order and commutator inputs. Applying the existing source kernel series
then gives the full second and third kernels, their natural quotient for
the original endpoint marking, the full-Borel two-core order q¹², and the
exact source parameters r=8, s=9. Both the reduced and original completion
path stabilizers of length at least nine have odd order.

This consumes LinearCenterNatural at the existing source-parameter API.
The same constructed center also supplies the literal marked top and
irreducible radius-two layers in SuzukiMarkedLayers. No natural-center
callback remains in these applications. The Suzuki and linear quotient
markings, common field order, critical geometry and earlier reciprocal
commutator inputs remain explicit; exhaustive source selection, the binary
alternatives, and final Chapter 12/13.1 discharge are still required.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.9)(c3)--(c5), printed pp.186--190.
-/

public noncomputable section
open Subgroup Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial BenderSuzuki.MatrixGroups
open Theory.GroupTheory.AmalgamGraph SimpleGraph
local instance suzukiLinearSeriesBinaryAlgebra {k : Type*} [Field k] [CharP k 2] : Algebra (ZMod 2) k := ZMod.algebra k 2
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The actual source path parameters and natural full-kernel series from the earlier geometric inputs. -/
theorem source_suzuki_linear_series_of_earlier
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
    (hbranch : ⁅V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥)
    (hnear : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) x,
      V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥) :
    let F := reducedFamily L S
    let m := base F i
    let y := base F (!i)
    let C := V F y 1 ⊓ Q F x
    let W := ballKernel F m 2
    let π := e.toMonoidHom.comp ((originalQuotient h i).symm.toMonoidHom.comp
      (QuotientGroup.mk' (pCore 2 (star L S i))))
    Nonempty (BinaryConjugationSection (star L S i) (Q F m) (V F m 2)
      ((SL2NaturalOffenders.NoStrong.natural (F := k)).comp π)) ∧
    NoncommutingProfile.HasSourcePathParameters
      (P := fun j => (P₀ L S j).subgroupOf (G₀ L S)) 8 9 ∧
    Nat.card ((commonBorel L S).pCoreIn 2) = Nat.card k ^ 12 ∧
    (∀ {r : ℕ} {v : Vertex F} (p : BasedWalk (graph F) r v),
      p.Nonbacktracking → 9 ≤ r →
      Odd (Nat.card (pathStabilizer F p)) ∧
      Odd (Nat.card ((pathStabilizer F p).map (G₀ L S).subtype))) ∧
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
  have hnat := source_linear_hasNaturalCenter h i T hT e hcard hcardy hzy hcommy.le hmin hz
  have hparameters := source_suzuki_source_path_parameters h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear
  have hBorel := (source_suzuki_exact_borel_order h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear).1
  obtain ⟨_,_,_,hodd⟩ := source_suzuki_exact_path_parameter h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear
  have hseries := source_suzuki_linear_kernel_series h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear
  obtain ⟨dQ,_,_⟩ := source_suzuki_marked_top_layer h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hbranch hnear
  exact ⟨⟨dQ⟩,hparameters,hBorel,hodd,hseries⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer

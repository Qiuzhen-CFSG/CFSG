module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCenterLayer
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCoreProduct

/-!
# The center layer from the preceding intersection argument

The proved middle-core product and intersection commutator imply
[V_y,L_y] = V_y. Apply that conclusion to SuzukiCenterLayer to obtain
the literal V_y/Z_y action, its order q^4 and |V_y| = q^5. The fixed
subgroup and span order are also retained under the original inclusion.
No product or full-movement hypothesis is added to the earlier inputs.

The retained common Sylows, natural center, center orders, commutator
identities and natural-center minimality are (12.1) inputs. The supplied
conjugated indices are earlier (12.3)(a) inputs, and the actual Suzuki
marking remains the (12.5) selection obligation. This is the nonbinary
center part of (12.6); the other source clauses are not asserted here.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.1), (12.3), (12.5)--(12.6), printed pp.178--183.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction
open BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Discharge full movement by the source intersection theorem before constructing the center layer. -/
theorem source_suzuki_center_layer_of_intersection
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
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
      (Q (reducedFamily L S) (base (reducedFamily L S) i))) :
    let F := reducedFamily L S
    let v := base F (!i)
    let V₀ := V F v 1
    let C := Z F v
    let := V_elementary F (reduced_triple h).generate
      (fun w => (source_Z_Q_U (reduced_triple h) w).1) (reduced_kernel_sylow h) hb v
    let : (C.subgroupOf V₀).Normal := normal_of_isMulCommutative _
    V₀.map (G₀ L S).subtype ⊓
      centralizer (starredParabolic L S (if !i then 1 else 0) : Set G) =
        C.map (G₀ L S).subtype ∧
    Nat.card V₀ = (2^(2*n+1))^5 ∧
    Nat.card (V₀.map (G₀ L S).subtype) = (2^(2*n+1))^5 ∧
    ∃ ρ : Representation (ZMod 2)
      (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0)))
      (Additive (V₀ ⧸ C.subgroupOf V₀)),
      Function.Injective ρ ∧ ρ.IsIrreducible ∧
      Nat.card (V₀ ⧸ C.subgroupOf V₀) = (2^(2*n+1))^4 ∧
      ∀ a : L (if !i then 1 else 0), ∀ x : V₀,
        (ρ (QuotientGroup.mk a) (Additive.ofMul (QuotientGroup.mk x))).toMul =
          QuotientGroup.mk ⟨(originalActor (L := L) (S := S) (!i) a : G₀ L S) * x *
            (originalActor (L := L) (S := S) (!i) a : G₀ L S)⁻¹,
            (mem_normalizer_iff.mp (star_normalizes_span h (!i)
              (originalActor (L := L) (S := S) (!i) a).property) x).mp x.property⟩ := by
  have hp := source_suzuki_product_and_intersection_commutator h i hb hxadj hne
    T R hT hR e hz hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor
    hn eSuz hfield Ry hRy hc hxa hmin
  have hm := hp.2.2.2.1
  have hh := source_suzuki_center_layer h (!i) hb hc hxa
    (by simpa only [Bool.not_not] using hxadj.symm) hn hfield eSuz
    (by cases i <;> exact e) (by cases i <;> exact R)
    (by cases i <;> exact hR) Ry (by simpa only [Bool.not_not] using hRy)
    (by simpa only [Bool.not_not] using hzy) hcommy
    (by cases i <;> exact T) (by cases i <;> exact hT)
    (by simpa only [Bool.not_not] using hnat) hm (hcardy.trans hfield)
  exact hh

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer

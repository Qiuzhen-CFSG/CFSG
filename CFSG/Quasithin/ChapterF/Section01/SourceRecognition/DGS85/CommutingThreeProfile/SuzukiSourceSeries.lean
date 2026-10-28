module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiLinearSeriesSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCentralKernelLayers

/-!
# The assembled nonbinary source kernel series

Combine the four Suzuki layers of DGS (12.9)(c2), the two full-kernel
identities (c3), the five linear layers (c4), and the odd path-stabilizer
conclusion (c5). The representations are on the literal subgroup quotients.
Their representative formulas use the original local actors; the three
natural linear layers use the same original SL₂ marking. The kernel
identities and path orders retain the original completion inclusion.

The proof constructs the neighboring natural center, applies the geometric
intersection argument to obtain span generation, and combines the resulting
irreducible and central layers. A separate conversion lemma transports the
radius-two automorphism action through the original quotient without
replacing it by an unrelated representation. The final consumer also retains
the full-Borel two-core order q¹² and the exact source parameters r=8, s=9.

The original linear and Suzuki markings, their common field parameter,
common Sylows, center orders/minimality, critical geometry and reciprocal
commutator/index inputs remain explicit earlier premises. This assembles
the selected nonbinary branch; it does not select the Suzuki quotient,
prove the binary TYPE alternatives, or discharge all Chapter 8/9 inputs.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.1)--(12.6) and (12.9)(c), printed pp.178--190, especially p.186.
-/

public noncomputable section
open Subgroup Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial BenderSuzuki.MatrixGroups
open Theory.GroupTheory.AmalgamGraph SimpleGraph
local instance sourceSeriesBinaryAlgebra {k : Type*} [Field k] [CharP k 2] : Algebra (ZMod 2) k := ZMod.algebra k 2
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- An irreducible binary section with the original local quotient and its literal conjugation action. -/
@[expose] def OriginalIrreducibleLayer (L : Fin 2 → Subgroup G) (S : Subgroup G)
    (i : Bool) (A B : Subgroup (G₀ L S)) (d : ℕ) : Prop :=
  B ≤ A ∧
  ∃ hA : star L S i ≤ normalizer (A : Set (G₀ L S)),
  ∃ hB : (B.subgroupOf A).Normal,
    letI := hB
    ∃ hE : IsElementaryAbelian 2 (A ⧸ B.subgroupOf A),
      letI := hE
      ∃ ρ : Representation (ZMod 2)
        (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0)))
        (Additive (A ⧸ B.subgroupOf A)),
        ρ.IsIrreducible ∧ Nat.card (A ⧸ B.subgroupOf A) = d ∧
        ∀ u : L (if i then 1 else 0), ∀ v : A,
          (ρ (QuotientGroup.mk u) (Additive.ofMul (QuotientGroup.mk v))).toMul =
            QuotientGroup.mk ⟨(originalActor (L := L) (S := S) i u : G₀ L S) * v *
              (originalActor (L := L) (S := S) i u : G₀ L S)⁻¹,
              (mem_normalizer_iff.mp (hA (originalActor (L := L) (S := S) i u).property) v).mp v.property⟩

/-- A central binary section of the original endpoint, including its actual quotient action. -/
@[expose] def OriginalCentralLayer (L : Fin 2 → Subgroup G) (S : Subgroup G)
    (i : Bool) (A B : Subgroup (G₀ L S)) (d : ℕ) : Prop :=
  B ≤ A ∧
  ∃ hA : star L S i ≤ normalizer (A : Set (G₀ L S)),
  ∃ hB : (B.subgroupOf A).Normal,
    letI := hB
    ∃ hE : IsElementaryAbelian 2 (A ⧸ B.subgroupOf A),
      letI := hE
      Nat.card (A ⧸ B.subgroupOf A) = d ∧
      ∃ ρ : Representation (ZMod 2)
        (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0)))
        (Additive (A ⧸ B.subgroupOf A)),
        ρ = 1 ∧
        ∀ u : L (if i then 1 else 0), ∀ v : A,
          (ρ (QuotientGroup.mk u) (Additive.ofMul (QuotientGroup.mk v))).toMul =
            QuotientGroup.mk ⟨(originalActor (L := L) (S := S) i u : G₀ L S) * v *
              (originalActor (L := L) (S := S) i u : G₀ L S)⁻¹,
              (mem_normalizer_iff.mp (hA (originalActor (L := L) (S := S) i u).property) v).mp v.property⟩

/-- The four literal Suzuki layers of DGS (12.9)(c2). -/
@[expose] def SuzukiSourceLayers (L : Fin 2 → Subgroup G) (S : Subgroup G) (i : Bool) (q : ℕ) : Prop :=
  let F := reducedFamily L S
  let y := base F (!i)
  OriginalIrreducibleLayer L S (!i) (Q F y) (ballKernel F y 2) (q^4) ∧
  OriginalIrreducibleLayer L S (!i) (V F y 1) (Z F y) (q^4) ∧
  IsElementaryAbelian 2 (Z F y) ∧ Nat.card (Z F y) = q ∧
  Z F y ≤ centralizer (star L S (!i) : Set (G₀ L S)) ∧
  OriginalCentralLayer L S (!i) (ballKernel F y 2) (V F y 1) q

/-- All five linear layers of DGS (12.9)(c4), for the same original SL₂ marking. -/
@[expose] def LinearSourceLayers {k : Type*} [Field k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k)) : Prop :=
  let F := reducedFamily L S
  let m := base F i
  let W := ballKernel F m 2
  let π := e.toMonoidHom.comp ((originalQuotient h i).symm.toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 (star L S i))))
  Nonempty (BinaryConjugationSection (star L S i) (Z F m) ⊥
    ((SL2NaturalOffenders.NoStrong.natural (F := k)).comp π)) ∧
  Nonempty (BinaryConjugationSection (star L S i) (Q F m) (V F m 2)
    ((SL2NaturalOffenders.NoStrong.natural (F := k)).comp π)) ∧
  OriginalIrreducibleLayer L S i (V F m 2) W (Nat.card k ^ 4) ∧
  OriginalCentralLayer L S i (ballKernel F m 3) (Z F m) (Nat.card k) ∧
  ∃ hWel : IsElementaryAbelian 2 W,
  ∃ hAW : star L S i ≤ normalizer (W : Set (G₀ L S)),
    letI := hWel
    letI : ((ballKernel F m 3).subgroupOf W).Normal := normal_of_isMulCommutative _
    ballKernel F m 3 ≤ W ∧
    Nat.card (W ⧸ (ballKernel F m 3).subgroupOf W) = Nat.card k ^ 2 ∧
    ∃ E : Additive (W ⧸ (ballKernel F m 3).subgroupOf W) ≃ₗ[ZMod 2] (Fin 2 → k),
      ∀ u : L (if i then 1 else 0), ∀ w : W,
        E (Additive.ofMul (QuotientGroup.mk
          ⟨(originalActor (L := L) (S := S) i u : G₀ L S) * w *
            (originalActor (L := L) (S := S) i u : G₀ L S)⁻¹,
            (mem_normalizer_iff.mp (hAW (originalActor (L := L) (S := S) i u).property) w).mp w.property⟩)) =
          Matrix.mulVec (e (QuotientGroup.mk u)).val (E (Additive.ofMul (QuotientGroup.mk w)))


/-- Construct all four Suzuki layers, discharging naturality and span generation from the earlier inputs. -/
theorem source_suzuki_source_layers
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
    SuzukiSourceLayers L S i (Nat.card k) := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hb : 2 < b F := by change 2 < b (reducedFamily L S); omega
  have hnat := source_linear_hasNaturalCenter h i T hT e hcard hcardy hzy hcommy.le hmin hz
  have hcent := source_suzuki_center_layer_of_intersection h i hb hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat
  have hprod := source_suzuki_product_and_intersection_commutator h i hb hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin
  have hQlayer := source_suzuki_second_kernel_layer h (!i) hb hc hxa
    (by simpa only [Bool.not_not] using hxadj.symm) hn hfield eSuz
    (by cases i <;> exact e) (by cases i <;> exact R) (by cases i <;> exact hR) Ry
    (by simpa only [Bool.not_not] using hRy) (by simpa only [Bool.not_not] using hzy) hcommy
    (by cases i <;> exact T) (by cases i <;> exact hT)
    (by simpa only [Bool.not_not] using hnat) hprod.2.2.2.1
  have hkc := source_suzuki_neighbor_kernel_central h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear
  have hKQ : ballKernel F y 2 ≤ Q F y := source_suzuki_second_kernel_le_core h (!i) eSuz
    (by cases i <;> exact e) (by
      rw [hfield]
      exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : 2 ≤ 2*n+1)) y
  have hYK : V F y 1 ≤ ballKernel F y 2 := V_le_ballKernel F (reduced_triple h).generate y
    (by change 3 ≤ b (reducedFamily L S); omega)
  dsimp only [SuzukiSourceLayers]
  refine ⟨?_,?_,Z_elementary F (fun v => (source_Z_Q_U (reduced_triple h) v).1) y,hcardy,?_,?_⟩
  · refine ⟨hKQ,(star_le_stabilizer (!i)).trans (CommutingTrivial.stabilizer_normalizes_Q F y),
      normal_subgroupOf_of_le_normalizer ((Q_le_stabilizer F y).trans (stabilizer_le_normalizer_ballKernel F y 2)),?_,?_⟩
    · exact source_second_kernel_elementary h (!i)
        (by simpa only [Bool.not_not] using ((le_sup_left.trans hT.ge).trans (map_subtype_le _)))
        (by simpa only [Bool.not_not] using hnat) hcommy.le
    · obtain ⟨ρ,_,hirr,hsize,hρ⟩ := hQlayer
      exact ⟨ρ,hirr,by simpa only [hfield] using hsize,hρ⟩
  · let := V_elementary F (reduced_triple h).generate
      (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb y
    refine ⟨Z_le_V F y 1,star_normalizes_span h (!i),normal_of_isMulCommutative _,inferInstance,?_⟩
    obtain ⟨ρ,_,hirr,hsize,hρ⟩ := hcent.2.2.2
    exact ⟨ρ,hirr,by simpa only [hfield] using hsize,hρ⟩
  · exact source_center_centralizes_star_of_neighbor_inclusion h (!i)
      (by simpa only [Bool.not_not] using hzy) Ry (by simpa only [Bool.not_not] using hRy)
  · obtain ⟨hAK,hY,hel,hsize,_,_,ρ,htriv,hρ⟩ := hkc
    exact ⟨hYK,hAK,hY,hel,hsize,ρ,htriv,hρ⟩

private theorem automorphism_representation_comp {A B E : Type*} [Group A] [Group B] [Group E]
    [IsElementaryAbelian 2 E] (ρ : B →* MulAut E) (f : A →* B) :
    FrattiniAction.ofAutomorphismHom (ρ.comp f) =
      (FrattiniAction.ofAutomorphismHom ρ).comp f := by
  ext a v
  rfl

private theorem originalIrreducibleLayer_of_automorphism
    {k : Type*} [Field k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    (A B : Subgroup (G₀ L S)) (hBA : B ≤ A)
    (hA : star L S i ≤ normalizer (A : Set (G₀ L S)))
    [(B.subgroupOf A).Normal] [IsElementaryAbelian 2 (A ⧸ B.subgroupOf A)]
    (ρ : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) →*
      MulAut (A ⧸ B.subgroupOf A))
    (hρ : ∀ t : star L S i, ∀ c : A,
      ρ ((originalQuotient h i).symm (QuotientGroup.mk' (pCore 2 (star L S i)) t))
        (QuotientGroup.mk' (B.subgroupOf A) c) =
        QuotientGroup.mk' (B.subgroupOf A) ⟨(t : G₀ L S)*c*(t : G₀ L S)⁻¹,
          (mem_normalizer_iff.mp (hA t.property) c).mp c.property⟩)
    (hirr : (FrattiniAction.ofAutomorphismHom (ρ.comp e.symm.toMonoidHom)).IsIrreducible)
    {d : ℕ} (hsize : Nat.card (A ⧸ B.subgroupOf A) = d) :
    OriginalIrreducibleLayer L S i A B d := by
  let τ := FrattiniAction.ofAutomorphismHom ρ
  have hτ : τ.IsIrreducible :=
    (Representation.irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective τ).mp (by
      rw [←automorphism_representation_comp]
      exact hirr)
  refine ⟨hBA,hA,inferInstance,inferInstance,τ,hτ,hsize,?_⟩
  intro u v
  have he : (originalQuotient h i).symm (QuotientGroup.mk
      (originalActor (L := L) (S := S) i u)) = QuotientGroup.mk u :=
    (congrArg (originalQuotient h i).symm (originalQuotient_mk h i u)).symm.trans
      ((originalQuotient h i).symm_apply_apply _)
  have hh := hρ (originalActor (L := L) (S := S) i u) v
  change ρ (QuotientGroup.mk u) (QuotientGroup.mk v) = _
  simpa only [QuotientGroup.mk'_apply, he] using hh

/-- Convert the radius-two quotient to its literal original local representation. -/
theorem source_suzuki_linear_middle_layer
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
    OriginalIrreducibleLayer L S i
      (V (reducedFamily L S) (base (reducedFamily L S) i) 2)
      (ballKernel (reducedFamily L S) (base (reducedFamily L S) i) 2) (Nat.card k ^ 4) := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hb : 2 < b F := by change 2 < b (reducedFamily L S); omega
  have hnat := source_linear_hasNaturalCenter h i T hT e hcard hcardy hzy hcommy.le hmin hz
  have hmid := source_suzuki_radius_two_quotient_irreducible h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hbranch hnear
  have hWV : ballKernel F m 2 ≤ V F m 2 :=
    (source_suzuki_centralizer_second_kernel h i hb3 hxadj hne T R hT hR e hz
      hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch).2.1.trans
    (source_suzuki_centralizer_eq_radius_two_span h i hb3 hxadj hne T R hT hR e hz
      hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear).1.le
  obtain ⟨hAC,hW,hsize,hel,ρ,hρ,hirr⟩ := hmid
  let := hW
  let := hel
  exact originalIrreducibleLayer_of_automorphism h i e _ _ hWV hAC ρ hρ hirr hsize

/-- Construct all five linear layers for the same original field and quotient marking. -/
theorem source_suzuki_linear_source_layers
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
    LinearSourceLayers h i e := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hb : 2 < b F := by change 2 < b (reducedFamily L S); omega
  have hnat := source_linear_hasNaturalCenter h i T hT e hcard hcardy hzy hcommy.le hmin hz
  have hlin := source_suzuki_linear_series_of_earlier h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hbranch hnear
  obtain ⟨dQ,_,_,_,hWel,hAW,hHW,_,_,hH,hWH,E,hE⟩ := hlin
  have hhc := source_suzuki_linear_third_kernel_central h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch
  have hZW : Z F m ≤ ballKernel F m 3 := by
    rw [hH]
    exact le_inf (Z_neighbor_le_V F hxadj.symm)
      (Z_neighbor_le_V F (by
        exact ⟨by change (!i) ≠ i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F (!i) i⟩))
  dsimp only [LinearSourceLayers]
  refine ⟨source_linear_center_marked_natural h i T hT e hcard hcardy hzy hcommy.le hmin,
    dQ,?_,?_,hWel,hAW,hHW,hWH,E,hE⟩
  · exact source_suzuki_linear_middle_layer h i hb3 hxadj hne T R hT hR e hz
      hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hbranch hnear
  · obtain ⟨hAH,hZ,hel,hsize,_,_,ρ,htriv,hρ⟩ := hhc
    exact ⟨hZW,hAH,hZ,hel,hsize,ρ,htriv,hρ⟩

/-- DGS (12.9)(c2)--(c5) after nonbinary Suzuki selection and the retained earlier geometric inputs. -/
theorem source_suzuki_nonbinary_series
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
    2 < Nat.card k ∧ Nat.card k = 2 ^ (2*n+1) ∧
    Nonempty ((L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n) ∧
    NoncommutingProfile.HasSourcePathParameters
      (P := fun j => (P₀ L S j).subgroupOf (G₀ L S)) 8 9 ∧
    Nat.card ((commonBorel L S).pCoreIn 2) = Nat.card k ^ 12 ∧
    ballKernel F m 2 = conjugateSpanBy (V F y 1 ⊓ Q F x) (stabilizer F m) ∧
    ballKernel F m 3 = V F x 1 ⊓ V F y 1 ∧
    (ballKernel F m 2).map (G₀ L S).subtype =
      (conjugateSpanBy (V F y 1 ⊓ Q F x) (stabilizer F m)).map (G₀ L S).subtype ∧
    (ballKernel F m 3).map (G₀ L S).subtype =
      (V F x 1 ⊓ V F y 1).map (G₀ L S).subtype ∧
    SuzukiSourceLayers L S i (Nat.card k) ∧
    LinearSourceLayers h i e ∧
    (∀ {r : ℕ} {v : Vertex F} (p : BasedWalk (graph F) r v),
      p.Nonbacktracking → 9 ≤ r →
      Odd (Nat.card (pathStabilizer F p)) ∧
      Odd (Nat.card ((pathStabilizer F p).map (G₀ L S).subtype))) := by

  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hb : 2 < b F := by change 2 < b (reducedFamily L S); omega
  have hnat := source_linear_hasNaturalCenter h i T hT e hcard hcardy hzy hcommy.le hmin hz
  have hlin := source_suzuki_linear_series_of_earlier h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hbranch hnear
  obtain ⟨_,hparam,hBorel,hodd,_,_,_,_,_,hH,_⟩ := hlin
  have hsecond := source_suzuki_full_linear_second_kernel h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear
  refine ⟨?_,hfield,⟨eSuz⟩,hparam,hBorel,hsecond.1,hH,hsecond.2,congrArg (Subgroup.map (G₀ L S).subtype) hH,?_,?_,hodd⟩
  · rw [hfield]
    exact lt_of_lt_of_le (by decide : 2 < 2^2)
      (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : 2 ≤ 2*n+1))
  · exact source_suzuki_source_layers h i hb3 hxadj hne T R hT hR e hz
      hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hbranch hnear
  · exact source_suzuki_linear_source_layers h i hb3 hxadj hne T R hT hR e hz
      hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hbranch hnear

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer

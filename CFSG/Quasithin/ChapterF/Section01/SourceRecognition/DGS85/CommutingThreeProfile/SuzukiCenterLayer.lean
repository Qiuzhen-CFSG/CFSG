module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCenterDenominator
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCenterFixed

/-!
# The actual nonbinary Suzuki center layer in DGS 12.6

Identify the fixed subgroup of the full starred endpoint with Z_beta,
then apply the already proved geometric q^4 fixed-quotient theorem.
This gives a faithful irreducible action on the literal V_beta/Z_beta,
with the original local quotient and conjugation representatives.
The earlier center order |Z_beta| = q then gives |V_beta| = q^5,
both in the reduced completion and under its original inclusion.

The markings and parameter compatibility are retained (12.5) inputs;
the common Sylows, neighboring natural center, center inclusion and
commutator identity are earlier (12.1) inputs. SuzukiCenterApplication
discharges the full-movement hypothesis using the proved (12.3) argument.
The binary upper bound, full second-kernel containment, intersection
order and remaining (12.7)--(12.9)/(13.1) conclusions remain separate.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.6)(a,b) and (12.9)(c2), printed pp.183 and186.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
open BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The geometric center quotient has its original irreducible action and the span has order q⁵. -/
theorem source_suzuki_center_layer
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (hb : 2 < b (reducedFamily L S))
    {a x : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) i))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hxm : (graph (reducedFamily L S)).Adj x (base (reducedFamily L S) (!i)))
    {n : ℕ} (hn : 0 < n) (hq : Nat.card k = 2^(2*n+1))
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      SuzukiMatrixGroup n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃*
      SL(2,k))
    (T : Sylow 2 (star L S (!i)))
    (hT : (T : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (R : Sylow 2 (star L S i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) i) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcomm : ⁅V (reducedFamily L S) (base (reducedFamily L S) i) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) i)⁆ =
        Z (reducedFamily L S) (base (reducedFamily L S) i))
    (T₀ : Sylow 2 (star L S (!i)))
    (hT₀ : (T₀ : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hnat : Noncommuting.HasNaturalCenter (star L S (!i))
      (Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
      (Q (reducedFamily L S) (base (reducedFamily L S) (!i))))
    (hfull : V (reducedFamily L S) (base (reducedFamily L S) i) 1 =
      ⁅V (reducedFamily L S) (base (reducedFamily L S) i) 1, star L S i⁆)
    (hcardZ : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = 2^(2*n+1)) :
    let F := reducedFamily L S
    let v := base F i
    let V₀ := V F v 1
    let C := Z F v
    let := V_elementary F (reduced_triple h).generate
      (fun w => (source_Z_Q_U (reduced_triple h) w).1) (reduced_kernel_sylow h) hb v
    let : (C.subgroupOf V₀).Normal := normal_of_isMulCommutative _
    V₀.map (G₀ L S).subtype ⊓
      centralizer (starredParabolic L S (if i then 1 else 0) : Set G) =
        C.map (G₀ L S).subtype ∧
    Nat.card V₀ = (2^(2*n+1))^5 ∧
    Nat.card (V₀.map (G₀ L S).subtype) = (2^(2*n+1))^5 ∧
    ∃ ρ : Representation (ZMod 2)
      (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0)))
      (Additive (V₀ ⧸ C.subgroupOf V₀)),
      Function.Injective ρ ∧ ρ.IsIrreducible ∧
      Nat.card (V₀ ⧸ C.subgroupOf V₀) = (2^(2*n+1))^4 ∧
      ∀ a : L (if i then 1 else 0), ∀ x : V₀,
        (ρ (QuotientGroup.mk a) (Additive.ofMul (QuotientGroup.mk x))).toMul =
          QuotientGroup.mk ⟨(originalActor (L := L) (S := S) i a : G₀ L S) * x *
            (originalActor (L := L) (S := S) i a : G₀ L S)⁻¹,
            (mem_normalizer_iff.mp (star_normalizes_span h i
              (originalActor (L := L) (S := S) i a).property) x).mp x.property⟩ := by
  have hcZ := source_suzuki_fixed_center_eq h i hb eSuz R hR hzy
  have hh := source_suzuki_fixed_center_layer h i hb hc hxa hxm hn hq
    eSuz eLin T hT R hR hzy hcomm T₀ hT₀ hnat hfull
  dsimp only at hh ⊢
  rw [hcZ] at hh
  let F := reducedFamily L S
  let v := base F i
  let V₀ := V F v 1
  let C := Z F v
  have hind : C.relIndex V₀ = (2^(2*n+1))^4 := hh.choose_spec.2.2.1
  have hmul := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) C V₀ bot_le (Z_le_V F v 1)
  rw [relIndex_bot_left, relIndex_bot_left, hind] at hmul
  have horder : Nat.card V₀ = (2^(2*n+1))^5 := by
    rw [←hmul, show Nat.card C = 2^(2*n+1) from hcardZ]
    ring
  have hfixed := congrArg (Subgroup.map (G₀ L S).subtype) hcZ
  rw [←map_inf_centralizer_of_injective _ (G₀ L S).subtype_injective] at hfixed
  have hstar : (star L S i).map (G₀ L S).subtype =
      starredParabolic L S (if i then 1 else 0) :=
    map_subgroupOf_eq_of_le (star_le_completion _)
  rw [hstar] at hfixed
  exact ⟨hfixed, horder,
    (card_map_of_injective (G₀ L S).subtype_injective).trans horder, hh⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer

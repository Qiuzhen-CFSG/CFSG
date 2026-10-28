module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.AdaptedCoreComplement
public import Theory.Representation.BinaryConjugationSection.CentralNaturalElementary

/-!
# Elementary adapted subgroups in the original core

The adapted subgroup W from the complement of V/Z has natural quotient W/Z.
The original equality Z = Ω₁Z(L) makes its kernel central in the whole actor
and elementary. The nonbinary central-cover calculation therefore proves
that W itself is elementary abelian. The final application keeps the literal
complement, its order, its adjacent-core escape, and its marked coordinates.

Source: DGS, *Groups and Graphs* (1985), printed p.150, first paragraph after
9.10(6). This supplies elementary abelianness for the two factors used in the
subsequent M-order argument. Constructing the invariant complement remains
the separate natural self-extension splitting premise.
-/

public noncomputable section
open Subgroup Representation
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G]

/-- The adapted natural subgroup is elementary over the original nonbinary field. -/
theorem adapted_core_elementary
    (Γ : Bool → Subgroup G) (beta : Vertex Γ)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (eβ : (graphLocalGroup Γ beta ⧸ pCore 2 (graphLocalGroup Γ beta)) ≃* SL(2,F))
    (W : Subgroup G)
    (cW : letI : Algebra (ZMod 2) F := ZMod.algebra F 2
      BinaryConjugationSection (graphLocalGroup Γ beta) W (Z Γ beta)
        (((specialLinearNatural (k := F) 2).restrictScalars (k := ZMod 2)).comp
          (eβ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup Γ beta))))))
    (hω : Z Γ beta = omegaCenterIn (graphLocalGroup Γ beta))
    (hF : 2 < Nat.card F) : IsElementaryAbelian 2 W := by
  classical
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let : IsElementaryAbelian 2 (Z Γ beta) := by rw [hω]; infer_instance
  have hcentral : Z Γ beta ≤ centralizer (graphLocalGroup Γ beta : Set G) := by
    intro z hz
    exact ((mem_omegaCenterIn_iff _ _).mp (hω ▸ hz)).2.1
  obtain ⟨a,ha0,ha1⟩ : ∃ a : F, a ≠ 0 ∧ a ≠ 1 := by
    by_contra! hall
    let := Fintype.ofFinite F
    have hle : Nat.card F ≤ 2 := by
      rw [Nat.card_eq_fintype_card]
      calc
        Fintype.card F ≤ ({0,1} : Finset F).card := Finset.card_le_card (by
          intro a _
          by_cases ha : a = 0
          · simp [ha]
          · simp [hall a ha])
        _ ≤ 2 := by simp
    omega
  exact BinaryConjugationSection.central_natural_elementary
    (eβ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup Γ beta))))
    (eβ.surjective.comp (QuotientGroup.mk'_surjective _)) cW hcentral a ha0 ha1

/-- The actual complement chosen after 9.10(6), including elementary abelianness. -/
theorem adapted_core_complement_elementary
    (Γ : Bool → Subgroup G) (beta x : Vertex Γ)
    {F Y : Type*} [Field F] [Finite F] [CharP F 2]
    [AddCommGroup Y] [Module (ZMod 2) Y]
    (eβ : (graphLocalGroup Γ beta ⧸ pCore 2 (graphLocalGroup Γ beta)) ≃* SL(2,F))
    (ρ : Representation (ZMod 2) SL(2,F) Y)
    (c : BinaryConjugationSection (graphLocalGroup Γ beta) (Q Γ beta) (Z Γ beta)
      (ρ.comp (eβ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup Γ beta))))))
    (hVQ : V Γ beta 1 ≤ Q Γ beta)
    (X K : Subrepresentation ρ) (hX : X.toSubmodule = c.imageSpace (V Γ beta 1))
    (hK : IsCompl X.toSubmodule K.toSubmodule)
    (eK : letI : Algebra (ZMod 2) F := ZMod.algebra F 2
      K.toSubmodule ≃ₗ[ZMod 2] (Fin 2 → F))
    (heK : ∀ g k, eK (K.toRepresentation g k) = Matrix.mulVec g.val (eK k))
    (hZcard : Nat.card (Z Γ beta) = Nat.card F)
    (hVx : V Γ beta 1 ≤ Q Γ x) (hQx : ¬ Q Γ beta ≤ Q Γ x)
    (hω : Z Γ beta = omegaCenterIn (graphLocalGroup Γ beta))
    (hF : 2 < Nat.card F) :
    let π := eβ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup Γ beta)))
    letI : Algebra (ZMod 2) F := ZMod.algebra F 2
    ∃ (W : Subgroup G) (hWQ : W ≤ Q Γ beta),
      W ⊓ V Γ beta 1 = Z Γ beta ∧ W ⊔ V Γ beta 1 = Q Γ beta ∧
      Nat.card W = Nat.card F ^ 3 ∧ ¬ W ≤ Q Γ x ∧ IsElementaryAbelian 2 W ∧
      ∃ cW : BinaryConjugationSection (graphLocalGroup Γ beta) W (Z Γ beta)
        (((specialLinearNatural (k := F) 2).restrictScalars (k := ZMod 2)).comp π),
        ∀ w : W, (eK.symm (cW.coordinates w).toAdd : Y) =
          (c.coordinates (inclusion hWQ w)).toAdd := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨W,hWQ,hWV,hWsup,hWcard,hWesc,cW,he⟩ :=
    adapted_core_complement Γ beta x eβ ρ c hVQ X K hX hK eK heK hZcard hVx hQx
  exact ⟨W,hWQ,hWV,hWsup,hWcard,hWesc,
    adapted_core_elementary Γ beta eβ W cW hω hF,cW,he⟩
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial

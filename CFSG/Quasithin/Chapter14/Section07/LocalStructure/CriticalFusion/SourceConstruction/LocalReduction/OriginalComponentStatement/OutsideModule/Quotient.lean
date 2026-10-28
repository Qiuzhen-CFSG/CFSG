module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.NoStrongMoved.Cubic
public import Theory.Representation.InvertedCubicTensor
public import Theory.Representation.BinaryOffender.TwoNoncentralLayers
public import Theory.Representation.BinaryOffender.QuadraticSection

/-!
# The retained outside component gives a faithful quotient action

Full cubic movement descends to every invariant quotient. If the original
quasisimple component still moves the quotient, the common-centralizer bound
and the cubic fixed-point calculation force quotient faithfulness. The same
quadratic actor retains its rank and its fixed codimension can only decrease.

Source: Aschbacher–Smith 14.7.42, printed pp.1061–1062.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory InvertedCubicTensor
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideModule
open Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections

variable {D V : Type*} [Group D] [Finite D]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- A quotient retaining the component is faithful, fully moved by the normal
cubic, and inherits the original ratio-two bound. -/
theorem retained_quotient
    (ρ : Representation (ZMod 2) D V)
    (K X : Subgroup D) [K.Normal] [X.Normal] [IsQuasisimple K]
    (hx : Nat.card X = 3)
    (hcommon : centralizer (K : Set D) ⊓ centralizer (X : Set D) ≤ X)
    (s : S₃ →* D) (hmark : (alternatingGroup (Fin 3)).map s = X)
    (hg : subspaceCommutator ρ ⊤ X = ⊤)
    (N : Subrepresentation ρ) (hretain : ¬ K ≤ N.quotientRepresentation.ker)
    (hratio : quadraticRatio ρ ≤ 2) :
    Function.Injective N.quotientRepresentation ∧
      subspaceCommutator N.quotientRepresentation ⊤ X = ⊤ ∧
      quadraticRatio N.quotientRepresentation ≤ 2 := by
  have hgN : subspaceCommutator N.quotientRepresentation ⊤ X = ⊤ := by
    have hm := map_moved_of_surjective_intertwining ρ N.quotientRepresentation X
      N.toSubmodule.mkQ N.toSubmodule.mkQ_surjective (fun _ _ => rfl)
    rw [hg,Submodule.map_top,LinearMap.range_eq_top.mpr N.toSubmodule.mkQ_surjective] at hm
    exact hm.symm
  have hfree : ∀ v, N.quotientRepresentation (s cubic) v = v → v = 0 :=
    ambient_fixedFree_of_commutator N.quotientRepresentation s (by rw [hmark]; exact hgN)
  have hn : ¬ ∀ k ∈ K, ∀ v, N.quotientRepresentation k v = v := by
    intro hh
    apply hretain
    intro k hk
    apply LinearMap.ext
    intro v
    exact hh k hk v
  have hcubic : s cubic ∈ X := by
    rw [← hmark]
    exact mem_map_of_mem s (by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel)
  refine ⟨LinearTwo.NoStrongMoved.faithful_of_cubic K X hx hcommon
    N.quotientRepresentation hn (s cubic) hcubic hfree,hgN,?_⟩
  obtain ⟨A,hA,hquad,hbound⟩ := (quadraticRatio_le_two_iff ρ).mp hratio
  refine (quadraticRatio_le_two_iff N.quotientRepresentation).mpr ⟨A,hA,?_,?_⟩
  · exact quadratic_of_equivariant_surjection ρ N.quotientRepresentation
      N.toSubmodule.mkQ N.toSubmodule.mkQ_surjective (fun _ _ => rfl) A hquad
  · have hb := fixedCodim_quotient_add_subrepresentation_le ρ N A
    omega

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideModule

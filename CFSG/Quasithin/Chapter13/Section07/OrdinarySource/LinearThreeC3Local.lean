module
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.LinearThreeParabolic
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.LinearThreeSource
public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks.SourceContainment.Ordinary
public import Theory.GroupTheory.SylowNormalizedResidual

/-!
# The actual local subgroups of the binary three-dimensional C₃ branch

The source middle group is K₀L₂T, where K₀ is the two-residual of C_K(V₂)
and L₂ is the two-residual of N_L(V₂). Both normalize V₂. Sylow supplementation
identifies the L₂T edge with N_LT(V₂), while the marked natural three-space
identifies K₀T with N_H(V₂). These give the two literal middle intersections.
The plane actor is normal in N_G(V₂), with its V₂-action kernel equal to its
two-core, giving [K₀,L₂] ≤ O₂(L₂).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.5.4(1), printed p.916, and proof of 13.7.6(1), printed p.940.
The subsequent product quotient and parabolic-lattice recognition retain
separate proofs; these subgroup identities do not assume a C₃ system.
-/

@[expose] public section
open Subgroup Representation Module
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section07.OrdinarySource.LinearThreeC3Local
open Section08.SourceCompletion
open Section08.TransvectionRecognition Component
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionRecognition.Component.RecognitionStep
open Section08.TransvectionParabolic.Marking
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open Section05.PlaneGeometry.TwoBlocks
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

noncomputable def pointResidual (K V₂ : Subgroup G) : Subgroup G :=
  residual (K ⊓ centralizer (V₂ : Set G))

noncomputable def middle (T : Sylow 2 G) (L K V₂ : Subgroup G) : Subgroup G :=
  pointResidual K V₂ ⊔ planeActor (L := L) (V₂ := V₂) ⊔ (T : Subgroup G)

omit [Finite G] in
theorem pointResidual_le : pointResidual K V₂ ≤ K ⊓ centralizer (V₂ : Set G) :=
  residual_le _

omit [Finite G] in
theorem sylow_le_middle : (T : Subgroup G) ≤ middle T L K V₂ := le_sup_right

omit [Finite G] in
theorem middle_le_generated (hKH : K ≤ H) :
    middle T L K V₂ ≤ (L ⊔ (T : Subgroup G)) ⊔ H := by
  exact sup_le (sup_le ((pointResidual_le.trans inf_le_left).trans (hKH.trans le_sup_right))
    ((planeActor_le.trans inf_le_left).trans (le_sup_left.trans le_sup_left)))
    (le_sup_right.trans le_sup_left)

theorem middle_le_plane_normalizer
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁) :
    middle T L K V₂ ≤ normalizer (V₂ : Set G) := by
  exact sup_le (sup_le ((pointResidual_le.trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)) (planeActor_le.trans inf_le_right)) d.plane_stable

theorem middle_normalizes_planeActor
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hm : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥) :
    middle T L K V₂ ≤ normalizer (planeActor (L := L) (V₂ := V₂) : Set G) :=
  (middle_le_plane_normalizer d).trans (Ordinary.source_planeActor_normalized d e hm)

/-- The actual source commutator assertion 13.5.4(1) at K₀. -/
theorem pointResidual_planeActor_commutator
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hm : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥) :
    ⁅pointResidual K V₂,planeActor (L := L) (V₂ := V₂)⁆ ≤
      (planeActor (L := L) (V₂ := V₂)).pCoreIn 2 := by
  rw [(Ordinary.planeActor_core_source d e).1]
  refine le_inf (le_normalizer_iff_commutator_le_right.mp ?_) ?_
  · exact ((pointResidual_le.trans inf_le_right).trans
      (Subgroup.centralizer_le_normalizer _)).trans (Ordinary.source_planeActor_normalized d e hm)
  · exact (commutator_mono (pointResidual_le.trans inf_le_right) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp
        ((planeActor_le.trans inf_le_right).trans (normalizer_le_normalizer_centralizer _)))

/-- The original plane parabolic is supplemented by the ambient Sylow. -/
theorem planeActor_sup_sylow
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁) :
    planeActor (L := L) (V₂ := V₂) ⊔ (T : Subgroup G) =
      (L ⊔ (T : Subgroup G)) ⊓ normalizer (V₂ : Set G) := by
  let N := normalizer (V₂ : Set G)
  have hn : (T : Subgroup G) ≤ normalizer (planeLocal (L := L) (V₂ := V₂) : Set G) :=
    (le_inf d.normalizes_L (d.plane_stable.trans N.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hp := le_embedded_pResidual_sup_sylow_of_normalizes T
    (planeLocal (L := L) (V₂ := V₂)) hn
  apply le_antisymm
  · exact sup_le (le_inf ((planeActor_le.trans inf_le_left).trans le_sup_left)
      (planeActor_le.trans inf_le_right)) (le_inf le_sup_right d.plane_stable)
  · intro x hx
    have hxprod : x ∈ (L : Set G) * ((T : Subgroup G) : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left L (T : Subgroup G) d.normalizes_L]
      exact hx.1
    obtain ⟨l,hl,t,ht,rfl⟩ := hxprod
    have hlN : l ∈ N := (N.mul_mem_cancel_right (d.plane_stable ht)).mp hx.2
    exact mul_mem (hp ⟨hl,hlN⟩) (mem_sup_right ht)

/-- The left edge is exactly the original plane parabolic. -/
theorem middle_inf_local
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁) :
    middle T L K V₂ ⊓ (L ⊔ (T : Subgroup G)) =
      planeActor (L := L) (V₂ := V₂) ⊔ (T : Subgroup G) := by
  have hp := planeActor_sup_sylow d
  apply le_antisymm
  · rw [hp]
    exact le_inf inf_le_right (inf_le_left.trans (middle_le_plane_normalizer d))
  · exact le_inf (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
      (hp.le.trans inf_le_left)

variable (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
  [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
include d

/-- The original right edge is the actual H-normalizer of V₂. -/
theorem point_parabolic
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinear.GL (Fin 3 → ZMod 2))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (linearRepresentation 3) eK) :
    pointResidual K V₂ ⊔ (T : Subgroup G) = H ⊓ normalizer (V₂ : Set G) ∧
      Nonempty (((pointResidual K V₂ ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (pointResidual K V₂ ⊔ (T : Subgroup G) : Subgroup G)) ≃*
          Equiv.Perm (Fin 3)) :=
  ModelExclusions.linear_three_point_parabolic_of_one_le d hH hF9 hKH hK hL₁K ρ hρ eK hs

/-- The middle vertex meets H in exactly K₀T. -/
theorem middle_inf_H
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinear.GL (Fin 3 → ZMod 2))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (linearRepresentation 3) eK) :
    middle T L K V₂ ⊓ H = pointResidual K V₂ ⊔ (T : Subgroup G) := by
  have hp := (point_parabolic d hH hF9 hKH hK hL₁K ρ hρ eK hs).1
  apply le_antisymm
  · rw [hp]
    exact le_inf inf_le_right (inf_le_left.trans (middle_le_plane_normalizer d))
  · exact le_inf (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
      (hp.le.trans inf_le_left)

end CFSG.Quasithin.Chapter13.Section07.OrdinarySource.LinearThreeC3Local

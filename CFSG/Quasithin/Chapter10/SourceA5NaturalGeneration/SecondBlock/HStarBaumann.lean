module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SecondBlock.HStarCore
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SecondBlock.ResidualBaumann
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.HStarSource.ComponentLocalClass
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.HStarSource.Classification
/-!
# Baumann placement inside the actual H* residual

The K-first block alternative makes the whole core moved. The seed
centralizer identifies the source kernel with that core, hence puts it in
the residual. The source Sylow theorem then puts Baum(S) in O²(H), and
maximality identifies it with S intersect O²(H). Neither an intrinsic natural
marking for K nor a cubic subgroup is needed, so this identity supplies the
normalizer geometry used to select the cubic.
Source: Aschbacher--Smith 10.2.3(4), printed p.747.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open ChapterB ChapterC ChapterE Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
variable {F : Type*} [Field F] [CharP F 2]
local instance hstarResidualBaumannFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- Exact residual Sylow placement in the actual H* first-block branch. -/
theorem source_hstar_baumann_in_residual_of_block
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G),H⁆ ≠ ⊥)
    (hF : Nat.card F = 4) (f : alternatingGroup (Fin 5) ≃* SL(2,F))
    (n : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))
    (hlarge : 1 < generationParameter H)
    (hCZ : centralizer ((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H) =
      (T.subtype hH.1.1.2 : Subgroup H))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) = ⊥)
    (K : Subgroup H) (hb : IsBlock K)
    (hR : pResidual 2 H = K ∨
      ∃ t : H, pResidual 2 H = K ⊔ K.map (MulAut.conj t).toMonoidHom) :
    Chapter1.IsSylowIn 2 (baumann (T.subtype hH.1.1.2 : Subgroup H)) (pResidual 2 H) ∧
      baumann (T.subtype hH.1.1.2 : Subgroup H) =
        (T.subtype hH.1.1.2 : Subgroup H) ⊓ pResidual 2 H := by
  let S := T.subtype hH.1.1.2
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  let Z := (omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H
  have hm := (source_hstar_block_full_core_moved D e hn hH hZH hF f n
    hlarge hCZ hz K hb hR).2
  have hkr : centralizer (U : Set H) ≤ pResidual 2 H := by
    rw [source_hstar_action_kernel_eq_core_of_seed_centralizer D hH hCZ,hm]
    exact Subgroup.commutator_le_right (H₁ := pCore 2 H) (H₂ := pResidual 2 H)
  have hs : ¬ Group.IsSolvable H := by
    intro hs
    let := hs
    exact (not_lt_of_ge (generationParameter_le_one_of_solvable (G := H))) hlarge
  have hS := source_baumann_sylow_in_residual_of_seed_centralizer
    (Chapter3.sqtk_of_mem_H D.simpleQTKE hH.1.1.1) S
    (source_a5_hstar_minimal_parabolic D e hn hH) U
    (source_hstar_omega_orbit_reduced D hH) hs
    (source_hstar_thompson_moves_omega_orbit_of_natural_four D e hn hH hZH hF f n)
    Z (subgroupOf_mono H (le_conjugateSpanBy _ _)) hCZ hkr
  refine ⟨hS,?_⟩
  have hBS : baumann (S : Subgroup H) ≤ (S : Subgroup H) := inf_le_left
  exact ((Chapter1.isSylowIn_iff.mp hS).2.2 _
    (S.isPGroup'.to_le inf_le_left)
    (le_inf hBS (Chapter1.isSylowIn_iff.mp hS).2.1) inf_le_right).symm
end CFSG.Quasithin.Chapter10

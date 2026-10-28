module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OrdinarySevenOriginal.SixComparison

/-!
# The literal local and replacement permutation images

The source normalizer residual maps onto the two-residual of the even
three-pair normalizer. The six-point replacement acts on precisely the
six-letter complement. All maps are restrictions of the same plus action.

Source: Aschbacher–Smith, Lemma 13.6.22, printed p.932.
-/

public section
open scoped IsMulCommutative
open Subgroup Equiv Representation.BinaryOffender
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OrdinarySevenOriginal
open AlternatingBranches.OrdinarySeven SourcePlacement Marking ModuleComparison LocalResidual
variable {G : Type*} [Group G] [Finite G]

private theorem image_residual {Q : Type*} [Group Q] (H N : Subgroup G)
    (hNH : N ≤ H) (f : H →* Q) :
    (((pResidual 2 N).map N.subtype).subgroupOf H).map f =
      (pResidual 2 ((N.subgroupOf H).map f)).map ((N.subgroupOf H).map f).subtype := by
  have hr := map_embedded_pResidual 2 (N.subgroupOf H) H.subtype
  rw [map_subgroupOf_eq_of_le hNH] at hr
  have hinside : ((pResidual 2 N).map N.subtype).subgroupOf H =
      (pResidual 2 (N.subgroupOf H)).map (N.subgroupOf H).subtype := by
    rw [← hr]
    exact comap_map_eq_self_of_injective H.subtype_injective _
  rw [hinside, map_embedded_pResidual]

/-- The source normalizer residual has the actual even pair-normalizer
residual as its image in the chosen permutation coordinates. -/
theorem local_image_eq_residual
    (K L T S : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hY : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (hS : S = ChapterB.baumann (Tv T v))
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (φ : Gplus K L T z v hL hz →* Perm (Fin 7)) (hi : Function.Injective φ)
    (hc : ∀ k : K, φ (plusMk K L T z v hL hz
      ⟨k, ComponentSelection.K_le_plusActor K L T v k.property⟩) =
        (blockProjection K e k : Perm (Fin 7)))
    (hJ : (plusImage K L T z v hL hz (Stellmacher.elementaryAbelianMaxJ (Tv T v))).map φ =
      threeTranspositions)
    (hSJ : plusImage K L T z v hL hz S =
      plusImage K L T z v hL hz (Stellmacher.elementaryAbelianMaxJ (Tv T v)))
    (hres : Lv L v = (pResidual 2 (K ⊓ normalizer (S : Set G) : Subgroup G)).map
      (K ⊓ normalizer (S : Set G)).subtype) :
    (plusImage K L T z v hL hz (Lv L v)).map φ =
      (pResidual 2 evenPairNormalizer).map evenPairNormalizer.subtype := by
  let H := plusActor K L T v
  let ρ := φ.comp (plusMk K L T z v hL hz)
  have hplus (A : Subgroup G) : (A.subgroupOf H).map ρ =
      (plusImage K L T z v hL hz A).map φ := (map_map _ _ _).symm
  have hKimage : (K.subgroupOf H).map ρ = alternatingGroup (Fin 7) :=
    actionImage_component K H (ComponentSelection.K_le_plusActor K L T v) e ρ hc
  have hNimage : ((K ⊓ normalizer (S : Set G)).subgroupOf H).map ρ =
      evenPairNormalizer := by
    rw [hplus, plus_normalizer_comparison K L T S z v hL hz hY hn hLK hS e φ hi hc,
      map_relative_normalizer_of_injective _ _ φ hi, hSJ, hJ, ← hplus K, hKimage]
    rfl
  rw [← hplus, hres, image_residual H _
    (inf_le_left.trans (ComponentSelection.K_le_plusActor K L T v)) ρ, hNimage]

omit [Finite G] in
/-- The same compatible action places every replacement element in the
stabilizer of the seventh letter. -/
theorem replacement_image_le_stabilizer
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (φ : Gplus K L T z v hL hz →* Perm (Fin 7))
    (hc : ∀ k : K, φ (plusMk K L T z v hL hz
      ⟨k, ComponentSelection.K_le_plusActor K L T v k.property⟩) =
        (blockProjection K e k : Perm (Fin 7))) :
    (plusImage K L T z v hL hz (replacement K e 6)).map φ ≤
      MulAction.stabilizer (Perm (Fin 7)) (6 : Fin 7) := by
  rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
  have hbK : (b : G) ∈ K := replacement_le K e 6 hb
  rw [hc ⟨b, hbK⟩]
  obtain ⟨k, hk, he⟩ := hb
  have hfix := (mem_sixStabilizer_iff 6 (blockProjection K e k)).mp
    (residualLift_le (blockProjection K e) 6 hk)
  have hek : k = (⟨b, hbK⟩ : K) := Subtype.ext he
  change (blockProjection K e ⟨b, hbK⟩ : Perm (Fin 7)) 6 = 6
  simpa only [hek] using hfix

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OrdinarySevenOriginal

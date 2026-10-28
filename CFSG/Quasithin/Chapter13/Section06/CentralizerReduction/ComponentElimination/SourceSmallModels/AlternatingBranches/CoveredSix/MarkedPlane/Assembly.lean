module

public import Theory.Representation.BinaryOffender.CentralSectionAction

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.MarkedPlane.SourceLine
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.MarkedPlane.BaumannLift
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.MarkedPlane.FixedSpace

/-!
# Applying a marked Thompson image to the source commutator

This assembly constructs the ambient fixed subgroup from a marked subgroup
of K/O₂(K). A commuting square with the literal plus map and identification
of the Baumann image turn the finite fixed-space normalizer calculation
into ambient placement using Baumann heredity and 13.6.5. The result is
applied to the same source line [V,Lᵥ].

The marking, its dimension and the finite normalizer calculation remain
explicit here. This is not the completed Thompson marking theorem.
Source: Aschbacher–Smith, combined manuscript, 13.6.22, printed p.932.
-/

@[expose] public section
open Subgroup CFSG.Quasithin.ChapterC Representation
open Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open ComponentSelection
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Earlier invariance and Lᵥ≤K identify the literal plus actor with KTᵥ,
so the original local-family Sylow witness controls the plus kernel. -/
theorem plus_kernel_le_sylow (K L T : Subgroup G) (z v : G)
    (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hk : IsPGroup 2 (plusMk K L T z v hL hz).ker) :
    (plusMk K L T z v hL hz).ker ≤ (Tv T v).subgroupOf (plusActor K L T v) := by
  have hSylow : Chapter1.IsSylowIn 2 (Tv T v) (plusActor K L T v) := by
    rw [plusActor, Kminus_eq_of_invariant K T v hn, sup_of_le_left hLK]
    exact hK.1.2.2.1
  obtain ⟨P, hP⟩ := hSylow
  intro x hx
  change (x : G) ∈ Tv T v
  rw [← hP]
  exact mem_map.mpr ⟨x, hk.le_sylow_of_normal P hx, rfl⟩

/-- The Frattini normalizer image is the whole normalizer of the marked
four-group; every core-quotient element is lifted through its actual map. -/
theorem core_baumann_normalizer_image
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hk : (plusMk K L T z v hL hz).ker ≤ (Tv T v).subgroupOf (plusActor K L T v))
    (A : Subgroup (K ⧸ pCore 2 K))
    (f : (K ⧸ pCore 2 K) →* Gplus K L T z v hL hz)
    (fi : Function.Injective f)
    (hf : ∀ k : K, f (QuotientGroup.mk' (pCore 2 K) k) =
      plusMk K L T z v hL hz (inclusion (K_le_plusActor K L T v) k))
    (hBA : plusImage K L T z v hL hz (ChapterB.baumann (Tv T v)) = A.map f) :
    ((K ⊓ normalizer (ChapterB.baumann (Tv T v) : Set G)).subgroupOf K).map
      (QuotientGroup.mk' (pCore 2 K)) = normalizer (A : Set _) := by
  have he := source_plus_baumann_normalizer_comap K L T z v hL hz hk
  have heA := (A.map f).comap_normalizer_eq_of_le_range (map_le_range f A)
  rw [comap_map_eq_self_of_injective fi] at heA
  apply le_antisymm
  · rintro x ⟨k, hkS, rfl⟩
    have hp : plusMk K L T z v hL hz (inclusion (K_le_plusActor K L T v) k) ∈
        normalizer (plusImage K L T z v hL hz (ChapterB.baumann (Tv T v)) : Set _) := by
      change inclusion (K_le_plusActor K L T v) k ∈ (normalizer _).comap _
      rw [he]
      exact hkS.2
    rw [hBA, ← hf] at hp
    exact heA.le hp
  · intro a ha
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) a
    have hp := A.le_normalizer_map f (mem_map_of_mem f ha)
    rw [hf, ← hBA] at hp
    change inclusion (K_le_plusActor K L T v) k ∈ (normalizer _).comap _ at hp
    rw [he] at hp
    exact mem_map.mpr ⟨k, ⟨k.property, hp⟩, rfl⟩

omit [Finite G] in
/-- The compatibility square also identifies images of all actual subgroups
of K, including both relative normalizers in the source sentence. -/
theorem plusImage_eq_coreImage_map
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (f : (K ⧸ pCore 2 K) →* Gplus K L T z v hL hz)
    (hf : ∀ k : K, f (QuotientGroup.mk' (pCore 2 K) k) =
      plusMk K L T z v hL hz (inclusion (K_le_plusActor K L T v) k))
    (D : Subgroup G) (hD : D ≤ K) :
    plusImage K L T z v hL hz D =
      ((D.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))).map f := by
  apply le_antisymm
  · rintro a ⟨d, hd, rfl⟩
    exact ⟨QuotientGroup.mk' (pCore 2 K) ⟨d, hD hd⟩,
      ⟨⟨d, hD hd⟩, hd, rfl⟩, hf ⟨d, hD hd⟩⟩
  · rintro a ⟨b, ⟨k, hk, rfl⟩, rfl⟩
    rw [hf]
    exact ⟨inclusion (K_le_plusActor K L T v) k, hk, rfl⟩

/-- The two literal plus normalizer images in the covered-six source
sentence coincide. The reverse inclusion uses invariance of fixed vectors
under the normalizer of their actor. -/
theorem source_normalizer_images_eq
    (K L T : Subgroup G) (z v : G)
    (h : IsExceptionalAhat6Block K) [IsElementaryAbelian 2 (blockU K)]
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hk : (plusMk K L T z v hL hz).ker ≤ (Tv T v).subgroupOf (plusActor K L T v))
    (A : Subgroup (K ⧸ pCore 2 K))
    (f : (K ⧸ pCore 2 K) →* Gplus K L T z v hL hz)
    (fi : Function.Injective f)
    (hf : ∀ k : K, f (QuotientGroup.mk' (pCore 2 K) k) =
      plusMk K L T z v hL hz (inclusion (K_le_plusActor K L T v) k))
    (hBA : plusImage K L T z v hL hz (ChapterB.baumann (Tv T v)) = A.map f)
    (hNA : subspaceStabilizer (binaryAction h) (fixedSpace (binaryAction h) A) ≤
      normalizer (A : Set _)) :
    plusImage K L T z v hL hz (K ⊓ normalizer (ChapterB.baumann (Tv T v) : Set G)) =
      plusImage K L T z v hL hz (K ⊓ normalizer (fixedSubgroup K A : Set G)) := by
  have he : subspaceStabilizer (binaryAction h) (fixedSpace (binaryAction h) A) =
      normalizer (A : Set _) :=
    le_antisymm hNA (fixedSpace_stable_of_normalizes (binaryAction h) le_rfl)
  rw [plusImage_eq_coreImage_map K L T z v hL hz f hf _ inf_le_left,
    plusImage_eq_coreImage_map K L T z v hL hz f hf _ inf_le_left,
    core_baumann_normalizer_image K L T z v hL hz hk A f fi hf hBA,
    fixedSubgroup_normalizer_image K h A, he]

/-- A compatible core-to-plus map preserves all quotient representatives.
The two image identities here are mathematical marking obligations, not
assumed ambient placement. -/
theorem fixedSubgroup_placement_of_marked_image
    (K L T M : Subgroup G) (z v : G)
    (h : IsExceptionalAhat6Block K) [IsElementaryAbelian 2 (blockU K)]
    (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hk : IsPGroup 2 (plusMk K L T z v hL hz).ker)
    (hc : Gv v ⊓ normalizer (ChapterB.baumann (Tv T v) : Set G) ≤ Mv M v)
    (A : Subgroup (K ⧸ pCore 2 K))
    (f : (K ⧸ pCore 2 K) →* Gplus K L T z v hL hz)
    (hf : ∀ k : K, f (QuotientGroup.mk' (pCore 2 K) k) =
      plusMk K L T z v hL hz (inclusion (K_le_plusActor K L T v) k))
    (hBA : plusImage K L T z v hL hz (ChapterB.baumann (Tv T v)) = A.map f)
    (hNA : subspaceStabilizer (binaryAction h) (fixedSpace (binaryAction h) A) ≤
      normalizer (A : Set (K ⧸ pCore 2 K))) :
    K ⊓ normalizer (fixedSubgroup K A : Set G) ≤ Mv M v := by
  intro k hkP
  let kK : K := ⟨k, hkP.1⟩
  have hs := (ambientSubspace_stabilizer K h (fixedSubgroup K A)
    (fixedSubgroup_le K A) kK).mpr hkP.2
  rw [ambientSubspace_fixedSubgroup K h] at hs
  have ha : f (QuotientGroup.mk' (pCore 2 K) kK) ∈ normalizer (A.map f : Set _) :=
    A.le_normalizer_map f (mem_map_of_mem f (hNA hs))
  rw [hf, ← hBA] at ha
  exact source_plus_baumann_normalizer_le K L T M z v hK.1.1 hL hz
    (plus_kernel_le_sylow K L T z v hK hn hLK hL hz hk) hc
    (mem_map.mpr ⟨inclusion (K_le_plusActor K L T v) kK, ha, rfl⟩)

/-- Actual application to [V,Lᵥ], constructing U₂ from the marked A.
Only the remaining quotient marking and finite plane-normalizer facts are
explicit; commutator placement and ambient normalizer placement are proved. -/
theorem source_line_for_marked_image
    {L M V : Subgroup G} (s : A5Module.Marking L V) (K T : Subgroup G)
    (h : IsExceptionalAhat6Block K) [IsElementaryAbelian 2 (blockU K)]
    (hK : K ∈ Yz L T (A5Module.markedZ s) (A5Module.markedV s))
    (hn : Tv T (A5Module.markedV s) ≤ normalizer (K : Set G))
    (hzT : A5Module.markedZ s ∈ Tv T (A5Module.markedV s))
    (hU : IsPGroup 2 (Uv (A5Module.markedZ s) (A5Module.markedV s)))
    (hLK : Lv L (A5Module.markedV s) ≤ K)
    (hL : Tv T (A5Module.markedV s) ≤ normalizer (Lv L (A5Module.markedV s) : Set G))
    (hz : Tv T (A5Module.markedV s) ≤ centralizer ({A5Module.markedZ s} : Set G))
    (hk : IsPGroup 2 (plusMk K L T (A5Module.markedZ s) (A5Module.markedV s) hL hz).ker)
    (hc : Gv (A5Module.markedV s) ⊓ normalizer (ChapterB.baumann (Tv T (A5Module.markedV s)) : Set G) ≤
      Mv M (A5Module.markedV s))
    (A : Subgroup (K ⧸ pCore 2 K))
    (f : (K ⧸ pCore 2 K) →* Gplus K L T (A5Module.markedZ s) (A5Module.markedV s) hL hz)
    (hf : ∀ k : K, f (QuotientGroup.mk' (pCore 2 K) k) =
      plusMk K L T (A5Module.markedZ s) (A5Module.markedV s) hL hz
        (inclusion (K_le_plusActor K L T (A5Module.markedV s)) k))
    (hBA : plusImage K L T (A5Module.markedZ s) (A5Module.markedV s) hL hz
      (ChapterB.baumann (Tv T (A5Module.markedV s))) = A.map f)
    (hNA : subspaceStabilizer (binaryAction h) (fixedSpace (binaryAction h) A) ≤ normalizer (A : Set _))
    (hML : M ≤ normalizer (L : Set G))
    (hMV : Mv M (A5Module.markedV s) ≤ normalizer (V : Set G)) :
    Module.finrank (ZMod 2) (ambientSubspace K ⁅V, Lv L (A5Module.markedV s)⁆) = 2 ∧
      subspaceStabilizer (binaryAction h) (fixedSpace (binaryAction h) A) ≤
        subspaceStabilizer (binaryAction h)
          (ambientSubspace K ⁅V, Lv L (A5Module.markedV s)⁆) := by
  have hp := fixedSubgroup_placement_of_marked_image K L T M
    (A5Module.markedZ s) (A5Module.markedV s) h hK hn hLK hL hz hk hc A f hf hBA hNA
  have hl := source_commutator_le_block s K T h hK hn hzT hU hLK
  have hs := source_line_invariant_of_placement K h s (fixedSubgroup K A)
    (fixedSubgroup_le K A) hl hp hML hMV
  rwa [ambientSubspace_fixedSubgroup K h] at hs

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix

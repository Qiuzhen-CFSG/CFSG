module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.SeedGeometry
public import Stellmacher.BaumannTwoOvergroupTransport
public import Stellmacher.BaumannNormalizer
public import Stellmacher.BaumannMap
public import Theory.GroupTheory.SylowNormalizerFrattini

/-!
# Frattini lifting for the actual Baumann image

The normalizer of the Baumann subgroup of a Sylow two-subgroup maps onto
its image normalizer under any surjective homomorphism. To prove this,
take the preimage of the Baumann image and a Sylow subgroup containing
the original Baumann subgroup. Baumann transport identifies its Baumann
subgroup with the original one. The relative Frattini argument then gives
the required lift, and the remaining factor has image in the Baumann image.

The source application uses the literal plus quotient of K₋L_vT_v.
The earlier centralizer Sylow and 13.6.4 identify its Baumann subgroup
with the original Baum(T). No centralizing-kernel hypothesis is needed.
This proves lifting for the full actor; restriction to N_K(Baum(T)) and
the Thompson/radical image identification are still separate obligations.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Lemma 13.6.20, printed p.931.
-/

@[expose] public section

open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry
open ChapterB

variable {G D : Type*} [Group G] [Group D] [Finite G]

/-- Baumann normalizers map onto their image normalizers, for arbitrary kernels. -/
theorem baumann_normalizer_map (P : Sylow 2 G) (f : G →* D)
    (hf : Function.Surjective f) :
    (normalizer (baumann (P : Subgroup G) : Set G)).map f =
      normalizer ((baumann (P : Subgroup G)).map f : Set D) := by
  let B := baumann (P : Subgroup G)
  let C := (B.map f).comap f
  let N := (normalizer (B.map f : Set D)).comap f
  have hBC : B ≤ C := le_comap_map f B
  have hBp : IsPGroup 2 B := P.isPGroup'.to_le inf_le_left
  have hBp' : IsPGroup 2 (B.subgroupOf C) :=
    hBp.of_injective (subgroupOfEquivOfLe hBC).toMonoidHom
      (subgroupOfEquivOfLe hBC).injective
  obtain ⟨Q, hBQ⟩ := hBp'.exists_le_sylow
  have hBQ' : B ≤ (Q : Subgroup C).map C.subtype := by
    rw [← map_subgroupOf_eq_of_le hBC]
    exact map_mono hBQ
  have hBaum : baumann ((Q : Subgroup C).map C.subtype) = B :=
    (twoSubgroup_thompson_baumann_eq P _ (Q.isPGroup'.map C.subtype) hBQ').2
  have hnorm : normalizer ((Q : Subgroup C).map C.subtype : Set G) ≤
      normalizer (B : Set G) := by
    rw [← hBaum]
    exact normalizer_le_normalizer_baumann _
  have hfr := le_normalizer_sylow_sup C N (comap_mono (B.map f).le_normalizer)
    ((comap_normalizer_eq_of_surjective (B.map f) hf).le) Q
  apply le_antisymm (B.le_normalizer_map f)
  have hmap := map_mono (f := f) hfr
  rw [Subgroup.map_sup, show C.map f = B.map f from map_comap_eq_self_of_surjective hf _] at hmap
  have hmap' : N.map f ≤ (normalizer (B : Set G)).map f :=
    hmap.trans (sup_le (map_mono hnorm) (map_mono B.le_normalizer))
  simpa only [N, map_comap_eq_self_of_surjective hf] using hmap'

open ComponentSelection

/-- Apply the Frattini lift to the actual plus map and the earlier source Sylow. -/
theorem plusActor_baumann_normalizer_image
    (K L T : Subgroup G) (z v : G) (hK : K ≤ Gv v)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (Gv v))
    (hP : (P : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (h1364 : baumann T = baumann (Tv T v)) :
    plusImage K L T z v hL hz
      (plusActor K L T v ⊓ normalizer (baumann T : Set G)) =
        normalizer (plusImage K L T z v hL hz (baumann T) : Set _) := by
  let A := plusActor K L T v
  obtain ⟨Q, hQ⟩ := P.exists_map_subtype_eq_of_le
    (plusActor_le_Gv K L T v hK)
    (show (P : Subgroup (Gv v)).map (Gv v).subtype ≤ A by
      rw [hP]
      exact le_sup_right)
  have hBQ : (baumann (Q : Subgroup A)).map A.subtype = baumann T := by
    change ((Q : Subgroup A) ⊓ centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (Q : Subgroup A)) : Set A)).map
        A.subtype = _
    rw [baumann_map_injective A.subtype A.subtype_injective, hQ, hP, h1364]
    rfl
  have hBA : baumann T ≤ A := hBQ ▸ map_subtype_le _
  have he : baumann (Q : Subgroup A) = (baumann T).subgroupOf A := by
    apply map_injective A.subtype_injective
    rw [hBQ, map_subgroupOf_eq_of_le hBA]
  have hi : (A ⊓ normalizer (baumann T : Set G)).subgroupOf A =
      normalizer ((baumann T).subgroupOf A : Set A) := by
    rw [← subgroupOf_normalizer_eq hBA]
    ext a
    exact and_iff_right a.property
  have h := baumann_normalizer_map Q (plusMk K L T z v hL hz)
    (plusMk_surjective K L T z v hL hz)
  rw [he] at h
  change ((A ⊓ normalizer (baumann T : Set G)).subgroupOf A).map
    (plusMk K L T z v hL hz) = _
  rw [hi]
  exact h

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry

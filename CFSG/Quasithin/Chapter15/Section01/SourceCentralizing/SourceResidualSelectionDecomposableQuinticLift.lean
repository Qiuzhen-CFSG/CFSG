module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticNormalizer
public import Mathlib.GroupTheory.Sylow

/-!
# Lifting a five-image normalizer through the actual action map

A five-subgroup of a finite action image can be lifted to a Sylow five
subgroup of the preimage. If the image centralizes the cubic residual, the
lift normalizes the residual together with the action kernel. The generic
five-normalizer theorem then removes the kernel and gives the desired image
normalizer. This is the literal map-lift needed for the proper diagonal
prime-five branch.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15
namespace DecomposableQuinticControl

/-- A five-subgroup of an action image which centralizes a cubic residual is
already contained in the image of the residual normalizer. -/
theorem five_image_le_normalizer_map_of_cubic_residual
    {L D : Type*} [Group L] [Finite L] [Group D] [Finite D]
    (f : L →* D) (hf : Function.Surjective f) (Y : Subgroup L)
    (hpY : IsPPerfect 2 Y) (hY : Nat.card (Y ⧸ pCore 2 Y) = 3)
    (hrL : primeRank 3 L ≤ 2)
    (A : Subgroup D) (hA5 : IsPGroup 5 A)
    (hAY : A ≤ centralizer (Y.map f : Set D))
    (hker : f.ker ≤ normalizer (Y : Set L)) :
    A ≤ (normalizer (Y : Set L)).map f := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let B := A.comap f
  let q : B →* A := f.subgroupComap A
  have hq : Function.Surjective q := f.subgroupComap_surjective_of_surjective A hf
  let P : Sylow 5 B := Sylow.nonempty.some
  have hPmap : (P : Subgroup B).map q = ⊤ :=
    ((P.mapSurjective hq).is_maximal' (hA5.to_subgroup ⊤) le_top).symm
  let P0 : Subgroup L := (P : Subgroup B).map B.subtype
  have hP0 : IsPGroup 5 P0 := P.isPGroup'.map B.subtype
  have hPmapA : P0.map f = A := by
    change ((P : Subgroup B).map B.subtype).map f = A
    rw [map_map]
    change (P : Subgroup B).map (A.subtype.comp q) = A
    rw [← map_map, hPmap, ← MonoidHom.range_eq_map, range_subtype]
  let K : Subgroup L := Y ⊔ f.ker
  have hYK : Y ≤ K := le_sup_left
  have hKnY : K ≤ normalizer (Y : Set L) :=
    sup_le Y.le_normalizer hker
  have hPK : P0 ≤ normalizer (K : Set L) := by
    have hm : P0.map f ≤ normalizer (Y.map f : Set D) :=
      hPmapA ▸ hAY.trans (Subgroup.centralizer_le_normalizer _)
    have hh := ((map_le_iff_le_comap).mp hm).trans ((Y.map f).le_normalizer_comap f)
    simpa only [Subgroup.comap_map_eq] using hh
  have hrK : primeRank 3 K ≤ 2 := (primeRank_subgroup_le 3 K).trans hrL
  have hPNY := five_normalizes_cubic_residual P0 K Y hYK hKnY hpY hY hrK hP0 hPK
  rw [← hPmapA]
  exact map_mono hPNY

end DecomposableQuinticControl
end CFSG.Quasithin.Chapter15

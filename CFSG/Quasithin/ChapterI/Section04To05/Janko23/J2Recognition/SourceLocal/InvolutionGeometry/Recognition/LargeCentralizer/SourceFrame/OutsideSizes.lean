module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.OutsideSizes.Extension

/-!
# Local centralizer sizes for outside involutions

Conjugation on the actual core identifies its fixed group with the model
fixed group of order four. The cocycle calculation makes the map onto the
A₅ quotient centralizer surjective, giving order sixteen in H = C_G(z).
Transport along the literal subgroup inclusions gives exactly the two
ambient intersections consumed by `SourceFrame.CubicGeometry.intersections`.
Only `HTypeAt` is needed; no ambient group order or second-centralizer
recognition enters the proof.

Source: Aschbacher, *Sporadic Groups* (1994), 46.8 and 46.11, pp.253–255,
and the beginning of 47.1, pp.259–260.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer
variable {G : Type*} [Group G] [Finite G]

public theorem outside_centralizer_sizes {z t : G} (h : HTypeAt z)
    (htH : t ∈ involutionCentralizer z) (ht : orderOf t = 2) (htQ : t ∉ ambientCore z) :
    Nat.card ↥(involutionCentralizer t ⊓ ambientCore z) = 4 ∧
    Nat.card ↥(involutionCentralizer t ⊓ involutionCentralizer z) = 16 := by
  let H := involutionCentralizer z
  let u : H := ⟨t, htH⟩
  let C := centralizer ({u} : Set H)
  have hu : orderOf u = 2 := (orderOf_coe u).symm.trans ht
  have huQ : u ∉ localCore z := fun hh => htQ (mem_map_of_mem H.subtype hh)
  obtain ⟨hQ, hC⟩ := J2OutsideSizesCalculation.extension_sizes (localCore z)
    h.core_equiv.some (centralizer_generalizedFitting_le _) h.quotient_equiv.some u hu huQ
  have hmap : C.map H.subtype = involutionCentralizer t ⊓ H := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy)), y.property⟩
    · rintro ⟨hxt, hxH⟩
      refine mem_map.mpr ⟨⟨x, hxH⟩, mem_centralizer_singleton_iff.mpr ?_, rfl⟩
      exact Subtype.ext (mem_centralizer_singleton_iff.mp hxt)
  have hmapQ : (C ⊓ localCore z).map H.subtype = involutionCentralizer t ⊓ ambientCore z := by
    rw [map_inf _ _ _ H.subtype_injective, hmap]
    change (involutionCentralizer t ⊓ H) ⊓ ambientCore z = _
    rw [inf_assoc, inf_eq_right.mpr (ambientCore_le z)]
  constructor
  · rw [← hmapQ, card_map_of_injective H.subtype_injective]
    exact hQ
  · rw [← hmap, card_map_of_injective H.subtype_injective]
    exact hC

public theorem outsideCentralizerSizes (D : Seed G) : SourceFrame.OutsideCentralizerSizes D :=
  fun _ htH ht htQ => outside_centralizer_sizes D.localType htH ht htQ
end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer

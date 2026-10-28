module
public import CFSG.Quasithin.ChapterE.Section02.Structure.OddLinearTwo.NonexceptionalSource
public import CFSG.Quasithin.ChapterE.Section02.Structure.NormalSimpleImage
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.Involution.Source
public import Theory.SpecificGroups.Alternating.FiveBorelCentralFactor
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# The original odd linear-two witness family

Pass the original normal C-component and elementary subgroup V through
H/J, with their prescribed Sylow and actual maximal subgroup. The proved
normal odd-PSL₂ source geometry forces the image of V to have order at
most two. The original outside-core assumption makes that image nontrivial.
The genuine involution-pair construction and its lifting theorem then
restore all of V, the internal conjugator, the actual Sylow intersection,
and the two-closed relative core with an odd-prime-power dihedral quotient.

No witness, placement, or automizer premise remains. The model exceptions
of orders five and nine are retained in the separate binary Bender and
symplectic source families. Source: Aschbacher–Smith E.2.7–9, printed
pp.218–222. The actual field exponent is independent of n(H).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Witnesses.OddLinearTwo
universe u
variable {H:Type u} [Group H] [Finite H] {κ:GroupClass.{u}}

/-- Construct the original dihedral E.2.9 witness for the complete nonexceptional normal odd-PSL₂ family. -/
theorem source_original
    (hA:ChapterA.Section02.TheoremA κ H) (hH:IsSQTK κ H)
    (T:Sylow 2 H) (hP:ChapterB.IsMinimalParabolicOver T ⊤)
    (hs:¬Group.IsSolvable H) (K:Subgroup H) (hK:K.IsCComponent) [K.Normal]
    (hgen:K⊔(T:Subgroup H)=⊤)
    {p n:ℕ} (hp:p.Prime) (ho:Odd p) (hlarge:5<p^n) (hnine:p^n≠9)
    (hm:ClassicalGroup.IsPSL (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 2 (p^n))
    (V:Subgroup H) [IsElementaryAbelian 2 V] (hVT:V≤T)
    (hvn:(V.subgroupOf (T:Subgroup H)).Normal)
    (hVM:V≤(ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout:¬V≤ChapterB.minimalParabolicCore T hP) :
    Nonempty (Solvable.Witness T (ChapterB.minimalParabolicMax T hP) V) := by
  let J:=ChapterB.minimalParabolicCore T hP
  let M:=ChapterB.minimalParabolicMax T hP
  let q:=QuotientGroup.mk' J
  let S:=T.mapSurjective (QuotientGroup.mk'_surjective J)
  let W:=V.map q
  let D:=K.map q
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map q
  let : Fact p.Prime := ⟨hp⟩
  have hi:=Structure.source_normal_simple_image T hP hs K hK hgen
  have hmin:ChapterB.IsMinimalParabolicOver S ⊤ := (Structure.source_star_minimal_core_free T hP).1
  have hcore:ChapterB.minimalParabolicCore S hmin=⊥ := (Structure.source_star_minimal_core_free T hP).2
  have hO:pCore 2 (H⧸J)=⊥ := bot_unique ((ChapterB.minimalParabolicTwoCore_le_core S hmin).trans hcore.le)
  have hmax:ChapterB.minimalParabolicMax S hmin=M.map q :=
    (ChapterB.minimalParabolicMax_map_core T hP q (QuotientGroup.mk'_surjective J)
      (by rw [QuotientGroup.ker_mk'])).symm
  have hWS:W≤(S:Subgroup (H⧸J)) := map_mono hVT
  have hSW:(S:Subgroup (H⧸J))≤normalizer (W:Set (H⧸J)) :=
    (map_mono ((normal_subgroupOf_iff_le_normalizer hVT).mp hvn)).trans (le_normalizer_map q)
  have hWcore:W≤(ChapterB.minimalParabolicMax S hmin).pCoreIn 2 := by
    rw [hmax]
    exact (map_mono hVM).trans (Theory.SpecificGroups.Alternating.FiveBorelCentralFactor.core_image_le q M)
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
  have hc:Nat.card W≤2 := Structure.odd_linear_source_elementary_card_le_two
    (Structure.source_star_sqtk hA hH T hP hs) S hmin hcore D hi.2.2.2 hO ho hcard
    (by simpa only [hcard] using hlarge) (by simpa only [hcard] using hnine)
    e W inferInstance hWcore hWS hSW
  have hne:W≠⊥ := by
    intro hh
    have hle := (map_eq_bot_iff V).mp hh
    exact hout (by simpa only [q,QuotientGroup.ker_mk'] using hle)
  have htwo:Nat.card W=2 := by
    have := (one_lt_card_iff_ne_bot W).mpr hne
    omega
  exact Involution.source_star_order_two T hP V hVT hvn hVM htwo
end CFSG.Quasithin.ChapterE.Witnesses.OddLinearTwo

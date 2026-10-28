module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.OddDegreeThree.LinearTI
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.OddDegreeThree.UnitaryCore
public import CFSG.Quasithin.ChapterE.Section02.Structure.NormalSimpleImage
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.Involution.Source
public import Theory.SpecificGroups.Alternating.FiveBorelCentralFactor
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# Original witnesses for both odd degree-three families

The original TI subgroup has elementary normal closure inside M. Its
image is therefore normal elementary in the literal star maximal subgroup;
the genuine graph-centralizer theorem bounds that image by two, even over
the field of three elements. The original outside-core condition forces
order two. The involution-pair lift then constructs the full original
witness, preserving V, its internal conjugator, Sylow intersection and
two-closed core. No TI condition is imposed after quotienting.

The unitary row supplies the same small image from its two-core placement
without a TI hypothesis. Source: Aschbacher–Smith E.2.8–9 and E.2.15,
pp.222,228.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Witnesses.OddDegreeThree
universe u
variable {H:Type u} [Group H] [Finite H] {κ:GroupClass.{u}}

/-- The original TI hypothesis supplies the full dihedral witness in the odd PSL₃ row. -/
theorem linear_source_original_of_ti
    (T:Sylow 2 H) (hP:ChapterB.IsMinimalParabolicOver T ⊤)
    (hs:¬Group.IsSolvable H) (K:Subgroup H) (hK:K.IsCComponent) [K.Normal]
    (hgen:K⊔(T:Subgroup H)=⊤)
    {p:ℕ} (hp:p.Prime) (ho:Odd p)
    (hm:ClassicalGroup.IsPSL (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 p)
    (V:Subgroup H) [IsElementaryAbelian 2 V] (hVT:V≤T)
    (hvn:(V.subgroupOf (T:Subgroup H)).Normal)
    (hVM:V≤(ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout:¬V≤ChapterB.minimalParabolicCore T hP)
    (hTI:∀g∈ChapterB.minimalParabolicMax T hP,
      V⊓V.map (MulAut.conj g).toMonoidHom=⊥ ∨ V.map (MulAut.conj g).toMonoidHom=V) :
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
  let : D.Normal := hi.2.2.1
  let : IsSimpleGroup D := hi.1
  have hc:Nat.card W≤2 := Structure.OddDegreeThree.linear_image_card_le_two_of_ti
    T M V (ChapterB.minimalParabolicMax_spec T hP).2 hVT hvn hVM hTI
    q S hmin D hi.2.2.2 hO hp ho hm hmax.symm
  have hne:W≠⊥ := by
    intro hh
    have hle := (map_eq_bot_iff V).mp hh
    exact hout (by simpa only [q,QuotientGroup.ker_mk'] using hle)
  have htwo:Nat.card W=2 := by
    have := (one_lt_card_iff_ne_bot W).mpr hne
    omega
  exact Involution.source_star_order_two T hP V hVT hvn hVM htwo

/-- The original odd unitary-three family needs no TI premise. -/
theorem unitary_source_original
    (T:Sylow 2 H) (hP:ChapterB.IsMinimalParabolicOver T ⊤)
    (hs:¬Group.IsSolvable H) (K:Subgroup H) (hK:K.IsCComponent) [K.Normal]
    (hgen:K⊔(T:Subgroup H)=⊤)
    {p:ℕ} (hp:p.Prime) (ho:Odd p)
    (hm:ClassicalGroup.IsPSU (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 p)
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
  let : D.Normal := hi.2.2.1
  let : IsSimpleGroup D := hi.1
  have hc:Nat.card W≤2 := Structure.OddDegreeThree.unitary_image_card_le_two
    M V hVM q S hmin D hi.2.2.2 hO hp ho hm hmax.symm
  have hne:W≠⊥ := by
    intro hh
    have hle := (map_eq_bot_iff V).mp hh
    exact hout (by simpa only [q,QuotientGroup.ker_mk'] using hle)
  have htwo:Nat.card W=2 := by
    have := (one_lt_card_iff_ne_bot W).mpr hne
    omega
  exact Involution.source_star_order_two T hP V hVT hvn hVM htwo
end CFSG.Quasithin.ChapterE.Witnesses.OddDegreeThree

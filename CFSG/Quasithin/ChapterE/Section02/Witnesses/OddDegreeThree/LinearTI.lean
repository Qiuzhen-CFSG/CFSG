module
public import CFSG.Quasithin.ChapterE.Section02.Structure.OddDegreeThree.NormalElementary
import all CFSG.Quasithin.ChapterE.Section02.Structure.OddDegreeThree.NormalElementary
public import CFSG.Quasithin.ChapterE.Section02.Structure.OddDegreeThree.Linear
public import Theory.GroupTheory.TIElementaryNormalClosure
/-!
# The original TI route for odd linear degree three

The core-free minimal-parabolic source row identifies its unique maximal
Sylow overgroup with an inner-involution centralizer in the actual graph
extension of PSL₃. Its normal elementary subgroups therefore have order at
most two, including the field of three elements.

For an original elementary TI subgroup V≤O₂(M), its normal closure inside
M is elementary. Map this closure through the caller's actual quotient map,
using the original marking of M. The result is normal elementary in the
reduced maximal overgroup, so V's image has order at most two. No TI
hypothesis is imposed on the image, and no cyclicity of the characteristic-
three two-core is asserted.

Source: Aschbacher–Smith E.2.2(2d), E.2.8 and E.2.15, pp.215, 222, 228.
-/
public section
open Subgroup
open scoped MatrixGroups
open Matrix.PSL3 Matrix.PSL3.OddPrimeGraphExtension Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
namespace CFSG.Quasithin.ChapterE.Structure.OddDegreeThree
variable {H:Type*} [Group H] [Finite H]

/-- Every normal elementary subgroup of the original linear maximal Sylow
overgroup has order at most two, including the prime three. -/
theorem linear_normal_elementary_card_le_two
    (T:Sylow 2 H) (hP:ChapterB.IsMinimalParabolicOver T ⊤)
    (K:Subgroup H) [K.Normal] [IsSimpleGroup K]
    (hgen:K⊔(T:Subgroup H)=⊤) (hcore:pCore 2 H=⊥)
    {p:ℕ} (hp:p.Prime) (ho:Odd p) (hm:ClassicalGroup.IsPSL K 3 p)
    (A:Subgroup H) [IsElementaryAbelian 2 A]
    (hAM:A≤ChapterB.minimalParabolicMax T hP)
    (hMA:ChapterB.minimalParabolicMax T hP≤normalizer (A:Set H)) :
    Nat.card A≤2 := by
  obtain ⟨t,ht,_,_,hM,_⟩:=linear_involution_centralizer T hP K hgen hcore hp ho hm
  obtain ⟨F,_,_,hF,⟨e⟩⟩:=hm
  let : IsSimpleGroup PSL(3,F):=e.symm.isSimpleGroup
  obtain ⟨f,hf⟩:=linear_graph_extension T hP K hgen hcore hp ho hF e
  let A':=A.map f.toMonoidHom
  let : IsElementaryAbelian 2 A':=IsElementaryAbelian.map f.toMonoidHom
  have hCM:(ChapterB.minimalParabolicMax T hP).map f.toMonoidHom=
      centralizer ({f (t:H)}:Set (graphExtension F)) := by
    rw [hM,NormalElementary.map_centralizer_singleton]
  have hAC:A'≤centralizer ({f (t:H)}:Set (graphExtension F)):=hCM ▸ map_mono hAM
  have hCA:centralizer ({f (t:H)}:Set (graphExtension F))≤normalizer (A':Set _) := by
    rw [←hCM]
    exact (map_mono hMA).trans (le_normalizer_map _)
  have hz:orderOf (f (t:H))=2 :=
    (orderOf_injective f.toMonoidHom f.injective (t:H)).trans
      ((orderOf_injective K.subtype K.subtype_injective t).trans ht)
  have hzI:f (t:H)∈innerPart F := hf ▸ mem_map_of_mem f.toMonoidHom t.property
  have h:=NormalElementary.card_le_two_of_inner_involution F
    (Field.two_ne_zero_of_odd_card F (hF ▸ ho)) _ hz hzI A' hAC hCA
  rwa [card_map_of_injective f.injective] at h

/-- The original TI subgroup has small image through the actual source map.
TI is used before taking the quotient, by forming its elementary normal
closure in the original maximal Sylow overgroup. -/
theorem linear_image_card_le_two_of_ti
    (T:Sylow 2 H) (M V:Subgroup H) [IsElementaryAbelian 2 V]
    (hTM:(T:Subgroup H)≤M) (hVT:V≤T)
    (hn:(V.subgroupOf (T:Subgroup H)).Normal) (hVcore:V≤M.pCoreIn 2)
    (hTI:∀g∈M,V⊓V.map (MulAut.conj g).toMonoidHom=⊥ ∨
      V.map (MulAut.conj g).toMonoidHom=V)
    {Q:Type*} [Group Q] [Finite Q] (f:H→*Q)
    (Tq:Sylow 2 Q) (hPq:ChapterB.IsMinimalParabolicOver Tq ⊤)
    (K:Subgroup Q) [K.Normal] [IsSimpleGroup K]
    (hgen:K⊔(Tq:Subgroup Q)=⊤) (hcore:pCore 2 Q=⊥)
    {p:ℕ} (hp:p.Prime) (ho:Odd p) (hm:ClassicalGroup.IsPSL K 3 p)
    (hM:M.map f=ChapterB.minimalParabolicMax Tq hPq) :
    Nat.card (V.map f)≤2 := by
  let E:=normalClosure (V.subgroupOf M:Set M)
  let : IsElementaryAbelian 2 E:=elementary_normalClosure_subgroupOf_ti T M V hTM hVT hn hVcore hTI
  let fm:=f.comp M.subtype
  let A:=E.map fm
  let : IsElementaryAbelian 2 A:=IsElementaryAbelian.map fm
  have hr:fm.range=ChapterB.minimalParabolicMax Tq hPq := by
    rw [MonoidHom.range_comp,range_subtype]
    exact hM
  have hAM:A≤ChapterB.minimalParabolicMax Tq hPq := hr ▸ map_le_range fm E
  have hMA:ChapterB.minimalParabolicMax Tq hPq≤normalizer (A:Set Q) := by
    rw [←hr,MonoidHom.range_eq_map,←E.normalizer_eq_top]
    exact le_normalizer_map _
  have hcard:=linear_normal_elementary_card_le_two Tq hPq K hgen hcore hp ho hm A hAM hMA
  have hVA:V.map f≤A := by
    have he:(V.subgroupOf M).map fm=V.map f := by
      change (V.subgroupOf M).map (f.comp M.subtype)=V.map f
      rw [←map_map,map_subgroupOf_eq_of_le (hVT.trans hTM)]
    rw [←he]
    exact map_mono le_normalClosure
  exact (card_le_of_le hVA).trans hcard
end CFSG.Quasithin.ChapterE.Structure.OddDegreeThree

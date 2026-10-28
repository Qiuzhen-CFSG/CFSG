module

public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicHexagon.Graph
public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicHexagon.BaseNeighbors
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.NormalizerSource
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.NormalizerCentralizer

/-!
# Aligning actual parabolic adjacency with the original base five

The endpoint normalizer is transitive on its four-group-invariant fives
and centralizes that four-group. Given an original incidence edge, use
its actual conjugator to align the first witness with B5. The other
parabolic retains its original involution color; its commuting five is
then the fixed subgroup of the genuine extraspecial O5(C_G(B5)).

All actors lie in the original first endpoint, and all conjugates and
five-subgroups remain literal ambient subgroups. The completion consumer
discharges fixed-subgroup orders through the original marked inverter.
This is the source adjacency reduction of J.4.10, printed p.444, formulated
without the false equality between the two opposite SL2 factors.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily
open Centralizers Centralizers.Choices MarkedInverter MarkedNormalizer
open Tits.ExceptionalParabolics.FullRee
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G}
  (p:Plane d) (B5:Sylow 5 d.toTypeRuSetup.H) (c:Choices d)
  (e:first≃*p.F₁ B5) (hz:(e modelZ:G)=c.z)

include hz in
/-- A colored original parabolic centralizes its specified central generator. -/
theorem colorFamily_le_centralizer {v:G} {E:Subgroup G}
    (hE:E∈colorFamily p B5 c.z (sourceU e) v) : E≤centralizer ({v}:Set G) := by
  have hh:=(colorFamily_center p B5 c e hz hE).1
  have hv:v∈(center E).map E.subtype := hh.symm ▸ mem_zpowers v
  obtain ⟨w,hw,hwv⟩:=hv
  intro x hx
  apply mem_centralizer_singleton_iff.mpr
  rw [←hwv]
  exact congrArg Subtype.val (mem_center_iff.mp hw (⟨x,hx⟩:E))

include hz in
/-- Every original adjacency can be aligned with B5 by an actor in the
literal first endpoint centralizing the original four-group. -/
theorem adjacent_base_reduction
    (hfive:(zpowers modelRotation).map ((p.F₁ B5).subtype.comp e.toMonoidHom)=B5Image B5)
    {v:G} (hv:v∈colors c.z (sourceU e)) {E:Subgroup G}
    (hE:E∈colorFamily p B5 c.z (sourceU e) v)
    (hadj:(Subgroup.PrimeIncidence.graph 5 (pairSpan c.z (sourceU e))).Adj (p.F₁ B5) E) :
    ∃n:G,n∈p.F₁ B5 ∧ n∈centralizer (pairSpan c.z (sourceU e):Set G) ∧
      n∈normalizer (pairSpan c.z (sourceU e):Set G) ∧
      E.conjBy n∈colorFamily p B5 c.z (sourceU e) v ∧
      ∃B:Subgroup G,B≤E.conjBy n ∧ Nat.card B=5 ∧
        pairSpan c.z (sourceU e)≤normalizer (B:Set G) ∧
        B≤centralizer (B5Image B5:Set G) ∧ B≤centralizer ({v}:Set G) := by
  obtain ⟨_,A,B,hAF,hBE,hA,hB,hVA,hVB,hc⟩:=
    (Subgroup.PrimeIncidence.adj_iff 5 _ _ _).mp hadj
  obtain ⟨m,hm,hmA⟩:=source_invariant_five_conjugator c B5 e hz hfive A hAF hA hVA
  have hmC:m∈centralizer (pairSpan c.z (sourceU e):Set G) :=
    source_plane_normalizer_centralizes c e hz hm
  have hnC:m⁻¹∈centralizer (pairSpan c.z (sourceU e):Set G) := inv_mem hmC
  have hnN:m⁻¹∈normalizer (pairSpan c.z (sourceU e):Set G) := inv_mem hm.2
  have hnv:m⁻¹*v*(m⁻¹)⁻¹=v := by
    apply mul_inv_eq_iff_eq_mul.mpr
    exact (hnC v ((colors_iff p B5 c e hz v).mp hv).1).symm
  have hE':E.conjBy m⁻¹∈colorFamily p B5 c.z (sourceU e) v := by
    have hh:=color_conjugate_mem p B5 c.z (sourceU e) m⁻¹ hnN hE
    rwa [hnv] at hh
  have ha:A.conjBy m⁻¹=B5Image B5 := by rw [←hmA,conjBy_inv]
  refine ⟨m⁻¹,(p.F₁ B5).inv_mem hm.1,hnC,hnN,hE',B.conjBy m⁻¹,
    map_mono hBE,(card_map_of_injective (MulAut.conj m⁻¹).injective).trans hB,?_,?_,?_⟩
  · have hh := (map_mono (f:=(MulAut.conj m⁻¹).toMonoidHom) hVB).trans
      (B.le_normalizer_map (MulAut.conj m⁻¹).toMonoidHom)
    have hfix:(pairSpan c.z (sourceU e)).map (MulAut.conj m⁻¹).toMonoidHom=
        pairSpan c.z (sourceU e) := mem_normalizer_iff_map_conj_eq.mp hnN
    rwa [hfix] at hh
  · rw [←ha]
    rintro b ⟨b,hb,rfl⟩ a ⟨a,ha,rfl⟩
    simpa only [map_mul,MulEquiv.coe_toMonoidHom] using
      congrArg (MulAut.conj m⁻¹) (hc ha b hb).symm
  · exact (map_mono hBE).trans (colorFamily_le_centralizer p B5 c e hz hE')

open CFSG.Quasithin.ChapterF.SourceCompletion.BinaryRee
include hz in
/-- In the original completion, adjacency is aligned with the fixed-five
label of the same original involution color. -/
theorem source_adjacent_fixed_reduction {D:Type*} [Group D] (q:Completion D) (f:D→*G)
    (hleft:∀a:first,f (q.left a)=(e a:G))
    (hfive:(zpowers modelRotation).map ((p.F₁ B5).subtype.comp e.toMonoidHom)=B5Image B5)
    {v:G} (hv:v∈colors c.z (sourceU e)) {E:Subgroup G}
    (hE:E∈colorFamily p B5 c.z (sourceU e) v)
    (hadj:(Subgroup.PrimeIncidence.graph 5 (pairSpan c.z (sourceU e))).Adj (p.F₁ B5) E) :
    ∃n:G,n∈p.F₁ B5 ∧ n∈centralizer (pairSpan c.z (sourceU e):Set G) ∧
      n∈normalizer (pairSpan c.z (sourceU e):Set G) ∧
      E.conjBy n∈colorFamily p B5 c.z (sourceU e) v ∧ fixedFive B5 v≤E.conjBy n := by
  obtain ⟨n,hn,hc,hnN,hEn,B,hBE,hB,hVB,hBB,hBv⟩:=
    adjacent_base_reduction p B5 c e hz hfive hv hE hadj
  have hfixed:Nat.card (fixedFive B5 v)=5 := by
    obtain ⟨hu,hi⟩:=source_inverter c B5 e hz hfive
    have hs:=source_three_fives c B5 (sourceU e) hu
      (PathTransport.source_fusion q c e f hleft hz) hi
    simp only [colors,Set.mem_insert_iff,Set.mem_singleton_iff] at hv
    rcases hv with rfl|rfl|rfl
    · obtain ⟨q₅⟩:=c.fiveQuaternionData_source B5
      change Nat.card (fiveOddPart B5⊓centralizer ({c.z}:Set G):Subgroup G)=5
      rw [c.fiveOddPart_inf_centralizer_z d.card_Z B5 q₅]
      exact B5Image_card d.card_Z B5
    · exact hs.1
    · exact hs.2.1
  have hBfix:=commuting_five_eq_fixed c B5 v hfixed B hB hBB hBv
  exact ⟨n,hn,hc,hnN,hEn,hBfix ▸ hBE⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily

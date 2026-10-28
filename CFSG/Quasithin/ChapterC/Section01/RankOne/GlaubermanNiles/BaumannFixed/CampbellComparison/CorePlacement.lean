module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.OmegaStructure.ThompsonCenter
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellComparison
public import Stellmacher.ElementaryAbelianMaxFamilyMap

/-!
# The first paired-overgroup placement in Campbell's comparison

Two original local groups are marked on the same abstract Thompson group.
Maximum elementary families transport through these exact markings. Thus
F from the first group lies in a maximum elementary subgroup in the second,
and the second replacement identity gives F'=V' C_F'(F). The centralizer
term, transported back to the first Sylow subgroup, lies in its two-core.
Consequently transferred V'≤O₂(H) implies transferred F'≤O₂(H).

This proves the opening reduction of Campbell II.5, printed p.27. It does
not assert the subsequent comparison centrality or uniform pair selection.
Source: Campbell, *Pushing up in Finite Groups* (1979), II.4.5 and II.5.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {B H J : Type*} [Group B] [Finite B] [Group H] [Finite H] [Group J]
  {e : B →* H} {k : Type} [Field k] [Finite k] [CharP k 2]

private theorem test_maxJ_family (S : Subgroup H) (A : Subgroup H) :
    A ∈ elementaryAbelianMaxSubgroups (Campbell.J S) ↔ A ∈ elementaryAbelianMaxSubgroups S := by
  have hJS : Campbell.J S ≤ S := sSup_le fun _ hA => hA.1
  constructor
  · intro hA
    obtain ⟨D,hD⟩ := elementaryAbelianMaxSubgroups_nonempty S
    exact ⟨hA.1.trans hJS,hA.2.1,fun C hC he =>
      (hD.2.2 C hC he).trans (hA.2.2 D (le_sSup hD) hD.2.1)⟩
  · intro hA
    exact ⟨le_sSup hA,hA.2.1,fun C hC he => hA.2.2 C (hC.trans hJS) he⟩

variable {H' : Type*} [Group H'] [Finite H']

theorem Campbell.Embedding.transfer_maxElementary (d : Campbell.Embedding J H) (d' : Campbell.Embedding J H')
    (A : Subgroup H') (hA : A ∈ elementaryAbelianMaxSubgroups (d'.sylow : Subgroup H')) :
    d.transfer d' A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H) := by
  have hAJ := (test_maxJ_family _ _).mpr hA
  have hAr : A ≤ d'.marking.range := by rw [d'.range_eq]; exact hAJ.1
  have hpre : d'.pull A ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup J) := by
    apply (maxFamily_map_injective_iff d'.marking d'.injective ⊤ _).mp
    rw [d'.map_pull A hAr,← MonoidHom.range_eq_map,d'.range_eq]
    exact hAJ
  apply (test_maxJ_family _ _).mp
  have hm := (maxFamily_map_injective_iff d.marking d.injective ⊤ (d'.pull A)).mpr hpre
  simpa only [Campbell.Embedding.transfer,← MonoidHom.range_eq_map,d.range_eq] using hm

omit [Finite H] [Finite H'] in
theorem Campbell.Embedding.transfer_le_centralizer (d : Campbell.Embedding J H) (d' : Campbell.Embedding J H')
    (X : Subgroup H') (Y : Subgroup H) (hY : Y ≤ d.marking.range)
    (hX : X ≤ centralizer (d'.transfer d Y : Set H')) :
    d.transfer d' X ≤ centralizer (Y : Set H) := by
  rintro x ⟨a,ha,rfl⟩ y hy
  obtain ⟨b,hb⟩ := hY hy
  have hh : d'.marking b ∈ d'.transfer d Y := ⟨b,by change d.marking b ∈ Y; rwa [hb],rfl⟩
  have hc := hX ha _ hh
  have hab : b*a=a*b := d'.injective (by simpa only [map_mul] using hc)
  rw [← hb,← map_mul,hab,map_mul]

variable {B' : Type*} [Group B'] [Finite B'] {e' : B' →* H'}
  {k' : Type} [Field k'] [Finite k'] [CharP k' 2]

theorem InLocalClass.transferred_campbellF_le_core (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e k) (h' : InLocalClass e') (hB' : IsBaumannFixed B')
    (m' : NaturalModel e' k') (d : Campbell.Embedding J H) (d' : Campbell.Embedding J H')
    (hV : d.transfer d' (Campbell.V H') ≤ pCore 2 H) :
    d.transfer d' (Campbell.F H') ≤ pCore 2 H := by
  obtain ⟨A,hA,hFA⟩ := InLocalClass.campbellF_le_some_maxElementary h hB d
  let Y := d'.transfer d (Campbell.F H)
  have hYA : Y ≤ d'.transfer d A := map_mono (comap_mono hFA)
  have hdec := (InLocalClass.campbellF_submaximal_control h' hB' m' d' Y _ (Campbell.Embedding.transfer_maxElementary d' d A hA) hYA).2
  have hFr : Campbell.F H ≤ d.marking.range := (h.campbell_marked_containments hB d).1
  have hF'r : Campbell.F H' ≤ d'.marking.range := (h'.campbell_marked_containments hB' d').1
  have hCr : Campbell.F H' ⊓ centralizer (Y : Set H') ≤ d'.marking.range := inf_le_left.trans hF'r
  have hC : d.transfer d' (Campbell.F H' ⊓ centralizer (Y : Set H')) ≤ pCore 2 H := by
    apply (InLocalClass.sylow_centralizer_campbellF_le_core h hB m d).trans'
    apply le_inf
    · exact (Campbell.transfer_le_marking_range d d' _ hCr).trans
        (d.range_eq ▸ (sSup_le fun _ hA => hA.1))
    · exact Campbell.Embedding.transfer_le_centralizer d d' _ _ hFr inf_le_right
  let : (Campbell.V H').Normal := by rw [h'.campbellV_eq_moved hB' m']; infer_instance
  rintro x ⟨a,ha,rfl⟩
  obtain ⟨v,hv,c,hc,he⟩ := mem_sup_of_normal_left.mp (hdec ▸ ha)
  obtain ⟨b,hb⟩ := hF'r (Campbell.V_le_F hv)
  obtain ⟨z,hz⟩ := hCr hc
  have hprod : b*z=a := d'.injective (by rw [map_mul,hb,hz]; exact he)
  rw [← hprod,map_mul]
  exact (pCore 2 H).mul_mem
    (hV ⟨b,by change d'.marking b ∈ Campbell.V H'; rwa [hb],rfl⟩)
    (hC ⟨z,by change d'.marking z ∈ Campbell.F H' ⊓ centralizer (Y : Set H'); rwa [hz],rfl⟩)
end CFSG.Quasithin.ChapterC.GlaubermanNiles

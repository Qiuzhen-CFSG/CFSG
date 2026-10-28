module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonEnlargement.Exceptional
public import Theory.Mathieu.M11.Properties.SylowOvergroups
/-!
# Full original source persistence, including the A₆–M₁₁ exception

The previously proved alternative supplies an ordinary containing M₁₁.
Project N(E) to it using its inner automorphisms. The original full Sylow
retains its image under the projection; the A₆ branch therefore has M₁₀
image. The kernel is exactly O₂(H), so this identifies the original
quotient and completes every alternative and local assertion of 2.5.6.
The M₁₀ model is the canonical proved semidihedral extension in Aut(A₆).
Source: Aschbacher–Smith 2.5.6, printed p.554.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement
variable {G:Type*} [Group G] [Finite G]
theorem MathieuSourceSetup.exceptional_quotient_m10
    {H K M E:Subgroup G} {S:Sylow 2 H} {z:G}
    (c:MathieuSourceSetup H K M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=K⊔(S:Subgroup H).map H.subtype)
    (hb:¬ClassificationModels.IsBenderModel K)
    (hE:E≠⊥) (hEC:E≤((S:Subgroup H).map H.subtype)⊓centralizer (K:Set G))
    (hSE:(S:Subgroup H).map H.subtype≤normalizer (E:Set G))
    (hne:¬IsComponentIn K (normalizer (E:Set G))) :
    Nonempty ((H⧸pCore 2 H)≃*AlternatingSix.M10.extension) := by
  obtain ⟨⟨eK⟩,hnK,_,hC,⟨eC⟩⟩ := MathieuSourceSetup.exceptional_alternating_six_orbit
    c hG hempty hgen hb hE hEC hSE hne
  let J := normalizer (E:Set G)
  let C := componentOrbit K J
  have hKC : K≤C := le_componentOrbit K J
  have hHJ : H≤J := normalizes_centralizer_subgroup hgen hEC hSE
  obtain ⟨hJ,⟨P,hP⟩,_⟩ := centralizer_subgroup_normalizer (MathieuSourceSetup.sourceTuple c)
    hgen hE hEC hSE
  let eCJ : C.subgroupOf J≃*Sporadic.Mathieu.M11 := (subgroupOfEquivOfLe hC.1).trans eC
  let : (C.subgroupOf J).Normal := small_component_normal hG.quasithin hJ (C.subgroupOf J)
    hC.2 (Or.inr ⟨eCJ⟩)
  obtain ⟨q,hq,hqC⟩ := Sporadic.Mathieu.exists_normal_m11_projection (C.subgroupOf J) eCJ
  let f : H→*Sporadic.Mathieu.M11 := q.comp (inclusion hHJ)
  let A := K.subgroupOf H
  let : A.Normal := hnK
  let eA : A≃*alternatingGroup (Fin 6) := (subgroupOfEquivOfLe c.component_le).trans eK
  have hgenA : A⊔(S:Subgroup H)=⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le c.component_le,←hgen]
    rw [←MonoidHom.range_eq_map,range_subtype]
  have hfA : Function.Injective (f.comp A.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    let y : C.subgroupOf J := ⟨inclusion hHJ (x:H),hKC x.property⟩
    have he : eCJ y=1 := (hqC y).symm.trans hx
    have hy : y=1 := eCJ.injective (he.trans (map_one eCJ).symm)
    exact Subtype.ext (Subtype.ext (congrArg (fun y:C.subgroupOf J=>((y:J):G)) hy))
  let Q := P.mapSurjective (f:=q) hq
  have hS : (S:Subgroup H).map (inclusion hHJ)=(P:Subgroup J) := by
    apply map_injective J.subtype_injective
    rw [map_map]
    change (S:Subgroup H).map H.subtype=(P:Subgroup J).map J.subtype
    exact hP.symm
  have hQ : (Q:Subgroup Sporadic.Mathieu.M11)=(S:Subgroup H).map f := by
    change (P:Subgroup J).map q=(S:Subgroup H).map f
    rw [←hS,map_map]
  exact Sporadic.Mathieu.quotient_m10_of_full_sylow_image A eA S hgenA f hfA Q hQ
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory ComponentRefinement
variable {G:Type*} [Group G] [Finite G]
/-- All original assertions of 2.5.6 on the actual normal two-core subgroup E. -/
theorem MathieuSourceSetup.lemma_2_5_6
    {H K M E:Subgroup G} {S:Sylow 2 H} {z:G}
    (c:MathieuSourceSetup H K M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=K⊔(S:Subgroup H).map H.subtype)
    (hb:¬ClassificationModels.IsBenderModel K)
    (hE:E≠⊥) (hEC:E≤twoCore H)
    (hSE:(S:Subgroup H).map H.subtype≤normalizer (E:Set G)) :
    normalizer (E:Set G)∈gammaZero (Chapter1.He G) M ∧
    (∃P:Sylow 2 (normalizer (E:Set G)),
      (P:Subgroup (normalizer (E:Set G))).map (normalizer (E:Set G)).subtype=
        (S:Subgroup H).map H.subtype) ∧
    (H∈gammaStar (Chapter1.He G) M → normalizer (E:Set G)∈gammaStar (Chapter1.He G) M) ∧
    (IsComponentIn K (normalizer (E:Set G)) ∨
      (Nonempty (K≃*alternatingGroup (Fin 6)) ∧
       componentOrbit K ((S:Subgroup H).map H.subtype)=K ∧
       Nonempty ((H⧸pCore 2 H)≃*AlternatingSix.M10.extension) ∧
       IsComponentIn (componentOrbit K (normalizer (E:Set G))) (normalizer (E:Set G)) ∧
       Nonempty (componentOrbit K (normalizer (E:Set G))≃*Sporadic.Mathieu.M11))) := by
  have hc := generated_orbit_core ⟨c.component_le,c.component⟩ S hgen
  have hEC' : E≤((S:Subgroup H).map H.subtype)⊓centralizer (K:Set G) := by
    rw [←hc] at hEC
    exact hEC.trans (inf_le_inf_left _ (centralizer_le (le_componentOrbit _ _)))
  obtain ⟨hj,hp,hs,_⟩ := centralizer_subgroup_normalizer (MathieuSourceSetup.sourceTuple c)
    hgen hE hEC' hSE
  refine ⟨hj,hp,hs,?_⟩
  by_cases hn:IsComponentIn K (normalizer (E:Set G))
  · exact Or.inl hn
  · obtain ⟨ha,_,ho,hC,hm⟩ := MathieuSourceSetup.exceptional_alternating_six_orbit
      c hG hempty hgen hb hE hEC' hSE hn
    exact Or.inr ⟨ha,ho,MathieuSourceSetup.exceptional_quotient_m10
      c hG hempty hgen hb hE hEC' hSE hn,hC,hm⟩
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection

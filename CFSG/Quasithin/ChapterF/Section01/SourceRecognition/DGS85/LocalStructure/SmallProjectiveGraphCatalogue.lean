module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallProjectiveGraphApplication
public import Theory.GroupTheory.NormalSubgroupCoreQuotient

/-!
# The normal nine-group in the exceptional graph quotient

The starred PSU₃(2) quotient is normal in its enlargement. Its characteristic
three-core is elementary of order nine, so its image remains normal in the
whole enlarged quotient. Conjugation and the original inclusion transport
this subgroup to every graph vertex, in either endpoint orbit.

The resulting exhaustive alternative retains the order-144 quotient together
with its normal nine-group. This is the precise input to the distance-two
Frattini obstruction; it does not exclude the unrestricted enlargement.
Source: DGS, Groups and Graphs (1985), pp.104,118--119, and (10.7)--(10.9),
pp.158--163; Aschbacher--Smith F.1.1 and F.1.9.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85
variable {G : Type*} [Group G] {P B : Subgroup G}

/-- The characteristic three-core of the starred quotient survives as a normal
elementary nine-group in the actual enlargement quotient. -/
theorem localEnlargement_projective_normal_nine (d : LocalRankOneData P B)
    (hm : ClassicalGroup.IsPSU (d.Pstar ⧸ pCore 2 d.Pstar) 3 2) :
    ∃ N : Subgroup (localEnlargement d ⧸ pCore 2 (localEnlargement d)),
      N.Normal ∧ IsElementaryAbelian 3 N ∧ Nat.card N = 9 := by
  obtain ⟨K,hK,hfin,J,hc,hconj,⟨e⟩⟩ := hm
  let := hK
  let := hfin
  let := d.finite_P
  let M := localEnlargement d
  let C := d.Pstar.subgroupOf M
  let q := QuotientGroup.mk' (pCore 2 M)
  let I := C.map q
  let : Finite M := Finite.of_injective (inclusion (localEnlargement_le d))
    (inclusion_injective _)
  let : C.Normal := normal_subgroupOf_of_le_normalizer ((localEnlargement_le d).trans
    ((normal_subgroupOf_iff_le_normalizer d.Pstar_le).mp d.normal))
  let : I.Normal := (inferInstance : C.Normal).map q (QuotientGroup.mk'_surjective _)
  let f : C ≃* d.Pstar := subgroupOfEquivOfLe le_sup_left
  let g : I ≃* ProjectiveSpecialUnitaryMatrixGroup J := (coreQuotientEquivImage 2 C).symm.trans
    ((QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans e)
  let N := (pCore 3 I).map I.subtype
  let a : pCore 3 I ≃* pCore 3 (ProjectiveSpecialUnitaryMatrixGroup J) :=
    ((pCore 3 I).equivMapOfInjective g.toMonoidHom g.injective).trans
      (MulEquiv.subgroupCongr (pCore_map_iso 3 g))
  let c : N ≃* pCore 3 (ProjectiveSpecialUnitaryMatrixGroup J) :=
    ((pCore 3 I).equivMapOfInjective I.subtype I.subtype_injective).symm.trans a
  obtain ⟨h9,hE,_⟩ := HermitianForm.SmallThreeCore.projective_core_structure J hc hconj
  let := hE
  exact ⟨N,inferInstance,IsElementaryAbelian.of_injective c.toMonoidHom c.injective,
    (Nat.card_congr c.toEquiv).trans h9⟩

namespace Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S

/-- The exhaustive original enlargement split records the normal nine-group
in its sole remaining exceptional row. -/
theorem reduced_enlargement_rankOne_or_normal_nine (h : HypothesisF11 L S) (i : Fin 2) :
    IsRankOneModel (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)) ∨
      (Nat.card (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)) = 144 ∧
        ∃ N : Subgroup (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)),
          N.Normal ∧ IsElementaryAbelian 3 N ∧ Nat.card N = 9) := by
  rcases reduced_enlargement_rankOne_or_small_unitary h i with hm | hp | hs
  · exact Or.inl hm
  · rcases original_small_projective_enlarged_marking_or_card h i hp with hm | hc
    · exact Or.inl (.projective_unitary 1 (by decide) (by simpa using hm))
    · refine Or.inr ⟨hc,?_⟩
      obtain ⟨K,hK,hfin,J,hcard,hconj,⟨e⟩⟩ := hp
      have hm : ClassicalGroup.IsPSU
          ((h.starredLocalRankOneData i).Pstar ⧸ pCore 2 (h.starredLocalRankOneData i).Pstar) 3 2 :=
        ⟨K,hK,hfin,J,hcard,hconj,⟨(h.starredQuotientEquiv i).symm.trans e⟩⟩
      exact localEnlargement_projective_normal_nine (h.starredLocalRankOneData i) hm
  · exact Or.inl (.special_unitary 1 (by decide)
      (by simpa using original_small_special_enlarged_marking h i hs))

/-- At any vertex, including either endpoint orientation, the only missing
rank-one marking has order 144 and an actual normal elementary nine-group. -/
theorem reduced_graph_rankOne_or_normal_nine (h : HypothesisF11 L S) (v : Vertex F) :
    IsRankOneModel (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ∨
      (Nat.card (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) = 144 ∧
        ∃ N : Subgroup (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)),
          N.Normal ∧ IsElementaryAbelian 3 N ∧ Nat.card N = 9) := by
  have hb (j : Bool) :
      IsRankOneModel (family (enlargedEndpoint L S) j ⧸ pCore 2 (family (enlargedEndpoint L S) j)) ∨
        (Nat.card (family (enlargedEndpoint L S) j ⧸ pCore 2 (family (enlargedEndpoint L S) j)) = 144 ∧
          ∃ N : Subgroup (family (enlargedEndpoint L S) j ⧸ pCore 2 (family (enlargedEndpoint L S) j)),
            N.Normal ∧ IsElementaryAbelian 3 N ∧ Nat.card N = 9) := by
    cases j
    · exact reduced_enlargement_rankOne_or_normal_nine h 0
    · exact reduced_enlargement_rankOne_or_normal_nine h 1
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  let M := graphLocalGroup F (base F v.type)
  have heq : M.map (MulAut.conj g).toMonoidHom = graphLocalGroup F v :=
    (graphLocalGroup_conjugate (reduced_triple h) g (base F v.type)).symm.trans
      (congrArg (graphLocalGroup F) hg)
  let a : M ≃* graphLocalGroup F v :=
    (M.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr heq)
  let e := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm.trans
    (reduced_graphEnlargementQuotient h v.type)
  rcases hb v.type with hm | ⟨hc,N,hN,hE,h9⟩
  · exact Or.inl (hm.of_equiv e)
  · let := hN
    let := hE
    let N' := N.map e.symm.toMonoidHom
    let f : N ≃* N' := N.equivMapOfInjective e.symm.toMonoidHom e.symm.injective
    exact Or.inr ⟨(Nat.card_congr e.toEquiv).trans hc,N',
      hN.map e.symm.toMonoidHom e.symm.surjective,
      IsElementaryAbelian.of_injective f.symm.toMonoidHom f.symm.injective,
      (Nat.card_congr f.symm.toEquiv).trans h9⟩

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85

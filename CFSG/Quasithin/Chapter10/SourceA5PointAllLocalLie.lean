module
public import CFSG.Quasithin.Chapter10.SourceA5PointLocalLie
public import CFSG.Quasithin.Chapter10.SourceA5PointAllLocalData

/-!
# Lie-family point markings from the full Sylow stabilizer

The full point-centralizer Sylow need only normalize the original component L.
Restriction to I and transport through I/Z(I) then supply the local A₅ data
used by the rank-two Lie placement theorems. These force field order four and
retain the actual subgroup marking. This formulation also applies when the
point is fixed by the orbit of L, using the separately proved stabilizer
containment for every escaping point.

The final point-inspection assembly supplies that stabilizer containment.
The concrete carriers, central quotient and original L remain unchanged.
Source: Aschbacher–Smith A.3.12/A.3.14 and 10.2.9, pp.750–752.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterA.Section03
open Theory.SpecificGroups.SymplecticFour
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

private theorem local_model_transport {H K : Type*} [Group H] [Group K] [Finite H] [Finite K]
    (eH : H ≃* K) (S : Sylow 2 H) (B : Subgroup H)
    (hl : B ∈ localCComponents S) (hp : B ≠ ⊤)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    let A := B.map eH.toMonoidHom
    A ∈ localCComponents (S.mapSurjective (f := eH.toMonoidHom) eH.surjective) ∧ A ≠ ⊤ ∧
      Nonempty ((A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 5)) := by
  let : Group.IsSolvable eH.toMonoidHom.ker := by
    rw [eH.toMonoidHom.ker_eq_bot eH.injective]
    infer_instance
  let a := eH.subgroupMap B
  refine ⟨Chapter1.Section02.localCComponents_map_of_solvable_ker hl eH.toMonoidHom, ?_,
    ⟨(QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm.trans eB⟩⟩
  intro ht
  apply hp
  apply map_injective (f := eH.toMonoidHom) eH.injective
  rw [map_top_of_surjective _ eH.surjective]
  exact ht


include D in
/-- The linear-three catalogue row has field four and the original marking
whenever the full point-centralizer Sylow stabilizes L. -/
theorem source_a5_point_linear_three_model_marking_of_normalizes
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {v : G} (hstab : (T : Subgroup G) ⊓ centralizer ({v} : Set G) ≤
      normalizer (L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    {I : Subgroup G} [Group.IsPerfect I] (hLI : L < I)
    (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    {n : ℕ} (hnF : 1 ≤ n) (hmodel : ClassicalGroup.IsPSL (I ⧸ center I) 3 (2 ^ n)) :
    n = 2 ∧ SourceA5PointQuasisimpleMarking.{u,0} L I := by
  obtain ⟨F,_,_,hF,⟨eI⟩⟩ := hmodel
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  have hn2 : 1 < n := by
    by_contra! h
    have he : n = 1 := by omega
    have hc := source_a5_containing_center_quotient_card_ge D e hLI.le
    rw [Nat.card_congr eI.toEquiv,Matrix.PSL3.LinearThree.card_projective F,hF,he] at hc
    norm_num at hc
  obtain ⟨S,_,_,hl,_,hp,⟨eB⟩,_⟩ :=
    source_a5_point_center_quotient_local_embedding_of_normalizes D e hstab hs hLI hIX hI
  let q := QuotientGroup.mk' (center I)
  let B := (L.subgroupOf I).map q
  let A := B.map eI.toMonoidHom
  let R := S.mapSurjective (QuotientGroup.mk'_surjective (center I))
  obtain ⟨hlA,hpA,⟨eA⟩⟩ := local_model_transport eI R B hl hp eB
  obtain ⟨h4,_⟩ := SourceEmbeddings.FiveLocalFF.linear_three_five_section_placement hF hn2
    (R.mapSurjective (f := eI.toMonoidHom) eI.surjective) A hlA hpA eA
  let := Fintype.ofFinite F
  let := Fintype.ofFinite Matrix.PSL3Four.F
  let a : F ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,h4,Matrix.PSL3Four.card_F])
  refine ⟨Nat.pow_right_injective (by decide : 2 ≤ 2) ?_,
    .linear (eI.trans (Atlas.fieldEquivPSL 3 a))⟩
  simpa only [← hF] using h4

include D in
/-- The G₂ catalogue row supplies field four and the literal subgroup marking
from the full point-centralizer Sylow stabilizer. -/
theorem source_a5_point_g2_model_marking_of_normalizes
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {v : G} (hstab : (T : Subgroup G) ⊓ centralizer ({v} : Set G) ≤
      normalizer (L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    {I : Subgroup G} [Group.IsPerfect I] (hLI : L < I)
    (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    {n : ℕ} (hnF : 2 ≤ n) (hmodel : ClassificationModels.IsG2At (I ⧸ center I) (2 ^ n)) :
    n = 2 ∧ SourceA5PointQuasisimpleMarking.{u,0} L I := by
  obtain ⟨F,_,_,hF,⟨eI⟩⟩ := hmodel
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact (by decide : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) (by omega)
  obtain ⟨S,_,_,hl,_,hp,⟨eB⟩,_⟩ :=
    source_a5_point_center_quotient_local_embedding_of_normalizes D e hstab hs hLI hIX hI
  let q := QuotientGroup.mk' (center I)
  let B := (L.subgroupOf I).map q
  let A := B.map eI.toMonoidHom
  let R := S.mapSurjective (QuotientGroup.mk'_surjective (center I))
  obtain ⟨hlA,hpA,⟨eA⟩⟩ := local_model_transport eI R B hl hp eB
  obtain ⟨h4,g,hg⟩ := SourceEmbeddings.FiveLocalFF.G2.five_section_placement hq
    (R.mapSurjective (f := eI.toMonoidHom) eI.surjective) A hlA hpA eA
  refine ⟨Nat.pow_right_injective (by decide : 2 ≤ 2) ?_,
    .g2 h4 (eI.trans (MulAut.conj g)) ?_⟩
  · simpa only [← hF] using h4
  · have he : (eI.trans (MulAut.conj g)).toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp eI.toMonoidHom := by ext; rfl
    simpa only [A,B,q,map_map, he, MonoidHom.comp_assoc] using hg

include D in
/-- The projective symplectic row supplies field four and the original marking
from the full point-centralizer Sylow stabilizer. -/
theorem source_a5_point_symplectic_model_marking_of_normalizes
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {v : G} (hstab : (T : Subgroup G) ⊓ centralizer ({v} : Set G) ≤
      normalizer (L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    {I : Subgroup G} [Group.IsPerfect I] (hLI : L < I)
    (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    {n : ℕ} (hnF : 2 ≤ n) (hmodel : ClassicalGroup.IsPSp (I ⧸ center I) 2 (2 ^ n)) :
    n = 2 ∧ SourceA5PointQuasisimpleMarking.{u,0} L I := by
  obtain ⟨F,_,_,hF,⟨eP⟩⟩ := hmodel
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  let eI := eP.trans (EvenProjective.equiv (F := F)).symm
  obtain ⟨S,_,_,hl,_,hp,⟨eB⟩,_⟩ :=
    source_a5_point_center_quotient_local_embedding_of_normalizes D e hstab hs hLI hIX hI
  let q := QuotientGroup.mk' (center I)
  let B := (L.subgroupOf I).map q
  let A := B.map eI.toMonoidHom
  let R := S.mapSurjective (QuotientGroup.mk'_surjective (center I))
  obtain ⟨hlA,hpA,⟨eA⟩⟩ := local_model_transport eI R B hl hp eB
  obtain ⟨h4,g,hg⟩ := SourceEmbeddings.FiveLocalFF.symplectic_five_section_placement
    hF (by omega : 1 < n) (R.mapSurjective (f := eI.toMonoidHom) eI.surjective) A hlA hpA eA
  refine ⟨Nat.pow_right_injective (by decide : 2 ≤ 2) ?_,
    .symplectic h4 (eI.trans (MulAut.conj g)) ?_⟩
  · simpa only [← hF] using h4
  · have he : (eI.trans (MulAut.conj g)).toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp eI.toMonoidHom := by ext; rfl
    simpa only [A,B,q,map_map, he, MonoidHom.comp_assoc] using hg

end CFSG.Quasithin.Chapter10

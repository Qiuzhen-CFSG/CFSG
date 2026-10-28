module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.ThreePathSylow
public import Theory.SpecificGroups.SU3.BinarySylowOrder
public import Theory.SpecificGroups.SU3.SylowOmega

/-!
# The unitary centralizer image along the original three-path

For a three-path shorter than the source parameter s, the interior-core
intersection has full Sylow image in the terminal local quotient. The
literal incoming-core product is the earlier (12.1)(c) premise. In the
unitary alternative the Sylow has order at least q³. Restricting an
index-at-most-q centralizer to that intersection and using the relative-index
tower gives index at most q in that same quotient Sylow and image order
at least q². The quotient is the actual
local group modulo its two-core, with its canonical projection.

UnitarySelectionRoot applies this to the involution constructed in (12.5),
constructs the three-path, and supplies the original quotient markings and
full edge product. This is the centralizer-index step preceding the source's
transitivity assertion; it does not itself assert that transitivity.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.5), printed p.182, using (12.4)(b) and (3.4)(c).
-/

public noncomputable section
open Subgroup SimpleGraph BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem unitary_sylow_cube_le {A : Type*} [Group A] [Finite A]
    {n : ℕ} (hn : 0 < n)
    (hu : ClassicalGroup.IsPSU A 3 (2^n) ∨ IsSU A 3 (2^n))
    (T : Sylow 2 A) : (2^n)^3 ≤ Nat.card T := by
  rcases hu with hu | hu
  · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
    let R := T.mapSurjective (f := e.toMonoidHom) e.surjective
    have he : Nat.card T = Nat.card R := Nat.card_congr
      ((T : Subgroup A).equivMapOfInjective e.toMonoidHom e.injective).toEquiv
    rw [he]
    exact HermitianForm.BinarySylowOrder.cube_le_sylow_card J (by omega) hK hconj R
  · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
    let R := T.mapSurjective (f := e.toMonoidHom) e.surjective
    have he : Nat.card T = Nat.card R := Nat.card_congr
      ((T : Subgroup A).equivMapOfInjective e.toMonoidHom e.injective).toEquiv
    rw [he,Nat.card_congr (HermitianForm.SylowOmega.specialSylowEquivProjective J R).toEquiv]
    exact HermitianForm.BinarySylowOrder.cube_le_sylow_card J (by omega) hK hconj _

/-- The actual interior-core intersection fills the quotient Sylow, and
the centralizer image has index at most q in that Sylow and order at least q². -/
theorem unitary_three_path_centralizer_image
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    (models : ∀ v, IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (hs : 3 < sourceS (P := P))
    {a : Vertex (family P)} (p : BasedWalk (graph (family P)) 3 a)
    (hp : p.Nonbacktracking)
    (hprod : Q (family P) p.2.1.val ⊔ Q (family P) p.endpoint =
      (stabilizer (family P) p.endpoint ⊓ stabilizer (family P) p.2.1.val).pCoreIn 2)
    {n : ℕ} (hn : 0 < n)
    (hu : ClassicalGroup.IsPSU (d.localGroup p.endpoint ⧸ pCore 2 (d.localGroup p.endpoint)) 3 (2^n) ∨
      IsSU (d.localGroup p.endpoint ⧸ pCore 2 (d.localGroup p.endpoint)) 3 (2^n))
    (t : G) (hi : (centralizer ({t} : Set G)).relIndex (Q (family P) p.1.val) ≤ 2^n) :
    let F := family P
    let A := d.localGroup p.endpoint
    let I := Q F p.1.val ⊓ Q F p.2.1.val
    let C := I ⊓ centralizer ({t} : Set G)
    let f := QuotientGroup.mk' (pCore 2 A)
    (∃ T : Sylow 2 (A ⧸ pCore 2 A), (I.subgroupOf A).map f = T ∧
      ((C.subgroupOf A).map f).relIndex (T : Subgroup (A ⧸ pCore 2 A)) ≤ 2^n) ∧
      (2^n)^2 ≤ (Q F p.endpoint).relIndex C ∧
      (2^n)^2 ≤ Nat.card ((C.subgroupOf A).map f) := by
  let F := family P
  let A := d.localGroup p.endpoint
  let I := Q F p.1.val ⊓ Q F p.2.1.val
  let C := I ⊓ centralizer ({t} : Set G)
  let f := QuotientGroup.mk' (pCore 2 A)
  let : ∀ i, Finite (F i) := finite_endpoints h
  let : Finite A := Finite.of_injective (inclusion (d.local_le p.endpoint)) (inclusion_injective _)
  let : Finite (Q F p.1.val) := Finite.of_injective
    (inclusion (Q_le_stabilizer F p.1.val)) (inclusion_injective _)
  let : Finite I := Finite.of_injective (inclusion (show I ≤ Q F p.1.val from inf_le_left)) (inclusion_injective _)
  have hedge : (graph F).Adj p.endpoint p.2.1.val := p.adj_penultimate_endpoint.symm
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow h hB d hedge
  have hgen : I ⊔ Q F p.endpoint = (R : Subgroup A).map A.subtype :=
    (three_path_core_supplement h hB hS d models hs p hp).trans (hprod.trans hR.symm)
  have hIA : I ≤ A := (le_sup_left.trans hgen.le).trans (map_subtype_le _)
  have hQA : Q F p.endpoint ≤ A := (le_sup_right.trans hgen.le).trans (map_subtype_le _)
  have hk : f.ker = (Q F p.endpoint).subgroupOf A := by
    rw [QuotientGroup.ker_mk',←localGroup_core_eq F d p.endpoint]
    exact (comap_map_eq_self_of_injective A.subtype_injective _).symm
  have hsR : I.subgroupOf A ⊔ (Q F p.endpoint).subgroupOf A = (R : Subgroup A) := by
    apply map_injective A.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hIA,map_subgroupOf_eq_of_le hQA]
    exact hgen
  let T := R.mapSurjective (f := f) (QuotientGroup.mk'_surjective _)
  have hIT : (I.subgroupOf A).map f = (T : Subgroup (A ⧸ pCore 2 A)) := by
    change _ = (R : Subgroup A).map f
    rw [←hsR,Subgroup.map_sup,←hk,Subgroup.map_ker_self,sup_bot_eq]
  have hlo : (2^n)^3 ≤ (Q F p.endpoint).relIndex I := by
    rw [←relIndex_subgroupOf hIA,←hk,relIndex_ker,hIT]
    exact unitary_sylow_cube_le hn hu T
  have hi' : (centralizer ({t} : Set G)).relIndex I ≤ 2^n :=
    (relIndex_le_of_le_right inf_le_left index_ne_zero_of_finite).trans hi
  have hindex : ((C.subgroupOf A).map f).relIndex (T : Subgroup (A ⧸ pCore 2 A)) ≤ 2^n := by
    rw [←hIT,←relIndex_comap,Subgroup.comap_map_eq]
    calc
      (C.subgroupOf A ⊔ f.ker).relIndex (I.subgroupOf A) ≤
          (C.subgroupOf A).relIndex (I.subgroupOf A) :=
        relIndex_le_of_le_left le_sup_left index_ne_zero_of_finite
      _ = C.relIndex I := relIndex_subgroupOf hIA
      _ = (centralizer ({t} : Set G)).relIndex I := inf_relIndex_left _ _
      _ ≤ 2^n := hi'
  have hmul : (2^n)^3 ≤ (Q F p.endpoint).relIndex C * 2^n := by
    calc
      (2^n)^3 ≤ (Q F p.endpoint).relIndex I := hlo
      _ ≤ (Q F p.endpoint ⊓ centralizer ({t} : Set G)).relIndex I :=
        relIndex_le_of_le_left inf_le_left index_ne_zero_of_finite
      _ = (Q F p.endpoint).relIndex C * (centralizer ({t} : Set G)).relIndex I := by
        rw [←relIndex_inf_mul_relIndex,inf_comm (centralizer ({t} : Set G)) I]
      _ ≤ (Q F p.endpoint).relIndex C * 2^n := Nat.mul_le_mul_left _ hi'
  have hlower : (2^n)^2 ≤ (Q F p.endpoint).relIndex C := by
    apply Nat.le_of_mul_le_mul_right (c := 2^n)
    · simpa only [pow_succ] using hmul
    · exact pow_pos (by decide) _
  refine ⟨⟨T,hIT,hindex⟩,hlower,?_⟩
  rwa [←relIndex_ker,hk,relIndex_subgroupOf (show C ≤ A from inf_le_left.trans hIA)]

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile

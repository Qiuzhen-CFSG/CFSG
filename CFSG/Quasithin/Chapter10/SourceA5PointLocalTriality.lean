module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Triality
public import CFSG.Quasithin.Chapter10.SourceA5PointLocalEmbedding
public import CFSG.Quasithin.Chapter10.SourceA5PointQuasisimpleDispatch

/-!
# Producing the triality marking from the original point data

The original point Sylow restricts to the same containing component I and
passes through its literal central quotient. The original moved module gives
a two-core center of order at least sixteen, so this local image has nontrivial
two-core. The native triality placement constructs an actual conjugation to
the central local factor and forces the parameter q = 4.

Composing that conjugation with the given central-quotient equivalence supplies
the exact marking consumed by the existing point-centralizer theorem. Thus a
triality carrier identification alone, together with the original source point
hypotheses, gives the original component alternative; no local marking or
core-shape callback remains.

Source: Aschbacher–Smith A.3.12(2), F.1.12(I)(4), and 10.2.9, printed
pp.47–48, 263–264, and 750–751.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Triality.Standard Triality.Standard.Parabolics
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

/-- The actual full-Sylow local image in a triality central quotient acquires
its central-parabolic marking, with field order four. -/
theorem source_a5_triality_local_image_marking
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {I : Subgroup G} (hLI : L ≤ I) (S : Sylow 2 I)
    (hlocal : L.subgroupOf I ∈ ChapterA.Section03.localCComponents S)
    (n : ℕ) (hn : 0 < n) (eI : (I ⧸ center I) ≃* BinaryCarrier n hn) :
    2 ^ n = 4 ∧ ∃ f : (I ⧸ center I) ≃* BinaryCarrier n hn,
      (L.subgroupOf I).map (f.toMonoidHom.comp (QuotientGroup.mk' (center I))) =
        localFactor (binaryParameters n hn) .central := by
  let q := QuotientGroup.mk' (center I)
  let A := (L.subgroupOf I).map q
  let B := A.map eI.toMonoidHom
  let f := eI.toMonoidHom.comp q
  have hf : Function.Surjective f := eI.surjective.comp (QuotientGroup.mk'_surjective _)
  let : Group.IsSolvable f.ker := by
    have hk : f.ker = center I := by
      ext x
      change eI (q x) = 1 ↔ x ∈ center I
      rw [←eI.map_one,eI.injective.eq_iff]
      exact QuotientGroup.eq_one_iff x
    rw [hk]
    exact Group.isSolvable_of_comm fun x y => mul_comm x y
  let S' := S.mapSurjective hf
  have hb : B ∈ ChapterA.Section03.localCComponents S' := by
    have h := Chapter1.Section02.localCComponents_map_of_solvable_ker hlocal f
    simpa only [B,A,map_map,S',Sylow.coe_mapSurjective,f] using h
  let c : A ≃* B := A.equivMapOfInjective eI.toMonoidHom eI.injective
  let eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).symm.trans
      (source_a5_containing_center_image_quotient e hLI)
  have hlow := source_a5_marked_core_center_card D e hLI c
  have hcore : pCore 2 B ≠ ⊥ := by
    intro hz
    have hc := Nat.card_le_card_of_injective (center (pCore 2 B)).subtype
      (center (pCore 2 B)).subtype_injective
    have hcard : Nat.card (pCore 2 B) = 1 := by rw [hz,card_bot]
    omega
  obtain ⟨hq,g,hg⟩ := ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Triality.five_section_placement
    n hn S' B hb hcore eB
  refine ⟨hq,eI.trans (MulAut.conj g),?_⟩
  have he : (eI.trans (MulAut.conj g)).toMonoidHom.comp q =
      (MulAut.conj g).toMonoidHom.comp (eI.toMonoidHom.comp q) := by
    ext x
    rfl
  rw [he]
  simpa only [B,A,map_map] using hg

/-- Original point-local geometry supplies every marking premise of the triality row. -/
theorem source_a5_point_triality_quasisimple_marking
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {v : G} (hvL : v ∈ centralizer (L : Set G))
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    {I : Subgroup G} (hLI : L ≤ I) (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    (n : ℕ) (hnpos : 0 < n) (eI : I ⧸ center I ≃* BinaryCarrier n hnpos) :
    SourceA5PointQuasisimpleMarking.{u,0} L I := by
  obtain ⟨S,_,_,hlocal⟩ := source_point_containing_component_local_sylow D hn hvL hv0 hs hLI hIX hI
  obtain ⟨hq,f,hf⟩ := source_a5_triality_local_image_marking D e hLI S hlocal n hnpos eI
  exact .triality n hnpos hq f (Or.inr hf)

/-- The unmarked triality carrier row gives the original point alternative. -/
theorem source_a5_point_triality_local_alternative
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (t : G) {v : G}
    (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    {I : Subgroup G} [Group.IsPerfect I] (hLI : L ≤ I)
    (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    (hNI : centralizer ({v} : Set G) ≤ normalizer (I : Set G))
    (n : ℕ) (hnpos : 0 < n) (eI : I ⧸ center I ≃* BinaryCarrier n hnpos) :
    SourceA5PointComponentAlternative D e t I :=
  source_a5_point_alternative_of_quasisimple_marking D e t I hLI hv hNI hcross
    (source_a5_point_triality_quasisimple_marking D e hn (hcross hv) hv0 hs hLI hIX hI n hnpos eI)

end CFSG.Quasithin.Chapter10

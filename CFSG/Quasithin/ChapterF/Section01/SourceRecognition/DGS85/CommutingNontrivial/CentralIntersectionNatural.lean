module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.CentralIntersectionEstimate

/-!
# Natural starting coordinates in the small-terminal branch of DGS 8.6

Conjugation carries the complete natural marking from a moving neighbor to
the original starting vertex. The central neighboring orbit kills the central
section kernel, so these are coordinates on the whole starting center. The
resulting SL₂ isomorphism uses the original local quotient and agrees with its
literal quotient map on every actor.

For each of the five small terminal models, the established distance-three
result and the implications 8.6(a)--(c) now force 8.6(d), and identify H with
the terminal center. The central-containment hypothesis 8.6(a), earlier local
obstruction and full model catalogue remain explicit. Larger terminal fields,
the general distance-five exclusion, and the equal-field conclusion of 8.7
remain separate obligations.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Chapter 8, pp. 139--140, proof of 8.6.
-/

@[expose] public noncomputable section
open Subgroup Representation BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Ambient isomorphisms transport the full natural marking, including
both the two-core actor kernel and the central section kernel. -/
theorem natural_center_map (e : G ≃* G) (L Z Q : Subgroup G)
    (hnat : Noncommuting.HasNaturalCenter L Z Q) :
    Noncommuting.HasNaturalCenter (L.map e.toMonoidHom) (Z.map e.toMonoidHom)
      (Q.map e.toMonoidHom) := by
  obtain ⟨k,_,_,_,π,hπ,hker,⟨d⟩⟩ := hnat
  let eL := e.subgroupMap L
  let eZ := e.subgroupMap Z
  let π' := π.comp eL.symm.toMonoidHom
  refine ⟨k,inferInstance,inferInstance,inferInstance,π',hπ.comp eL.symm.surjective,?_,?_⟩
  · ext l
    change eL.symm l ∈ π.ker ↔ (l : G) ∈ Q.map e.toMonoidHom
    rw [hker]
    change e.symm (l : G) ∈ Q ↔ (l : G) ∈ Q.map e.toMonoidHom
    exact (mem_map_equiv (f := e) (K := Q) (x := (l : G))).symm
  · refine ⟨{
      section_le := map_mono d.section_le
      kernel_le := ?_
      normalized := ?_
      coordinates := d.coordinates.comp eZ.symm.toMonoidHom
      onto := d.onto.comp eZ.symm.surjective
      kernel_eq := ?_
      equivariant := ?_ }⟩
    · rw [Stellmacher.omegaOneCenterAmbient_map_injective _ e.injective]
      exact map_mono d.kernel_le
    · rw [←map_equiv_normalizer_eq]
      exact map_mono d.normalized
    · ext z
      change d.coordinates (eZ.symm z) = 1 ↔
        (z : G) ∈ Stellmacher.omegaOneCenterAmbient (L.map e.toMonoidHom)
      rw [d.coordinates_eq_one_iff,Stellmacher.omegaOneCenterAmbient_map_injective _ e.injective]
      exact mem_map_equiv.symm
    · intro l z
      change (d.coordinates (eZ.symm _)).toAdd =
        SL2NaturalOffenders.NoStrong.natural (π (eL.symm l)) (d.coordinates (eZ.symm z)).toAdd
      convert d.equivariant (eL.symm l) (eZ.symm z) using 1
      · congr 2
        apply Subtype.ext
        change e.symm ((l : G) * (z : G) * (l : G)⁻¹) =
          e.symm (l : G) * e.symm (z : G) * (e.symm (l : G))⁻¹
        simp only [map_mul,map_inv]
      · rfl

/-- Natural coordinates are transported along the actual vertex orbit,
with unchanged field and the literal local group, center and core. -/
theorem source_natural_center_of_type (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P)) {v w : Vertex (family P)}
    (ht : v.type = w.type)
    (hnat : Noncommuting.HasNaturalCenter (d.localGroup v) (Z (family P) v) (Q (family P) v)) :
    Noncommuting.HasNaturalCenter (d.localGroup w) (Z (family P) w) (Q (family P) w) := by
  let := finite_endpoints h
  obtain ⟨g,rfl⟩ := (same_orbit_iff (family P) v w).mpr ht
  rw [d.conjugate,Z_translate,Q_translate]
  exact natural_center_map (MulAut.conj g) _ _ _ hnat

/-- A central neighboring orbit kills the central section kernel. The
natural action is therefore on the whole original center, and its quotient
isomorphism agrees with the literal quotient map on every local actor. -/
theorem source_natural_center_coordinates_of_neighbor_central
    (h : LocallyRankOneTriple P B) (d : EarlierLocalTheorems (family P))
    {v w : Vertex (family P)} (he : (graph (family P)).Adj v w)
    (hcentral : Z (family P) w = omegaCenterIn (d.localGroup w))
    (hnat : Noncommuting.HasNaturalCenter (d.localGroup v) (Z (family P) v) (Q (family P) v)) :
    ∃ (k : Type u) (_ : Field k) (_ : Finite k) (_ : Algebra (ZMod 2) k),
      ∃ (π : d.localGroup v →* SL(2,k))
        (e : (d.localGroup v ⧸ pCore 2 (d.localGroup v)) ≃* SL(2,k)),
        Function.Surjective π ∧ π.ker = pCore 2 (d.localGroup v) ∧
        (∀ l, e (QuotientGroup.mk' (pCore 2 (d.localGroup v)) l) = π l) ∧
        Nonempty (BinaryConjugationSection (d.localGroup v) (Z (family P) v) ⊥
          (SL2NaturalOffenders.NoStrong.natural.comp π)) := by
  obtain ⟨k,_,_,_,π,hπ,hker,⟨δ⟩⟩ := hnat
  let L := d.localGroup v
  have hcore : (Q (family P) v).subgroupOf L = pCore 2 L := by
    rw [←localGroup_core_eq (family P) d v]
    exact comap_map_eq_self_of_injective L.subtype_injective _
  have hk := hker.trans hcore
  let e : (L ⧸ pCore 2 L) ≃* SL(2,k) :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπ)
  refine ⟨k,inferInstance,inferInstance,inferInstance,π,e,hπ,hk,?_,?_⟩
  · intro l
    rfl
  · have hω : Stellmacher.omegaOneCenterAmbient L = ⊥ :=
      local_omega_eq_bot_of_neighbor_central h d he hcentral
    exact ⟨hω ▸ δ⟩

/-- In every small terminal model, source 8.6(a) forces 8.6(d) at the
original starting vertex, with its actual quotient and natural action. -/
theorem reduced_small_terminal_central_start_natural
    {J : Fin 2 → Subgroup G} {S₀ : Subgroup G} (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥)
    (hsmall :
      let D := graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')
      ClassicalGroup.IsPSL D 2 2 ∨ Nonempty (D ≃* DihedralGroup 5) ∨
      Nonempty (D ≃* SuzukiMatrixGroup 0) ∨ ClassicalGroup.IsPSU D 3 2 ∨ IsSU D 3 2)
    (hH : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≤ Z (Reduction.reducedFamily J S₀) a') :
    let F := Reduction.reducedFamily J S₀
    b F = 3 ∧ ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆ = Z F a' ∧
      Noncommuting.HasNaturalCenter (graphLocalGroup F a) (Z F a) (Q F a) ∧
      ∃ (k : Type u) (_ : Field k) (_ : Finite k) (_ : Algebra (ZMod 2) k),
        ∃ (π : graphLocalGroup F a →* SL(2,k))
          (e : (graphLocalGroup F a ⧸ pCore 2 (graphLocalGroup F a)) ≃* SL(2,k)),
          Function.Surjective π ∧ π.ker = pCore 2 (graphLocalGroup F a) ∧
          (∀ l, e (QuotientGroup.mk' (pCore 2 (graphLocalGroup F a)) l) = π l) ∧
          Nonempty (BinaryConjugationSection (graphLocalGroup F a) (Z F a) ⊥
            (SL2NaturalOffenders.NoStrong.natural.comp π)) := by
  obtain ⟨hb3,hHeq,w,R,hm,hR,hnat⟩ :=
    reduced_small_terminal_central_commutator_natural h hob models hc hab hd hb hcomm hne hsmall hH
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily J S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  have hodd : Odd ((graph F).dist a a') := by rw [hc.1,hb3]; decide
  have hne : a.type ≠ a'.type := (odd_dist_iff F ht.generate a a').mp hodd
  have hwn : a'.type ≠ w.val.type := w.property.1
  have hwa : w.val.type = a.type := by
    cases hw : w.val.type <;> cases ha : a.type <;> cases ha' : a'.type <;> simp_all
  have hn := source_natural_center_of_type ht d hwa hnat
  exact ⟨hb3,hHeq,hn,source_natural_center_coordinates_of_neighbor_central ht d hab
    (source_critical_geometry ht d hc hab hd hb hcomm).2.2.1 hn⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial

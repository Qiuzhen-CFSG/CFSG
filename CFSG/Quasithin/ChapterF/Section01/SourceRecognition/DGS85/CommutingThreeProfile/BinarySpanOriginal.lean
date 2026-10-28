module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.BinarySpanRecognition

/-!
# The Chapter 13 symmetric-four quotient in the original parabolic

The genuine binary markings identify the graph local groups with their
full stabilizers, so the natural-center sections supplied by Chapter 9
apply to BinarySpanRecognition. At either base vertex, its denominator
Q_a ∩ Q_c maps through the original reduced-completion inclusion. We
identify the resulting original parabolic quotient with S₄, prove its
order is 24, and keep the quotient square on every original representative.
Normality is proved inside each displayed parabolic, not in the ambient
completion.

This is the original-group application of DGS (13.1)(f). The earlier
Chapter 9 binary markings, b > 2, order-eight span, order-two middle center
and natural-center sections remain explicit. Their production and the
full (12.9)/(13.1) assembly remain with the existing source owners; this
module does not claim the Chapter 9 branch selection.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(13.1), printed p.191; the original source reduction retains both endpoints
and the full Borel from Aschbacher--Smith F.1.9.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open Reduction ReducedLayer Subgroup.CosetGeometry.RankTwo
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem transport_quotient_marking
    {A P M : Type*} [Group A] [Group P] [Group M]
    (N : Subgroup A) (N₀ : Subgroup P) (E : A ≃* P)
    (hmap : N.map E.toMonoidHom = N₀) [hn : N.Normal]
    (f : (A ⧸ N) ≃* M) :
    ∃ hn₀ : N₀.Normal, letI := hn₀
      ∃ f₀ : (P ⧸ N₀) ≃* M, ∀ x : A,
        f₀ (QuotientGroup.mk (E x)) = f (QuotientGroup.mk x) := by
  let : N₀.Normal := hmap ▸ hn.map E.toMonoidHom E.surjective
  let q := QuotientGroup.congr N N₀ E hmap
  refine ⟨inferInstance,q.symm.trans f,?_⟩
  intro x
  change f (q.symm (QuotientGroup.mk (E x))) = f (QuotientGroup.mk x)
  rw [← QuotientGroup.congr_mk N N₀ E hmap x]
  exact congrArg f (q.symm_apply_apply _)

/-- The original quotient is S₄, with the literal denominator and representative square. -/
theorem source_original_binary_span_symmetric_four (h : HypothesisF11 L S)
    (e : ∀ j, (L j ⧸ pCore 2 (L j)) ≃* SL(2,ZMod 2))
    (i : Bool) (hb : 2 < b (reducedFamily L S))
    {a c : Vertex (reducedFamily L S)}
    (ha : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) a)
    (hc : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) c)
    (hspan : V (reducedFamily L S) (base (reducedFamily L S) i) 1 =
      Z (reducedFamily L S) a ⊔ Z (reducedFamily L S) c)
    (hV : Nat.card (V (reducedFamily L S) (base (reducedFamily L S) i) 1) = 8)
    (hZ : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = 2)
    (hna : Noncommuting.HasNaturalCenter (graphLocalGroup (reducedFamily L S) a)
      (Z (reducedFamily L S) a) (Q (reducedFamily L S) a))
    (hnc : Noncommuting.HasNaturalCenter (graphLocalGroup (reducedFamily L S) c)
      (Z (reducedFamily L S) c) (Q (reducedFamily L S) c)) :
    let F := reducedFamily L S
    let A := stabilizer F (base F i)
    let P := parabolic L S (if i then 1 else 0)
    let N := (Q F a ⊓ Q F c).subgroupOf A
    let N₀ := ((Q F a ⊓ Q F c).map (G₀ L S).subtype).subgroupOf P
    ∃ hn : N.Normal, ∃ hn₀ : N₀.Normal, letI := hn; letI := hn₀
      Nat.card (P ⧸ N₀) = 24 ∧
      ∃ f : (A ⧸ N) ≃* Equiv.Perm (Fin 4),
        ∃ f₀ : (P ⧸ N₀) ≃* Equiv.Perm (Fin 4),
          ∀ x : A, f₀ (QuotientGroup.mk (binaryBaseStabilizerEquiv h e i x)) =
            f (QuotientGroup.mk x) := by
  let F := reducedFamily L S
  let A := stabilizer F (base F i)
  let P := parabolic L S (if i then 1 else 0)
  let I := Q F a ⊓ Q F c
  let N := I.subgroupOf A
  let I₀ := I.map (G₀ L S).subtype
  let N₀ := I₀.subgroupOf P
  let E := binaryBaseStabilizerEquiv h e i
  have hna' : Noncommuting.HasNaturalCenter (stabilizer F a) (Z F a) (Q F a) := by
    rw [← both_binary_graphLocalGroup_eq_stabilizer h e a]
    exact hna
  have hnc' : Noncommuting.HasNaturalCenter (stabilizer F c) (Z F c) (Q F c) := by
    rw [← both_binary_graphLocalGroup_eq_stabilizer h e c]
    exact hnc
  have hC := source_binary_span_centralizer h e ha hc hspan hna' hnc'
  have hIA : I ≤ A := hC.symm.le.trans inf_le_left
  have hI₀P : I₀ ≤ P := by
    rintro x ⟨y,hy,rfl⟩
    have hey := binaryBaseStabilizerEquiv_coe h e i (⟨y,hIA hy⟩ : A)
    exact (congrArg (fun z : G => z ∈ P) hey).mp (E ⟨y,hIA hy⟩).property
  have hmap : N.map E.toMonoidHom = N₀ := by
    apply map_injective P.subtype_injective
    rw [Subgroup.map_map, map_subgroupOf_eq_of_le hI₀P]
    have hcomp : P.subtype.comp E.toMonoidHom = (G₀ L S).subtype.comp A.subtype :=
      MonoidHom.ext (binaryBaseStabilizerEquiv_coe h e i)
    rw [hcomp, ← Subgroup.map_map, map_subgroupOf_eq_of_le hIA]
  obtain ⟨hn,_,⟨f⟩⟩ := source_binary_span_symmetric_four h e hb ha hc hspan hV hZ hna' hnc'
  let : N.Normal := hn
  obtain ⟨hn₀,f₀,hf₀⟩ := transport_quotient_marking N N₀ E hmap f
  let : N₀.Normal := hn₀
  refine ⟨hn,hn₀,?_,f,f₀,hf₀⟩
  rw [Nat.card_congr f₀.toEquiv]
  norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile

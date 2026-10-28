module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.BinarySpanKernel
public import Theory.GroupTheory.ElementaryEightBinaryQuotient
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearGraphApplication
/-!
# The symmetric-four quotient in DGS (13.1)(f)

On the actual binary source graph, the neighboring natural centers span
an elementary group of order eight. Its middle center has order two, so
the middle stabilizer fixes a nonidentity vector. BinarySpanKernel
identifies the kernel of this action with Q_a ∩ Q_c. The proved linear
(6.5) obstruction makes this kernel properly smaller than Q_v. The
finite elementary-eight recognition then identifies the literal quotient
G_v/(Q_a ∩ Q_c) with S₄ and gives its exact order 24.

No extra nonnormality premise is assumed: it is discharged using the
original binary quotient markings. The binary markings, b > 2, natural
center sections, order-eight span and order-two middle center are the
earlier Chapter 9 conclusions, retained explicitly with their producer
qt-dgs85-critical-commuting-trivial. This proves the last recognition step
of (13.1), not the preceding Chapter 9 selection or the whole theorem.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(13.1), printed p.191, using (6.5) and (9.1),(9.3),(9.4),(9.8),(9.10),(9.11).
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open Reduction ReducedLayer Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.AmalgamGraph CommutingNontrivial
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The literal neighboring-core quotient is S₄, with relative normality proved. -/
theorem source_binary_span_symmetric_four (h : HypothesisF11 L S)
    (e : ∀ j, (L j ⧸ pCore 2 (L j)) ≃* SL(2,ZMod 2))
    (hb : 2 < b (reducedFamily L S))
    {a v c : Vertex (reducedFamily L S)}
    (ha : (graph (reducedFamily L S)).Adj v a)
    (hc : (graph (reducedFamily L S)).Adj v c)
    (hspan : V (reducedFamily L S) v 1 =
      Z (reducedFamily L S) a ⊔ Z (reducedFamily L S) c)
    (hV : Nat.card (V (reducedFamily L S) v 1) = 8)
    (hZ : Nat.card (Z (reducedFamily L S) v) = 2)
    (hna : Noncommuting.HasNaturalCenter (stabilizer (reducedFamily L S) a)
      (Z (reducedFamily L S) a) (Q (reducedFamily L S) a))
    (hnc : Noncommuting.HasNaturalCenter (stabilizer (reducedFamily L S) c)
      (Z (reducedFamily L S) c) (Q (reducedFamily L S) c)) :
    let N := (Q (reducedFamily L S) a ⊓ Q (reducedFamily L S) c).subgroupOf
      (stabilizer (reducedFamily L S) v)
    ∃ hN : N.Normal, letI := hN
      Nat.card (stabilizer (reducedFamily L S) v ⧸ N) = 24 ∧
      Nonempty ((stabilizer (reducedFamily L S) v ⧸ N) ≃* Equiv.Perm (Fin 4)) := by
  have hob := reduced_linear_graph_core_obstruction h
    ((e 0).trans (Theory.PSL2.sl2QuotientEquiv (ZMod 2)))
    ((e 1).trans (Theory.PSL2.sl2QuotientEquiv (ZMod 2))) v a ha
  let F := reducedFamily L S
  let A := stabilizer F v
  let W := V F v 1
  let N := (Q F a ⊓ Q F c).subgroupOf A
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let hZW := fun w => (source_Z_Q_U (reduced_triple h) w).1
  let : IsElementaryAbelian 2 W := V_elementary F (reduced_triple h).generate
    hZW (reduced_kernel_sylow h) hb v
  have hWA : W ≤ A := (V_le_Q F (reduced_triple h).generate hZW
    (reduced_kernel_sylow h) hb v).trans (map_subtype_le _)
  let : Finite W := Finite.of_injective (inclusion hWA) (inclusion_injective _)
  let ρ := W.normalizerMonoidHom.comp (inclusion (stabilizer_normalizes_V F v 1))
  have hC := source_binary_span_centralizer h e ha hc hspan hna hnc
  have hk : ρ.ker = N := by
    ext x
    change W.normalizerMonoidHom ⟨x.val,stabilizer_normalizes_V F v 1 x.property⟩ = 1 ↔ _
    rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker]
    change (x : G₀ L S) ∈ centralizer (W : Set (G₀ L S)) ↔ (x : G₀ L S) ∈ Q F a ⊓ Q F c
    constructor
    · intro hx
      exact hC ▸ (show (x : G₀ L S) ∈ A ⊓ centralizer (W : Set (G₀ L S)) from ⟨x.property,hx⟩)
    · intro hx
      exact (show (x : G₀ L S) ∈ A ⊓ centralizer (W : Set (G₀ L S)) from hC.symm ▸ hx).2
  have hkernel : A ⊓ centralizer (W : Set (G₀ L S)) ≤ Q F v :=
    (source_span_centralizer_le_kernel (reduced_triple h) ha).trans_eq
      (source_both_binary_kernel_eq_core h e ha)
  have hQ : (Q F v).subgroupOf A = pCore 2 A :=
    comap_map_eq_self_of_injective A.subtype_injective _
  have hkQ : ρ.ker ≤ pCore 2 A := by
    rw [hk,← hQ]
    intro x hx
    exact hkernel (hC.symm ▸ hx)
  have hstrict : ρ.ker < pCore 2 A := by
    refine lt_of_le_of_ne hkQ ?_
    intro he
    have hQa : Q F v ≤ Q F a := by
      intro x hx
      have hxA : x ∈ A := map_subtype_le _ hx
      have hxQ : (⟨x,hxA⟩ : A) ∈ pCore 2 A := hQ ▸ hx
      have hxN : (⟨x,hxA⟩ : A) ∈ N := hk ▸ (he.symm ▸ hxQ)
      exact hxN.1
    apply hob
    rw [inf_eq_right.mpr hQa]
    exact stabilizer_normalizes_Q F v
  let Z₀ := (Z F v).subgroupOf A
  let : Z₀.Normal := (normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer F v)).mpr
    (stabilizer_normalizes_Z F v)
  have hZ₀ : Nat.card Z₀ = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe (Z_le_stabilizer F v)).toEquiv).trans hZ
  have hcent := central_of_normal_card_two Z₀ hZ₀
  let : Finite (Z F v) := Finite.of_injective (inclusion (Z_le_stabilizer F v))
    (inclusion_injective _)
  let : Nontrivial (Z F v) := Finite.one_lt_card_iff_nontrivial.mp (by
    change 1 < Nat.card (Z (reducedFamily L S) v)
    omega)
  obtain ⟨z₀,hz₀⟩ := exists_ne (1 : Z F v)
  let z : W := inclusion (Z_le_V F v 1) z₀
  have hz : z ≠ 1 := by
    intro he
    have hh : (z₀ : G₀ L S) = 1 := congrArg (fun w : W => (w : G₀ L S)) he
    exact hz₀ (Subtype.ext hh)
  have hfix : ∀ g : A, ρ g z = z := by
    intro g
    apply Subtype.ext
    change (g : G₀ L S) * (z₀ : G₀ L S) * (g : G₀ L S)⁻¹ = (z₀ : G₀ L S)
    have hh := mem_center_iff.mp (hcent (show
      (⟨z₀,Z_le_stabilizer F v z₀.property⟩ : A) ∈ Z₀ from z₀.property)) g
    have hh' : (g : G₀ L S) * (z₀ : G₀ L S) = (z₀ : G₀ L S) * (g : G₀ L S) :=
      congrArg (fun y : A => (y : G₀ L S)) hh
    rw [hh', mul_inv_cancel_right]
  obtain ⟨eq⟩ := both_binary_vertex_quotient h e v
  obtain ⟨hcard,⟨f⟩⟩ := elementaryEight_fixed_point_symmetricThree_core_quotient hV ρ z hz hfix
    (eq.trans SLTwoPermThree.sl2Two_equiv_perm_three.some) hstrict
  let : N.Normal := hk ▸ ρ.normal_ker
  let fN := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans f
  refine ⟨inferInstance,?_,⟨fN⟩⟩
  rw [Nat.card_congr fN.toEquiv]
  norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile

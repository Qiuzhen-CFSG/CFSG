module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiNeighborOrbits

/-!
# Full-edge complements after the middle-core move

All full edge stabilizers of the reduced graph are conjugate. Consequently
their orders and intrinsic two-core orders agree. An odd subgroup of the
new edge with the order of the old complement is therefore complementary
to the new edge core. This supplies the supplement property that does not
follow merely from fixing the three selected vertices.

Apply this to the actual middle-core conjugate constructed from the linear
and nonbinary Suzuki quotient markings. The original inclusion and the
literal conjugator are retained. The common-Sylow marking remains the
earlier Chapter 8 / 12.1(c) input.

Source: DGS85, Groups and Graphs, (12.3)(a), printed p.179.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open Subgroup.CosetGeometry.RankTwo Reduction Theory.GroupTheory.AmalgamGraph
namespace ReducedLayer
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem edge_equiv (h : HypothesisF11 L S)
    {x m y z : Vertex (reducedFamily L S)}
    (hxm : (graph (reducedFamily L S)).Adj x m)
    (hyz : (graph (reducedFamily L S)).Adj y z) :
    Nonempty ((stabilizer (reducedFamily L S) x ⊓ stabilizer (reducedFamily L S) m :
      Subgroup (G₀ L S)) ≃*
      (stabilizer (reducedFamily L S) y ⊓ stabilizer (reducedFamily L S) z :
      Subgroup (G₀ L S))) := by
  obtain ⟨g, _, hg⟩ := source_edge_transport (reduced_triple h) hxm
  obtain ⟨t, _, ht⟩ := source_edge_transport (reduced_triple h) hyz
  let B := (B₀ L S).subgroupOf (G₀ L S)
  let eg := (B.equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr hg.symm)
  let et := (B.equivMapOfInjective (MulAut.conj t).toMonoidHom
    (MulAut.conj t).injective).trans (MulEquiv.subgroupCongr ht.symm)
  exact ⟨eg.symm.trans et⟩

/-- Moving an odd complement into another full edge preserves its complement property. -/
theorem source_edge_complement_transfer (h : HypothesisF11 L S)
    {x m y z : Vertex (reducedFamily L S)}
    (hxm : (graph (reducedFamily L S)).Adj x m)
    (hyz : (graph (reducedFamily L S)).Adj y z)
    (K : Subgroup (stabilizer (reducedFamily L S) x ⊓ stabilizer (reducedFamily L S) m :
      Subgroup (G₀ L S)))
    (hK : (pCore 2 (stabilizer (reducedFamily L S) x ⊓ stabilizer (reducedFamily L S) m :
      Subgroup (G₀ L S))).IsComplement' K)
    (C : Subgroup (G₀ L S))
    (hC : C ≤ stabilizer (reducedFamily L S) y ⊓ stabilizer (reducedFamily L S) z)
    (hodd : Odd (Nat.card C)) (hcard : Nat.card C = Nat.card K) :
    (pCore 2 (stabilizer (reducedFamily L S) y ⊓ stabilizer (reducedFamily L S) z :
      Subgroup (G₀ L S))).IsComplement'
        (C.subgroupOf (stabilizer (reducedFamily L S) y ⊓ stabilizer (reducedFamily L S) z)) := by
  let F := reducedFamily L S
  let E := stabilizer F y ⊓ stabilizer F z
  let E₀ := stabilizer F x ⊓ stabilizer F m
  let : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  let : Finite E := Finite.of_injective (inclusion (show E ≤ stabilizer F y from inf_le_left))
    (inclusion_injective _)
  obtain ⟨e⟩ := edge_equiv h hxm hyz
  have hc : Nat.card (C.subgroupOf E) = Nat.card C :=
    Nat.card_congr (subgroupOfEquivOfLe hC).toEquiv
  have hP : Nat.card (pCore 2 E₀) = Nat.card (pCore 2 E) :=
    Nat.card_congr ((e.subgroupMap (pCore 2 E₀)).trans
      (MulEquiv.subgroupCongr (pCore_map_iso 2 e))).toEquiv
  apply isComplement'_of_coprime
  · rw [hc, hcard, ← hP, hK.card_mul_card]
    exact Nat.card_congr e.toEquiv
  · obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := E)).exists_card_eq
    rw [hn, hc]
    exact (Nat.coprime_two_left.mpr hodd).pow_left n

open BenderSuzuki.MatrixGroups BenderSuzuki.Converse

/-- Both actual edge complements, with the original conjugation map preserved. -/
theorem source_linear_suzuki_edge_complements
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) {n : ℕ} (hn : 0 < n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL2 k)
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (T : Sylow 2 (star L S i))
    (hcommon : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    {x z : Vertex (reducedFamily L S)}
    (hx : (graph (reducedFamily L S)).Adj x (base (reducedFamily L S) (!i)))
    (hxne : base (reducedFamily L S) i ≠ x)
    (hz : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) z)
    (hzne : z ≠ base (reducedFamily L S) (!i)) :
    let F := reducedFamily L S
    let E := stabilizer F x ⊓ stabilizer F (base F (!i))
    let W := V F x 1 ⊓ Q F (base F i)
    ∃ K : Subgroup E,
      (pCore 2 E).IsComplement' K ∧ Odd (Nat.card K) ∧
      K.map E.subtype ≤ stabilizer F (base F i) ∧
      ∃ q ∈ Q F (base F (!i)),
        (K.map E.subtype).map (MulAut.conj q).toMonoidHom ≤
          stabilizer F x ⊓ stabilizer F (base F i) ⊓ stabilizer F z ∧
        (pCore 2 (stabilizer F (base F i) ⊓ stabilizer F z : Subgroup (G₀ L S))).IsComplement'
          (((K.map E.subtype).map (MulAut.conj q).toMonoidHom).subgroupOf
            (stabilizer F (base F i) ⊓ stabilizer F z)) ∧
        (K.map E.subtype).map (MulAut.conj q).toMonoidHom ≤ normalizer (W : Set (G₀ L S)) ∧
        Nat.card ((K.map E.subtype).map (MulAut.conj q).toMonoidHom) = Nat.card K ∧
        ((K.map E.subtype).map (MulAut.conj q).toMonoidHom).map (G₀ L S).subtype =
          ((K.map E.subtype).map (G₀ L S).subtype).map (MulAut.conj (q : G)).toMonoidHom := by
  let F := reducedFamily L S
  let E := stabilizer F x ⊓ stabilizer F (base F (!i))
  obtain ⟨K, hK, hodd, hKy, q, hq, hfix, hnorm, hc, hmap⟩ :=
    source_linear_suzuki_complements h i hn eLin eSuz T hcommon hx hxne hz hzne
  have hnew := source_edge_complement_transfer h hx hz K hK
    ((K.map E.subtype).map (MulAut.conj q).toMonoidHom)
    (le_inf (hfix.trans (inf_le_left.trans inf_le_right)) (hfix.trans inf_le_right))
    (hc.symm ▸ hodd) hc
  exact ⟨K, hK, hodd, hKy, q, hq, hfix, hnew, hnorm, hc, hmap⟩

end ReducedLayer
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile

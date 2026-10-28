module

public import Theory.GroupAction.RankTwoCosetCover.PathTransport

/-!
# The coset-cover and path-transport ingredients of F.3

For explicit groups and pairs of subgroups, `ofHom` takes a surjection which is
an isomorphism on each subgroup and maps their intersection onto the target
intersection. `covering_of_hom` proves the covering assertion of F.3.1.
The subsequent theorems apply the constructed path equivalences to discharge
the equivariance, stabilizer, and transitivity assertions of F.3.3 and F.3.4.

These are the generic homomorphism prerequisites. The source assembly must
instantiate the homomorphisms with the universal completion from F.2; no such
completion or its faithfulness is assumed to have been constructed here.

The graph and action are the existing tagged cosets from `RankTwoCosetGeometry`.
Inversion translates the source's right action to the left action, with the
literal covering formula supplied by `CoverData.vertex_rightVertex`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
F.3.1–F.3.4, printed pp.269–270.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.CosetCover
open Subgroup Subgroup.CosetGeometry.RankTwo SimpleGraph SimpleGraph.BasedWalk
variable {A B C : Type*} [Group A] [Group B] [Group C]

/-- `false` denotes points (`H`), and `true` denotes lines (`K`). -/
def family (H K : Subgroup A) : Bool → Subgroup A := fun i => bif i then K else H

/-- Construct the generic cover hypotheses from the two explicit subgroup isomorphisms.
The universal-completion owner supplies these homomorphism facts; no covering or path
correspondence is assumed. -/
theorem ofHom (H K : Subgroup A) (H' K' : Subgroup B) (f : A →* B)
    (hf : Function.Surjective f) (hH : H.map f = H') (hK : K.map f = K')
    (hiH : Function.Injective (fun a : H => f a))
    (hiK : Function.Injective (fun a : K => f a))
    (hI : (H ⊓ K).map f = H' ⊓ K') : CoverData (family H K) (family H' K') f where
  surjective := hf
  map_eq i := by cases i; exact hH; exact hK
  injective i := by cases i; exact hiH; exact hiK
  map_inf := hI

/-- F.3.1's graph construction and covering assertion for the actual two coset spaces. -/
theorem covering_of_hom (H K : Subgroup A) (H' K' : Subgroup B) (f : A →* B)
    (hf : Function.Surjective f) (hH : H.map f = H') (hK : K.map f = K')
    (hiH : Function.Injective (fun a : H => f a))
    (hiK : Function.Injective (fun a : K => f a))
    (hI : (H ⊓ K).map f = H' ⊓ K') :
    let c := ofHom H K H' K' f hf hH hK hiH hiK hI
    Function.Surjective c.vertex ∧
      (∀ v, Function.Bijective (c.hom.mapNeighborSet v)) ∧
      (graph (family H K)).IsBipartite ∧
      (H ⊔ K = ⊤ → (graph (family H K)).Connected) ∧
      stabilizer (family H K) (base (family H K) false) = H ∧
      stabilizer (family H K) (base (family H K) true) = K := by
  dsimp only
  let c := ofHom H K H' K' f hf hH hK hiH hiK hI
  refine ⟨c.vertex_surjective, c.neighbor_bijective,
    (coset_bipartition _).isBipartite, fun h => connected _ h, ?_, ?_⟩
  · exact Subgroup.CosetGeometry.stabilizer_base (family H K) false
  · exact Subgroup.CosetGeometry.stabilizer_base (family H K) true

variable {H K : Subgroup A} {H' K' : Subgroup B} {H'' K'' : Subgroup C}
variable {f : A →* B} {g : A →* C}
variable (c : CoverData (family H K) (family H' K') f)
variable (d : CoverData (family H K) (family H'' K'') g)

/-- F.3.3(1)–(2): the explicit all-length path equivalence is a quasiequivalence. -/
theorem path_quasiequivalence (v : Vertex (family H K)) :
    (∀ a : stabilizer (family H K) v, ∀ p : Σ n, BasedWalk (graph (family H K)) n v,
      c.allPathEquiv v (a • p) = c.stabilizerEquiv v a • c.allPathEquiv v p) ∧
    (∀ p : Σ n, BasedWalk (graph (family H K)) n v, (c.allPathEquiv v p).1 = p.1) :=
  ⟨c.allPathEquiv_smul, c.allPathEquiv_length v⟩

/-- F.3.3(3): equality of the literal homomorphic image and an isomorphism with that same map. -/
theorem path_stabilizers {n : ℕ} {v : Vertex (family H K)}
    (p : BasedWalk (graph (family H K)) n v) :
    (pathStabilizer (family H K) p).map f =
      pathStabilizer (family H' K') (c.pathEquiv n v p) ∧
    ∃ e : pathStabilizer (family H K) p ≃*
      pathStabilizer (family H' K') (c.pathEquiv n v p),
      ∀ a, (e a : B) = f a :=
  ⟨c.pathStabilizer_map p, c.pathStabilizerEquiv p, c.pathStabilizerEquiv_val p⟩

/-- F.3.3(4), for the inherited action on the actual fixed-length nonbacktracking paths. -/
theorem path_transitivity (n : ℕ) (v : Vertex (family H K))
    (ht : MulAction.IsPretransitive (stabilizer (family H K) v)
      {p : BasedWalk (graph (family H K)) n v // p.Nonbacktracking}) :
    MulAction.IsPretransitive (stabilizer (family H' K') (c.vertex v))
      {p : BasedWalk (graph (family H' K')) n (c.vertex v) // p.Nonbacktracking} :=
  c.nbPath_transitive n v ht

/-- F.3.4(1)–(2): the composite path equivalence and the composite local group isomorphism
intertwine the permutation actions and map their actual stabilizers onto one another. -/
theorem comparison_quasiequivalence (v : Vertex (family H K)) :
    (∀ b : stabilizer (family H' K') (c.vertex v),
      ∀ p : Σ n, BasedWalk (graph (family H' K')) n (c.vertex v),
      c.transportAllPathEquiv d v (b • p) =
        c.transportStabilizer d v b • c.transportAllPathEquiv d v p) ∧
    (∀ p : Σ n, BasedWalk (graph (family H' K')) n (c.vertex v),
      (MulAction.stabilizer (stabilizer (family H' K') (c.vertex v)) p).map
        (c.transportStabilizer d v).toMonoidHom =
        MulAction.stabilizer (stabilizer (family H'' K'') (d.vertex v))
          (c.transportAllPathEquiv d v p)) :=
  ⟨c.transportAllPathEquiv_smul d, c.transport_allPath_stabilizer_map d v⟩

/-- F.3.4(2) on ambient pointwise path stabilizers, with the local isomorphism marked. -/
theorem comparison_path_stabilizers {n : ℕ} {v : Vertex (family H K)}
    (p : BasedWalk (graph (family H' K')) n (c.vertex v)) :
    ∃ e : pathStabilizer (family H' K') p ≃*
      pathStabilizer (family H'' K'') (c.transportPathEquiv d n v p),
      ∀ a, (e a : C) =
        (c.transportStabilizer d v ⟨a, pathStabilizer_le (family H' K') p a.property⟩ : C) :=
  ⟨c.transportPathStabilizerEquiv d p, c.transportPathStabilizerEquiv_val d p⟩

/-- F.3.4(3), transferring the exact fixed-length nonbacktracking action. -/
theorem comparison_transitivity (n : ℕ) (v : Vertex (family H K))
    (ht : MulAction.IsPretransitive (stabilizer (family H' K') (c.vertex v))
      {p : BasedWalk (graph (family H' K')) n (c.vertex v) // p.Nonbacktracking}) :
    MulAction.IsPretransitive (stabilizer (family H'' K'') (d.vertex v))
      {p : BasedWalk (graph (family H'' K'')) n (d.vertex v) // p.Nonbacktracking} :=
  c.transport_nbPath_transitive d n v ht

end CFSG.Quasithin.ChapterF.CosetCover

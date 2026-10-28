module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenDescentEdges
public import Theory.GroupTheory.SubgroupEnumerationBinary
public import Theory.GroupTheory.PGroup.MaximalIndex

/-!
# Binary certificates for the small even maximal-subgroup census

The edge table records one representative for every eligible maximal subgroup
of each of the 600 nodes.  The reusable part of the argument is independent
of the particular table: a maximal subgroup of the Sylow two group has relative
index two, hence is recovered by the binary Schreier construction.  A finite
certificate only has to identify each resulting Schreier closure with an edge,
or discharge it by the core-character or centralizer alternative.

This module supplies that certificate interface and its soundness theorem.  It
keeps the 600-node and 3617-edge public data in `SmallEvenDescentEdges`; the
finite table itself is intentionally a separate kernel-checked certificate.

Source: the maximal-chain descent of Shinoda (1975), (2.3), pp. 81–82, and
the binary Schreier reduction in `SubgroupEnumerationBinary`.
-/

namespace ReeTwo.SylowModel

open Theory.GroupTheory.SubgroupEnumeration

/-- A finite certificate for all binary Schreier branches below the 600 nodes.

`generators i` generates node `i`.  For each nonzero signature, the resulting
Schreier closure is either in the core-character kernel, is noncentric by an
explicit outside centralizer element, or is exactly one of the recorded edges.
The last alternative is deliberately stated as equality, since the edge list
already fixes representatives in the parent node.
-/
public def SmallEvenMaximalCoverageCertificate : Prop :=
  ∀ (i : Fin 600),
    ∃ (n : Nat) (generators : Fin n → SylowModel),
      Subgroup.closure (Set.range generators) = smallEvenDescentNode i ∧
      (∀ (σ : Fin n → Bool) (j : Fin n), σ j = true →
        let L := Subgroup.closure
          (Set.range (binarySchreierGenerator generators (generators j) σ))
        L ≤ coreCharacter.ker ∨
          (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨
          (∃ e : Fin 3617, L =
            ReeTwo.SylowModel.SmallEvenDescentEdges.edge e))

/-- Construct the coverage certificate from generating families and their
branch trichotomies, without exposing the certificate definition to clients. -/
public theorem SmallEvenMaximalCoverageCertificate.mk
    (h : ∀ (i : Fin 600),
      ∃ (n : Nat) (generators : Fin n → SylowModel),
        Subgroup.closure (Set.range generators) = smallEvenDescentNode i ∧
        (∀ (σ : Fin n → Bool) (j : Fin n), σ j = true →
          let L := Subgroup.closure
            (Set.range (binarySchreierGenerator generators (generators j) σ))
          L ≤ coreCharacter.ker ∨
            (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨
            (∃ e : Fin 3617, L = SmallEvenDescentEdges.edge e))) :
    SmallEvenMaximalCoverageCertificate := h

/-- The binary certificate proves exhaustive eligible maximal-subgroup coverage.

The proof uses the actual index-two Schreier witness for an arbitrary maximal
subgroup.  Thus the certificate also covers parents which are removed by later
Frattini witnesses; no pruning of the parent family occurs here.
-/
public theorem smallEvenMaximalCoverage_of_certificate
    (hcert : SmallEvenMaximalCoverageCertificate) :
    ∀ (i : Fin 600) (H : Subgroup SylowModel),
      H ⋖ smallEvenDescentNode i →
      Subgroup.centralizer (H : Set SylowModel) ≤ H →
      ¬ H ≤ coreCharacter.ker →
      ∃ e : Fin 3617, H = ReeTwo.SylowModel.SmallEvenDescentEdges.edge e := by
  intro i H hmax hcent hcore
  obtain ⟨n, generators, hgen, hbranches⟩ := hcert i
  obtain ⟨σ, j, hj, hL⟩ :=
    exists_binarySchreier_of_covBy
      (IsPGroup.of_card (p := 2) (n := 12) ReeTwo.SylowModel.card)
      hmax generators hgen
  have hbranch := hbranches σ j hj
  dsimp only at hbranch
  rw [hL] at hbranch
  rcases hbranch with hcoreL | ⟨c, hcentral, hcnot⟩ | ⟨e, he⟩
  · exact (hcore hcoreL).elim
  · exact (hcnot (hcent hcentral)).elim
  · exact ⟨e, he⟩

end ReeTwo.SylowModel

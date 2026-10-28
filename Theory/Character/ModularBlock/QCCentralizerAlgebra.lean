module
public import Theory.Character.ModularBlock.QCCentralizer
public import Theory.Character.ModularBlock.Basic
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
/-!
# Embedding a centralizer algebra into its product with a subgroup

The canonical inclusion C_G(Q) into Q C_G(Q) induces an injective group
algebra homomorphism. Nonzero coefficients in its image centralize Q.
The embedding preserves centrality, idempotence, factor identities, and
augmentation over the stated semiring or commutative-ring coefficients.

For centrality, write each indexing group element as a product of an
element of Q and one of C_G(Q). The first factor commutes with every
centralizer basis element; the second commutes with the given central
element. Extending this calculation linearly proves centrality in the
larger algebra. The remaining facts follow from injectivity, coefficient
support, and the ring-homomorphism laws.

Ported from revision c3503435 of public/lean-eval/glauberman_zStar,
Submission/ZStar/NormalizerBrauerPair.lean. The embedding has an exposed
coefficient implementation for the ensuing support and normalizer arguments;
no finiteness or block-correspondence hypothesis is used.
-/

public section
noncomputable section
namespace ModularBlock.NormalizerBrauerPair
open Subgroup
open scoped Pointwise
universe u
/-- Embed the centralizer group algebra into the group algebra of
`Q C_G(Q)`. -/
@[expose] noncomputable def qcCentralizerAlgebraEmbedding
    (R : Type*) {G : Type u} [Semiring R] [Group G]
    (Q : Subgroup G) :
    MonoidAlgebra R (Subgroup.centralizer (Q : Set G)) →+*
      MonoidAlgebra R (qcCentralizer Q) :=
  MonoidAlgebra.mapDomainRingHom R (centralizerToQcCentralizer Q)

@[simp] theorem qcCentralizerAlgebraEmbedding_single
    {R : Type*} {G : Type u} [Semiring R] [Group G]
    (Q : Subgroup G)
    (c : Subgroup.centralizer (Q : Set G)) (r : R) :
    qcCentralizerAlgebraEmbedding R Q (MonoidAlgebra.single c r) =
      MonoidAlgebra.single (centralizerToQcCentralizer Q c) r := by
  simp [qcCentralizerAlgebraEmbedding]

/-- The centralizer algebra embedding does not kill a nonzero element. -/
theorem qcCentralizerAlgebraEmbedding_ne_zero
    {R : Type*} {G : Type u} [Semiring R] [Group G]
    (Q : Subgroup G)
    (b : MonoidAlgebra R (Subgroup.centralizer (Q : Set G)))
    (hb : b ≠ 0) :
    qcCentralizerAlgebraEmbedding R Q b ≠ 0 := by
  intro hzero
  apply hb
  apply MonoidAlgebra.mapDomain_injective (centralizerToQcCentralizer_injective Q)
  exact hzero.trans (MonoidAlgebra.mapDomain_zero _).symm

/-- Every nonzero coefficient of an embedded centralizer element is indexed
by an element of `C_G(Q)`. -/
theorem coeff_mem_centralizer_of_qcCentralizerAlgebraEmbedding_ne_zero
    {R : Type*} {G : Type u} [Semiring R] [Group G]
    (Q : Subgroup G)
    (b : MonoidAlgebra R (Subgroup.centralizer (Q : Set G)))
    (x : qcCentralizer Q)
    (hx : (qcCentralizerAlgebraEmbedding R Q b).coeff x ≠ 0) :
    (x : G) ∈ Subgroup.centralizer (Q : Set G) := by
  have hxrange : x ∈ Set.range (centralizerToQcCentralizer Q) := by
    by_contra hnot
    apply hx
    exact Finsupp.mapDomain_of_notMem_range b.coeff x hnot
  obtain ⟨c, rfl⟩ := hxrange
  exact c.property

/-- Consequently every nonzero coefficient of the embedded element
centralizes the copy of `Q` inside `Q C_G(Q)`. -/
theorem coeff_centralizes_subgroupOf_qcCentralizer_of_embedding_ne_zero
    {R : Type*} {G : Type u} [Semiring R] [Group G]
    (Q : Subgroup G)
    (b : MonoidAlgebra R (Subgroup.centralizer (Q : Set G)))
    (x : qcCentralizer Q)
    (hx : (qcCentralizerAlgebraEmbedding R Q b).coeff x ≠ 0) :
    x ∈ Subgroup.centralizer
      ((Q.subgroupOf (qcCentralizer Q) : Subgroup (qcCentralizer Q)) :
        Set (qcCentralizer Q)) := by
  have hxC :=
    coeff_mem_centralizer_of_qcCentralizerAlgebraEmbedding_ne_zero Q b x hx
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  apply Subtype.ext
  exact Subgroup.mem_centralizer_iff.mp hxC (q : G) hq

/-- A central element of `K[C_G(Q)]` remains central after embedding into
`K[Q C_G(Q)]`: elements of `Q` commute pointwise with `C_G(Q)`, while the
centralizer factor commutes by the original centrality hypothesis. -/
theorem qcCentralizerAlgebraEmbedding_mem_center
    {R : Type*} {G : Type u} [CommRing R] [Group G]
    (Q : Subgroup G)
    (b : MonoidAlgebra R (Subgroup.centralizer (Q : Set G)))
    (hb : b ∈ Set.center
      (MonoidAlgebra R (Subgroup.centralizer (Q : Set G)))) :
    qcCentralizerAlgebraEmbedding R Q b ∈
      Set.center (MonoidAlgebra R (qcCentralizer Q)) := by
  rw [Semigroup.mem_center_iff]
  intro a
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | single l r =>
      let C : Subgroup G := Subgroup.centralizer (Q : Set G)
      let L : Subgroup G := qcCentralizer Q
      have hlmem : (l : G) ∈ Q ⊔ C := l.property
      have hlprod : (l : G) ∈ (Q : Set G) * (C : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left Q C
          (Subgroup.centralizer_le_normalizer (Q : Set G))]
        exact hlmem
      obtain ⟨q, hq, c, hc, hqc⟩ := hlprod
      let qL : L := ⟨q, by
        exact (le_sup_left : Q ≤ Q ⊔ C) hq⟩
      let cC : C := ⟨c, hc⟩
      let cL : L := centralizerToQcCentralizer Q cC
      have hl : qL * cL = l := by
        apply Subtype.ext
        exact hqc
      have hqcomm_all
          (b' : MonoidAlgebra R (Subgroup.centralizer (Q : Set G))) :
          MonoidAlgebra.of R L qL * qcCentralizerAlgebraEmbedding R Q b' =
            qcCentralizerAlgebraEmbedding R Q b' *
              MonoidAlgebra.of R L qL := by
        induction b' using MonoidAlgebra.induction_linear with
        | zero => simp
        | add x y hx hy => rw [map_add, mul_add, add_mul, hx, hy]
        | single c' s =>
            rw [qcCentralizerAlgebraEmbedding_single]
            change MonoidAlgebra.single qL 1 *
                MonoidAlgebra.single (centralizerToQcCentralizer Q c') s =
              MonoidAlgebra.single (centralizerToQcCentralizer Q c') s *
                MonoidAlgebra.single qL 1
            rw [MonoidAlgebra.single_mul_single,
              MonoidAlgebra.single_mul_single]
            simp only [one_mul, mul_one]
            congr 1
            apply Subtype.ext
            exact Subgroup.mem_centralizer_iff.mp c'.property q hq
      have hqcomm :
          MonoidAlgebra.of R L qL * qcCentralizerAlgebraEmbedding R Q b =
            qcCentralizerAlgebraEmbedding R Q b *
              MonoidAlgebra.of R L qL := hqcomm_all b
      have hccommC := Semigroup.mem_center_iff.mp hb
        (MonoidAlgebra.of R C cC)
      have hccommMap := congrArg
        (qcCentralizerAlgebraEmbedding R Q) hccommC
      have hccomm :
          MonoidAlgebra.of R L cL * qcCentralizerAlgebraEmbedding R Q b =
            qcCentralizerAlgebraEmbedding R Q b *
              MonoidAlgebra.of R L cL := by
        simpa [C, L, cL, cC] using hccommMap
      have hprodcomm :
          (MonoidAlgebra.of R L qL * MonoidAlgebra.of R L cL) *
              qcCentralizerAlgebraEmbedding R Q b =
            qcCentralizerAlgebraEmbedding R Q b *
              (MonoidAlgebra.of R L qL * MonoidAlgebra.of R L cL) := by
        calc
          (MonoidAlgebra.of R L qL * MonoidAlgebra.of R L cL) *
                qcCentralizerAlgebraEmbedding R Q b =
              MonoidAlgebra.of R L qL *
                (MonoidAlgebra.of R L cL *
                  qcCentralizerAlgebraEmbedding R Q b) := by rw [mul_assoc]
          _ = MonoidAlgebra.of R L qL *
                (qcCentralizerAlgebraEmbedding R Q b *
                  MonoidAlgebra.of R L cL) := by rw [hccomm]
          _ = (MonoidAlgebra.of R L qL *
                qcCentralizerAlgebraEmbedding R Q b) *
                  MonoidAlgebra.of R L cL := by rw [mul_assoc]
          _ = (qcCentralizerAlgebraEmbedding R Q b *
                MonoidAlgebra.of R L qL) *
                  MonoidAlgebra.of R L cL := by rw [hqcomm]
          _ = qcCentralizerAlgebraEmbedding R Q b *
                (MonoidAlgebra.of R L qL *
                  MonoidAlgebra.of R L cL) := by rw [mul_assoc]
      have hlOf : MonoidAlgebra.of R L l =
          MonoidAlgebra.of R L qL * MonoidAlgebra.of R L cL := by
        rw [← map_mul, hl]
      rw [show MonoidAlgebra.single l r =
          r • MonoidAlgebra.of R L l by simp]
      simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
      exact congrArg (fun x : MonoidAlgebra R L => r • x)
        (by simpa [hlOf] using hprodcomm)

theorem qcCentralizerAlgebraEmbedding_isIdempotent
    {R : Type*} {G : Type u} [Semiring R] [Group G]
    (Q : Subgroup G)
    (b : MonoidAlgebra R (Subgroup.centralizer (Q : Set G)))
    (hb : IsIdempotentElem b) :
    IsIdempotentElem (qcCentralizerAlgebraEmbedding R Q b) := by
  exact hb.map (qcCentralizerAlgebraEmbedding R Q)

theorem qcCentralizerAlgebraEmbedding_mul_eq_self
    {R : Type*} {G : Type u} [Semiring R] [Group G]
    (Q : Subgroup G)
    (a b : MonoidAlgebra R (Subgroup.centralizer (Q : Set G)))
    (hba : b * a = b) :
    qcCentralizerAlgebraEmbedding R Q b *
        qcCentralizerAlgebraEmbedding R Q a =
      qcCentralizerAlgebraEmbedding R Q b := by
  rw [← map_mul, hba]

/-- Embedding `K[C_G(Q)]` into `K[Q C_G(Q)]` preserves augmentation. -/
theorem augmentation_qcCentralizerAlgebraEmbedding
    {R : Type*} {G : Type u} [CommSemiring R] [Group G]
    (Q : Subgroup G)
    (b : MonoidAlgebra R (Subgroup.centralizer (Q : Set G))) :
    groupAlgebraAugmentation R (qcCentralizer Q)
        (qcCentralizerAlgebraEmbedding R Q b) =
      groupAlgebraAugmentation R
        (Subgroup.centralizer (Q : Set G)) b := by
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single c r =>
      simp [qcCentralizerAlgebraEmbedding_single,
        groupAlgebraAugmentation_single]

end ModularBlock.NormalizerBrauerPair


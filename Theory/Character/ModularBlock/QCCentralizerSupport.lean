module
public import Theory.Character.ModularBlock.QCCentralizerAlgebra
public import Theory.Character.ModularBlock.SubgroupBrauerHom

/-!
# Maximal support under centralizer embeddings

Let Q be a maximal two-subgroup coefficient support of an element e in a
finite group algebra. Restrict e to C_G(Q) and embed in Q C_G(Q). The
canonical copy of Q remains a maximal support subgroup. In characteristic
two the same holds for any nonzero central factor of that restriction.

The embedded coefficients centralize the normal copy of Q. Adjoin Q to any
supporting subgroup, map the join back to G, and use the original maximality
to bound its order. For central factors, multiplicativity of subgroup
Brauer restriction transfers nonzero support to the parent. An arbitrary
nonzero embedded centralizer element also has maximal support containing Q,
by the normal-two-subgroup support lemma.

Ported from revision c3503435 of public/lean-eval/glauberman_zStar,
Submission/ZStar/NormalizerBrauerPair.lean. These coefficient arguments
supply the support part of the normalizer layer without block correspondence.
-/

public section
noncomputable section
namespace ModularBlock.NormalizerBrauerPair
open Subgroup
open scoped Pointwise
universe u
/-- The canonical copy of `Q` supports every nonzero element embedded from
`K[C_G(Q)]`. -/
theorem subgroupOf_qcCentralizer_hasSupport_embedding
    {R : Type*} {G : Type u} [Semiring R] [Group G] [Finite G]
    (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (b : MonoidAlgebra R (Subgroup.centralizer (Q : Set G)))
    (hb : b ≠ 0) :
    DefectSupport.HasTwoCoefficientSupport
      (qcCentralizerAlgebraEmbedding R Q b)
      (Q.subgroupOf (qcCentralizer Q)) := by
  have hQsub : IsPGroup 2 (Q.subgroupOf (qcCentralizer Q)) :=
    hQ.of_equiv (Subgroup.subgroupOfEquivOfLe
      (H := Q) (K := qcCentralizer Q) le_sup_left).symm
  have hcoeff : ∃ c : Subgroup.centralizer (Q : Set G), b.coeff c ≠ 0 := by
    by_contra h
    push Not at h
    apply hb
    ext c
    exact h c
  obtain ⟨c, hc⟩ := hcoeff
  let x : qcCentralizer Q := centralizerToQcCentralizer Q c
  have hx : (qcCentralizerAlgebraEmbedding R Q b).coeff x ≠ 0 := by
    change Finsupp.mapDomain (centralizerToQcCentralizer Q) b.coeff x ≠ 0
    rw [Finsupp.mapDomain_apply
      (centralizerToQcCentralizer_injective Q)]
    exact hc
  exact ⟨hQsub, x,
    coeff_centralizes_subgroupOf_qcCentralizer_of_embedding_ne_zero
      Q b x hx,
    hx⟩

/-- The direct `Q`-coefficient restriction of an element whose maximal
support is `Q`, embedded into `Q C_G(Q)`, still has exactly the canonical
copy of `Q` as a maximal support subgroup.  This is coefficientwise
transitivity: a support subgroup upstairs maps back to a support subgroup of
the original element. -/
theorem subgroupOf_qcCentralizer_isMaximalSupport_of_embedding_restriction
    [Fact (Nat.Prime 2)]
    {R : Type*} {G : Type u} [Semiring R] [Group G] [Finite G]
    (e : MonoidAlgebra R G) (Q : Subgroup G)
    (hQmax : DefectSupport.IsMaximalTwoCoefficientSupport e Q) :
    DefectSupport.IsMaximalTwoCoefficientSupport
      (qcCentralizerAlgebraEmbedding R Q
        (DefectSupport.subgroupCentralizerRestriction R Q e))
      (Q.subgroupOf (qcCentralizer Q)) := by
  let L : Subgroup G := qcCentralizer Q
  let P : Subgroup L := Q.subgroupOf L
  let eQ := DefectSupport.subgroupCentralizerRestriction R Q e
  let eL := qcCentralizerAlgebraEmbedding R Q eQ
  have hPp : IsPGroup 2 P :=
    hQmax.1.1.of_equiv (Subgroup.subgroupOfEquivOfLe
      (H := Q) (K := L) le_sup_left).symm
  have hPnormal : P.Normal := by
    change (Q.subgroupOf
      (Q ⊔ Subgroup.centralizer (Q : Set G))).Normal
    rw [sup_comm]
    exact Subgroup.normal_subgroupOf_sup_of_le_normalizer
      (Subgroup.centralizer_le_normalizer (Q : Set G))
  refine ⟨?_, ?_⟩
  · rcases hQmax.1 with ⟨_hQp, x, hxC, hxe⟩
    let c : Subgroup.centralizer (Q : Set G) := ⟨x, hxC⟩
    let xL : L := centralizerToQcCentralizer Q c
    have hxcoeff : eL.coeff xL ≠ 0 := by
      change Finsupp.mapDomain (centralizerToQcCentralizer Q) eQ.coeff xL ≠ 0
      rw [Finsupp.mapDomain_apply
        (centralizerToQcCentralizer_injective Q)]
      exact hxe
    refine ⟨hPp, xL, ?_, hxcoeff⟩
    exact
      coeff_centralizes_subgroupOf_qcCentralizer_of_embedding_ne_zero
        Q eQ xL hxcoeff
  · intro D hD
    rcases hD with ⟨hDp, y, hyD, hycoeff⟩
    have hyP : y ∈ Subgroup.centralizer (P : Set L) :=
      coeff_centralizes_subgroupOf_qcCentralizer_of_embedding_ne_zero
        Q eQ y hycoeff
    have hPcy : P ≤ Subgroup.centralizer ({y} : Set L) := by
      intro p hp
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hyP p hp
    have hDcy : D ≤ Subgroup.centralizer ({y} : Set L) := by
      intro d hd
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hyD d hd
    let : P.Normal := hPnormal
    let S : Subgroup L := P ⊔ D
    have hSp : IsPGroup 2 S := by
      exact IsPGroup.to_sup_of_normal_left hPp hDp
    have hyS : y ∈ Subgroup.centralizer (S : Set L) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact Subgroup.mem_centralizer_singleton_iff.mp
        (sup_le hPcy hDcy hs)
    let SG : Subgroup G := S.map L.subtype
    have hSGp : IsPGroup 2 SG := hSp.map L.subtype
    have hySG : (y : G) ∈ Subgroup.centralizer (SG : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      obtain ⟨sL, hsL, rfl⟩ := Subgroup.mem_map.mp hs
      exact congrArg Subtype.val
        (Subgroup.mem_centralizer_iff.mp hyS sL hsL)
    have hye : e.coeff (y : G) ≠ 0 := by
      have hyC :=
        coeff_mem_centralizer_of_qcCentralizerAlgebraEmbedding_ne_zero
          Q eQ y hycoeff
      let c : Subgroup.centralizer (Q : Set G) := ⟨(y : G), hyC⟩
      have hcy : centralizerToQcCentralizer Q c = y := by
        apply Subtype.ext
        rfl
      change Finsupp.mapDomain (centralizerToQcCentralizer Q) eQ.coeff y ≠ 0 at hycoeff
      rw [← hcy, Finsupp.mapDomain_apply
        (centralizerToQcCentralizer_injective Q)] at hycoeff
      exact hycoeff
    have hSGSupport : DefectSupport.HasTwoCoefficientSupport e SG :=
      ⟨hSGp, (y : G), hySG, hye⟩
    have hbound : Nat.card SG ≤ Nat.card Q :=
      hQmax.2 SG hSGSupport
    calc
      Nat.card D ≤ Nat.card S :=
        Subgroup.card_le_of_le le_sup_right
      _ = Nat.card SG := Nat.card_congr
        (Subgroup.equivMapOfInjective S L.subtype
          L.subtype_injective).toEquiv
      _ ≤ Nat.card Q := hbound
      _ = Nat.card P := (Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe
          (H := Q) (K := L) le_sup_left).toEquiv).symm

/-- A central factor of the embedded `Q`-Brauer restriction cannot have a
larger coefficient defect: its nonzero Brauer restrictions transfer back to
the original element by the characteristic-two subgroup Brauer product
calculation. -/
theorem subgroupOf_qcCentralizer_isMaximalSupport_of_embedding_factor
    [Fact (Nat.Prime 2)]
    {R : Type*} {G : Type u} [CommRing R] [CharP R 2]
    [Group G] [Finite G]
    (e : MonoidAlgebra R G) (hecenter : e ∈ Set.center (MonoidAlgebra R G))
    (Q : Subgroup G)
    (hQmax : DefectSupport.IsMaximalTwoCoefficientSupport e Q)
    (b : MonoidAlgebra R (Subgroup.centralizer (Q : Set G)))
    (hbcenter : b ∈ Set.center
      (MonoidAlgebra R (Subgroup.centralizer (Q : Set G))))
    (hbfactor : b * DefectSupport.subgroupCentralizerRestriction R Q e = b)
    (hbne : b ≠ 0) :
    DefectSupport.IsMaximalTwoCoefficientSupport
      (qcCentralizerAlgebraEmbedding R Q b)
      (Q.subgroupOf (qcCentralizer Q)) := by
  let a := DefectSupport.subgroupCentralizerRestriction R Q e
  let eb := qcCentralizerAlgebraEmbedding R Q b
  let ea := qcCentralizerAlgebraEmbedding R Q a
  have hacenter : a ∈ Set.center
      (MonoidAlgebra R (Subgroup.centralizer (Q : Set G))) := by
    exact SubgroupBrauerMap.subgroupCentralizerRestriction_mem_center
      Q e hecenter
  have hebcenter : eb ∈ Set.center
      (MonoidAlgebra R (qcCentralizer Q)) := by
    simpa [eb] using qcCentralizerAlgebraEmbedding_mem_center Q b hbcenter
  have heacenter : ea ∈ Set.center
      (MonoidAlgebra R (qcCentralizer Q)) := by
    simpa [ea] using qcCentralizerAlgebraEmbedding_mem_center Q a hacenter
  have hebne : eb ≠ 0 := by
    simpa [eb] using qcCentralizerAlgebraEmbedding_ne_zero Q b hbne
  have hefactor : eb * ea = eb := by
    simpa [eb, ea, a] using
      qcCentralizerAlgebraEmbedding_mul_eq_self Q a b hbfactor
  have hbase := subgroupOf_qcCentralizer_hasSupport_embedding Q
    hQmax.1.1 b hbne
  refine ⟨hbase, ?_⟩
  intro D hD
  have hebRestrNe :
      DefectSupport.subgroupCentralizerRestriction R D eb ≠ 0 :=
    (DefectSupport.hasTwoCoefficientSupport_iff_restriction_ne_zero eb D).mp
      hD |>.2
  have heaRestrNe :
      DefectSupport.subgroupCentralizerRestriction R D ea ≠ 0 := by
    intro hzero
    apply hebRestrNe
    have hmul :=
      SubgroupBrauerMap.subgroupCentralizerRestriction_mul_of_mem_center
        D hD.1 eb ea hebcenter heacenter
    rw [hefactor, hzero, mul_zero] at hmul
    exact hmul
  have hEaSupport : DefectSupport.HasTwoCoefficientSupport ea D := by
    rw [DefectSupport.hasTwoCoefficientSupport_iff_restriction_ne_zero]
    exact ⟨hD.1, heaRestrNe⟩
  have hAmax := subgroupOf_qcCentralizer_isMaximalSupport_of_embedding_restriction
    e Q hQmax
  exact hAmax.2 D (by simpa [ea, a] using hEaSupport)

/-- A maximal coefficient-support subgroup of an embedded nonzero
centralizer element contains the canonical copy of `Q`.  This supplies the
first half of the defect statement for the intermediate block on
`Q C_G(Q)` without invoking First Main or Third Main. -/
theorem exists_maximalSupport_qcCentralizerEmbedding_containing
    [Fact (Nat.Prime 2)]
    {R : Type*} {G : Type u} [Semiring R] [Group G] [Finite G]
    (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (b : MonoidAlgebra R (Subgroup.centralizer (Q : Set G)))
    (hb : b ≠ 0) :
    ∃ D : Subgroup (qcCentralizer Q),
      DefectSupport.IsMaximalTwoCoefficientSupport
          (qcCentralizerAlgebraEmbedding R Q b) D ∧
        Q.subgroupOf (qcCentralizer Q) ≤ D := by
  let e := qcCentralizerAlgebraEmbedding R Q b
  have he : e ≠ 0 := qcCentralizerAlgebraEmbedding_ne_zero Q b hb
  obtain ⟨D, hD⟩ :=
    DefectSupport.exists_isMaximalTwoCoefficientSupport e he
  have hQsub : IsPGroup 2 (Q.subgroupOf (qcCentralizer Q)) :=
    hQ.of_equiv (Subgroup.subgroupOfEquivOfLe
      (H := Q) (K := qcCentralizer Q) le_sup_left).symm
  have hQnormal : (Q.subgroupOf (qcCentralizer Q)).Normal := by
    rw [qcCentralizer, sup_comm]
    exact Subgroup.normal_subgroupOf_sup_of_le_normalizer
      (Subgroup.centralizer_le_normalizer (Q : Set G))
  refine ⟨D, hD, ?_⟩
  exact
    DefectSupport.normalTwoSubgroup_le_of_isMaximalTwoCoefficientSupport_of_coeff_centralizes
      e D hD (Q.subgroupOf (qcCentralizer Q)) hQsub hQnormal
      (fun x hx =>
        coeff_centralizes_subgroupOf_qcCentralizer_of_embedding_ne_zero
          Q b x hx)

end ModularBlock.NormalizerBrauerPair


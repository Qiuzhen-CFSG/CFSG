module

public import Theory.AlgebraicGroup.BNPair.StandardParabolicCore
public import Theory.AlgebraicGroup.RootSystems.StandardParabolicConjugacy
public import Theory.GroupTheory.SubgroupConjugation

/-!
Standard parabolics for a Tits system aligned with a finite crystallographic
root system.

`WeylIdentification` records both the quotient/Weyl-group equivalence and its
compatibility with distinguished generators.  Pulling a simple-root subset
back along this identification defines the BN-pair standard parabolic.  The
Bruhat saturation theorem in `StandardParabolicCore` then gives its exact
double-coset carrier, classification and uniqueness among subgroups containing
`B`, order reflection, the empty and full endpoints, and classification after
conjugating `B`.

For self-normalization, classify the normalizer and consider a distinguished
cell which it contains.  The rank-one nontriviality witness has the form
`n b n`; normalizing the parabolic puts this witness back in the parabolic, so
the whole cell was already present.  For conjugacy rigidity, strip the two
`B`-factors from a Bruhat representative, descend conjugation to the Weyl
quotient, and replace the resulting element by a minimum-length parabolic
double-coset representative.  The Coxeter/root argument in
`StandardParabolicConjugacy` then transports the simple-root supports exactly.

This is the abstract BN-pair and Coxeter content of GLS3, Theorem 1.13.2.  No
numbered algebraic-group theorem is used.
-/

namespace Theory.AlgebraicGroup.TitsSystem

open scoped Pointwise

variable {X : Type*} [Group X]

/-- Standard parabolics in an abstract Tits system are self-normalizing. -/
public theorem standardParabolic_normalizer_eq (T : TitsSystem (X := X))
    {I : Set (T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N)} (hI : I ⊆ T.S) :
    Subgroup.normalizer (T.standardParabolic I : Set X) = T.standardParabolic I := by
  let P := T.standardParabolic I
  apply le_antisymm
  · have hB : T.B ≤ Subgroup.normalizer (P : Set X) := by
      exact (T.B_le_standardParabolic I).trans (Subgroup.le_normalizer)
    have hclass := T.subgroup_eq_standardParabolic_simpleIndices
      (Subgroup.normalizer (P : Set X)) hB
    rw [hclass]
    apply T.standardParabolic_mono
    intro s hs
    rcases (T.mem_simpleIndices_iff _ _).1 hs with ⟨hsS, hsCell⟩
    obtain ⟨ns, b, hns, hb, hz⟩ := T.exists_rankOne_witness hsS
    have hnsNorm : (ns : X) ∈ Subgroup.normalizer (P : Set X) :=
      hsCell (T.representative_mem_bruhatCell s ns hns)
    have hconj : (ns : X) * b * (ns : X)⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp hnsNorm b).1 (T.B_le_standardParabolic I hb)
    have hsq : ((ns : X) ^ 2) ∈ P := by
      apply T.B_le_standardParabolic I
      exact (T.representative_sq_mem_intersection hsS ns hns).1
    have hzP : (ns : X) * b * (ns : X) ∈ P := by
      have := P.mul_mem hconj hsq
      simpa only [pow_two, mul_assoc, inv_mul_cancel_left] using this
    have hsCellP : T.bruhatCell s ⊆ P :=
      T.bruhatCell_subset_of_mem P (T.B_le_standardParabolic I) hz hzP
    have hsSimple : s ∈ T.simpleIndices P :=
      (T.mem_simpleIndices_iff _ _).2 ⟨hsS, hsCellP⟩
    simpa only [P, T.simpleIndices_standardParabolic hI] using hsSimple
  · exact Subgroup.le_normalizer

end Theory.AlgebraicGroup.TitsSystem

namespace Theory.AlgebraicGroup

variable {X ι M N : Type*} [Group X] [Finite ι]
  [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
  {P : RootPairing ι ℝ M N} [P.IsRootSystem]
  [P.IsCrystallographic] [P.IsReduced]

/-- An identification of a Tits quotient and its distinguished generators with
a Weyl group and the simple reflections of a chosen base. -/
public structure TitsSystem.WeylIdentification (T : TitsSystem (X := X))
    (b : P.Base) where
  quotientEquiv : (T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) ≃* P.weylGroup
  simpleEquiv : T.S ≃ b.support
  map_simple : ∀ s : T.S,
    quotientEquiv s = b.simpleReflection (simpleEquiv s)

namespace TitsSystem.WeylIdentification

variable {T : TitsSystem (X := X)} {b : P.Base}

@[expose] public def simpleIndices (A : T.WeylIdentification b) (J : Set b.support) :
    Set (T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) :=
  (fun j : b.support => ((A.simpleEquiv.symm j : T.S) :
    T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N)) '' J

omit [Finite ι] [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] in
public theorem simpleIndices_subset (A : T.WeylIdentification b) (J : Set b.support) :
    A.simpleIndices J ⊆ T.S := by
  rintro s ⟨j, hj, rfl⟩
  exact (A.simpleEquiv.symm j).property

omit [Finite ι] [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] in
public theorem quotientEquiv_image_simpleIndices (A : T.WeylIdentification b)
    (J : Set b.support) :
    A.quotientEquiv '' A.simpleIndices J = b.simpleReflection '' J := by
  ext w
  constructor
  · rintro ⟨s, ⟨j, hj, rfl⟩, rfl⟩
    refine ⟨j, hj, ?_⟩
    simpa using (A.map_simple (A.simpleEquiv.symm j)).symm
  · rintro ⟨j, hj, rfl⟩
    refine ⟨((A.simpleEquiv.symm j : T.S) : _), ⟨j, hj, rfl⟩, ?_⟩
    simpa using A.map_simple (A.simpleEquiv.symm j)

omit [Finite ι] [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] in
public theorem map_closure_simpleIndices (A : T.WeylIdentification b)
    (J : Set b.support) :
    (Subgroup.closure (A.simpleIndices J)).map A.quotientEquiv.toMonoidHom =
      b.parabolicSubgroup J := by
  rw [MonoidHom.map_closure]
  congr 1
  exact A.quotientEquiv_image_simpleIndices J

omit [Finite ι] [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] in
public theorem mem_closure_simpleIndices_iff (A : T.WeylIdentification b)
    (J : Set b.support) (w : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) :
    w ∈ Subgroup.closure (A.simpleIndices J) ↔
      A.quotientEquiv w ∈ b.parabolicSubgroup J := by
  rw [← A.map_closure_simpleIndices J]
  constructor
  · intro hw
    exact Subgroup.mem_map.mpr ⟨w, hw, rfl⟩
  · rintro ⟨v, hv, heq⟩
    have : v = w := A.quotientEquiv.injective heq
    subst v
    exact hv

@[expose] public def standardParabolic (A : T.WeylIdentification b)
    (J : Set b.support) : Subgroup X :=
  T.standardParabolic (A.simpleIndices J)

@[expose] public def rootIndices (A : T.WeylIdentification b)
    (H : Subgroup X) : Set b.support :=
  {j | ((A.simpleEquiv.symm j : T.S) :
    T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) ∈ T.simpleIndices H}

omit [Finite ι] [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] in
public theorem simpleIndices_rootIndices (A : T.WeylIdentification b) (H : Subgroup X) :
    A.simpleIndices (A.rootIndices H) = T.simpleIndices H := by
  ext s
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact hj
  · intro hs
    have hsS := T.simpleIndices_subset H hs
    let sS : T.S := ⟨s, hsS⟩
    refine ⟨A.simpleEquiv sS, ?_, ?_⟩
    · change ((A.simpleEquiv.symm (A.simpleEquiv sS) : T.S) :
          T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) ∈ T.simpleIndices H
      simpa [sS] using hs
    · simp [sS]

omit [Finite ι] [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] in
public theorem simpleIndices_injective (A : T.WeylIdentification b) :
    Function.Injective A.simpleIndices := by
  intro J K h
  apply Set.Subset.antisymm
  · intro j hj
    have hm : ((A.simpleEquiv.symm j : T.S) :
        T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) ∈ A.simpleIndices J := ⟨j, hj, rfl⟩
    rw [h] at hm
    rcases hm with ⟨k, hk, heq⟩
    have hkj : k = j := A.simpleEquiv.symm.injective (Subtype.ext heq)
    exact hkj ▸ hk
  · intro k hk
    have hm : ((A.simpleEquiv.symm k : T.S) :
        T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) ∈ A.simpleIndices K := ⟨k, hk, rfl⟩
    rw [← h] at hm
    rcases hm with ⟨j, hj, heq⟩
    have hjk : j = k := A.simpleEquiv.symm.injective (Subtype.ext heq)
    exact hjk ▸ hj

end TitsSystem.WeylIdentification

namespace TitsSystem

variable {T : TitsSystem (X := X)} {b : P.Base}

omit [Finite ι] [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] in
public theorem standardParabolic_bruhat (A : T.WeylIdentification b)
    (J : Set b.support) :
    (A.standardParabolic J : Set X) =
      {x | ∃ w, A.quotientEquiv w ∈ b.parabolicSubgroup J ∧
        x ∈ T.bruhatCell w} := by
  rw [WeylIdentification.standardParabolic,
    T.standardParabolic_carrier (A.simpleIndices_subset J)]
  ext x
  constructor
  · rintro ⟨w, hw, hx⟩
    exact ⟨w, (A.mem_closure_simpleIndices_iff J w).1 hw, hx⟩
  · rintro ⟨w, hw, hx⟩
    exact ⟨w, (A.mem_closure_simpleIndices_iff J w).2 hw, hx⟩

omit [Finite ι] [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] in
public theorem standardParabolic_classification_eq (A : T.WeylIdentification b)
    (H : Subgroup X) (hB : T.B ≤ H) :
    H = A.standardParabolic (A.rootIndices H) := by
  calc
    H = T.standardParabolic (T.simpleIndices H) :=
      T.subgroup_eq_standardParabolic_simpleIndices H hB
    _ = T.standardParabolic (A.simpleIndices (A.rootIndices H)) := by
      rw [A.simpleIndices_rootIndices H]
    _ = A.standardParabolic (A.rootIndices H) := rfl

set_option linter.unusedSectionVars false in
public theorem standardParabolic_classification (A : T.WeylIdentification b)
    (H : Subgroup X) (hB : T.B ≤ H) :
    ∃! J : Set b.support, H = A.standardParabolic J := by
  let hcanonical := standardParabolic_classification_eq A H hB
  refine ⟨A.rootIndices H, hcanonical, ?_⟩
  intro J hJ
  apply A.simpleIndices_injective
  have heq : T.standardParabolic (A.simpleIndices (A.rootIndices H)) =
      T.standardParabolic (A.simpleIndices J) := hcanonical.symm.trans hJ
  exact (T.standardParabolic_eq_iff
    (I := A.simpleIndices (A.rootIndices H)) (J := A.simpleIndices J)
    (A.simpleIndices_subset _) (A.simpleIndices_subset _)).1 heq |>.symm

omit [Finite ι] [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] in
public theorem alignedStandardParabolic_le_iff (A : T.WeylIdentification b)
    (J K : Set b.support) :
    A.standardParabolic J ≤ A.standardParabolic K ↔ J ⊆ K := by
  change T.standardParabolic (A.simpleIndices J) ≤
    T.standardParabolic (A.simpleIndices K) ↔ J ⊆ K
  rw [T.standardParabolic_le_iff (A.simpleIndices_subset J)
    (A.simpleIndices_subset K)]
  constructor
  · intro h j hj
    have hm := h ⟨j, hj, rfl⟩
    rcases hm with ⟨k, hk, heq⟩
    have hkj : k = j := A.simpleEquiv.symm.injective (Subtype.ext heq)
    exact hkj ▸ hk
  · rintro h _ ⟨j, hj, rfl⟩
    exact ⟨j, h hj, rfl⟩

omit [Finite ι] [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] in
public theorem alignedStandardParabolic_eq_iff (A : T.WeylIdentification b)
    (J K : Set b.support) :
    A.standardParabolic J = A.standardParabolic K ↔ J = K := by
  constructor
  · intro h
    exact Set.Subset.antisymm
      ((alignedStandardParabolic_le_iff A J K).1 h.le)
      ((alignedStandardParabolic_le_iff A K J).1 h.ge)
  · rintro rfl
    rfl

omit [Finite ι] [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] in
@[simp] public theorem alignedStandardParabolic_empty (A : T.WeylIdentification b) :
    A.standardParabolic ∅ = T.B := by
  change T.standardParabolic (A.simpleIndices ∅) = T.B
  simp [WeylIdentification.simpleIndices]

omit [Finite ι] [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] in
@[simp] public theorem alignedStandardParabolic_univ (A : T.WeylIdentification b) :
    A.standardParabolic Set.univ = ⊤ := by
  have hsimple : A.simpleIndices Set.univ = T.S := by
    ext s
    constructor
    · intro hs
      exact A.simpleIndices_subset Set.univ hs
    · intro hs
      let sS : T.S := ⟨s, hs⟩
      refine ⟨A.simpleEquiv sS, Set.mem_univ _, ?_⟩
      simp [sS]
  change T.standardParabolic (A.simpleIndices Set.univ) = ⊤
  rw [hsimple, T.standardParabolic_S]

omit [Finite ι] [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] in
public theorem standardParabolic_normalizer (A : T.WeylIdentification b)
    (J : Set b.support) :
    Subgroup.normalizer (A.standardParabolic J : Set X) = A.standardParabolic J :=
  T.standardParabolic_normalizer_eq (A.simpleIndices_subset J)

set_option linter.unusedSectionVars false in
public theorem standardParabolic_conjugate_classification
    (A : T.WeylIdentification b) (H : Subgroup X) (g : X)
    (hB : T.B.conjBy g ≤ H) :
    ∃! J : Set b.support, H = (A.standardParabolic J).conjBy g := by
  let H' := H.conjBy g⁻¹
  have hB' : T.B ≤ H' := by
    intro x hx
    have hxg : g * x * g⁻¹ ∈ H := by
      apply hB
      exact Subgroup.mem_map.mpr ⟨x, hx, by simp [MulAut.conj_apply]⟩
    exact Subgroup.mem_map.mpr ⟨g * x * g⁻¹, hxg, by
      simp [mul_assoc]⟩
  obtain ⟨J, hJ, hJunq⟩ := standardParabolic_classification A H' hB'
  refine ⟨J, ?_, ?_⟩
  · have := congrArg (fun K : Subgroup X => K.conjBy g) hJ
    simpa only [H', Subgroup.conjBy_inv'] using this
  · intro K hK
    apply hJunq
    have := congrArg (fun L : Subgroup X => L.conjBy g⁻¹) hK
    simpa only [H', Subgroup.conjBy_inv] using this

private theorem subgroup_conjBy_eq_self_of_mem {G : Type*} [Group G]
    (H : Subgroup G) {h : G} (hh : h ∈ H) : H.conjBy h = H := by
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mp
  exact H.le_normalizer hh

omit [Finite ι] [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] in
public theorem representative_mem_alignedStandardParabolic_iff
    (A : T.WeylIdentification b) (J : Set b.support) (n : T.N) :
    (n : X) ∈ A.standardParabolic J ↔
      A.quotientEquiv (QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) n) ∈
        b.parabolicSubgroup J := by
  let q := QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) n
  have hnq : (n : X) ∈ T.bruhatCell q := T.representative_mem_bruhatCell q n rfl
  constructor
  · intro hn
    obtain ⟨w, hw, hnw⟩ :=
      (T.mem_standardParabolic_iff (A.simpleIndices_subset J) (n : X)).1 hn
    have hqw : q = w := T.doubleCoset_index_unique hnq hnw
    exact (A.mem_closure_simpleIndices_iff J q).1 (hqw ▸ hw)
  · intro hq
    apply (T.mem_standardParabolic_iff (A.simpleIndices_subset J) (n : X)).2
    exact ⟨q, (A.mem_closure_simpleIndices_iff J q).2 hq, hnq⟩

omit [Finite ι] [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] in
private theorem quotient_conj_le_of_representative_conj
    (A : T.WeylIdentification b) (J K : Set b.support) (n : T.N)
    (hn : (A.standardParabolic K).conjBy (n : X) = A.standardParabolic J) :
    (b.parabolicSubgroup K).conjBy
      (A.quotientEquiv (QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) n)) ≤
        b.parabolicSubgroup J := by
  let q := QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) n
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨m, hm⟩ := QuotientGroup.mk'_surjective
    ((T.B ⊓ T.N).subgroupOf T.N) (A.quotientEquiv.symm x)
  have hmx : A.quotientEquiv
      (QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) m) = x := by
    rw [hm, A.quotientEquiv.apply_symm_apply]
  have hmP : (m : X) ∈ A.standardParabolic K :=
    (representative_mem_alignedStandardParabolic_iff A K m).2 (hmx ▸ hx)
  have hconjmem : (n : X) * (m : X) * (n : X)⁻¹ ∈ A.standardParabolic J := by
    rw [← hn]
    exact Subgroup.mem_map.mpr ⟨(m : X), hmP, by simp [MulAut.conj_apply]⟩
  let z : T.N := n * m * n⁻¹
  have hzP : (z : X) ∈ A.standardParabolic J := by simpa [z] using hconjmem
  have hz := (representative_mem_alignedStandardParabolic_iff A J z).1 hzP
  rw [← hmx]
  simpa [q, z, map_mul, MulAut.conj_apply] using hz

omit [Finite ι] [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] in
private theorem quotient_conj_eq_of_representative_conj
    (A : T.WeylIdentification b) (J K : Set b.support) (n : T.N)
    (hn : (A.standardParabolic K).conjBy (n : X) = A.standardParabolic J) :
    (b.parabolicSubgroup K).conjBy
      (A.quotientEquiv (QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) n)) =
        b.parabolicSubgroup J := by
  apply le_antisymm
  · exact quotient_conj_le_of_representative_conj A J K n hn
  · have hninv : (A.standardParabolic J).conjBy ((n : X)⁻¹) =
        A.standardParabolic K := by rw [← hn, Subgroup.conjBy_inv]
    have hinv := quotient_conj_le_of_representative_conj A K J n⁻¹ hninv
    intro y hy
    let q := A.quotientEquiv
      (QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) n)
    have hy' : q⁻¹ * y * q ∈ b.parabolicSubgroup K := by
      apply hinv
      exact Subgroup.mem_map.mpr ⟨y, hy, by
        simp [q]⟩
    exact Subgroup.mem_map.mpr ⟨q⁻¹ * y * q, hy', by
      change q * (q⁻¹ * y * q) * q⁻¹ = y
      simp [mul_assoc]⟩

public theorem standardParabolic_conjugacy_type
    (A : T.WeylIdentification b) (J K : Set b.support) (g : X)
    (hconj : (A.standardParabolic K).conjBy g = A.standardParabolic J) :
    ∃ v : P.weylGroup,
      IsDistinguishedDoubleCoset b J K v ∧
      P.weylGroupToPerm v '' ((fun k : b.support => (k : ι)) '' K) =
        ((fun j : b.support => (j : ι)) '' J) := by
  obtain ⟨w, hgw⟩ := T.exists_mem_doubleCoset g
  obtain ⟨z, hz, b₂, hb₂, hzg⟩ := Set.mem_mul.mp hgw
  obtain ⟨b₁, hb₁, nx, ⟨n, hn, rfl⟩, hzval⟩ := Set.mem_mul.mp hz
  subst z
  have hb₁J : b₁ ∈ A.standardParabolic J := T.B_le_standardParabolic _ hb₁
  have hb₂K : b₂ ∈ A.standardParabolic K := T.B_le_standardParabolic _ hb₂
  have hnconj : (A.standardParabolic K).conjBy (n : X) =
      A.standardParabolic J := by
    have hg := hconj
    rw [← hzg, Subgroup.conjBy_mul, Subgroup.conjBy_mul,
      subgroup_conjBy_eq_self_of_mem _ hb₂K,
      ] at hg
    have hg' := congrArg (fun H : Subgroup X => H.conjBy b₁⁻¹) hg
    rw [Subgroup.conjBy_inv,
      subgroup_conjBy_eq_self_of_mem _ ((A.standardParabolic J).inv_mem hb₁J)] at hg'
    exact hg'
  let wn := A.quotientEquiv w
  have hwn : A.quotientEquiv
      (QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) n) = wn := by rw [hn]
  have hWconj : (b.parabolicSubgroup K).conjBy wn = b.parabolicSubgroup J := by
    rw [← hwn]
    exact quotient_conj_eq_of_representative_conj A J K n hnconj
  obtain ⟨v, hvdc, hvmin, hvD⟩ := exists_minimalDoubleCoset b J K wn
  obtain ⟨a, ha, c, hc, hv⟩ := DoubleCoset.mem_doubleCoset.mp hvdc
  have hvconj : (b.parabolicSubgroup K).conjBy v = b.parabolicSubgroup J := by
    rw [hv, Subgroup.conjBy_mul, Subgroup.conjBy_mul,
      subgroup_conjBy_eq_self_of_mem _ hc, hWconj,
      subgroup_conjBy_eq_self_of_mem _ ha]
  exact ⟨v, hvD,
    distinguished_standardParabolic_support_image_eq b J K v hvD hvconj⟩

end TitsSystem

end Theory.AlgebraicGroup

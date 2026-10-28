module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Paired.Structure
public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.Paired.Original
public import Theory.GroupTheory.Hall.ConjugateTorusConstruction
public import Theory.GroupTheory.Hall.NormalTwoCore
public import Theory.GroupTheory.SolvableMutualCommutator

/-!
# The source Hall subgroup and its Sylow exchange element

The binary rank-one model makes the unique Sylow maximal subgroup of H/J
solvable. Lifting through J and restricting to H ∩ N_G(L) proves solvability
of the literal overlap. Its component normalizer has index two.

Choose an odd Hall subgroup, use Hall conjugacy inside the index-two
subgroup, and then conjugate a Sylow subgroup of its normalizer into the
prescribed Sylow. This constructs A and the same t in N_T(A) outside N_T(K).
The original component geometry proves disjointness of A ∩ K and its
t-conjugate. No splitting of O₂(H) is assumed.

The model-indexed variants retain an independent positive field exponent.
The original interfaces specialize them to the actual generation parameter.
The abelian Hall product, its prime divisors, the square action on torsion,
and compatible natural coordinates are subsequent source obligations.
Source: Aschbacher--Smith, 11.3.5(2), printed pp.771--772.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K : Subgroup G}

/-- Solvability of the original overlap for either binary rank-one component model.
The quotient is the literal K/O₂(K), independently of its field exponent. -/
theorem ComponentSeed.paired_binary_rankOne_overlap_solvable (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : ¬ (K.subgroupOf H).Normal)
    (hm : (∃ f : ℕ, 0 < f ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) ∨
      ∃ m : ℕ, Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) :
    Group.IsSolvable (H ⊓ normalizer (L : Set G) : Subgroup G) := by
  let P := T.subtype h.outside.1.1.2
  let J := K.subgroupOf H
  have hP := outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h p hc)
  have hsolv := counterexample_not_solvable h p hc hs
  have hgen := ComponentSeed.intrinsic_supplement s h.outside.1.1.2
  let R := ChapterB.minimalParabolicCore P hP
  let q := QuotientGroup.mk' R
  have hq := QuotientGroup.mk'_surjective R
  have hcore : R = pCore 2 H :=
    (ChapterB.minimalParabolic_nonsolvable_core_eq_radical P hP hsolv).trans
      (s.paired_radical_eq_twoCore h p hc hs hn)
  let e := ComponentSeed.quotientImageEquivOfCore s R hcore
  have hi := ChapterE.Structure.source_component_simple_image P hP hsolv J s.component.2 hgen
  let : IsSimpleGroup (J.map q) := hi.1
  let : Group.IsSolvable R := ChapterB.minimalParabolic_core_solvable P hP
  have hJn : ¬ (J.map q).Normal := fun hh =>
    hn (cComponent_normal_of_quotient_normal s.component.2 R hh)
  let M := ChapterB.minimalParabolicMax P hP
  have hMmap : Group.IsSolvable (M.map q) := by
    dsimp only [M]
    rw [ChapterB.minimalParabolicMax_map_core P hP q hq
      (by rw [QuotientGroup.ker_mk'])]
    exact ChapterE.Structure.NumericalBounds.Paired.rankOne_maximal_solvable
      (ChapterE.Structure.source_star_sqtk ChapterA.Section02.theoremA_knownSimple
        (outside_sqtk h) P hP hsolv).stronglyQuasithin
      (P.mapSurjective hq) (ChapterE.Structure.source_star_minimal_core_free P hP).1
      (J.map q) hi.2.1 hi.2.2.2 hJn
      (by
        rcases hm with ⟨f,hf,hm⟩ | ⟨m,⟨em⟩⟩
        · exact .linear f hf (hm.of_mulEquiv e.symm)
        · exact .suzuki m ⟨e.symm.trans em⟩)
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    infer_instance
  let : Group.IsSolvable M := (Group.isSolvable_map_iff_of_solvable_ker q M).mp hMmap
  let B := (normalizer (L : Set G)).subgroupOf H
  have hBM : B ≤ M := by
    apply hP.1.le_maximal
      ⟨(ChapterB.minimalParabolicMax_spec P hP).2,
        (ChapterB.minimalParabolicMax_spec P hP).1.covBy_top⟩
    · exact fun x hx => D.sylow_normalizes_component hx
    · apply lt_top_iff_ne_top.mpr
      intro he
      apply h.outside.1.2
      intro x hx
      exact (show (⟨x,hx⟩ : H) ∈ B from he ▸ mem_top _)
  let : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective
    (f := inclusion hBM) (inclusion_injective hBM)
  have hh : B.map H.subtype = H ⊓ normalizer (L : Set G) := by
    rw [subgroupOf_map_subtype, inf_comm]
  rw [← hh]
  exact Group.isSolvable_of_surjective (H.subtype.subgroupMap_surjective B)

theorem ComponentSeed.paired_linear_overlap_solvable_of_model (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : ¬ (K.subgroupOf H).Normal)
    {f : ℕ} (hf : 0 < f)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) :
    Group.IsSolvable (H ⊓ normalizer (L : Set G) : Subgroup G) :=
  s.paired_binary_rankOne_overlap_solvable h p hc hs hn (.inl ⟨f,hf,hm⟩)

/-- Specialization to the original generation minimum. -/
theorem ComponentSeed.paired_linear_overlap_solvable (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : ¬ (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ ChapterE.generationParameter H)) :
    Group.IsSolvable (H ⊓ normalizer (L : Set G) : Subgroup G) := by
  have hf : 0 < ChapterE.generationParameter H := by
    have := degree_le_parameter h p hc hs
    have := S.nonbinary
    omega
  exact s.paired_linear_overlap_solvable_of_model h p hc hs hn hf hm

private theorem hall_and_outside_sylow_element {X : Type*} [Group X] [Finite X]
    (hsolv : Group.IsSolvable X) (P : Sylow 2 X) (N : Subgroup X) (hi : N.index = 2) :
    ∃ A : Subgroup X, IsHallSubgroup OddHall.oddPrimes A ∧
      ∃ t : P, (t : X) ∈ normalizer (A : Set X) ∧ (t : X) ∉ N := by
  let := hsolv
  let : N.Normal := normal_of_index_eq_two hi
  let _ : MulDistribMulAction Unit X := {
    smul _ x := x
    one_smul _ := rfl
    mul_smul _ _ _ := rfl
    smul_one _ := rfl
    smul_mul _ _ _ := rfl }
  obtain ⟨A,hA,_⟩ := exists_isHallSubgroup_isInvariant
    (A := Unit) hsolv (by simp) OddHall.oddPrimes
  have htwo : IsPGroup 2 (X ⧸ N) := IsPGroup.of_card (n := 1) (by
    simpa only [pow_one, index_eq_card] using hi)
  have hAN := hall_le_normal_of_two_quotient N A htwo hA
  have hn : ¬ (⊤ : Subgroup X) ≤ N := by
    intro hn
    have he := top_unique hn
    simp only [he, index_top] at hi
    omega
  obtain ⟨u,_,hu⟩ := SetLike.not_le_iff_exists.mp hn
  have hAu : A.map (MulAut.conj u).toMonoidHom ≤ N := by
    rintro _ ⟨a,ha,rfl⟩
    exact (inferInstance : N.Normal).conj_mem a (hAN ha) u
  obtain ⟨n,hn⟩ := exists_conj_eq_of_isHallSubgroup_of_solvable
    (inferInstance : Group.IsSolvable N) (hA.subgroupOf hAN)
    ((hA.map_conj u).subgroupOf hAu)
  have he : A.map (MulAut.conj u).toMonoidHom =
      A.map (MulAut.conj (n : X)).toMonoidHom := by
    have hh := congrArg (map N.subtype) hn
    rw [map_subgroupOf_eq_of_le hAu, map_map] at hh
    have hcomp : N.subtype.comp (MulAut.conj n).toMonoidHom =
        (MulAut.conj (n : X)).toMonoidHom.comp N.subtype := rfl
    rw [hcomp, ← map_map, map_subgroupOf_eq_of_le hAN] at hh
    exact hh
  let v := (n : X)⁻¹ * u
  have hvA : v ∈ normalizer (A : Set X) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change A.map (MulAut.conj v).toMonoidHom = A
    have hh := congrArg (map (MulAut.conj (n : X)⁻¹).toMonoidHom) he
    simp only [map_map] at hh
    have hleft : (MulAut.conj (n : X)⁻¹).toMonoidHom.comp (MulAut.conj u).toMonoidHom =
        (MulAut.conj v).toMonoidHom := by ext x; simp [v,mul_assoc]
    have hright : (MulAut.conj (n : X)⁻¹).toMonoidHom.comp
        (MulAut.conj (n : X)).toMonoidHom = MonoidHom.id X := by
      ext x
      simp [mul_assoc]
    simpa only [hleft,hright,map_id] using hh
  have hvN : v ∉ N := by
    intro hv
    exact hu (by simpa only [v,mul_inv_cancel_left] using N.mul_mem n.property hv)
  let C := normalizer (A : Set X)
  have hiC : (N.subgroupOf C).index = 2 := by
    have hd := relIndex_dvd_index_of_normal N C
    rw [hi] at hd
    apply (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left
    intro hone
    exact hvN (relIndex_eq_one.mp hone hvA)
  let Q : Sylow 2 C := Classical.choice inferInstance
  have hQN : ¬ (Q : Subgroup C) ≤ N.subgroupOf C := by
    intro hle
    have hd := index_dvd_of_le hle
    rw [hiC] at hd
    exact Q.not_dvd_index hd
  obtain ⟨w,hw,hwN⟩ := SetLike.not_le_iff_exists.mp hQN
  obtain ⟨U,hU⟩ := (Q.isPGroup'.map C.subtype).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq X U P
  have hg' : (U : Subgroup X).map (MulAut.conj g).toMonoidHom = (P : Subgroup X) := by
    exact congrArg (fun R : Sylow 2 X => (R : Subgroup X)) hg
  let t : X := g * (w : X) * g⁻¹
  have htP : t ∈ (P : Subgroup X) := by
    rw [←hg']
    exact mem_map_of_mem _ (hU (mem_map_of_mem C.subtype hw))
  refine ⟨A.map (MulAut.conj g).toMonoidHom,hA.map_conj g,⟨t,htP⟩,?_,?_⟩
  · exact A.le_normalizer_map (MulAut.conj g).toMonoidHom (mem_map_of_mem _ w.property)
  · intro htN
    apply hwN
    have hh := (inferInstance : N.Normal).conj_mem t htN g⁻¹
    change (w : X) ∈ N
    simpa [t,mul_assoc] using hh

/-- Construct the original Hall subgroup and its Sylow exchange element from
solvability of the actual overlap; no particular component model is required. -/
theorem ComponentSeed.paired_hall_exchange_of_solvable (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : ¬ (K.subgroupOf H).Normal)
    (hsolv : Group.IsSolvable (H ⊓ normalizer (L : Set G) : Subgroup G)) :
    ∃ A : Subgroup G, A ≤ H ⊓ normalizer (L : Set G) ∧
      IsHallSubgroup OddHall.oddPrimes (A.subgroupOf (H ⊓ normalizer (L : Set G))) ∧
      Odd (Nat.card A) ∧ ∃ t : T, (t : G) ∈ normalizer (A : Set G) ∧
        (t : G) ∉ normalizer (K : Set G) ∧
        Disjoint (A ⊓ K) ((A ⊓ K).map (MulAut.conj (t : G)).toMonoidHom) := by
  let B := H ⊓ normalizer (L : Set G)
  have hTB : (T : Subgroup G) ≤ B := le_inf h.outside.1.1.2 D.sylow_normalizes_component
  have hTN : ¬ (T : Subgroup G) ≤ normalizer (K : Set G) := by
    intro hh
    apply hn
    apply (normal_subgroupOf_iff_le_normalizer s.component.1).mpr
    rw [← s.supplement]
    exact sup_le K.le_normalizer hh
  obtain ⟨u,hu,huN⟩ := SetLike.not_le_iff_exists.mp hTN
  have hiH : (normalizer (K : Set G)).relIndex H = 2 := by
    change ((normalizer (K : Set G)).subgroupOf H).index = 2
    rw [subgroupOf_normalizer_eq s.component.1]
    exact s.paired_normalizer_index h p hc hs hn
  have hiB : ((normalizer (K : Set G)).subgroupOf B).index = 2 := by
    have hle := relIndex_le_of_le_right (H := normalizer (K : Set G))
      (show B ≤ H from inf_le_left) (by omega : (normalizer (K : Set G)).relIndex H ≠ 0)
    have hne : (normalizer (K : Set G)).relIndex B ≠ 1 :=
      fun he => huN (relIndex_eq_one.mp he (hTB hu))
    have hpos : (normalizer (K : Set G)).relIndex B ≠ 0 := index_ne_zero_of_finite
    change (normalizer (K : Set G)).relIndex B = 2
    omega
  obtain ⟨A,hA,t,htA,htK⟩ := hall_and_outside_sylow_element
    hsolv (T.subtype hTB)
    ((normalizer (K : Set G)).subgroupOf B) hiB
  let A' := A.map B.subtype
  have hAB : A' ≤ B := map_subtype_le _
  have hHall : IsHallSubgroup OddHall.oddPrimes (A'.subgroupOf B) := by
    simpa only [A',subgroupOf,comap_map_eq_self_of_injective B.subtype_injective] using hA
  have hodd : Odd (Nat.card A') := by
    rw [show Nat.card A' = Nat.card A from card_map_of_injective B.subtype_injective]
    exact OddHall.odd_hall_odd hA
  let t' : T := ⟨(t : B),t.property⟩
  have ht'A : (t' : G) ∈ normalizer (A' : Set G) :=
    A.le_normalizer_map B.subtype (mem_map_of_mem B.subtype htA)
  exact ⟨A',hAB,hHall,hodd,t',ht'A,htK,
    s.paired_odd_factors_disjoint h p hc hs A' hodd t' (h.outside.1.1.2 t'.property) htK⟩

theorem ComponentSeed.paired_linear_hall_exchange_of_model (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : ¬ (K.subgroupOf H).Normal)
    {f : ℕ} (hf : 0 < f)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) :
    ∃ A : Subgroup G, A ≤ H ⊓ normalizer (L : Set G) ∧
      IsHallSubgroup OddHall.oddPrimes (A.subgroupOf (H ⊓ normalizer (L : Set G))) ∧
      Odd (Nat.card A) ∧ ∃ t : T, (t : G) ∈ normalizer (A : Set G) ∧
        (t : G) ∉ normalizer (K : Set G) ∧
        Disjoint (A ⊓ K) ((A ⊓ K).map (MulAut.conj (t : G)).toMonoidHom) :=
  s.paired_hall_exchange_of_solvable h p hc hs hn
    (s.paired_linear_overlap_solvable_of_model h p hc hs hn hf hm)

/-- Specialization to the original generation minimum. -/
theorem ComponentSeed.paired_linear_hall_exchange (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : ¬ (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ ChapterE.generationParameter H)) :
    ∃ A : Subgroup G, A ≤ H ⊓ normalizer (L : Set G) ∧
      IsHallSubgroup OddHall.oddPrimes (A.subgroupOf (H ⊓ normalizer (L : Set G))) ∧
      Odd (Nat.card A) ∧ ∃ t : T, (t : G) ∈ normalizer (A : Set G) ∧
        (t : G) ∉ normalizer (K : Set G) ∧
        Disjoint (A ⊓ K) ((A ⊓ K).map (MulAut.conj (t : G)).toMonoidHom) := by
  have hf : 0 < ChapterE.generationParameter H := by
    have := degree_le_parameter h p hc hs
    have := S.nonbinary
    omega
  exact s.paired_linear_hall_exchange_of_model h p hc hs hn hf hm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent

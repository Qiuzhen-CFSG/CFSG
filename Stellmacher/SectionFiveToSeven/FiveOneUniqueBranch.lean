module

public import Stellmacher.SectionFiveToSeven.FiveOneMaximalLocal
public import Stellmacher.SectionFiveToSeven.PFamilyConjugation
public import Stellmacher.SectionFiveToSeven.PFamilyOmegaCentralizer
public import Stellmacher.SectionThree.LemmaThreeTwo

/-!
# The unique-maximal branch of Stellmacher (5.1)

Suppose the fixed Sylow 2-subgroup `S0` lies in a unique maximal 2-local
subgroup `M`. The consecutive-maxima package supplies subgroups `S≤S0` and
`N` with the normalizer, Sylow, and stability properties required by the
source. Section 3.2 then gives a local-family member `P` outside `M`: otherwise
all members over `N` would lie over `M`, and the Section 3 generation formula,
together with the Sylow Frattini factorization, would force `N≤M`.

The 2-group normalizer condition provides `x∈N_{S0}(S)∖S` whose square lies
in `S`. Set `P2=P^x`. Conjugation preserves membership in the local family and
keeps `P2` outside `M`. If `O₂(P⊔P2)` were nontrivial, its normalizer would be
an outside 2-local subgroup in which `S` is Sylow; the element `x` lies in
both that normalizer and `S0`, contradicting `x∉S`. Thus the joined 2-core is
trivial.

The normalizer and centralizer bounds in `FiveOneMaximalLocalData` rule out
normality of `J(S)` and `Ω₁(Z(S))` in either family member, and its exact
two-local stability field is preserved in alternative (c), while its (c3)
specialization supplies the endpoint equality. This proves the source's full
alternative (c) without adding hypotheses to `FiveOneConditions`.

Source: the proof of Stellmacher (5.1), journal p. 27 / lines 1088--1118 of
`refs/latex/stellmacher-n-group.tex`. The scan's relation is
`P(N,S) ⊄ P(M,S)`, which is the noncontainment used to choose `P`.
-/

open scoped Pointwise

namespace Stellmacher.SectionsFiveToSeven

universe u

variable {H : Type u} [Group H] [Finite H]

private theorem twoPrimeResidualSubgroup_characteristic
    (U : Subgroup H) : (twoPrimeResidualSubgroup U).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro e
  unfold twoPrimeResidualSubgroup
  rw [Subgroup.map_iSup]
  apply le_antisymm
  · exact iSup_le fun P =>
      le_iSup (fun Q : Sylow 2 U => (Q : Subgroup U))
        (P.mapSurjective e.surjective)
  · refine iSup_le fun Q => ?_
    obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective
      (f := e.toMonoidHom) e.surjective 2 Q
    rw [← hP]
    exact le_iSup (fun R : Sylow 2 U =>
      (R : Subgroup U).map e.toMonoidHom) P

private theorem twoPrimeResidualSubgroup_normal
    (U : Subgroup H) : (twoPrimeResidualSubgroup U).Normal := by
  let _ : (twoPrimeResidualSubgroup U).Characteristic :=
    twoPrimeResidualSubgroup_characteristic U
  exact Subgroup.normal_of_characteristic _

omit [Finite H] in
private theorem sylow_le_twoPrimeResidualSubgroup
    (U : Subgroup H) (S : Sylow 2 U) :
    (S : Subgroup U) ≤ twoPrimeResidualSubgroup U := by
  unfold twoPrimeResidualSubgroup
  exact le_iSup (fun T : Sylow 2 U ↦ (T : Subgroup U)) S

private theorem exists_normalizer_factor
    (U S : Subgroup H) (hSylow : IsSylowSubgroupIn S U) :
    ∃ N : Subgroup H,
      S ≤ N ∧ N ≤ U ∧ N ≤ Subgroup.normalizer (S : Set H) ∧
        U ≤ twoPrimeResidualAmbient U ⊔ N := by
  obtain ⟨T, hTmap⟩ := hSylow
  let R : Subgroup U := twoPrimeResidualSubgroup U
  let _ : R.Normal := twoPrimeResidualSubgroup_normal U
  let N0 : Subgroup U := Subgroup.normalizer ((T : Subgroup U) : Set U)
  let N : Subgroup H := N0.map U.subtype
  have hTR : (T : Subgroup U) ≤ R := sylow_le_twoPrimeResidualSubgroup U T
  have hfrattini : N0 ⊔ R = ⊤ := Sylow.normalizer_sup_eq_top' T hTR
  have hmapped := congrArg (fun K : Subgroup U ↦ K.map U.subtype) hfrattini
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmapped
  refine ⟨N, ?_, Subgroup.map_subtype_le N0, ?_, ?_⟩
  · rw [← hTmap]
    exact Subgroup.map_mono (Subgroup.le_normalizer (H := (T : Subgroup U)))
  · apply (Subgroup.le_normalizer_map U.subtype).trans
    simp [hTmap]
  · calc
      U = N ⊔ R.map U.subtype := by simpa [N] using hmapped.symm
      _ ≤ twoPrimeResidualAmbient U ⊔ N := sup_le le_sup_right (by
        simp [R, twoPrimeResidualAmbient])

omit [Finite H] in
private theorem map_conj_eq_self_of_mem_normalizer
    (S : Subgroup H) (x : H)
    (hx : x ∈ Subgroup.normalizer (S : Set H)) :
    S.map (MulAut.conj x).toMonoidHom = S :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp hx

omit [Finite H] in
private theorem normalizer_le_normalizer_J (S : Subgroup H) :
    Subgroup.normalizer (S : Set H) ≤
      Subgroup.normalizer (elementaryAbelianMaxJ S : Set H) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hS := map_conj_eq_self_of_mem_normalizer S x hx
  have hJ := elementaryAbelianMaxJ_map_equiv (MulAut.conj x) S
  rw [hS] at hJ
  exact hJ.symm

private theorem exists_normalizer_element
    (S0 : Sylow 2 H) (S : Subgroup H)
    (hSle : S ≤ (S0 : Subgroup H)) (hSne : S ≠ (S0 : Subgroup H)) :
    ∃ x : H, x ∈ (S0 : Subgroup H) ∧
      x ∈ Subgroup.normalizer (S : Set H) ∧ x ∉ S ∧ x ^ 2 ∈ S := by
  let A : Subgroup S0 := S.subgroupOf (S0 : Subgroup H)
  have hAproper : A < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hSne
    exact le_antisymm hSle (Subgroup.subgroupOf_eq_top.mp htop)
  let _ : Group.IsNilpotent S0 := S0.isPGroup'.isNilpotent
  have hAlt : A < Subgroup.normalizer A :=
    Group.normalizerCondition_of_isNilpotent A hAproper
  let N : Subgroup S0 := Subgroup.normalizer A
  let AN : Subgroup N := A.subgroupOf N
  let _ : AN.Normal := inferInstance
  have hANne : AN ≠ ⊤ := by
    intro htop
    have hNA : N ≤ A := Subgroup.subgroupOf_eq_top.mp htop
    exact (not_le_of_gt hAlt) hNA
  let Q := N ⧸ AN
  let : Nontrivial Q := not_subsingleton_iff_nontrivial.mp (by
    intro hsub
    exact hANne ((QuotientGroup.subsingleton_iff (N := AN)).mp hsub))
  have hNp : IsPGroup 2 N := S0.isPGroup'.to_subgroup N
  have hQp : IsPGroup 2 Q := hNp.to_quotient AN
  obtain ⟨n, hnpos, hcard⟩ := hQp.nontrivial_iff_card.mp inferInstance
  have htwo_dvd : 2 ∣ Nat.card Q := by
    rw [hcard]
    exact dvd_pow_self 2 (Nat.ne_of_gt hnpos)
  obtain ⟨q, hqord⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2 htwo_dvd
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective AN q
  have hxnotA : (x : S0) ∉ A := by
    intro hxA
    have hqone : QuotientGroup.mk' AN x = 1 :=
      (QuotientGroup.eq_one_iff x).mpr hxA
    have : orderOf (QuotientGroup.mk' AN x) = 1 :=
      orderOf_eq_one_iff.mpr hqone
    omega
  have hxsqA : (x : S0) ^ 2 ∈ A := by
    have hxAN : x ^ 2 ∈ AN := by
      apply (QuotientGroup.eq_one_iff (x ^ 2)).mp
      change (QuotientGroup.mk' AN x) ^ 2 = 1
      calc
        (QuotientGroup.mk' AN x) ^ 2 =
            (QuotientGroup.mk' AN x) ^ orderOf (QuotientGroup.mk' AN x) :=
          congrArg (fun n : ℕ => (QuotientGroup.mk' AN x) ^ n) hqord.symm
        _ = 1 := pow_orderOf_eq_one _
    exact hxAN
  refine ⟨(x : H), x.1.property, ?_, ?_, ?_⟩
  · have hxN : (x : S0) ∈
        (Subgroup.normalizer (S : Set H)).subgroupOf (S0 : Subgroup H) := by
      rw [Subgroup.subgroupOf_normalizer_eq hSle]
      exact x.property
    exact hxN
  · exact hxnotA
  · exact hxsqA

omit [Finite H] in
private theorem twoCoreIn_isPGroup (P : Subgroup H) :
    IsPGroup 2 (twoCoreIn P) :=
  (pCore_isPGroup (p := 2) (G := P)).map P.subtype

omit [Finite H] in
private theorem twoCoreIn_normal_subgroupOf (P : Subgroup H) :
    ((twoCoreIn P).subgroupOf P).Normal := by
  rw [← Subgroup.comap_subtype, twoCoreIn,
    Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
  exact (inferInstance : (pCore 2 P).Normal)

omit [Finite H] in
private theorem le_normalizer_twoCoreIn (P : Subgroup H) :
    P ≤ Subgroup.normalizer (twoCoreIn P : Set H) := by
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer
    (Subgroup.map_subtype_le (pCore 2 P))).mp
      (twoCoreIn_normal_subgroupOf P)

omit [Finite H] in
private theorem twoCoreIn_map_equiv
    (e : H ≃* H) (P : Subgroup H) :
    twoCoreIn (P.map e.toMonoidHom) =
      (twoCoreIn P).map e.toMonoidHom := by
  let eP : P ≃* P.map e.toMonoidHom :=
    P.equivMapOfInjective e.toMonoidHom e.injective
  have hcore : (pCore 2 P).map eP.toMonoidHom =
      pCore 2 (P.map e.toMonoidHom) := pCore_map_iso 2 eP
  unfold twoCoreIn
  rw [← hcore, Subgroup.map_map, Subgroup.map_map]
  congr 1

omit [Finite H] in
private theorem normalIn_imp_le_normalizer
    (A P : Subgroup H) (h : NormalIn A P) :
    P ≤ Subgroup.normalizer (A : Set H) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer h.1).mp h.2

omit [Finite H] in
private theorem pSubgroup_eq_of_sylowTwoIn
    (S K X : Subgroup H) (hSylow : IsSylowTwoIn S K)
    (hXK : X ≤ K) (hSX : S ≤ X) (hXp : IsPGroup 2 X) : X = S := by
  obtain ⟨-, T, hTmap⟩ := hSylow
  let XK : Subgroup K := X.subgroupOf K
  have hXKp : IsPGroup 2 XK :=
    hXp.of_equiv (Subgroup.subgroupOfEquivOfLe hXK).symm
  have hTX : (T : Subgroup K) ≤ XK := by
    apply Subgroup.map_subtype_le_map_subtype.mp
    rw [hTmap, Subgroup.map_subgroupOf_eq_of_le hXK]
    exact hSX
  have hXeq : XK = (T : Subgroup K) := T.is_maximal' hXKp hTX
  calc
    X = XK.map K.subtype := (Subgroup.map_subgroupOf_eq_of_le hXK).symm
    _ = (T : Subgroup K).map K.subtype := congrArg (fun Y => Y.map K.subtype) hXeq
    _ = S := hTmap

omit [Finite H] in
private theorem conjugate_not_le
    (M P : Subgroup H) (x : H) (hxM : x ∈ M) (hP : ¬ P ≤ M) :
    ¬ conjugateBy P x ≤ M := by
  intro hconj
  apply hP
  intro p hp
  have hxp : x * p * x⁻¹ ∈ conjugateBy P x := by
    exact ⟨p, hp, rfl⟩
  have : x * p * x⁻¹ ∈ M := hconj hxp
  have hxi : x⁻¹ ∈ M := M.inv_mem hxM
  have := M.mul_mem (M.mul_mem hxi this) hxM
  simpa [mul_assoc] using this

omit [Finite H] in
private theorem double_conjugate_eq
    (P S : Subgroup H) (x : H) (hSP : S ≤ P) (hx2 : x ^ 2 ∈ S) :
    (conjugateBy P x).map (MulAut.conj x).toMonoidHom = P := by
  have hx2P : x * x ∈ P := hSP (by simpa [pow_two] using hx2)
  have hx2norm : x * x ∈ Subgroup.normalizer (P : Set H) :=
    Subgroup.le_normalizer hx2P
  unfold conjugateBy
  rw [Subgroup.map_map]
  have hcomp : (MulAut.conj x).toMonoidHom.comp
      (MulAut.conj x).toMonoidHom =
      (MulAut.conj (x * x)).toMonoidHom := by
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  rw [hcomp]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hx2norm

omit [Finite H] in
private theorem conjugator_normalizes_join
    (P S : Subgroup H) (x : H) (hSP : S ≤ P) (hx2 : x ^ 2 ∈ S) :
    x ∈ Subgroup.normalizer ((P ⊔ conjugateBy P x : Subgroup H) : Set H) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup]
  change conjugateBy P x ⊔
      (conjugateBy P x).map (MulAut.conj x).toMonoidHom =
    P ⊔ conjugateBy P x
  rw [double_conjugate_eq P S x hSP hx2, sup_comm]

omit [Finite H] in
private theorem conjugator_normalizes_join_core
    (P S : Subgroup H) (x : H) (hSP : S ≤ P) (hx2 : x ^ 2 ∈ S) :
    x ∈ Subgroup.normalizer
      (twoCoreIn (P ⊔ conjugateBy P x) : Set H) := by
  let L : Subgroup H := P ⊔ conjugateBy P x
  have hxL : L.map (MulAut.conj x).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (conjugator_normalizes_join P S x hSP hx2)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hcore := twoCoreIn_map_equiv (MulAut.conj x) L
  rw [hxL] at hcore
  exact hcore.symm

private theorem pSet_escape
    (S0 : Sylow 2 H) (h : HypothesisOne H S0) (M : Subgroup H)
    (d : FiveOneMaximalLocalData S0 M) :
    ∃ P : Subgroup H,
      P ∈ PFamily (⊤ : Subgroup H) d.S ∧ ¬ P ≤ M := by
  have hSp : IsPGroup 2 d.S := S0.isPGroup'.to_le d.S_le_S0
  let hthree : SectionThree.Hypotheses H d.S :=
    { even_order := h.even_order
      nontrivial_two_subgroup := ⟨d.S_nontrivial, hSp⟩ }
  have hres := SectionThree.lemma_three_two d.S hthree d.N d.N_mem_LSet
  by_contra hnone
  push Not at hnone
  have hfamily : SectionThree.PSet d.N d.S ⊆ SectionThree.PSet M d.S := by
    intro P hP
    have hPle : P ≤ M := hnone P
      ((pFamily_iff_pSet (⊤ : Subgroup H) d.S P).2
        ⟨⟨le_top, hP.1.2.1, hP.1.2.2.1, hP.1.2.2.2⟩, hP.2⟩)
    exact ⟨⟨hPle, hP.1.2.1, hP.1.2.2.1, hP.1.2.2.2⟩, hP.2⟩
  have hresM : twoPrimeResidualAmbient d.N ≤ M := by
    rw [hres]
    refine iSup_le fun P ↦ ?_
    exact (hfamily P.property).1.1
  obtain ⟨N0, -, -, hN0norm, hfactor⟩ :=
    exists_normalizer_factor d.N d.S d.N_mem_LSet.2.1
  have hN0M : N0 ≤ M :=
    hN0norm.trans (normalizer_le_normalizer_J d.S) |>.trans d.normalizer_J_le_M
  exact d.N_not_le_M (hfactor.trans (sup_le hresM hN0M))

private theorem unique_branch_of_maximalLocalData
    (S0 : Sylow 2 H) (h : HypothesisOne H S0) (M : Subgroup H)
    (hM : UniqueMaximalTwoLocalContaining (S0 : Subgroup H) M)
    (d : FiveOneMaximalLocalData S0 M) :
    ∃ S P1 P2 : Subgroup H, FiveOneConditions H S0 S P1 P2 := by
  obtain ⟨P, hPmem, hPnot⟩ := pSet_escape S0 h M d
  obtain ⟨x, hxS0, hxnormS, hxnotS, hx2⟩ :=
    exists_normalizer_element S0 d.S d.S_le_S0 d.S_ne_S0
  let P2 : Subgroup H := conjugateBy P x
  have hP2mem : P2 ∈ PFamily (⊤ : Subgroup H) d.S :=
    (conjugateBy_mem_pFamily_iff d.S P x hxnormS).2 hPmem
  have hxM : x ∈ M := hM.1.2 hxS0
  have hP2not : ¬ P2 ≤ M := conjugate_not_le M P x hxM hPnot
  have hSP : d.S ≤ P := hPmem.1.2.1.1
  have hSP2 : d.S ≤ P2 := hP2mem.1.2.1.1
  have hcoreP : twoCoreIn P ≠ ⊥ := hPmem.1.2.2.1
  have hcoreP2 : twoCoreIn P2 ≠ ⊥ := hP2mem.1.2.2.1
  have hPN : P ≤ Subgroup.normalizer (twoCoreIn P : Set H) :=
    le_normalizer_twoCoreIn P
  have hP2N : P2 ≤ Subgroup.normalizer (twoCoreIn P2 : Set H) :=
    le_normalizer_twoCoreIn P2
  have hSylowP : IsSylowTwoIn d.S
      (Subgroup.normalizer (twoCoreIn P : Set H)) := by
    apply d.sylow_of_twoLocal_not_le_M
    · exact ⟨twoCoreIn P, hcoreP, twoCoreIn_isPGroup P, rfl⟩
    · intro hle
      exact hPnot (hPN.trans hle)
    · exact hSP.trans hPN
  have hSylowP2 : IsSylowTwoIn d.S
      (Subgroup.normalizer (twoCoreIn P2 : Set H)) := by
    apply d.sylow_of_twoLocal_not_le_M
    · exact ⟨twoCoreIn P2, hcoreP2, twoCoreIn_isPGroup P2, rfl⟩
    · intro hle
      exact hP2not (hP2N.trans hle)
    · exact hSP2.trans hP2N
  have hjoinCore : twoCoreIn (P ⊔ P2) = ⊥ := by
    by_contra hne
    let K : Subgroup H :=
      Subgroup.normalizer (twoCoreIn (P ⊔ P2) : Set H)
    have hjoinK : P ⊔ P2 ≤ K := le_normalizer_twoCoreIn (P ⊔ P2)
    have hKlocal : IsTwoLocal K :=
      ⟨twoCoreIn (P ⊔ P2), hne, twoCoreIn_isPGroup (P ⊔ P2), rfl⟩
    have hKnot : ¬ K ≤ M := by
      intro hKM
      exact hPnot (le_sup_left.trans (hjoinK.trans hKM))
    have hSK : d.S ≤ K := hSP.trans (le_sup_left.trans hjoinK)
    have hSylowK := d.sylow_of_twoLocal_not_le_M K hKlocal hKnot hSK
    let X : Subgroup H := (S0 : Subgroup H) ⊓ K
    have hXK : X ≤ K := inf_le_right
    have hSX : d.S ≤ X := le_inf d.S_le_S0 hSK
    have hXp : IsPGroup 2 X := S0.isPGroup'.to_le inf_le_left
    have hXS : X = d.S := pSubgroup_eq_of_sylowTwoIn d.S K X hSylowK hXK hSX hXp
    have hxK : x ∈ K :=
      conjugator_normalizes_join_core P d.S x hSP hx2
    have hxX : x ∈ X := ⟨hxS0, hxK⟩
    exact hxnotS (hXS ▸ hxX)
  have hnormalOmegaP : ¬ NormalIn (omegaOneCenter d.S) P := by
    intro hnormal
    exact hPnot ((normalInOmega_imp_le_centralizer d.S P hPmem hnormal).trans
      d.centralizer_omega_le_M)
  have hnormalOmegaP2 : ¬ NormalIn (omegaOneCenter d.S) P2 := by
    intro hnormal
    exact hP2not ((normalInOmega_imp_le_centralizer d.S P2 hP2mem hnormal).trans
      d.centralizer_omega_le_M)
  have hnormalJP : ¬ NormalIn (elementaryAbelianMaxJ d.S) P := by
    intro hnormal
    exact hPnot ((normalIn_imp_le_normalizer _ _ hnormal).trans d.normalizer_J_le_M)
  have hnormalJP2 : ¬ NormalIn (elementaryAbelianMaxJ d.S) P2 := by
    intro hnormal
    exact hP2not ((normalIn_imp_le_normalizer _ _ hnormal).trans d.normalizer_J_le_M)
  refine ⟨d.S, P, P2, d.S_nontrivial, d.S_le_S0, hPmem, hP2mem,
    hjoinCore, FiveOneAlternative.c M hM d.S_ne_S0
      hnormalOmegaP hnormalOmegaP2 hnormalJP hnormalJP2
      hPnot hP2not hSylowP hSylowP2 d.j_stable_of_twoLocal_not_le_M ?_⟩
  intro T hJT hTS0 P1 P2 hP1 hP2 hcore
  by_cases hle : P1 ⊔ P2 ≤ M
  · exact Or.inl hle
  · exact Or.inr (d.c3_stable T hJT hTS0 P1 P2 hP1 hP2 hcore hle)

/-! The public wrapper obtains the source-selected maximal-local data and
applies the checked construction above. -/

/-- Alternative (c) of Stellmacher (5.1) when `S0` lies in a unique maximal
2-local subgroup. -/
public theorem five_one_unique_branch
    (S0 : Sylow 2 H) (h : HypothesisOne H S0)
    (M : Subgroup H)
    (hM : UniqueMaximalTwoLocalContaining (S0 : Subgroup H) M) :
    ∃ S P1 P2 : Subgroup H, FiveOneConditions H S0 S P1 P2 := by
  obtain ⟨d⟩ := exists_fiveOneMaximalLocalData S0 h M hM
  exact unique_branch_of_maximalLocalData S0 h M hM d

end Stellmacher.SectionsFiveToSeven

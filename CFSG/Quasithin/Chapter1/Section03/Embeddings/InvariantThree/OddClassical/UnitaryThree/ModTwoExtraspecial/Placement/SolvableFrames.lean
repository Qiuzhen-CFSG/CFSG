module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.UnitaryThree.ModTwoExtraspecial.Placement.Frames
public import Theory.SpecificGroups.SL3.SplitMonomial.SolvableNormal
public import Theory.SpecificGroups.SL3.SplitMonomial.AbelianBasis

/-!
# A frame or a small Sylow two-subgroup in the solvable unitary case

Embed the special-unitary subgroup faithfully in SL₃ over the same field.
If there is a noncentral abelian normal subgroup, Clifford theory gives an
invariant line basis unless its restriction is irreducible. In that latter
case the determinant argument for an involution in its normalizer makes every
two-subgroup trivial. If no such abelian normal subgroup exists, Fitting
self-centralization supplies a nonabelian normal three-subgroup. Its normalizer
has two-subgroups of order at most eight, by the abelian index-three weight
stabilizer and normalizer-orbit bounds.

The nonabelian three-subgroup in the hypothesis gives absolute irreducibility;
it need not be normal or have order 27. All normal subgroups used in the
argument are normal relative to the given overgroup. The embedding in SL₃
retains every scalar, so the argument applies unchanged to projective preimages.
Finally, the inverse coordinate map of the invariant basis gives an actual
matrix whose column lines are preserved over the original field.

Source: GLS3, proof of Theorem 6.5.3(a)–(d), especially (6.5.1),
`refs/KGroup/GLS3/chapter6.tex`; Aschbacher–Smith, proof of Proposition 1.3.4,
printed p.511 (PDF p.528 of `refs/quasithin.pdf`). This is the Fitting version
of the solvable reduction; orthogonalization is a separate step.
-/

public section

open Subgroup Matrix Representation BenderSuzuki.MatrixGroups
open scoped Pointwise IsMulCommutative

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.UnitaryThree.ModTwoExtraspecial.Placement
variable {E : Type*} [Field E]

private theorem invariantBasis_or_small_two_subgroups [Finite E]
    {p : ℕ} [Fact p.Prime] [CharP E p] (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (H : Subgroup (SpecialLinearGroup (Fin 3) E)) (hs : Group.IsSolvable H)
    (hU : ∃ U : Subgroup (SpecialLinearGroup (Fin 3) E),
      U ≤ H ∧ IsPGroup 3 U ∧ ¬ IsMulCommutative U) :
    SL3.SplitMonomial.HasInvariantBasis H ∨
      ∀ P : Subgroup (SpecialLinearGroup (Fin 3) E),
        IsPGroup 2 P → P ≤ H → Nat.card P ≤ 8 := by
  classical
  have h2 : (2 : E) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime E Nat.prime_two hp2
  by_cases hA : SL3.SplitMonomial.HasNoncentralAbelianNormal H
  · obtain ⟨A, hAH, hAn, hAc, hAnc⟩ := hA
    let : IsMulCommutative A := hAc
    by_cases hi : IsIrreducible ((specialLinearNatural (k := E) 3).comp A.subtype)
    · right
      intro P hP hPH
      let : IsIrreducible ((specialLinearNatural (k := E) 3).comp A.subtype) := hi
      by_contra hlarge
      obtain ⟨n, hn⟩ := hP.exists_card_eq
      have hn0 : n ≠ 0 := by
        intro he
        simp only [he, pow_zero] at hn
        omega
      have hd : 2 ∣ Nat.card P := hn ▸ dvd_pow_self 2 hn0
      obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 hd
      have ht2 : (t : SpecialLinearGroup (Fin 3) E) ^ 2 = 1 := by
        have hh : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
        exact congrArg Subtype.val hh
      have he : t = 1 := Subtype.ext
        (SL3.SplitMonomial.AbelianBasis.involution_eq_one_of_normalizes_irreducible_abelian
          h2 A t.val ht2
          (((normal_subgroupOf_iff_le_normalizer hAH).mp hAn) (hPH t.property)))
      simp [he] at ht
    · left
      let : IsAbsolutelyIrreducible ((specialLinearNatural (k := E) 3).comp H.subtype) :=
        SL3.SplitMonomial.natural_isAbsolutelyIrreducible_of_nonabelian_three_subgroup hp3 H hU
      exact SL3.SplitMonomial.hasInvariantBasis_of_reducible_normal H A hAH hAn hAnc
        (IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible _) hi
  · have hn : ¬ IsMulCommutative H := by
      intro hc
      let := hc
      obtain ⟨U, hUH, _, hUn⟩ := hU
      apply hUn
      refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
      exact congrArg (fun x : H => x.val)
        (mul_comm (⟨a.val, hUH a.property⟩ : H) ⟨b.val, hUH b.property⟩)
    obtain ⟨Q, hQH, hQn, hQ, hQna⟩ :=
      SL3.SplitMonomial.exists_nonabelian_normal_three_of_not_hasNoncentralAbelianNormal
        H hs hn hA
    right
    intro P hP hPH
    exact SL3.SplitMonomial.two_subgroup_card_le_eight_of_odd_weight_kernels p hp3.symm Q hQ hQna
      (SL3.SplitMonomial.odd_card_weightCentralizer_normalizer hp3.symm Q hQ hQna)
      P hP (hPH.trans ((normal_subgroupOf_iff_le_normalizer hQH).mp hQn))


private def toSL (J : HermitianForm 3 E) : J.specialSubgroup →* SpecialLinearGroup (Fin 3) E where
  toFun a := ⟨a.val.val, congrArg Units.val ((J.mem_specialSubgroup_iff a.val).mp a.property).2⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

private theorem toSL_injective (J : HermitianForm 3 E) : Function.Injective (toSL J) := by
  intro a b h
  exact Subtype.ext (Units.ext (congrArg Subtype.val h))

private theorem hasFrame_of_invariantBasis (J : HermitianForm 3 E)
    (H : Subgroup J.specialSubgroup)
    (h : SL3.SplitMonomial.HasInvariantBasis (H.map (toSL J))) : HasFrame H := by
  classical
  obtain ⟨b, hb⟩ := h
  let e := Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv E (Fin 3 → E))
  let C : GL (Fin 3) E := e.symm b.equivFun.symm
  have hCv (v : Fin 3 → E) : C • v = b.equivFun.symm v := by
    exact congrArg (fun f : (Fin 3 → E) ≃ₗ[E] (Fin 3 → E) => f v)
      (e.apply_symm_apply b.equivFun.symm)
  have hCsingle (i : Fin 3) (a : E) : C • Pi.single i a = a • b i := by
    rw [hCv]
    apply b.equivFun.injective
    rw [b.equivFun.apply_symm_apply]
    ext j
    simp [Pi.single_apply, Finsupp.single_apply, eq_comm]
  have hmem (v : Fin 3 → E) :
      v ∈ C • HermitianForm.OddThreeLocal.Monomial.coordinateVectors (E := E) ↔
        ∃ (i : Fin 3) (a : E), a ≠ 0 ∧ v = a • b i := by
    constructor
    · rintro ⟨w, ⟨i, hi, hw⟩, rfl⟩
      have heq : w = Pi.single i (w i) := by
        ext j
        by_cases hj : j = i
        · subst j; simp
        · simp [hj, hw j hj]
      refine ⟨i, w i, hi, ?_⟩
      change C • w = (w i) • b i
      exact (congrArg (fun v : Fin 3 → E => C • v) heq).trans (hCsingle i (w i))
    · rintro ⟨i, a, ha, rfl⟩
      exact ⟨Pi.single i a,
        HermitianForm.OddThreeLocal.Monomial.single_mem_coordinateVectors i ha, hCsingle i a⟩
  have hforward (g : J.specialSubgroup) (hg : g ∈ H) :
      (g : GL (Fin 3) E) • (C • HermitianForm.OddThreeLocal.Monomial.coordinateVectors (E := E)) ⊆
        C • HermitianForm.OddThreeLocal.Monomial.coordinateVectors (E := E) := by
    apply Set.smul_set_subset_iff.mpr
    intro v hv
    obtain ⟨i, a, ha, rfl⟩ := (hmem v).mp hv
    obtain ⟨j, c, hc, hg⟩ := hb (toSL J g) (mem_map_of_mem (toSL J) hg) i
    apply (hmem _).mpr
    refine ⟨j, a * c, mul_ne_zero ha hc, ?_⟩
    change (toSL J g) • (a • b i) = _
    rw [smul_comm (toSL J g) a, hg, smul_smul]
  refine ⟨C, fun g hg => Set.Subset.antisymm (hforward g hg) ?_⟩
  rw [Set.subset_smul_set_iff]
  exact hforward g⁻¹ (H.inv_mem hg)


/-- A solvable source subgroup preserves an actual three-line frame over E,
or each of its Sylow two-subgroups has order at most eight. The proof uses the
cross-characteristic determinant-one action; the additional source hypotheses
are retained in the public interface. -/
theorem frame_or_small_sylow {p : ℕ} (hp : p.Prime) (_hpodd : Odd p)
    (hp3 : 3 < p) (_hpmod : p % 3 = 2) [Finite E] (J : HermitianForm 3 E)
    (hE : Nat.card E = p ^ 2) (_hconj : ∀ x, J.conj x = x ^ p)
    (H : Subgroup J.specialSubgroup) (hH : Group.IsSolvable H)
    (_hprimes : ∀ r : ℕ, r.Prime → r ∣ Nat.card H → r = 2 ∨ r = 3)
    (hU : ∃ U : Subgroup J.specialSubgroup,
      U ≤ H ∧ IsPGroup 3 U ∧ ¬ IsMulCommutative U) :
    HasFrame H ∨ ∀ T : Sylow 2 H, Nat.card T ≤ 8 := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype E := Fintype.ofFinite E
  let : CharP E p := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hE)
  let K := H.map (toSL J)
  let eH := H.equivMapOfInjective (toSL J) (toSL_injective J)
  have hsK : Group.IsSolvable K := by
    let := hH
    exact Group.isSolvable_of_surjective (f := eH.toMonoidHom) eH.surjective
  have hUK : ∃ U : Subgroup (SpecialLinearGroup (Fin 3) E),
      U ≤ K ∧ IsPGroup 3 U ∧ ¬ IsMulCommutative U := by
    obtain ⟨U, hUH, hU, hn⟩ := hU
    refine ⟨U.map (toSL J), map_mono hUH, hU.map (toSL J), ?_⟩
    intro hc
    let := hc
    let eU := U.equivMapOfInjective (toSL J) (toSL_injective J)
    apply hn
    refine ⟨⟨fun a b => eU.injective ?_⟩⟩
    simp only [map_mul, mul_comm]
  rcases invariantBasis_or_small_two_subgroups
      (ne_of_gt (lt_trans (by decide : 2 < 3) hp3)) (ne_of_gt hp3) K hsK hUK with h | h
  · exact Or.inl (hasFrame_of_invariantBasis J H h)
  · right
    intro T
    let f := (toSL J).comp H.subtype
    have hf : Function.Injective f := (toSL_injective J).comp H.subtype_injective
    have hTK : (T : Subgroup H).map f ≤ K := by
      rintro _ ⟨x, _, rfl⟩
      exact mem_map_of_mem (toSL J) x.property
    have hsmall := h ((T : Subgroup H).map f) (T.isPGroup'.map f) hTK
    rwa [card_map_of_injective hf] at hsmall

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.UnitaryThree.ModTwoExtraspecial.Placement

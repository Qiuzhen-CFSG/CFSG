module

public import Theory.SpecificGroups.PSL2.SemilinearCoverage.MatrixBasics

/-!
# Root coordinates for automorphisms of binary SL₂

An automorphism preserving the upper root group induces an additive equivalence
of the coefficient field. Agreement on this root group and on the Weyl matrix
determines an automorphism, by generation by upper and lower transvections.
Thus multiplicativity of the root coordinates suffices to identify a normalized
automorphism with the actual entrywise field action.

These are elementary reductions toward GLS, Volume 4, Chapter 4, Lemma 3.1(a)
and the automorphism classification used in Lemma 3.4(c). They do not assert that
an arbitrary automorphism can be normalized or that its coordinates preserve
multiplication.

Adapted from the corresponding module under
`BenderSuzuki/ZD/Recognition/MinimalReduction/LocalEmbedding/BenderAutomorphisms/Linear/`.
The Theory consumer is GLS2, Chapter G, the automorphism paragraph before
Theorem 26.24, Step 5 (`refs/KGroup/GLS2/ChapterG.tex`).
-/

namespace Theory.PSL2.SemilinearCoverage

variable {K : Type*} [Field K]

/-- The upper-right entry of the image of an upper transvection. -/
@[expose] public def rootParameter (a : MulAut (SL2 K)) (t : K) : K :=
  (a (uni t)).val 0 1

public theorem map_uni_of_preserves_root (a : MulAut (SL2 K))
    (hU : (Unip K).map a.toMonoidHom = Unip K) (t : K) :
    a (uni t) = uni (rootParameter a t) := by
  have hm : a (uni t) ∈ (Unip K).map a.toMonoidHom :=
    ⟨uni t, (mem_Unip_iff _).mpr ⟨t, rfl⟩, rfl⟩
  rw [hU] at hm
  obtain ⟨s, hs⟩ := (mem_Unip_iff _).mp hm
  have hp : rootParameter a t = s := by simp [rootParameter, hs]
  rw [hp]
  exact hs

public theorem rootParameter_add (a : MulAut (SL2 K))
    (hU : (Unip K).map a.toMonoidHom = Unip K) (s t : K) :
    rootParameter a (s + t) = rootParameter a s + rootParameter a t := by
  apply uni_injective
  rw [← map_uni_of_preserves_root a hU, ← uni_mul_uni, map_mul,
    map_uni_of_preserves_root a hU, map_uni_of_preserves_root a hU, uni_mul_uni]

public theorem rootParameter_bijective (a : MulAut (SL2 K))
    (hU : (Unip K).map a.toMonoidHom = Unip K) :
    Function.Bijective (rootParameter a) := by
  constructor
  · intro s t h
    apply uni_injective
    apply a.injective
    rw [map_uni_of_preserves_root a hU, map_uni_of_preserves_root a hU, h]
  · intro t
    have ht : uni t ∈ (Unip K).map a.toMonoidHom := by
      rw [hU]
      exact (mem_Unip_iff _).mpr ⟨t, rfl⟩
    obtain ⟨g, hg, hgt⟩ := ht
    obtain ⟨s, rfl⟩ := (mem_Unip_iff _).mp hg
    refine ⟨s, ?_⟩
    apply uni_injective
    rw [← map_uni_of_preserves_root a hU]
    exact hgt

/-- The additive field coordinates of an automorphism preserving the upper root group. -/
@[expose] public noncomputable def rootParameterEquiv (a : MulAut (SL2 K))
    (hU : (Unip K).map a.toMonoidHom = Unip K) : K ≃+ K :=
  { Equiv.ofBijective (rootParameter a) (rootParameter_bijective a hU) with
    map_add' := rootParameter_add a hU }

public theorem rootParameterEquiv_apply (a : MulAut (SL2 K))
    (hU : (Unip K).map a.toMonoidHom = Unip K) (t : K) :
    rootParameterEquiv a hU t = rootParameter a t := rfl

section CharTwo
variable [CharP K 2]

public theorem lower_transvection_eq_weyl_uni (t : K) :
    Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) one_ne_zero t =
      weyl K * uni t * weyl K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- The upper root group and the Weyl involution determine an SL₂ homomorphism. -/
public theorem sl2_hom_ext_root_weyl {G : Type*} [_root_.Group G] (a b : SL2 K →* G)
    (hU : ∀ t : K, a (uni t) = b (uni t)) (hw : a (weyl K) = b (weyl K)) : a = b := by
  ext g
  apply Matrix.SL2.transvection_induction (fun g => a g = b g)
  · intro i j hij t
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hU t
    · rw [lower_transvection_eq_weyl_uni]
      simp only [map_mul, hw, hU]
    · exact (hij rfl).elim
  · intro x y hx hy
    simp only [map_mul, hx, hy]

omit [CharP K 2] in
public theorem sl2FieldAut_uni (σ : K ≃+* K) (t : K) :
    sl2FieldAut σ (uni t) = uni (σ t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2FieldAut]

public theorem sl2FieldAut_weyl (σ : K ≃+* K) :
    sl2FieldAut σ (weyl K) = weyl K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2FieldAut]

/-- The braid relation at parameter one forces normalized root coordinates to fix one. -/
public theorem rootParameter_one (a : MulAut (SL2 K))
    (hU : (Unip K).map a.toMonoidHom = Unip K) (hw : a (weyl K) = weyl K) :
    rootParameter a 1 = 1 := by
  have hbraid : uni (1 : K) * weyl K * uni 1 = weyl K * uni 1 * weyl K := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  have h := congrArg a hbraid
  simp only [map_mul, map_uni_of_preserves_root a hU, hw] at h
  have he := congrArg (fun g : SL2 K => g.val 1 1) h
  simpa [Matrix.mul_apply, Fin.sum_univ_two] using he

/-- Once the root coordinates preserve multiplication, the normalized automorphism
is the entrywise field action. This lemma does not assume semilinearity. -/
public theorem eq_sl2FieldAut_of_rootParameter_mul (a : MulAut (SL2 K))
    (hU : (Unip K).map a.toMonoidHom = Unip K) (hw : a (weyl K) = weyl K)
    (hmul : ∀ s t : K, rootParameter a (s * t) = rootParameter a s * rootParameter a t) :
    ∃ σ : K ≃+* K, a = sl2FieldAut σ := by
  let σ : K ≃+* K :=
    { rootParameterEquiv a hU with map_mul' := hmul }
  refine ⟨σ, ?_⟩
  apply MulEquiv.toMonoidHom_injective
  apply sl2_hom_ext_root_weyl
  · intro t
    change a (uni t) = sl2FieldAut σ (uni t)
    rw [map_uni_of_preserves_root a hU, sl2FieldAut_uni]
    rfl
  · change a (weyl K) = sl2FieldAut σ (weyl K)
    simpa only [sl2FieldAut_weyl] using hw

end CharTwo
end Theory.PSL2.SemilinearCoverage

module

public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# Residual normalizers from an intermediate kernel

For finite groups, if Oᵖ(P) is contained in K ≤ P, then Oᵖ(K) = Oᵖ(P),
with both residuals embedded in the ambient group. This follows from
p-perfectness of Oᵖ(P) and monotonicity. If K is a kernel in an overgroup Q,
its residual is normal in Q. A p-group image of P guarantees Oᵖ(P) ≤ K.

This is the group-theoretic reduction used for the endpoint single-node
parabolics in binary five-space. All normality assertions are relative.
Source application: Aschbacher–Smith, 13.8.25, combined manuscript of
1 March 2004, printed p.960 (PDF p.977).
-/

public section

namespace Subgroup
variable {G H : Type*} [Group G] [Group H] [Finite G]

/-- A finite residual is unchanged on passing to an intermediate subgroup. -/
theorem embedded_pResidual_eq_of_sandwich (p : ℕ) (K P : Subgroup G)
    (hKP : K ≤ P) (hRK : (pResidual p P).map P.subtype ≤ K) :
    (pResidual p K).map K.subtype = (pResidual p P).map P.subtype := by
  apply le_antisymm (embedded_pResidual_mono p hKP)
  let R := (pResidual p P).map P.subtype
  have hR : pResidual p R = ⊤ :=
    (pResidual_eq_top_iff p R).mpr (isPPerfect_embedded_pResidual p P)
  have h := embedded_pResidual_mono p hRK
  rw [hR, ← MonoidHom.range_eq_map, range_subtype] at h
  exact h

/-- An overgroup normalizing an intermediate subgroup also normalizes the residual. -/
theorem le_normalizer_embedded_pResidual_of_sandwich (p : ℕ) (K P Q : Subgroup G)
    (hKP : K ≤ P) (hRK : (pResidual p P).map P.subtype ≤ K)
    (hKQ : K ≤ Q) (hQN : Q ≤ normalizer K) :
    Q ≤ normalizer ((pResidual p P).map P.subtype) := by
  rw [← embedded_pResidual_eq_of_sandwich p K P hKP hRK]
  exact (normal_subgroupOf_iff_le_normalizer ((map_subtype_le _).trans hKQ)).mp
    (normal_embedded_pResidual_subgroupOf p hKQ
      ((normal_subgroupOf_iff_le_normalizer hKQ).mpr hQN))

omit [Finite G] in
/-- The p-residual is killed by any homomorphism with p-group range. -/
theorem pResidual_le_ker_of_range_isPGroup (p : ℕ) (f : G →* H)
    (hf : IsPGroup p f.range) : pResidual p G ≤ f.ker :=
  sInf_le ⟨inferInstance,
    hf.of_equiv (QuotientGroup.quotientKerEquivRange f).symm⟩

/-- A normal kernel contained in `P` controls its residual normalizer when
the restricted action has p-group image. Normality is relative to `Q`. -/
theorem le_normalizer_embedded_pResidual_of_kernel (p : ℕ) (P Q : Subgroup G)
    (hPQ : P ≤ Q) (f : Q →* H)
    (hKP : f.ker.map Q.subtype ≤ P)
    (hf : IsPGroup p (f.comp (inclusion hPQ)).range) :
    Q ≤ normalizer ((pResidual p P).map P.subtype) := by
  apply le_normalizer_embedded_pResidual_of_sandwich p (f.ker.map Q.subtype) P Q hKP
  · rintro x ⟨g, hg, rfl⟩
    exact mem_map.mpr ⟨inclusion hPQ g,
      pResidual_le_ker_of_range_isPGroup p (f.comp (inclusion hPQ)) hf hg, rfl⟩
  · exact map_subtype_le _
  · have hn := f.ker.le_normalizer_map Q.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hn
end Subgroup

end

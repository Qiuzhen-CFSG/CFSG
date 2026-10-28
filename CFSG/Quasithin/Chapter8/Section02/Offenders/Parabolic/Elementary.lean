module

public import CFSG.Quasithin.Chapter8.Section02.Offenders.FixedPoints
public import CFSG.Quasithin.ChapterE.Section02.Elementary

/-!
# Subgroup and rank deductions for the selected two-conjugate parabolic

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Proposition 8.2.2, printed pp.714–715
(PDF pp.731–732), and E.2.13–14, printed pp.224–228.

The source conjugate V^h is h⁻¹ V h, so the offender APIs receive h⁻¹.
Both the center and the two-core are computed inside I before embedding in G.
In particular the core need not be normal in G. Conjugation within I preserves
this core; relative-index transport then identifies the corank in V^h with
the rank of the literal image of V in I/O₂(I). The action-kernel identity gives
the rank of the induced automizer, and E.2.14(7)'s small-rank restriction gives
the strict action ratio. Abelianness of V and the centralizer bound on AB
supply the final fixed-subgroup containment.

The consumer `Parabolic.selected_pair_conclusions` applies these deductions
to the source A, B and Z. Neither the exceptional Aut(M22) exclusion nor the
classified E.2.4 witness is asserted here. Their source assembly must supply
the E.2 premises, the concrete quotient models, and the cyclic fixed points.
-/

public section
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic
open Subgroup Representation.BinaryOffender ChapterE
variable {G : Type*} [Group G]

/-- The centrality clause of 8.2.2(3), with the intrinsic center of I embedded
in the original group. Nontriviality of the intersection is a separate E.2.13(5)
deduction and is not needed for centrality. -/
theorem intersection_central (I V : Subgroup G) [IsElementaryAbelian 2 V]
    (h : G) (hgen : V ⊔ V.map (MulAut.conj h⁻¹).toMonoidHom = I) :
    V ⊓ V.map (MulAut.conj h⁻¹).toMonoidHom ≤ (center I).map I.subtype := by
  let W := V.map (MulAut.conj h⁻¹).toMonoidHom
  let _ : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hZI : V ⊓ W ≤ I := inf_le_left.trans (hgen ▸ le_sup_left)
  have hC : V ⊓ W ≤ centralizer (I : Set G) := by
    apply le_centralizer_iff.mpr
    rw [← hgen]
    exact sup_le_centralizer_inf_of_abelian V W
  intro z hz
  refine ⟨⟨z, hZI hz⟩, mem_center_iff.mpr ?_, rfl⟩
  intro x
  apply Subtype.ext
  exact hC hz x.val x.property

/-- The TI argument in 8.2.2(4). The right side is the ambient image of
N_I(V), not the full normalizer in G. -/
theorem relative_normalizer (I M V : Subgroup G) [IsElementaryAbelian 2 V]
    (h : G) (hgen : V ⊔ V.map (MulAut.conj h⁻¹).toMonoidHom = I)
    (hTI : ∀ x ∈ M, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj x).toMonoidHom = V)
    (hNV : normalizer (V : Set G) ≤ M)
    (hZ : V ⊓ V.map (MulAut.conj h⁻¹).toMonoidHom ≠ ⊥) :
    M ⊓ I = I ⊓ normalizer (V : Set G) := by
  simpa only [hgen, inf_comm M I] using ti_generated_pair_normalizer M V hTI hNV h⁻¹ hZ

/-- Conjugation by the source h inside I preserves its two-core. Thus the
corank of A in V^h is the corank of B in V, for the literal embedded core. -/
theorem conjugate_core_corank (I V : Subgroup G) (h : G) (hh : h ∈ I) :
    subgroupCorank (V.map (MulAut.conj h⁻¹).toMonoidHom)
      (V.map (MulAut.conj h⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype) =
      subgroupCorank V (V ⊓ (pCore 2 I).map I.subtype) := by
  let x : I := ⟨h, hh⟩
  have he : (MulAut.conj h⁻¹).toMonoidHom.comp I.subtype =
      I.subtype.comp (MulAut.conj x⁻¹).toMonoidHom := by ext; rfl
  have hi : (pCore 2 I).map (MulAut.conj x⁻¹).toMonoidHom = pCore 2 I :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top _))
  have hQ : ((pCore 2 I).map I.subtype).map (MulAut.conj h⁻¹).toMonoidHom =
      (pCore 2 I).map I.subtype := by
    rw [map_map, he, ← map_map, hi]
  rw [← hQ, ← map_inf _ _ _ (MulAut.conj h⁻¹).injective]
  unfold subgroupCorank
  rw [relIndex_map_map_of_injective _ _ (MulAut.conj h⁻¹).injective, hQ]

/-- The last step of 8.2.2(7). Since B lies in the abelian group V,
C_V(A) centralizes A join B. The earlier E.2 centralizer bound then places
C_V(A) in the embedded two-core of I. -/
theorem fixed_le_core_intersection (I V A : Subgroup G) [IsElementaryAbelian 2 V]
    (hVI : V ≤ I)
    (hC : I ⊓ centralizer (A ⊔ (V ⊓ (pCore 2 I).map I.subtype) : Subgroup G) ≤
      (pCore 2 I).map I.subtype) :
    V ⊓ centralizer (A : Set G) ≤ V ⊓ (pCore 2 I).map I.subtype := by
  have hCB : V ⊓ centralizer (A : Set G) ≤
      centralizer (V ⊓ (pCore 2 I).map I.subtype : Subgroup G) :=
    (inf_le_left.trans V.le_centralizer).trans (centralizer_le inf_le_left)
  have hCAB : V ⊓ centralizer (A : Set G) ≤
      centralizer (A ⊔ (V ⊓ (pCore 2 I).map I.subtype) : Subgroup G) := by
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp inf_le_right) (le_centralizer_iff.mp hCB)
  exact le_inf inf_le_left ((le_inf (inf_le_left.trans hVI) hCAB).trans hC)

/-- The binary rank of the actual image V* in I/O₂(I) is the corank of
V intersect O₂(I) in V. The quotient map and subgroup restriction are literal. -/
theorem quotient_rank_eq_core_corank (I V : Subgroup G) (hVI : V ≤ I) :
    rank ((V.subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))) =
      subgroupCorank V (V ⊓ (pCore 2 I).map I.subtype) := by
  have hQ : ((pCore 2 I).map I.subtype).subgroupOf I = pCore 2 I := by
    rw [subgroupOf, comap_map_eq_self_of_injective I.subtype_injective]
  unfold rank subgroupCorank
  rw [← relIndex_ker, QuotientGroup.ker_mk', ← hQ, relIndex_subgroupOf hVI,
    inf_relIndex_left, hQ]

/-- The rank identity in 8.2.2(7), from E.2.13(2)'s normalizer and kernel
identities and the model calculation m(V*) = k. This uses `intersection_corank`
with the inverse of the source conjugator. -/
theorem actor_rank [Finite G] (I V : Subgroup G) [IsElementaryAbelian 2 V]
    (h : G) (hh : h ∈ I) (hVI : V ≤ I) (k : ℕ)
    (hA : V.map (MulAut.conj h⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype =
      offenderNormalizer V h⁻¹)
    (hkernel : offenderNormalizer V h⁻¹ ⊓ centralizer (V : Set G) =
      V ⊓ V.map (MulAut.conj h⁻¹).toMonoidHom)
    (hquotient : rank ((V.subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))) = k) :
    rank (inducedAutomizer V (offenderNormalizer V h⁻¹)) =
      subgroupCorank V (V ⊓ V.map (MulAut.conj h⁻¹).toMonoidHom) - k := by
  rw [quotient_rank_eq_core_corank I V hVI] at hquotient
  have hc := conjugate_core_corank I V h hh
  rw [hA, hquotient] at hc
  have hr := intersection_corank V h⁻¹ hkernel
  omega

/-- The strict ratio in 8.2.2(7) from the numerical consequence of
E.2.14(7): an actor of rank at most 2k has rank exactly 2k. This premise is
available when the local quadratic ratio is greater than one. It forces
m(Abar) at least 2k; meanwhile Z lies in C_V(A), so the fixed codimension is
at most m(Abar) + k, strictly smaller than 2m(Abar). The conclusion concerns
the specified actor, not just the minimum cubic ratio. -/
theorem actor_ratio_lt_two [Finite G]
    (I V : Subgroup G) [IsElementaryAbelian 2 V]
    (h : G) (hh : h ∈ I) (hVI : V ≤ I) (k : ℕ) (hk : 0 < k)
    (hA : V.map (MulAut.conj h⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype =
      offenderNormalizer V h⁻¹)
    (hkernel : offenderNormalizer V h⁻¹ ⊓ centralizer (V : Set G) =
      V ⊓ V.map (MulAut.conj h⁻¹).toMonoidHom)
    (hquotient : rank ((V.subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))) = k)
    (hsmall : rank (inducedAutomizer V (offenderNormalizer V h⁻¹)) ≤ 2 * k →
      rank (inducedAutomizer V (offenderNormalizer V h⁻¹)) = 2 * k) :
    actionRatio (automizerRepresentation V) (inducedAutomizer V (offenderNormalizer V h⁻¹)) < 2 := by
  have hrank : 2 * k ≤ rank (inducedAutomizer V (offenderNormalizer V h⁻¹)) := by
    by_cases hs : rank (inducedAutomizer V (offenderNormalizer V h⁻¹)) ≤ 2 * k
    · rw [hsmall hs]
    · omega
  have hpos : 0 < rank (inducedAutomizer V (offenderNormalizer V h⁻¹)) := by omega
  rw [quotient_rank_eq_core_corank I V hVI] at hquotient
  have hc := conjugate_core_corank I V h hh
  rw [hA, hquotient] at hc
  have hr := intersection_corank V h⁻¹ hkernel
  have hadd := offender_corank_add (intersection_le_fixed V h⁻¹)
    (show V ⊓ centralizer (offenderNormalizer V h⁻¹ : Set G) ≤ V from inf_le_left)
  have hfixed : fixedCodim (automizerRepresentation V)
      (inducedAutomizer V (offenderNormalizer V h⁻¹)) <
        2 * rank (inducedAutomizer V (offenderNormalizer V h⁻¹)) := by
    rw [fixedCodim_inducedAutomizer V (offenderNormalizer V h⁻¹) inf_le_right]
    omega
  unfold actionRatio
  rw [ENNReal.div_lt_iff (Or.inl (by exact_mod_cast (Nat.ne_of_gt hpos)))
    (Or.inl (by simp))]
  exact_mod_cast hfixed

end CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic

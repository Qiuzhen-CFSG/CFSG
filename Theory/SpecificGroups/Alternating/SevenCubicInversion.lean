module
public import Theory.SpecificGroups.AlternatingSevenSylowNormalizer
public import Theory.GroupTheory.CubicSylowInversion
public import Theory.GroupTheory.SylowIndexThreeQuotient
public import Theory.GroupTheory.CoprimeProductIntersection

/-!
# Inverting specified cubics in seven-point Sylow overgroups

A cubic cannot normalize a full Sylow two-subgroup of A7: the established
seven-point normalizer calculation makes that Sylow self-normalizing.

Above an arbitrary two-group kernel, an index-three overgroup of the
specified Sylow therefore has nonnormal Sylow. Its three-coset action
identifies the quotient by its two-core with S3. The cubic lifting theorem
then inverts the original cubic from the original Sylow, without assuming
an involutory lift or a split extension.

Source: Aschbacher--Smith 5.1.13, printed p.637, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace AlternatingSeven

private theorem cubic_not_normalizes_sylow (S : Sylow 2 (alternatingGroup (Fin 7)))
    (D : Subgroup (alternatingGroup (Fin 7))) (hD : Nat.card D = 3) :
    ¬ D ≤ normalizer (S : Set (alternatingGroup (Fin 7))) := by
  rw [AlternatingSevenSylow.sylow_normalizer_eq_self]
  intro hn
  have hp : IsPGroup 3 D := IsPGroup.of_card (n := 1) (by simpa using hD)
  have hd : Disjoint D (S : Subgroup _) := hp.disjoint_of_coprime S.isPGroup' (by decide)
  have hb : D = ⊥ := le_bot_iff.mp ((le_inf le_rfl hn).trans hd.le_bot)
  simp [hb] at hD

/-- An order-three subgroup in an index-three Sylow overgroup above A7 is
inverted from the prescribed Sylow. The kernel may be any two-group. -/
theorem cubic_inverted_of_two_kernel {G : Type*} [Group G] [Finite G]
    (f : G →* alternatingGroup (Fin 7)) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (S : Sylow 2 G)
    (J D : Subgroup G) (hSJ : (S : Subgroup G) ≤ J) (hDJ : D ≤ J)
    (hJ : Nat.card J = 3 * Nat.card S) (hD : Nat.card D = 3) :
    ∃ t ∈ (S : Subgroup G), ∀ d ∈ D, t*d*t⁻¹ = d⁻¹ := by
  let SJ := S.subtype hSJ
  have hi : (SJ : Subgroup J).index = 3 := by
    have hh := (SJ : Subgroup J).card_mul_index
    have hc : Nat.card SJ = Nat.card S :=
      Nat.card_congr (subgroupOfEquivOfLe hSJ).toEquiv
    rw [hc,hJ] at hh
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (hh.trans (Nat.mul_comm _ _))
  have hp : pCore 2 J < (SJ : Subgroup J) := by
    refine lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal SJ) ?_
    intro he
    have hn : (SJ : Subgroup J).Normal := he ▸ inferInstance
    have hnorm : D ≤ normalizer (S : Set G) :=
      hDJ.trans ((normal_subgroupOf_iff_le_normalizer hSJ).mp hn)
    let Q := S.mapSurjective hf
    have hDn : D.map f ≤ normalizer (Q : Set (alternatingGroup (Fin 7))) :=
      (map_mono (f := f) hnorm).trans (le_normalizer_map f)
    have hinj : Function.Injective (f.comp D.subtype) := by
      apply (injective_iff_map_eq_one _).mpr
      intro x hx
      have hd : Disjoint D f.ker := by
        apply disjoint_of_coprime_natCard
        obtain ⟨k,hk⟩ := hk.exists_card_eq
        rw [hD,hk]
        exact (by decide : Nat.Coprime 3 2).pow_right k
      exact Subtype.ext (disjoint_def.mp hd x.property hx)
    have hDc : Nat.card (D.map f) = 3 := by
      rw [←range_subtype D,←MonoidHom.range_comp]
      exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans hD
    exact cubic_not_normalizes_sylow Q (D.map f) hDc hDn
  obtain ⟨e⟩ := sylow_index_three_core_quotient SJ hi hp
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqk : IsPGroup 2 q.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  obtain ⟨t,ht,hinv⟩ := cubic_inverted_in_sylow_of_two_kernel q hq hqk
    (D.subgroupOf J) (by rw [Nat.card_congr (subgroupOfEquivOfLe hDJ).toEquiv,hD]) SJ
  exact ⟨t,ht,fun d hd => congrArg Subtype.val (hinv ⟨d,hDJ hd⟩ hd)⟩

end AlternatingSeven

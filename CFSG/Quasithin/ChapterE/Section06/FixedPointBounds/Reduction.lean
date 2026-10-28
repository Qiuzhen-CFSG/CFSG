module

public import CFSG.Quasithin.ChapterB.Section06To07.Elementary
public import Theory.GroupTheory.PResidual.PrimeTo
public import Theory.GroupTheory.NormalFourCentralizerSeparation

/-!
# Sylow promotion and the minimal-parabolic reduction in E.6.27

Local Sylow maximality and control of the ambient normalizer promote a Sylow
subgroup of `M ∩ K` to a Sylow subgroup of `K`. The prime-to-two residual
contains this Sylow subgroup, so Frattini reduces containment of `K` in `M`
to containment of the residual. The checked normalizer-plus-parabolics
generation theorem gives that containment from its minimal parabolics.

The argument also covers a residual which is itself a two-group. In that
case the family of minimal parabolics can be empty, and its normalizer still
supplies the required generators. No assertion that the residual lies in
its Sylow subgroup is used.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), Proposition
E.6.27, printed p.257, and B.6.4--6, printed pp.112--113.
-/

public section

namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- The promotion in the first paragraph of E.6.27, with literal subgroup maps. -/
theorem exists_sylow_of_local_normalizer {K M : Subgroup G}
    (P : Sylow 2 ↥(M ⊓ K))
    (hN : normalizer ((P : Subgroup ↥(M ⊓ K)).map (M ⊓ K).subtype : Set G) ≤ M) :
    ∃ S : Sylow 2 K, (S : Subgroup K).map K.subtype =
      (P : Subgroup ↥(M ⊓ K)).map (M ⊓ K).subtype := by
  let Q := (P : Subgroup ↥(M ⊓ K)).map (M ⊓ K).subtype
  have hQ : IsPGroup 2 Q := P.isPGroup'.map _
  have hQK : Q ≤ K := (map_subtype_le _).trans inf_le_right
  have hi : Q.relIndex (M ⊓ K) = (P : Subgroup ↥(M ⊓ K)).index := by
    simpa only [← MonoidHom.range_eq_map, range_subtype, relIndex_top_right] using
      relIndex_map_map_of_injective (P : Subgroup ↥(M ⊓ K)) ⊤
        (M ⊓ K).subtype_injective
  have hindex := not_dvd_relIndex_of_normalizer_inf_le Q (M ⊓ K) K hQ hQK
    (hi ▸ P.not_dvd_index) (inf_le_inf_right K hN)
  exact ⟨(hQ.comap_subtype (K := K)).toSylow hindex,
    map_subgroupOf_eq_of_le hQK⟩

omit [Finite G] in
theorem sylow_le_primeToResidual {K : Subgroup G} (S : Sylow 2 K) :
    (S : Subgroup K) ≤ primeToResidual 2 K := by
  intro x hx
  obtain ⟨n, hn⟩ := S.isPGroup' ⟨x, hx⟩
  exact mem_primeToResidual_of_pow (congrArg Subtype.val hn)

/-- The residual's Sylow subgroup, retaining the original embedding. -/
@[expose] def residualSylow {K : Subgroup G} (S : Sylow 2 K) :
    Sylow 2 (primeToResidual 2 K) :=
  S.subtype (sylow_le_primeToResidual S)

omit [Finite G] in
theorem residualSylow_map {K : Subgroup G} (S : Sylow 2 K) :
    (residualSylow S : Subgroup (primeToResidual 2 K)).map
      (primeToResidual 2 K).subtype = (S : Subgroup K) :=
  map_subgroupOf_eq_of_le (sylow_le_primeToResidual S)

omit [Finite G] in
/-- Containment follows from all minimal parabolics and the Sylow normalizer.
The map may be any homomorphism, so the same proof handles nested residuals. -/
theorem range_le_of_minimalParabolics {X : Type*} [Group X] [Finite X]
    (f : X →* G) (S : Sylow 2 X) (M : Subgroup G)
    (hN : normalizer ((S : Subgroup X).map f : Set G) ≤ M)
    (hP : ∀ H : Subgroup X, ChapterB.IsMinimalParabolicOver S H → H.map f ≤ M) :
    f.range ≤ M := by
  have htop : (⊤ : Subgroup X) ≤ M.comap f := by
    rw [← ChapterB.minimalParabolics_sup_normalizer S]
    refine sup_le (sSup_le fun H hH => map_le_iff_le_comap.mp (hP H hH)) ?_
    exact map_le_iff_le_comap.mp ((le_normalizer_map f).trans hN)
  simpa only [← MonoidHom.range_eq_map] using map_le_iff_le_comap.mpr htop

/-- The second paragraph of E.6.27: it suffices to contain every minimal
parabolic of the actual `O^{2'}(K)`, with no assumption `O^{2'}(K) ≤ S`. -/
theorem le_of_residual_minimalParabolics {K M : Subgroup G} (S : Sylow 2 K)
    (hN : normalizer ((S : Subgroup K).map K.subtype : Set G) ≤ M)
    (hP : ∀ H : Subgroup (primeToResidual 2 K),
      ChapterB.IsMinimalParabolicOver (residualSylow S) H →
      (H.map (primeToResidual 2 K).subtype).map K.subtype ≤ M) : K ≤ M := by
  let R := primeToResidual 2 K
  have hR : R.map K.subtype ≤ M := by
    have hrange := range_le_of_minimalParabolics
      (K.subtype.comp R.subtype) (residualSylow S) M ?_ ?_
    · simpa only [MonoidHom.range_comp, range_subtype] using hrange
    · rw [← map_map, residualSylow_map]
      exact hN
    · intro H hH
      rw [← map_map]
      exact hP H hH
  have hfr := Sylow.normalizer_sup_eq_top' S (sylow_le_primeToResidual S)
  have htop : (⊤ : Subgroup K) ≤ M.comap K.subtype := by
    rw [← hfr]
    exact sup_le
      (map_le_iff_le_comap.mp ((le_normalizer_map K.subtype).trans hN))
      (map_le_iff_le_comap.mp hR)
  simpa only [← MonoidHom.range_eq_map, range_subtype] using map_le_iff_le_comap.mpr htop

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds

end

module

public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.WeakClosure.ConjugateSpan
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.WeakClosure.SmallLinear.ModelAction
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.WeakClosure.SmallLinear.RelativeSylow

/-!
# Universal inner placement for the PSL₂(4) conjugate family

For every conjugate of Ω₁(R) lying in T, each involution generator lies in
a conjugate K′ of K = C_G(L). If K′ = K its placement is immediate.
Otherwise extend its cyclic subgroup to a Sylow subgroup of K′ ∩ N_G(K)
and conjugate that Sylow into T through N_G(K) = N_G(L). The universal
earlier-source exclusion 16.4.6 applies to this newly arranged setup.
The actual PSL₂(4) ≃ A₅ ≃ PSL₂(5) comparison makes the resulting action
inner. Since N_G(L) normalizes KL, conjugation back gives the required
placement in the original coordinates. Generation then gives the whole
conjugate omega subgroup.

The established placement feeds the conjugate-family span theorem and hence
weak closure. Source 16.4.6 is retained as an explicit earlier-source input
for all applicable conjugate configurations; placement, a span identity and
weak closure are conclusions, not inputs.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Proposition
16.5.1, printed p.1194, using Lemma 16.4.6, printed pp.1184–1186.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.WeakClosure.SmallLinear
open Subgroup GorensteinWalter

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {z g : G} {L R : Subgroup G}

/-- Apply the universal exclusion in an arranged relative Sylow and transport
the inner-action preimage back through N_G(L). The case K′ = K is separate. -/
theorem involution_mem_inner_join_of_conjugate
    (h : StandardSetup T z L) (e : L ≃* PSL2 (ZMod 5))
    (hex : FiveOuterPGLExclusion T z L) {b r : G}
    (hrK : r ∈ (centralizer (L : Set G)).conjBy b) (hrT : r ∈ T)
    (hr2 : orderOf r = 2) : r ∈ centralizer (L : Set G) ⊔ L := by
  by_cases hb : (centralizer (L : Set G)).conjBy b = centralizer (L : Set G)
  · exact (le_sup_left : centralizer (L : Set G) ≤ centralizer (L : Set G) ⊔ L)
      (hb ▸ hrK)
  obtain ⟨c, hc, S, hS, hrS⟩ :=
    exists_intersectionSetup_containing_involution h hb hrK hrT hr2
  have hrc2 : (MulAut.conj c r) ^ 2 = 1 := by
    rw [← map_pow, ← hr2, pow_orderOf_eq_one, map_one]
  have hrΩ : MulAut.conj c r ∈ omegaOneAmbient S :=
    (omegaOneAmbient_le_iff S (omegaOneAmbient S)).mp le_rfl _ hrS hrc2
  have hrJ := omega_le_inner_join hS e hex hrΩ
  have hcL : c ∈ normalizer (L : Set G) := h.normalizers_eq ▸ hc
  have hfix : (centralizer (L : Set G) ⊔ L).conjBy c = centralizer (L : Set G) ⊔ L := by
    change (centralizer (L : Set G) ⊔ L).map (MulAut.conj c).toMonoidHom = _
    rw [Subgroup.map_sup]
    exact congrArg₂ (· ⊔ ·) (mem_normalizer_iff_map_conj_eq.mp hc)
      (mem_normalizer_iff_map_conj_eq.mp hcL)
  exact ((mem_normalizer_iff.mp (mem_normalizer_iff_map_conj_eq.mpr hfix)) r).mpr hrJ

/-- Every ambient conjugate of Ω₁(R) contained in T acts inner on the actual
PSL₂(4) component. No elementary-abelian assumption on Ω₁(R) is needed. -/
theorem inner_placement (h : IntersectionSetup T z L g R)
    (hZ : center L = ⊥) (hmodel : ClassicalGroup.IsPSL (L ⧸ center L) 2 4)
    (hex : FiveOuterPGLExclusion T z L) :
    ∀ a : G, (omegaOneAmbient R).conjBy a ≤ (T : Subgroup G) →
      (omegaOneAmbient R).conjBy a ≤ centralizer (L : Set G) ⊔ L := by
  obtain ⟨e⟩ := exists_five_equiv hZ hmodel
  intro a ha
  change (omegaOneAmbient R).map (MulAut.conj a).toMonoidHom ≤ _
  rw [map_le_iff_le_comap]
  apply (omegaOneAmbient_le_iff _ _).mpr
  intro r hr hr2
  change MulAut.conj a r ∈ centralizer (L : Set G) ⊔ L
  by_cases hr1 : r = 1
  · simpa only [hr1, map_one] using (centralizer (L : Set G) ⊔ L).one_mem
  apply involution_mem_inner_join_of_conjugate h.toStandardSetup e hex (b := a * g)
  · have hm : MulAut.conj a r ∈ ((centralizer (L : Set G)).conjBy g).conjBy a :=
      mem_map_of_mem _ (h.sylow.le hr).1
    simpa only [conjBy_conjBy] using hm
  · exact ha (mem_map_of_mem _
      ((omegaOneAmbient_le_iff R (omegaOneAmbient R)).mp le_rfl r hr hr2))
  · rw [(MulAut.conj a).orderOf_eq]
    exact orderOf_eq_prime hr2 hr1

/-- The source span identity in the small linear branch, with the universal
placement premise discharged from the earlier outer-PGL exclusion. -/
theorem space_eq_conjugate_span (h : IntersectionSetup T z L g R)
    (hZ : center L = ⊥) (hmodel : ClassicalGroup.IsPSL (L ⧸ center L) 2 4)
    (d : LocalAction T L R 2) (hconj : R = (commutingSylow T L).conjBy g)
    (hfaith : Disjoint R (centralizer (L : Set G)))
    (hex : FiveOuterPGLExclusion T z L) :
    benderSpace T L = SubgroupFamily.span (conjugateFamily (omegaOneAmbient R)) T :=
  space_eq_conjugate_span_of_inner_placement h.toStandardSetup hZ d hconj hfaith
    (inner_placement h hZ hmodel hex)

/-- Weak closure of V in T in the small linear branch. -/
theorem space_weakly_closed (h : IntersectionSetup T z L g R)
    (hZ : center L = ⊥) (hmodel : ClassicalGroup.IsPSL (L ⧸ center L) 2 4)
    (d : LocalAction T L R 2) (hconj : R = (commutingSylow T L).conjBy g)
    (hfaith : Disjoint R (centralizer (L : Set G)))
    (hex : FiveOuterPGLExclusion T z L)
    (a : G) (ha : (benderSpace T L).conjBy a ≤ (T : Subgroup G)) :
    (benderSpace T L).conjBy a = benderSpace T L :=
  space_weakly_closed_of_inner_placement h.toStandardSetup hZ d hconj hfaith
    (inner_placement h hZ hmodel hex) a ha

end CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.WeakClosure.SmallLinear

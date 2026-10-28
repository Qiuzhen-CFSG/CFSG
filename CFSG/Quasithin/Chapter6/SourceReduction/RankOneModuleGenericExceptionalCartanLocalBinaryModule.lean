module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryOmega
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalRecognition

/-!
# Original module recognition and minus torus at binary triality

The original ambient input selects a noncentral constituent. Outside
omega-centralization kills its fixed space. If its Sylow orbit is larger,
the proved moved-constituent theorem gives degree two. Otherwise Chapter K
supplies actual natural or Hermitian coordinates on that orbit. The original
centralizing cubic excludes the natural row; its fixation of a nonzero
Sylow-fixed Hermitian vector forces odd half-degree. No invariance or model
is supplied as a premise.

Consequently the original degree is two modulo four. The roots of order
dividing 2^(n/2)+1 in the original cyclic Cartan form the actual minus torus.
It contains the same escaping cubic and fixes a nonidentity omega-point.
The original cubic inverter in the original containing component inverts
this torus modulo the same Sylow. The original reduced subgroup W, both
Hall conditions and all two-core quotient kernels remain unchanged.

This excludes the degrees divisible by four in the binary-triality row.
It does not place the minus torus in the containing component or exclude
the remaining degrees. Those ambient steps and the other containing rows
are still needed for the original local Cartan sieve.

Source: Aschbacher--Smith 5.1.3 and 5.1.13, printed pp.630--631,635--638,
with the genuine constituent classification of Chapter K (`refs/quasithin.pdf`).
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Representation Stellmacher
open scoped MatrixGroups
open Representation.OrthogonalFourMinus
local instance (s : ℕ) : Algebra (ZMod 2) (FiniteModel.fixedField s) := ZMod.algebra _ 2
local instance (s : ℕ) [NeZero s] : Module (ZMod 2) (FiniteModel.Space s) :=
  Module.compHom (FiniteModel.Space s) (algebraMap (ZMod 2) (FiniteModel.fixedField s))
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
open Chapter12.Section02

private theorem fixed_chosen_seed
    {T : Sylow 2 G} {L W V H : Subgroup G} {n : ℕ}
    (D : ChosenModule T L V) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHC : H ≤ omegaCentralizer T) : V ⊓ centralizer (L : Set G) = ⊥ := by
  have hz := h.centralOmega_disjoint_of_outside_centralizes hH hHC
  have hw : RankOneModule.wholeReduced T L ⊓ centralizer (L : Set G) = ⊥ :=
    Subgroup.inf_centralizer_eq_bot_of_omega_disjoint T L _
      RankOneModule.wholeReduced_mem.2.1 RankOneModule.wholeReduced_le_sylow
      (le_sup_right.trans RankOneModule.wholeReduced_normalized) h.sylow_normalizes hz
  exact bot_unique ((inf_le_inf_right _ D.le_reduced).trans_eq hw)

/-- A centralizing original cubic gives actual Hermitian coordinates at every
left degree greater than two, without a constituent-invariance assumption. -/
theorem hermitian_subgroup_of_centralizing_cubic
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hHC : H ≤ omegaCentralizer T)
    (hDA : D ≤ A) (hDc : Nat.card D = 3) (hDC : D ≤ omegaCentralizer T)
    (hn : n ≠ 2) :
    ∃ (U : Subgroup G) (s : ℕ) (hs : 0 < s),
      letI : NeZero s := ⟨hs.ne'⟩;
      n = 2*s ∧ Odd s ∧ IsElementaryAbelian 2 U ∧ U ≤ (T : Subgroup G) ∧
      (T : Subgroup G) ≤ normalizer (U : Set G) ∧ U ≠ ⊥ ∧
      IsConjugationModel L U (SL2.BinarySmall.hermitian s) := by
  obtain ⟨V,⟨a⟩⟩ := h.original_section1221.exists_chosen_of_normalizes h.sylow_normalizes
  have hc := fixed_chosen_seed a h hH hHC
  have hv : a.sourceOrbit = V := by
    by_contra he
    exact hn (a.localCartan_degree_two_of_moved_seed h hc
      (lt_of_le_of_ne (le_componentOrbit V T) (fun hh => he (a.sourceOrbit_eq.trans hh.symm))))
  rcases a.localCartan_invariant_seed_models h hc hv with hm | ⟨s,he,hs,hm⟩
  · exact (not_natural_of_cubic_centralizes_omega
      (inferInstance : IsElementaryAbelian 2 a.sourceOrbit)
      a.sourceOrbit_weakClosure_setup.le_sylow a.sourceOrbit_weakClosure_setup.normalizes
      a.sourceOrbit_weakClosure_setup.nontrivial
      (hDA.trans (c.left_le.trans inf_le_left)) hDc hDC hm).elim
  · let : NeZero s := ⟨hs.ne'⟩
    have ho := (hermitian_omega_torus s h.sylow_normalizes
      (inferInstance : IsElementaryAbelian 2 a.sourceOrbit)
      a.sourceOrbit_weakClosure_setup.le_sylow a.sourceOrbit_weakClosure_setup.normalizes
      a.sourceOrbit_weakClosure_setup.nontrivial (hDA.trans c.left_le) hDc hDC hm).1
    exact ⟨a.sourceOrbit,s,hs,he,ho,inferInstance,a.sourceOrbit_weakClosure_setup.le_sylow,
      a.sourceOrbit_weakClosure_setup.normalizes,a.sourceOrbit_weakClosure_setup.nontrivial,hm⟩

/-- The original left degree is twice an odd number. -/
theorem odd_half_degree_of_centralizing_cubic
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hHC : H ≤ omegaCentralizer T)
    (hDA : D ≤ A) (hDc : Nat.card D = 3) (hDC : D ≤ omegaCentralizer T) :
    n = 2*(n/2) ∧ Odd (n/2) := by
  by_cases hn : n = 2
  · subst n
    norm_num
  · obtain ⟨U,s,hs,he,ho,_⟩ :=
      hermitian_subgroup_of_centralizing_cubic h hH c hHC hDA hDc hDC hn
    have hh : n/2=s := by omega
    exact ⟨by omega,hh ▸ ho⟩

private theorem elementary_omega_point
    {T : Sylow 2 G} {U : Subgroup G}
    (hU : IsElementaryAbelian 2 U) (hUT : U ≤ (T : Subgroup G))
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G)) (hU0 : U ≠ ⊥) :
    ∃ z : G, z ∈ U ∧ z ∈ omegaOneCenterAmbient (T : Subgroup G) ∧ z ≠ 1 := by
  obtain ⟨z,hz1⟩ := ne_bot_iff_exists_ne_one.mp
    (inf_centerIn_ne_bot T.isPGroup' hU0 hUT hTU)
  let := hU
  exact ⟨z,z.property.1,(mem_omegaOneCenterAmbient_iff _ _).mpr
    ⟨hUT z.property.1,elemPow_eq_one_of_isElementaryAbelian (p:=2) (z:G) z.property.1,
      z.property.2.2⟩,fun he => hz1 (Subtype.ext he)⟩

/-- Construct the actual minus torus, a nonidentity omega-point it fixes,
and inversion modulo the original Sylow by the specified original inverter.
There is no exceptional-component or module-model assumption. -/
theorem minus_torus_of_centralizing_inverted_cubic
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hHC : H ≤ omegaCentralizer T)
    (hDA : D ≤ A) (hDc : Nat.card D = 3) (hDC : D ≤ omegaCentralizer T)
    {t : G} (ht : t ∈ (T : Subgroup G)) (hi : ∀ d ∈ D, t*d*t⁻¹=d⁻¹) :
    n = 2*(n/2) ∧ Odd (n/2) ∧
      ∃ (E : Subgroup G) (z : G), E ≤ A ∧ D ≤ E ∧ Nat.card E = 2^(n/2)+1 ∧
        (∀ x : G, x ∈ E ↔ x ∈ A ∧ x^(2^(n/2)+1)=1) ∧
        z ∈ omegaOneCenterAmbient (T : Subgroup G) ∧ z ≠ 1 ∧
        E ≤ centralizer ({z} : Set G) ∧
        ∀ x ∈ E, t*x*t⁻¹*x ∈ (T : Subgroup G) := by
  obtain ⟨hn,ho⟩ := odd_half_degree_of_centralizing_cubic h hH c hHC hDA hDc hDC
  have hl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^(2*(n/2))) := hn ▸ h.linear
  obtain ⟨E,hEA,hEc,hroot⟩ := c.exists_minus_torus h.sylow_normalizes hl
  have h3 : 3 ∣ 2^(n/2)+1 := by
    apply Nat.dvd_of_mod_eq_zero
    have hp := Nat.BinaryTorusParity.two_pow_mod_three (n/2)
    rw [Nat.odd_iff.mp ho] at hp
    norm_num at hp
    omega
  have hDE : D ≤ E := by
    intro x hx
    refine (hroot x).mpr ⟨hDA hx,?_⟩
    apply orderOf_dvd_iff_pow_eq_one.mp
    apply (orderOf_dvd_of_pow_eq_one (show x^3=1 from ?_)).trans h3
    rw [←hDc]
    exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨x,hx⟩ : D)))
  have hinv := c.inverts_minus_torus_mod_sylow h.sylow_normalizes hl ho hDA hDc ht hi hEA hEc
  have hpoint : ∃ z : G, z ∈ omegaOneCenterAmbient (T : Subgroup G) ∧ z ≠ 1 ∧
      E ≤ centralizer ({z} : Set G) := by
    by_cases htwo : n = 2
    · have hED : E = D := (eq_of_le_of_card_ge hDE (by rw [hEc,hDc,htwo]; decide)).symm
      obtain ⟨z,_,hz,hz1⟩ := elementary_omega_point h.reduced.2.1 h.reduced_le_sylow
        (le_sup_right.trans (reduced_normalizes h.reduced))
        (fun he => h.noncentral (by rw [he,commutator_bot_left]))
      exact ⟨z,hz,hz1,hED ▸ (hDC.trans (centralizer_le (Set.singleton_subset_iff.mpr hz)))⟩
    · obtain ⟨U,s,hs,he,_,hU,hUT,hTU,hU0,hm⟩ :=
        hermitian_subgroup_of_centralizing_cubic h hH c hHC hDA hDc hDC htwo
      let : NeZero s := ⟨hs.ne'⟩
      have hh : n/2=s := by omega
      obtain ⟨z,hzU,hz,hz1⟩ := elementary_omega_point hU hUT hTU hU0
      refine ⟨z,hz,hz1,?_⟩
      intro x hx
      have hp := (hroot x).mp hx |>.2
      rw [hh] at hp
      exact hermitian_minus_root_fixes_omega_intersection s h.sylow_normalizes hm
        (c.left_le (hEA hx)) hp hzU hz
  obtain ⟨z,hz,hz1,hEz⟩ := hpoint
  exact ⟨hn,ho,E,z,hEA,hDE,hEc,hroot,hz,hz1,hEz,hinv⟩

namespace BinaryOmega
/-- The binary-triality escape has original degree congruent to two modulo
four. Its SAME escaping cubic and inverter lie in the constructed minus
torus and containing component, respectively; the torus fixes an actual
nonidentity omega-point. The full two-core is retained. -/
theorem original_inverted_minus_torus
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    n % 4 = 2 ∧
      ∃ (D E : Subgroup G) (t z : G),
        D ≤ A ∧ D ≤ C.map Y.subtype ∧ Nat.card D = 3 ∧
        ¬ D ≤ normalizer (residual H : Set G) ∧
        t ∈ (T : Subgroup G) ⊓ C.map Y.subtype ∧ t ∉ L ∧
        (∀ d ∈ D, t*d*t⁻¹=d⁻¹) ∧
        E ≤ A ∧ D ≤ E ∧ Nat.card E = 2^(n/2)+1 ∧
        (∀ x : G, x ∈ E ↔ x ∈ A ∧ x^(2^(n/2)+1)=1) ∧
        z ∈ omegaOneCenterAmbient (T : Subgroup G) ∧ z ≠ 1 ∧
        E ≤ centralizer ({z} : Set G) ∧
        ∀ x ∈ E, t*x*t⁻¹*x ∈ (T : Subgroup G) := by
  have hc := original_container_centralizes h hH c hKH hK hKT horbit hY hescape C hC hKC hm
  have hKR := (LocalSieve.binaryTriality_seed_eq_residual_and_normal h.qtke hKH hH.1.1.2
    hK hKT horbit hY hescape C hC hKC hm).1
  have hHC := (residual_le_omegaCentralizer_iff hH.1.1.2).mp ((hKR ▸ hKC).trans hc)
  obtain ⟨D,hDA,hDC,hDc,hDn⟩ := LocalSieve.binaryTriality_escape_cubic
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  obtain ⟨t,ht,htL,hi⟩ := LocalSieve.binaryTriality_cubic_inverted
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm hDA hDC hDc
  obtain ⟨hn,ho,E,z,hEA,hDE,hEc,hroot,hz,hz1,hEz,hinv⟩ :=
    minus_torus_of_centralizing_inverted_cubic h hH c hHC hDA hDc (hDC.trans hc) ht.1 hi
  refine ⟨?_,D,E,t,z,hDA,hDC,hDc,hDn,ht,htL,hi,hEA,hDE,hEc,hroot,hz,hz1,hEz,hinv⟩
  obtain ⟨k,hk⟩ := ho
  omega
end BinaryOmega

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric

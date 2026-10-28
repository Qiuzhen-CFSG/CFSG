module
public import CFSG.Quasithin.ChapterI.Section06To08.TightPGroup.Frattini
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import CFSG.Quasithin.ChapterI.Section06To08.Basic

/-!
# Cyclic TI subgroups and the span of their conjugates in a two-group

A cyclic two-subgroup is TI if the normalizer of its point of order two
normalizes the whole subgroup: every nontrivial intersection contains the
unique involution. For a cyclic TI subgroup of order four, I.7.5 applies
with K=Q=D and H=G. Its Frattini subgroup is nontrivial, so the conjugates
contained in a two-group commute and generate an abelian subgroup.

The span is the literal supremum of the ambient conjugates contained in T.
Its weak closure follows directly from this definition and finite cardinality.
Consequently any normalizer of an intermediate subgroup containing the span
also normalizes the span.

Source: Aschbacher--Smith I.7.5, applied in 14.3.22, printed p.998.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterI.Section06To08
variable {G : Type*} [Group G]

def conjugateSpanIn (D T : Subgroup G) : Subgroup G :=
  sSup (tightConjugateFamily ⊤ D T)

theorem conjugateSpanIn_le (D T : Subgroup G) : conjugateSpanIn D T ≤ T :=
  sSup_le fun _ hA => hA.1

theorem le_conjugateSpanIn {D T : Subgroup G} (hDT : D ≤ T) :
    D ≤ conjugateSpanIn D T :=
  le_sSup ⟨hDT, 1, mem_top _, conjSubgroup_one D⟩

theorem conjugate_le_conjugateSpanIn {D T : Subgroup G} (g : G)
    (h : conjSubgroup D g ≤ T) : conjSubgroup D g ≤ conjugateSpanIn D T :=
  le_sSup ⟨h, g, mem_top _, rfl⟩

theorem conjugateSpanIn_conjugate_le {D T : Subgroup G} (g : G)
    (h : conjSubgroup (conjugateSpanIn D T) g ≤ T) :
    conjSubgroup (conjugateSpanIn D T) g ≤ conjugateSpanIn D T := by
  change (sSup (tightConjugateFamily ⊤ D T)).map (MulAut.conj g).toMonoidHom ≤ _
  rw [map_le_iff_le_comap]
  apply sSup_le
  intro A hA
  rw [← map_le_iff_le_comap]
  change conjSubgroup A g ≤ _
  obtain ⟨hAT, a, _, rfl⟩ := hA
  have ha : conjSubgroup (conjSubgroup D a) g ≤ T :=
    (conjSubgroup_mono (conjugate_le_conjugateSpanIn a hAT) g).trans h
  rw [conjSubgroup_conjSubgroup] at ha ⊢
  exact conjugate_le_conjugateSpanIn _ ha

variable [Finite G]

theorem conjugateSpanIn_weakly_closed {D T : Subgroup G} (g : G)
    (h : conjSubgroup (conjugateSpanIn D T) g ≤ T) :
    conjSubgroup (conjugateSpanIn D T) g = conjugateSpanIn D T :=
  eq_of_le_of_card_ge (conjugateSpanIn_conjugate_le g h)
    (card_conjSubgroup _ _).ge

theorem normalizer_le_normalizer_conjugateSpanIn {D T P : Subgroup G}
    (hXP : conjugateSpanIn D T ≤ P) (hPT : P ≤ T) :
    normalizer (P : Set G) ≤ normalizer (conjugateSpanIn D T : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply conjugateSpanIn_weakly_closed
  exact (conjSubgroup_mono hXP g).trans
    ((mem_normalizer_iff_map_conj_eq.mp hg).le.trans hPT)

private theorem cyclic_four_frattini_ne_bot (D : Subgroup G) [IsCyclic D]
    (hD : Nat.card D = 4) : frattini D ≠ ⊥ := by
  have hp : IsPGroup 2 D := IsPGroup.of_card (n := 2) hD
  let : Fact (IsPGroup 2 D) := ⟨hp⟩
  intro hΦ
  let := (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hΦ
  have hh := IsElementaryAbelian.exponent_dvd_p 2 D
  rw [IsCyclic.exponent_eq_card, hD] at hh
  norm_num at hh

theorem conjugateSpanIn_abelian_of_cyclic_four {D T : Subgroup G}
    [IsCyclic D] (hD : Nat.card D = 4) (hTI : IsTISubgroup D)
    (hT : IsPGroup 2 T) (hDT : D ≤ T) :
    IsMulCommutative (conjugateSpanIn D T) := by
  have htight : Theory.GroupTheory.IsTightlyEmbedded D := by
    refine ⟨?_, ?_⟩
    · rw [hD]; decide
    · intro g hg
      have hi : D ⊓ D.map (MulAut.conj g).toMonoidHom = ⊥ := by
        apply eq_bot_iff.mpr
        intro x hx
        obtain ⟨y, hy, rfl⟩ := hx.2
        exact hTI g hg ⟨hx.1, y, hy, rfl⟩
      rw [hi]
      simp
  have hsetup : TightPGroupSetup D ⊤ D T := by
    refine ⟨htight, IsPGroup.of_card (n := 2) hD, ?_, ?_, ?_, hT, le_top, hDT⟩
    · intro he
      simp [he] at hD
    · exact le_inf le_top le_rfl
    · intro R _ hR _
      exact hR.trans inf_le_right
  have hc := hsetup.family_commuting_of_frattini_ne_bot (cyclic_four_frattini_ne_bot D hD)
  apply commutator_self_eq_bot_iff.mp
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply sSup_le
  intro A hA
  apply le_centralizer_iff.mp
  apply sSup_le
  intro B hB
  by_cases hBA : B = A
  · subst B
    obtain ⟨_, a, _, rfl⟩ := hA
    let : IsCyclic (conjSubgroup D a) :=
      isCyclic_of_surjective _ (D.equivMapOfInjective _ (MulAut.conj a).injective).surjective
    exact le_centralizer _
  · exact hc hB hA hBA

end CFSG.Quasithin.ChapterI.Section06To08

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]

theorem cyclic_two_TI_of_point_normalizer (D Z : Subgroup G) [IsCyclic D]
    (hD : IsPGroup 2 D) (hZ : Nat.card Z = 2) (hZD : Z ≤ D)
    (hn : normalizer (Z : Set G) ≤ normalizer (D : Set G)) :
    IsTISubgroup D := by
  obtain ⟨z, hz⟩ := ne_bot_iff_exists_ne_one.mp (show Z ≠ ⊥ by
    intro he; simp [he] at hZ)
  have hgen : Z = zpowers (z : G) := by
    have hh := congrArg (map Z.subtype) (zpowers_eq_top_of_prime_card hZ hz)
    simpa only [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, range_subtype,
      Subgroup.subtype_apply] using hh.symm
  have hz2 : orderOf (z : G) = 2 := by
    rw [← Nat.card_zpowers, ← hgen, hZ]
  let zD : D := ⟨z, hZD z.property⟩
  have hzD : orderOf zD = 2 := (orderOf_coe zD).symm.trans hz2
  apply (isTISubgroup_iff D).mpr
  intro g hg x hx hgx
  by_contra hx1
  let a : D := ⟨x, hx⟩
  have ha1 : a ≠ 1 := fun he => hx1 (congrArg Subtype.val he)
  have hao : orderOf (a ^ (orderOf a / 2)) = 2 :=
    orderOf_pow_orderOf_div (orderOf_pos a).ne' (hD.dvd_orderOf ha1)
  have hap : x ^ (orderOf a / 2) = z :=
    congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two hao hzD)
  have hgzD : MulAut.conj g (z : G) ∈ D := by
    rw [← hap, map_pow]
    exact D.pow_mem hgx _
  let b : D := ⟨MulAut.conj g z, hgzD⟩
  have hb : orderOf b = 2 := by
    rw [← orderOf_coe]
    exact ((MulAut.conj g).orderOf_eq _).trans hz2
  have hfix : MulAut.conj g (z : G) = z :=
    congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two hb hzD)
  apply hg
  apply hn
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [hgen, MonoidHom.map_zpowers]
  exact congrArg zpowers hfix

end CFSG.Quasithin.ChapterI.Section06To08
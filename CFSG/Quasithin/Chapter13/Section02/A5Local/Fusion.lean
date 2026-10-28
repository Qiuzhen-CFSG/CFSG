module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.Flags
public import Theory.GroupTheory.NormalFourCentralizerSeparation

/-!
# Full fusion in the original A₅ module from the nonsingular centralizer

The source flag calculation makes C_T(v) Sylow in N_G(V) ∩ C_G(v).
When the already required nonsingular centralizer bound holds, this is
Sylow in C_G(v). Its order is smaller than |T|, while the singular mark z
is central in T. Thus v and z are not conjugate, and the two transitive
A₅ orbits give full L-control of fusion on V. The final theorem supplies
the literal N_G(V) fusion callback of the terminal 13.6 contradiction.

This is a direct terminal application of the centralizer comparison in
Aschbacher–Smith 13.2.6, printed p.879, using the later 13.6.7(1) bound,
printed p.928. The original proof of 13.6.7 itself requires the independent
earlier Baumann route to fusion; this lemma does not replace that input.
-/

public section
open Subgroup BinaryPermutation BinaryPermutation.FiveGeometry BinaryPermutation.FiveCentralizerGeometry
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
open FlagCoordinates FlagCoordinates.SylowCalculation Stellmacher ChapterB
variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}

private theorem v_nonsingular : form v ≠ 0 := by decide
private theorem z_singular : form z = 0 := by decide

omit [Finite G] in
/-- Lift transitivity on a quadratic-value orbit to actual elements of L. -/
theorem Marking.conjugate_of_same_form (s : Marking L V)
    (x y : Space) (hx : x ≠ 0) (hy : y ≠ 0) (hq : form x = form y) :
    ∃ l : L, MulAut.conj (l : G) (s.map (Multiplicative.ofAdd x)) =
      s.map (Multiplicative.ofAdd y) := by
  obtain ⟨a,ha⟩ := exists_even_transport x y hx hy hq
  obtain ⟨l,hl⟩ := s.onto a
  refine ⟨l, ?_⟩
  rw [s.equivariant,hl]
  exact congrArg (fun x : Space => s.map (Multiplicative.ofAdd x)) ha

omit [Finite G] in
/-- Separation of the two marked classes gives full L-control of fusion on V. -/
theorem Marking.controls_fusion_of_nonconjugate (s : Marking L V)
    (hsep : ¬IsConj (markedV s) (markedZ s)) :
    ∀ x ∈ V, x ≠ 1 → ∀ a : G, MulAut.conj a x ∈ V →
      ∃ l : L, MulAut.conj (l : G) x = MulAut.conj a x := by
  intro x hx hx1 a ha
  obtain ⟨u,hu⟩ := s.range_eq.ge hx
  obtain ⟨w,hw⟩ := s.range_eq.ge ha
  have hu0 : u.toAdd ≠ 0 := by
    intro he
    have he' : u = 1 := he
    exact hx1 (hu.symm.trans (he' ▸ s.map.map_one))
  have hw0 : w.toAdd ≠ 0 := by
    intro he
    have he' : w = 1 := he
    have hx' : MulAut.conj a x = 1 := hw.symm.trans (he' ▸ s.map.map_one)
    exact hx1 ((MulAut.conj a).map_eq_one_iff.mp hx')
  have hconj : IsConj (s.map u) (s.map w) := by
    rw [hu,hw]
    exact isConj_iff.mpr ⟨a,rfl⟩
  have same : form u.toAdd = form w.toAdd := by
    by_contra hn
    have hdiff : (form u.toAdd = 0 ∧ form w.toAdd ≠ 0) ∨
        (form u.toAdd ≠ 0 ∧ form w.toAdd = 0) :=
      (show ∀ a b : ZMod 2, a ≠ b → (a = 0 ∧ b ≠ 0) ∨ (a ≠ 0 ∧ b = 0) by decide) _ _ hn
    rcases hdiff with ⟨hz,hv⟩ | ⟨hv,hz⟩
    · obtain ⟨l,hl⟩ := s.conjugate_of_same_form z u.toAdd z_ne_zero hu0 (z_singular.trans hz.symm)
      obtain ⟨m,hm⟩ := s.conjugate_of_same_form v w.toAdd v_ne_zero hw0
        ((show ∀ a b : ZMod 2, a ≠ 0 → b ≠ 0 → a = b by decide) _ _ v_nonsingular hv)
      exact hsep ((isConj_iff.mpr ⟨(m : G),hm⟩).trans
        (hconj.symm.trans (isConj_iff.mpr ⟨(l : G),hl⟩).symm))
    · obtain ⟨l,hl⟩ := s.conjugate_of_same_form v u.toAdd v_ne_zero hu0
        ((show ∀ a b : ZMod 2, a ≠ 0 → b ≠ 0 → a = b by decide) _ _ v_nonsingular hv)
      obtain ⟨m,hm⟩ := s.conjugate_of_same_form z w.toAdd z_ne_zero hw0 (z_singular.trans hz.symm)
      exact hsep ((isConj_iff.mpr ⟨(l : G),hl⟩).trans
        (hconj.trans (isConj_iff.mpr ⟨(m : G),hm⟩).symm))
  obtain ⟨l,hl⟩ := s.conjugate_of_same_form u.toAdd w.toAdd hu0 hw0 same
  change MulAut.conj (l : G) (s.map u) = s.map w at hl
  exact ⟨l,by simpa only [hu,hw] using hl⟩

variable {T : Sylow 2 G} {V₁ V₂ : Subgroup G}

/-- No Sylow subgroup fixes a nonsingular vector in the original module. -/
theorem FlagSource.not_centralizes_nonsingular (d : FlagSource T L V V₁ V₂)
    (x : Space) (hx : form x ≠ 0) :
    ¬ (T : Subgroup G) ≤ centralizer ({d.module.map (Multiplicative.ofAdd x)} : Set G) := by
  intro hc
  apply hx
  apply sylow_fixed_singular d.image d.alternating_le_image d.imageSylow x
  intro p hp
  obtain ⟨t,ht,rfl⟩ := hp
  apply Multiplicative.ofAdd.injective
  apply d.module.injective
  change d.module.map (Multiplicative.ofAdd (coreRepresentation (Fin 5) (d.normalizerAction t) x)) = _
  rw [←d.normalizer_equivariant]
  exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp (hc ht))

/-- Sylow centralizer orders separate the actual singular and nonsingular marks. -/
theorem FlagSource.marked_not_conjugate_of_centralizer (d : FlagSource T L V V₁ V₂)
    (hCv : Gv (markedV d.flag.module) ≤ normalizer (V : Set G)) :
    ¬IsConj (markedV d.flag.module) (markedZ d.flag.module) := by
  have hlocal := d.flag_localIndex
  rw [inf_eq_right.mpr hCv] at hlocal
  have hproper : Tv (T : Subgroup G) (markedV d.flag.module) ≠ (T : Subgroup G) := by
    intro he
    have hcentral : (T : Subgroup G) ≤ Gv (markedV d.flag.module) := he ▸ inf_le_right
    obtain ⟨g,hg⟩ := d.flag_relabel
    rw [hg] at hcentral
    apply d.not_centralizes_nonsingular (rho g v) _ hcentral
    rw [form_invariant]
    exact v_nonsingular
  have hz : (T : Subgroup G) ≤ Gv (markedZ d.flag.module) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr
      (((mem_omegaOneCenterAmbient_iff (T : Subgroup G) _).mp d.flag.z_central).2.2 t ht)
  apply Subgroup.not_isConj_of_sylow_centralizer_card_lt
    (markedV d.flag.module) (markedZ d.flag.module)
    (Tv (T : Subgroup G) (markedV d.flag.module)) (T : Subgroup G)
    (T.isPGroup'.to_le inf_le_left) T.isPGroup' inf_le_right hz hlocal
  exact lt_of_le_of_ne (card_le_of_le inf_le_left)
    (fun he => hproper (eq_of_le_of_card_ge inf_le_left he.ge))

/-- Full L-control on V, using the nonsingular centralizer already required at the terminal consumer. -/
theorem FlagSource.controls_fusion_of_nonsingular_centralizer
    (d : FlagSource T L V V₁ V₂)
    (hCv : Gv (markedV d.flag.module) ≤ normalizer (V : Set G)) :
    ∀ x ∈ V, x ≠ 1 → ∀ a : G, MulAut.conj a x ∈ V →
      ∃ l : L, MulAut.conj (l : G) x = MulAut.conj a x :=
  d.flag.module.controls_fusion_of_nonconjugate (d.marked_not_conjugate_of_centralizer hCv)

/-- The full normalizer fusion callback consumed by the terminal A₅ argument. -/
theorem FlagSource.normalizer_controls_fusion_of_nonsingular_centralizer
    (d : FlagSource T L V V₁ V₂)
    (hCv : Gv (markedV d.flag.module) ≤ normalizer (V : Set G)) :
    ∀ x : V, x ≠ 1 → ∀ a : G, MulAut.conj a x.val ∈ V →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n x.val = MulAut.conj a x.val := by
  intro x hx a ha
  obtain ⟨l,hl⟩ := d.controls_fusion_of_nonsingular_centralizer hCv x.val x.property
    (fun he => hx (Subtype.ext he)) a ha
  exact ⟨l,d.module.normalizes l.property,hl⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module

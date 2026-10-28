module

public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.Action
public import Theory.SpecificGroups.PSL2.PrimeSylowFixers
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order360
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.SylowGeometry
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.NaturalFixed
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.ExceptionalFixed

/-!
# Intrinsic geometry of the projective shadow models

This file records the model facts used by the shadow argument.  The prime
field case is obtained from the proved projective-semilinear coverage theorem:
the coefficient factor is trivial for `ZMod p`, so the faithful projective
map is an equivalence onto the full automorphism group.  The exceptional
field is transported through the checked PSL₂(9)–A₆ generator-action
comparison; the resulting automorphism equivalence is the full
`Aut(A₆)`, with the marked natural `S₆` and inner `A₆` subgroups.

The remaining declarations are the elementary index-two complement and
marked Sylow identities used by the source proof.  They are stated with the
actual subgroups and actual equivalences, rather than model labels.

Source: Aschbacher–Smith, combined manuscript, Lemma 16.4.6, pp.1184–1186.
-/

@[expose] public section

open Subgroup GorensteinWalter
open AlternatingSix.ShadowLocal

namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow

/-- The odd prime-field hypotheses used by the projective coverage theorem. -/
theorem primeFieldOddPrimePower (p : ℕ) [Fact p.Prime] (hp : Odd p)
    : IsOddPrimePower (Nat.card (ZMod p)) :=
  ⟨p, 1, Fact.out, hp, by omega, by simp⟩

theorem primeField_card_gt_three {p : ℕ} [Fact p.Prime] (_hp : Odd p)
    (hlarge : 3 < p) : 3 < Nat.card (ZMod p) := by
  simpa using hlarge

/-- In a prime field, every automorphism of the actual PSL₂ group is induced
by a unique projective matrix.  Both injectivity and surjectivity are proved
for the same canonical projective action. -/
noncomputable def primeFieldPGLAutEquiv {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (hlarge : 3 < p) :
    PGL2 (ZMod p) ≃* MulAut (PSL2 (ZMod p)) := by
  let hK := primeFieldOddPrimePower p hp
  let hc : 3 < Nat.card (ZMod p) := primeField_card_gt_three hp hlarge
  let f := pgl2InnerAutPSL2 (ZMod p) hK hc
  exact MulEquiv.ofBijective f ⟨pgl2InnerAutPSL2_injective _ hK hc,
    fun a => by
      simpa [f, hK, hc] using Theory.PSL2.primeField_pgl_coverage hp hlarge a⟩

theorem primeFieldPGLAutEquiv_apply {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (hlarge : 3 < p) (a : PGL2 (ZMod p)) :
    primeFieldPGLAutEquiv hp hlarge a =
      pgl2InnerAutPSL2 (ZMod p) (primeFieldOddPrimePower p hp)
        (primeField_card_gt_three hp hlarge) a := by
  rfl

/-- The checked exceptional comparison transports the full automorphism group
of PSL₂(9) to the actual automorphism group of A₆. -/
noncomputable def nineAutEquiv {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 9) :
    MulAut (PSL2 K) ≃* MulAut (alternatingGroup (Fin 6)) :=
  MulAut.congr (Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6 hK)

theorem nineAutEquiv_inner_image {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 9) :
    (nineAutEquiv hK).toMonoidHom ''
      ((MulAut.conj : PSL2 K →* MulAut (PSL2 K)).range : Set (MulAut (PSL2 K))) =
      (AlternatingSix.ShadowLocal.inner : Set (MulAut (alternatingGroup (Fin 6)))) := by
  ext a
  constructor
  · rintro ⟨b, ⟨c, hc⟩, rfl⟩
    subst b
    refine ⟨Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6 hK c, ?_⟩
    change MulAut.conj
      (Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6 hK c) =
      MulAut.congr (Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6 hK)
        (MulAut.conj c)
    rw [MulAut.congr_conj]
  · rintro ⟨b, hb⟩
    rcases hb with ⟨c, hc⟩
    let e := Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6 hK
    refine ⟨MulAut.conj (e.symm b), ⟨e.symm b, rfl⟩, ?_⟩
    change MulAut.congr e (MulAut.conj (e.symm b)) = MulAut.conj b
    rw [MulAut.congr_conj, e.apply_symm_apply]

/-- The natural `S₆` is an index-two complement over the actual inner `A₆`. -/
theorem natural_index_two_over_inner :
    (natural : Subgroup (MulAut (alternatingGroup (Fin 6)))).index = 2 :=
  GLS3.Chapter5.naturalAlternatingAutomorphismSubgroup_index

theorem inner_le_natural_actual :
    AlternatingSix.ShadowLocal.inner ≤ natural :=
  AlternatingSix.ShadowLocal.inner_le_natural

theorem natural_outer_fixed_model
    (β : MulAut (alternatingGroup (Fin 6))) (hβ : orderOf β = 2)
    (hβn : β ∈ natural) (hβi : β ∉ AlternatingSix.ShadowLocal.inner) :
    Nonempty (GLS3.Chapter5.automorphismFixedSubgroup β ≃*
      Equiv.Perm (Fin 4)) :=
  AlternatingSix.ShadowLocal.natural_outer_involution_fixed_equiv_symmetricFour
    β hβ hβn hβi

theorem exceptional_outer_fixed_model
    (β : MulAut (alternatingGroup (Fin 6))) (hβ : orderOf β = 2)
    (hβn : β ∉ natural) :
    Nonempty (GLS3.Chapter5.automorphismFixedSubgroup β ≃*
      DihedralGroup 5) :=
  AlternatingSix.ShadowLocal.outside_natural_involution_fixed_equiv_dihedral β hβ hβn

/-- If an index-two subgroup is avoided by an involution, it and that
involution generate the whole ambient group. -/
theorem sup_zpowers_eq_top_of_index_two_not_mem
    {G : Type*} [Group G] [Finite G] (H : Subgroup G) (hH : H.index = 2)
    {r : G} (hr : r ∉ H) :
    H ⊔ zpowers r = ⊤ := by
  apply Subgroup.index_eq_one.mp
  have htop_or : H ⊔ zpowers r = H ∨ H ⊔ zpowers r = ⊤ := by
    have hidx : (H ⊔ zpowers r).index ∣ H.index :=
      Subgroup.index_dvd_of_le le_sup_left
    rw [hH] at hidx
    rcases (Nat.dvd_prime Nat.prime_two).mp hidx with h | h
    · exact Or.inr (Subgroup.index_eq_one.mp h)
    · left
      apply (Subgroup.eq_of_le_of_card_ge le_sup_left ?_).symm
      have hmulH := H.card_mul_index
      have hmulS := (H ⊔ zpowers r).card_mul_index
      rw [hH] at hmulH
      rw [h] at hmulS
      omega
  rcases htop_or with htop | htop
  · exfalso
    apply hr
    rw [← htop]
    exact (le_sup_right : zpowers r ≤ H ⊔ zpowers r) (mem_zpowers r)
  · exact Subgroup.index_eq_one.mpr htop

/-- The two possible complements in the exceptional model are represented by
actual subgroups: the inner image in the prime case and natural `S₆` in the
field-nine case. -/
theorem natural_sup_zpowers_eq_top {r : MulAut (alternatingGroup (Fin 6))}
    (hr : r ∉ natural) : natural ⊔ zpowers r = ⊤ :=
  sup_zpowers_eq_top_of_index_two_not_mem natural natural_index_two_over_inner hr

theorem pgl2_range_sup_zpowers_eq_top
    {K : Type*} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (_hcard : 3 < Nat.card K)
    {r : PGL2 K}
    (hr : r ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (n := Fin 2) (R := K)).range) :
    (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (n := Fin 2) (R := K)).range ⊔ zpowers r = ⊤ := by
  let _ : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  exact sup_zpowers_eq_top_of_index_two_not_mem _
    (pgl2_psl2Range_index_eq_two K hK) hr

/-- Marked Sylow geometry in `Aut(A₆)`: the inner intersection is the actual
normal D₈, and its pointwise centralizer is the marked natural subgroup. -/
theorem marked_sylow_inner_centralizer (P : Sylow 2 (MulAut (alternatingGroup (Fin 6)))) :
    centralizer (sylowInner P : Set P) = center P ⊔
      SylowGeometry.transpositionSubgroup P :=
  AlternatingSix.ShadowLocal.SylowGeometry.centralizer_inner P

theorem marked_sylow_transposition_centralizer
    (P : Sylow 2 (MulAut (alternatingGroup (Fin 6)))) :
    centralizer (SylowGeometry.transpositionSubgroup P : Set P) =
      AlternatingSix.ShadowLocal.sylowNatural P :=
  AlternatingSix.ShadowLocal.SylowGeometry.centralizer_transposition P

theorem marked_sylow_center
    (P : Sylow 2 (MulAut (alternatingGroup (Fin 6)))) :
    center P = zpowers (Identification.sylowEquiv P (Holomorph.rotation ^ 4)) :=
  AlternatingSix.ShadowLocal.SylowGeometry.center_eq P

theorem marked_sylow_cyclicFour_card
    (P : Sylow 2 (MulAut (alternatingGroup (Fin 6)))) :
    Nat.card (SylowGeometry.cyclicFour P) = 4 :=
  AlternatingSix.ShadowLocal.SylowGeometry.cyclicFour_card P

theorem marked_sylow_normal_cyclicFour_sup_transposition
    (P : Sylow 2 (MulAut (alternatingGroup (Fin 6))))
    (V : Subgroup P) [IsCyclic V] [V.Normal] (hV : Nat.card V = 4) :
    V ⊔ SylowGeometry.transpositionSubgroup P =
      SylowGeometry.cyclicFour P ⊔ SylowGeometry.transpositionSubgroup P :=
  AlternatingSix.ShadowLocal.SylowGeometry.normal_cyclicFour_sup_transposition P V hV

theorem marked_sylow_inner_involution_not_square
    (P : Sylow 2 (MulAut (alternatingGroup (Fin 6)))) (u : P)
    (huD : u ∈ AlternatingSix.ShadowLocal.sylowInner P)
    (huZ : u ∉ center P) (hu2 : u ^ 2 = 1) :
    ∀ x : P, x ^ 2 ≠ u :=
  AlternatingSix.ShadowLocal.SylowGeometry.inner_involution_not_square P u huD huZ hu2

theorem marked_sylow_inner_involution_inverts_normal_cyclicFour
    (P : Sylow 2 (MulAut (alternatingGroup (Fin 6))))
    (V : Subgroup P) [IsCyclic V] [V.Normal] (hV : Nat.card V = 4)
    (u : P) (huD : u ∈ AlternatingSix.ShadowLocal.sylowInner P)
    (huZ : u ∉ center P) (hu2 : u ^ 2 = 1) :
    ∀ x ∈ V, u * x * u⁻¹ = x⁻¹ :=
  AlternatingSix.ShadowLocal.SylowGeometry.inner_involution_inverts_normal_cyclicFour
    P V hV u huD huZ hu2

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow

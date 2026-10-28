module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeChiefRanks
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.SolvableActorLayers
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeChiefQuotients
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeParabolicInputs

/-!
# The solvable chief branch of the exceptional original M22-code parabolic

The same original maximum elementary actor has rank at least two on every
noncentral chief factor.  A four-subgroup cannot embed in S₃, so the
solvable chief-image alternatives reduce to S₃ wreath C₂, with offender
layer S₃ × S₃.  The literal action-kernel quotient retains this marking.

When the original H is solvable, a noncentral factor exists by the proved
count two. Its wreath image identifies the normal core of the unique
maximal overgroup, and the original Sylow modulo O₂(H) is dihedral eight.
B.6.8 then identifies the two-residual of H/O₂(H) with its three-core,
and quotienting by that core gives the same dihedral eight. Both inside-core
containment and solvability remain explicit branch inputs. The nonsolvable
sieve and the full quotient by O₂(H) are subsequent steps.

Source: Aschbacher–Smith, 3.1.9(4,6), B.6.8–9 and 8.2.2(1), printed
pp.113–116,577–578,715, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open ChapterD ChapterD.UniqueFactor NoncentralChiefRefinement
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private theorem not_symmetric_three_of_large_elementary
    {K : Type*} [Group K] [Finite K] (A : Subgroup K)
    (hA : IsElementaryTwo A) (hr : 2 ≤ rank A) :
    ¬ Nonempty (K ≃* Equiv.Perm (Fin 3)) := by
  rintro ⟨e⟩
  have hc : Nat.card K = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    decide
  have hd : 4 ∣ Nat.card A := by
    rw [hA.card_eq_two_pow_rank]
    exact Nat.pow_dvd_pow 2 hr
  have hf := hd.trans A.card_subgroup_dvd_card
  rw [hc] at hf
  norm_num at hf

private theorem original_minimal_parabolic
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2) :
    ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤ := by
  obtain ⟨c,_,hq,_⟩ := D.sourceOrbit_m22_code_inside_core_inputs h hmany hV hnon d hH hcore
  obtain ⟨_,hu⟩ := D.original_uniqueness h
  let q := c.toQRCConfiguration (c.no_common_normal hu)
  exact source_intrinsic_minimalParabolic_of_notFF q
    D.sourceOrbit_weakClosure_setup.nontrivial (source_notFF_of_ratio_two q hq)
    (T.subtype hH.1.1.2) (map_subgroupOf_eq_of_le hH.1.1.2)

/-- All original noncentral chief images exclude S₃; a solvable image has
the full wreath actor and the corresponding product offender layer. -/
theorem sourceOrbit_m22_code_inside_core_chief_sieve
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2) :
    let U := (conjugateSpan H D.sourceOrbit).subgroupOf H
    ∃ hU : IsElementaryAbelian 2 U,
      let := hU
      ∀ (s : SeriesOn U) (i : Fin s.series.length), ¬ s.Central i →
        ¬ Nonempty (actionImage (s.factorRepresentation i) ≃* Equiv.Perm (Fin 3)) ∧
        (Group.IsSolvable (actionImage (s.factorRepresentation i)) →
          Nonempty ((H ⧸ (actionHom (s.factorRepresentation i)).ker) ≃*
            RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) ∧
          Nonempty (offenderSubgroup (Representation.BinaryOffender.imageRepresentation
            (s.factorRepresentation i)) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) := by
  obtain ⟨hU,A,hA,hAR,hquad,hr,hmin,hchief⟩ :=
    D.sourceOrbit_m22_code_inside_core_large_chief_actor h hmany hV hnon d hH hcore
  let := hU
  have hp := D.original_minimal_parabolic h hmany hV hnon d hH hcore
  refine ⟨hU,?_⟩
  dsimp only
  intro s i hi
  have hs := hchief s i hi
  have hrank : 2 ≤ rank (actionSubgroup (s.factorRepresentation i) A) := by
    rw [hs.2.2]
    exact hr
  have hn := not_symmetric_three_of_large_elementary _ hs.1.1 hrank
  refine ⟨hn,?_⟩
  intro hsolv
  let := s.factorRepresentation_irreducible i
  rcases ChapterB.chief_solvable_image_actor_and_offender_types
    (s.factorRepresentation i) (Chapter3.sqtk_of_mem_H h.simpleQTKE hH.1.1.1)
    (T.subtype hH.1.1.2) hp ⟨_,hs.1⟩ hsolv with he | he
  · exact (hn he.1).elim
  · exact ⟨⟨(QuotientGroup.quotientKerEquivOfSurjective
      (actionHom (s.factorRepresentation i))
      (s.factorRepresentation i).asGroupHom.rangeRestrict_surjective).trans
        (Classical.choice he.1)⟩,he.2⟩


/-- In the solvable branch the original normal-core quotient is the full
wreath actor, and the same original Sylow modulo O₂(H) is dihedral eight. -/
theorem sourceOrbit_m22_code_inside_core_solvable_quotients
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2) (hsolv : Group.IsSolvable H) :
    ∃ hp : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤,
      Nonempty ((H ⧸ ChapterB.minimalParabolicCore (T.subtype hH.1.1.2) hp) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) ∧
      Nonempty (((T.subtype hH.1.1.2) ⧸ (pCore 2 H).subgroupOf
        ((T.subtype hH.1.1.2) : Subgroup H)) ≃* DihedralGroup 4) := by
  obtain ⟨hU,hchief⟩ := D.sourceOrbit_m22_code_inside_core_chief_sieve h hmany hV hnon d hH hcore
  let := hU
  let U := (conjugateSpan H D.sourceOrbit).subgroupOf H
  obtain ⟨s⟩ := SeriesOn.exists_series U
  have hex : ∃ i : Fin s.series.length, ¬ s.Central i := by
    by_contra! hz
    have hz' := s.noncentralCount_eq_zero_iff.mpr hz
    have htwo := D.sourceOrbit_m22_code_inside_core_two_chiefs h hmany hV hnon d hH hcore s
    omega
  obtain ⟨i,hi⟩ := hex
  have hs : Group.IsSolvable (actionImage (s.factorRepresentation i)) := by
    let := hsolv
    exact Group.isSolvable_of_surjective
      (f := actionHom (s.factorRepresentation i))
      (s.factorRepresentation i).asGroupHom.rangeRestrict_surjective
  obtain ⟨⟨e⟩,_⟩ := (hchief s i hi).2 hs
  obtain ⟨e₃⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  let w := RegularWreathProduct.congr e₃ (MulEquiv.refl (Multiplicative (ZMod 2)))
  let f := (w.symm.toMonoidHom.comp e.toMonoidHom).comp
    (QuotientGroup.mk' (actionHom (s.factorRepresentation i)).ker)
  have hf : Function.Surjective f := w.symm.surjective.comp
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hp := D.original_minimal_parabolic h hmany hV hnon d hH hcore
  obtain ⟨⟨a⟩,b⟩ := Chapter8.MathieuShadowRows.wreath_parabolic_quotients
    (T.subtype hH.1.1.2) hp f hf
  exact ⟨hp,⟨a.trans w⟩,b⟩

/-- The same solvable original parabolic has three-core two-residual modulo
O₂(H), and its literal quotient by that three-core is dihedral eight. -/
theorem sourceOrbit_m22_code_inside_core_solvable_residual
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2) (hsolv : Group.IsSolvable H) :
    pResidual 2 (H ⧸ pCore 2 H) = pCore 3 (H ⧸ pCore 2 H) ∧
      Nonempty (((H ⧸ pCore 2 H) ⧸ pCore 3 (H ⧸ pCore 2 H)) ≃* DihedralGroup 4) := by
  obtain ⟨hp,⟨e⟩,_⟩ :=
    D.sourceOrbit_m22_code_inside_core_solvable_quotients h hmany hV hnon d hH hcore hsolv
  obtain ⟨e₃⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  let w := RegularWreathProduct.congr e₃ (MulEquiv.refl (Multiplicative (ZMod 2)))
  let f := (w.symm.toMonoidHom.comp e.toMonoidHom).comp
    (QuotientGroup.mk' (ChapterB.minimalParabolicCore (T.subtype hH.1.1.2) hp))
  have hf : Function.Surjective f := w.symm.surjective.comp
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  exact Chapter8.MathieuShadowRows.solvable_wreath_parabolic_residual
    (T.subtype hH.1.1.2) hp hsolv f hf


end CFSG.Quasithin.Chapter12.Section02.ChosenModule

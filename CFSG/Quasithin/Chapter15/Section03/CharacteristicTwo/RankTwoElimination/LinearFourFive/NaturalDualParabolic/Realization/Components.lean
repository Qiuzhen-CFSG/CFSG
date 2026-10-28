module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Actions
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.MSData
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.FourComponent.Lifting

/-!
# The actual residual component of the point parabolic

The quotient P/O₂(P) ≃ PSL₃(2) lifts to a normal C-component of P.
Its perfectness puts it in O²(P), while the lifting theorem gives the
reverse containment. Thus the component is the literal two-residual,
and its own two-core quotient is genuinely SL₃(2).

When P is normalized by S and lies in O²(P)S, relative subnormality
transports this C-component into the MS ambient group. No normality in
the original ambient G is asserted. Normalization by S and the separate
commutator comparison with Q_P still require the local argument.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
A.3.3 and 15.3.24, printed pp.1129–1130; C.1.31, printed p.135.
-/

@[expose] public section

open Subgroup BinaryLinear.OuterCyclic

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization

universe u
variable {G : Type u} [Group G] {d : LocalData G} {L : Subgroup G}

private theorem perfect_twoPerfect {J : Type*} [Group J] [Finite J]
    [Group.IsPerfect J] : IsPPerfect 2 J := by
  intro N hN hp
  let := hN
  have hs : Subsingleton (J ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (J ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

/-- The parabolic's two-residual is its C-component, with its actual intrinsic quotient. -/
theorem point_residual_component [Finite G] (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) :
    ((Stellmacher.twoResidualAmbient (point h x)).subgroupOf (point h x)).IsCComponent ∧
      Nonempty (((Stellmacher.twoResidualAmbient (point h x)) ⧸
        pCore 2 (Stellmacher.twoResidualAmbient (point h x))) ≃* Projective 3) := by
  obtain ⟨K, hKP, hK, _, hr, f, _⟩ :=
    BinaryLinear.SmallParabolicLevi.FourComponent.exists_component_of_twoCoreQuotient
      (point h x) (pointQuotientEquiv h hx)
  let := hK.perfect
  have hk := map_mono (f := (point h x).subtype)
    (le_pResidual_of_isPPerfect (K.subgroupOf (point h x)) perfect_twoPerfect)
  rw [map_subgroupOf_eq_of_le hKP] at hk
  have he : K = Stellmacher.twoResidualAmbient (point h x) := by
    rw [ComponentIntersection.twoResidualAmbient_eq_map_pResidual]
    exact le_antisymm hk hr
  subst K
  exact ⟨hK, ⟨f⟩⟩

private theorem component_in_overgroup {E P J : Subgroup G} (hEP : E ≤ P) (hPJ : P ≤ J)
    (hE : (E.subgroupOf P).IsCComponent) (hP : (P.subgroupOf J).IsSubnormal) :
    (E.subgroupOf J).IsCComponent := by
  let e := (subgroupOfEquivOfLe hPJ).symm
  have hc := (hE.map_equiv e).map_subtype hP
  convert hc using 1
  apply map_injective J.subtype_injective
  rw [map_subgroupOf_eq_of_le (hEP.trans hPJ), map_map, map_map]
  change E = (E.subgroupOf P).map P.subtype
  exact (map_subgroupOf_eq_of_le hEP).symm

/-- Relative normalization, rather than ambient normality, puts O²(P) in C(O²(P)S). -/
theorem residualComponent_isCComponent [Finite G] (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0)
    (hPJ : point h x ≤ residualOvergroup h x)
    (hn : d.S ≤ normalizer (point h x : Set G)) :
    (residualComponent h x).IsCComponent := by
  have hnorm : ((point h x).subgroupOf (residualOvergroup h x)).Normal :=
    normal_subgroupOf_of_le_normalizer
      (sup_le ((map_subtype_le _).trans (point h x).le_normalizer) hn)
  exact component_in_overgroup (map_subtype_le _) hPJ (point_residual_component h hx).1
    hnorm.isSubnormal

/-- The quotient required by BinaryMS.Input, for its literal residual component. -/
theorem residualComponent_quotient [Finite G] (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) :
    Nonempty (((residualComponent h x) ⧸ pCore 2 (residualComponent h x)) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  obtain ⟨f⟩ := (point_residual_component h hx).2
  let e : residualComponent h x ≃* Stellmacher.twoResidualAmbient (point h x) :=
    subgroupOfEquivOfLe le_sup_left
  exact ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    (f.trans (projectiveEquivSL (by decide)))⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization

end

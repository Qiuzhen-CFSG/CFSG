module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.ShortQuotient
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFactors

/-!
# The chosen module's actual short-root line-normalizer quotient

The literal whole-reduced chosen module constructs the original short and
long roots and the full q-element fixed line. In N_{C_G(t)}(U)/U the
long-root normal closure has elementary abelian image of order q². Its
nonzero elements are conjugate to the surviving marked root under the
image of O^{2′}(C_L(t)). The quotient map has exactly the original line
as its kernel. Both orientations, degree-two rows and q=4 are preserved.

Source: Aschbacher–Smith F.4.42 and its 5.3/12.2 application, printed
pp.295–296,659,795 of `refs/quasithin.pdf`. Ambient unique fixed cosets,
normalizer control and short-root centralizer containment remain unproved.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open UnitaryCompletion
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- The entire line is killed in any target quotient, and residual conjugators
reach all nonzero images of the original long-root normal closure. -/
theorem rankOne_unitary_short_root_quotient_orbits
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    1 < m ∧ n = 2*m ∧
    ∃ t : L, orderOf t.val = 2 ∧
    ∃ z : centralizer ({t} : Set L), orderOf z.val.val = 2 ∧
    ∃ U : Subgroup (centralizer ({t} : Set L)),
      let V := normalClosure ({z} : Set (centralizer ({t} : Set L)))
      IsElementaryAbelian 2 V ∧
      Nat.card V = (2^m)^3 ∧ Nat.card U = 2^m ∧ U.relIndex V = (2^m)^2 ∧
      U ≤ V ∧ U ≤ center (centralizer ({t} : Set L)) ∧
      zpowers (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) < U ∧
      ∀ {J : Type u} [Group J] (f : centralizer ({t} : Set L) →* J),
        U ≤ f.ker → ∀ v ∈ V.map f, v ≠ 1 →
          ∃ a ∈ primeToResidual 2 (centralizer ({t} : Set L)),
            f a * f z * (f a)⁻¹ = v := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_short_root_quotient_orbits hi hH hp m hm hc

/-- The literal ambient normalizer quotient has a q²-element module with
the original kernel and a surviving transitive long-root representative. -/
theorem rankOne_unitary_short_root_ambient_quotient
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    1 < m ∧ n = 2*m ∧
    ∃ t : L, orderOf t.val = 2 ∧
    ∃ z : centralizer ({t} : Set L), orderOf z.val.val = 2 ∧
    ∃ U : Subgroup (centralizer ({t} : Set L)),
    ∃ hU : U ≤ center (centralizer ({t} : Set L)),
      let V := normalClosure ({z} : Set (centralizer ({t} : Set L)))
      let f := UnitarySource.shortLineQuotientMap L t U hU
      Nat.card U = 2^m ∧ f.ker = U ∧
      IsElementaryAbelian 2 (V.map f) ∧ Nat.card (V.map f) = (2^m)^2 ∧
      zpowers (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) < U ∧
      f (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) = 1 ∧
      f z ≠ 1 ∧ ∀ v ∈ V.map f, v ≠ 1 →
        ∃ a ∈ primeToResidual 2 (centralizer ({t} : Set L)),
          f a * f z * (f a)⁻¹ = v := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_short_root_ambient_quotient hi hH hp m hm hc

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

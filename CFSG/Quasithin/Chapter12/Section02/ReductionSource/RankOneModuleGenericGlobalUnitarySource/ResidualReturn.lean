module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.ResidualReturn
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFactors

/-!
# Ambient long-root returns through the original unitary residual

The whole reduced chosen module supplies the original prepared hypotheses.
Every ambient conjugate of the marked long root returning to L belongs to
O₂(L). In C_G(t), these returns are already in the residual long-root orbit,
and every such transporter normalizes L. The same conclusion holds for
returns to the residual image modulo the entire short-root line.

Source: Aschbacher–Smith F.4.35 and F.4.42, pp.292,295, and 5.3/12.2.
The additional returns through outer elements of N_G(L) are not settled
here; unique fixed cosets and the remaining source assembly stay open.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- Every original right-center involution has all its ambient returns
through L in the actual left two-core. No new choice of root is required. -/
theorem rankOne_unitary_long_residual_return
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (z : G) (hz : z ∈ (center (residual H)).map (residual H).subtype)
    (hz2 : orderOf z = 2) (x : L) (hx : IsConj z x.val) : x ∈ pCore 2 L := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_long_residual_return hi hH hp m hm hc z hz hz2 x hx

/-- The original chosen-module row controls long-root returns through its
residual and the corresponding full-line quotient, without an extra premise. -/
theorem rankOne_unitary_short_residual_return
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
      z.val.val ∈ (center (residual H)).map (residual H).subtype ∧
      centralizer ({t.val} : Set G) ⊓ centralizer ({z.val.val} : Set G) ≤ normalizer (L : Set G) ∧
    ∃ U : Subgroup (centralizer ({t} : Set L)),
    ∃ hU : U ≤ center (centralizer ({t} : Set L)),
      let V := normalClosure ({z} : Set (centralizer ({t} : Set L)))
      let f := UnitarySource.shortLineQuotientMap L t U hU
      U ≤ V ∧ IsElementaryAbelian 2 V ∧ Nat.card V = (2^m)^3 ∧
      Nat.card U = 2^m ∧ f.ker = U ∧
      IsElementaryAbelian 2 (V.map f) ∧ Nat.card (V.map f) = (2^m)^2 ∧
      zpowers (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) < U ∧
      (∀ x : L, IsConj z.val.val x.val → x ∈ pCore 2 L) ∧
      (∀ g : centralizer ({t.val} : Set G), g.val*z.val.val*g.val⁻¹ ∈ L →
        g.val ∈ normalizer (L : Set G) ∧
        ∃ a : centralizer ({t} : Set L),
          a.val.val*z.val.val*a.val.val⁻¹ = g.val*z.val.val*g.val⁻¹) ∧
      (∀ g : UnitarySource.shortLineNormalizer L t U ⧸ UnitarySource.shortLineKernel L t U,
        g*f z*g⁻¹ ∈ (L.comap (UnitarySource.shortLineAmbientEmbedding L t U)).map
          (QuotientGroup.mk' (UnitarySource.shortLineKernel L t U)) →
        g ∈ UnitarySource.shortLineLocalQuotient L t U) := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_short_residual_return hi hH hp m hm hc

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

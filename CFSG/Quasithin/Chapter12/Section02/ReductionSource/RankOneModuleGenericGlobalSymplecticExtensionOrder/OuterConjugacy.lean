module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.OuterConjugacy
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalSymplecticExtensionOrder.FixedRoot

/-!
# Chapter 12 original outer-involution conjugacy

The same marked Borel supplies actual source conjugators between outer
involutions. Each is therefore fused to an original root involution, and
its entire ambient centralizer lies in a conjugate original normalizer.

These applications retain Hypothesis 12.2.1, many locals, the original
n>1 and PSL2 quotient, HStar, Preparation and the perfect whole residual,
with W=wholeReduced T L. Both amalgam orientations are included. The fixed
binary quotient obstruction and the final ambient order bound remain open.

Source: Aschbacher--Smith F.4.37, printed p.293, used in 5.3.3 and
Chapter 12, pp.659,795 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Outer involutions are conjugate through the original whole pure Borel. -/
theorem rankOne_global_symplectic_outer_involutions_borel_conjugate
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
    (f t : T) (hf : orderOf f=2) (ht : orderOf t=2)
    (hfo : f.val ∉ Global.sourceS L H) (hto : t.val ∉ Global.sourceS L H) :
    ∃ c : (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0 ⊓
      ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1 : Subgroup G),
      c.val*f.val*c.val⁻¹=t.val :=
  d.symplectic_outer_involutions_borel_conjugate
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he f t hf ht hfo hto

/-- Every outer involution is an actual ambient conjugate of an original root involution. -/
theorem rankOne_global_symplectic_outer_involution_root_conjugate
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
    (f : T) (hf : orderOf f=2) (hfo : f.val ∉ Global.sourceS L H) :
    ∃ i : Fin 2, ∃ z : G, orderOf z=2 ∧
      z ∈ (center (![L,residual H] i)).map (![L,residual H] i).subtype ∧
      ∃ g : G, g*z*g⁻¹=f.val :=
  d.symplectic_outer_involution_root_conjugate
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he f hf hfo

/-- The full outer-involution centralizer lies in a conjugate original root normalizer. -/
theorem rankOne_global_symplectic_outer_centralizer_le_conjugate_normalizer
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
    (f : T) (hf : orderOf f=2) (hfo : f.val ∉ Global.sourceS L H) :
    ∃ i : Fin 2, ∃ z : G, orderOf z=2 ∧
      z ∈ (center (![L,residual H] i)).map (![L,residual H] i).subtype ∧
      ∃ g : G, g*z*g⁻¹=f.val ∧
        centralizer ({f.val} : Set G) ≤
          (normalizer (![L,residual H] i : Set G)).map (MulAut.conj g).toMonoidHom :=
  d.symplectic_outer_centralizer_le_conjugate_normalizer
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he f hf hfo

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

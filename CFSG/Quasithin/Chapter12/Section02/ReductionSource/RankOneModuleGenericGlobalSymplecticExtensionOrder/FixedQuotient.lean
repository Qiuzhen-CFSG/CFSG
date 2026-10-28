module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.FixedQuotient
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalSymplecticExtensionOrder.FixedPair

/-!
# Chapter 12 field-four exclusion and ambient Sylow equality

The actual fixed residual cores descend into the same conjugate original
local and give the D8 obstruction in its PSL2(4) section. Thus the original
inner Sylow equals T for every n>1. The third involution centralizer and the
normalizer of the Sylow center have their full common-normalizer bounds.

These applications retain Hypothesis 12.2.1, many locals, n>1, the original
PSL2 quotient, HStar, Preparation, the perfect whole residual and both
amalgam orientations. The generic input uses W=wholeReduced T L.
The three-class comparison and full ambient order/completion remain required.

Source: Aschbacher--Smith F.4.37,39, pp.293--294, through 5.3.3 and Chapter12,
pp.659,795 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F=2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
include D h hmany hn hpsl hH d hp hm hF he

/-- Both fixed cores lie in the same conjugate original local, with its
prescribed root-normalizer placement retained. -/
theorem rankOne_global_symplectic_outer_fixed_cores_le_conjugate_local
    (f : T) (hf : orderOf f=2) (ho : f.val ∉ Global.sourceS L H)
    (i : Fin 2) (g : G)
    (hC : centralizer ({f.val} : Set G) ≤
      (normalizer (![L,residual H] i : Set G)).map (MulAut.conj g).toMonoidHom) :
    ∀ j : Fin 2,
      ((pResidual 2 (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) j ⊓
        centralizer ({f.val} : Set G) : Subgroup G)).map
        (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) j ⊓
          centralizer ({f.val} : Set G)).subtype).pCoreIn 2 ≤
      (![L,residual H] i).map (MulAut.conj g).toMonoidHom :=
  d.symplectic_outer_fixed_cores_le_conjugate_local
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he f hf ho i g hC

/-- The D8/PSL2(4) obstruction excludes every original outer involution. -/
theorem rankOne_global_symplectic_outer_involution_false
    (f : T) (hf : orderOf f=2) (ho : f.val ∉ Global.sourceS L H) : False :=
  d.symplectic_outer_involution_false
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he f hf ho

/-- The original inner Sylow equals T, including n=2. -/
theorem rankOne_global_symplectic_sourceS_eq_sylow : Global.sourceS L H=(T : Subgroup G) :=
  d.symplectic_sourceS_eq_sylow
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he

/-- Full ambient containment for the third symplectic involution centralizer. -/
theorem rankOne_global_symplectic_square_centralizer_le_middle
    (z : Global.sourceS L H) (hz : orderOf z=2)
    (hsq : ∃ y : Global.sourceS L H, y^2=z) :
    centralizer ({z.val} : Set G)≤normalizer (L : Set G)⊓normalizer (residual H : Set G) :=
  d.symplectic_square_centralizer_le_middle
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he z hz hsq

/-- The normalizer of the inner Sylow center is the entire original middle. -/
theorem rankOne_global_symplectic_center_normalizer_eq_middle :
    normalizer ((center (Global.sourceS L H)).map (Global.sourceS L H).subtype : Set G)=
      normalizer (L : Set G)⊓normalizer (residual H : Set G) :=
  d.symplectic_center_normalizer_eq_middle
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

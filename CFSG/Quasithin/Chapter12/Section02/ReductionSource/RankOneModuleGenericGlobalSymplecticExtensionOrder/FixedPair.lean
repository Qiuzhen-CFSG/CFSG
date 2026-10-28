module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.FixedPair
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalSymplecticExtensionOrder.FixedEndpoint

/-!
# Chapter 12 fixed dihedral pair and the normalizer quotient

The actual fixed residual four-groups generate D8. Minimality and opposite
endpoint-core noncontainment prove that this same D8 avoids the two-core of
the conjugate full root normalizer. Its map to that normalizer's literal
quotient is therefore injective, with the original root witness retained.

These applications retain Hypothesis 12.2.1, many locals, the original
exponent and PSL2 quotient, HStar, Preparation, perfectness of the whole
residual, W=wholeReduced T L, and both amalgam orientations.

Source: Aschbacher--Smith F.4.37, printed p.293, through 5.3.3 and Chapter12,
pp.659,795 of refs/quasithin.pdf. Placement in the PSL2(4) section, the
q=4 exclusion and the same-extension ambient order bound remain required.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The two actual fixed residual cores generate D8 with the original middle. -/
theorem rankOne_global_symplectic_outer_fixed_residual_pair
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
    (f : T) (hf : orderOf f=2) (ho : f.val ∉ Global.sourceS L H) :
    let P := ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H)
    let D : Fin 2 → Subgroup G := fun i => P i ⊓ centralizer ({f.val} : Set G)
    let U : Fin 2 → Subgroup G := fun i => ((pResidual 2 (D i)).map (D i).subtype).pCoreIn 2
    U 0≤D 0⊓D 1 ∧ U 1≤D 0⊓D 1 ∧
      Nonempty (↥(U 0⊔U 1)≃*DihedralGroup 4) ∧ U 0⊓U 1≠⊥ ∧
      ¬ U 0≤(D 1).pCoreIn 2 ∧ ¬ U 1≤(D 0).pCoreIn 2 :=
  d.symplectic_outer_fixed_residual_pair
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he f hf ho

/-- The fixed residual cores avoid every two-kernel normalized by both endpoints. -/
theorem rankOne_global_symplectic_outer_fixed_cores_disjoint
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
    (f : T) (hf : orderOf f=2) (ho : f.val ∉ Global.sourceS L H)
    (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hnQ : ∀ i : Fin 2,
      ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) i ⊓
        centralizer ({f.val} : Set G) ≤ normalizer (Q : Set G)) :
    ∀ i : Fin 2,
      Disjoint (((pResidual 2 (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) i ⊓
        centralizer ({f.val} : Set G) : Subgroup G)).map
        (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) i ⊓
          centralizer ({f.val} : Set G)).subtype).pCoreIn 2) Q :=
  d.symplectic_outer_fixed_cores_disjoint
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he f hf ho Q hQ hnQ

/-- The actual D8 embeds in the conjugate full normalizer modulo its two-core. -/
theorem rankOne_global_symplectic_outer_fixed_dihedral_normalizer_quotient
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
    (f : T) (hf : orderOf f=2) (ho : f.val ∉ Global.sourceS L H) :
    ∃ i : Fin 2, ∃ z : G, orderOf z=2 ∧
      z ∈ (center (![L,residual H] i)).map (![L,residual H] i).subtype ∧
      ∃ g : G, g*z*g⁻¹=f.val ∧
      let M := (normalizer (![L,residual H] i : Set G)).map (MulAut.conj g).toMonoidHom
      let P := ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H)
      let D : Fin 2 → Subgroup G := fun j => P j ⊓ centralizer ({f.val} : Set G)
      let U : Fin 2 → Subgroup G := fun j => ((pResidual 2 (D j)).map (D j).subtype).pCoreIn 2
      let J := U 0⊔U 1
      centralizer ({f.val} : Set G)≤M ∧
        ∃ hJM : J≤M, Nonempty (J≃*DihedralGroup 4) ∧ Disjoint J (M.pCoreIn 2) ∧
          Function.Injective ((QuotientGroup.mk' (pCore 2 M)).comp (inclusion hJM)) :=
  d.symplectic_outer_fixed_dihedral_normalizer_quotient
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he f hf ho

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

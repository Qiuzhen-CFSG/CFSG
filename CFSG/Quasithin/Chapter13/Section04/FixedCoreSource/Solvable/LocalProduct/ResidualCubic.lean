module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.PairQuotient
public import Theory.GroupTheory.PResidual.CubicCoreQuotient
public import Theory.GroupTheory.PResidual.TwoKernelComparison
public import Theory.SpecificGroups.SymmetricTwoResidual

/-!
# The cubic section of the literal first residual

The five-dimensional core marking identifies C_L(z)/O₂(C_L(z)) with S₃
in the ordinary A₆ row. Normal-subgroup core restriction and functoriality
of O^{3′} identify L₁/O₂(L₁) with O^{3′}(S₃)=A₃, hence give order three.
Transport through the original inclusion H → G then supplies this order
for O²(C_H(V_H))/O₂(O²(C_H(V_H))) when earlier 13.4.4(ii) identifies
that residual with L₁. The residual identity is an explicit earlier-source
input; the cubic-order premise is constructed here.

The actual larger-kernel application is in `LargerSelection`.
Source: Aschbacher–Smith 13.4.4(2) and 13.4.8, printed pp.897 and904–905.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The five-dimensional marking identifies the literal first residual's
intrinsic two-core quotient as a group of order three in the ordinary row. -/
theorem firstCentralizerResidual_core_quotient_card
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hcore : IsPGroup 2 (centralCore L)) (z : V)
    (hz : z.val ∉ centralizer (L : Set G)) :
    Nat.card (firstCentralizerResidual L z.val ⧸
      pCore 2 (firstCentralizerResidual L z.val)) = 3 := by
  let C := L ⊓ centralizer ({z.val} : Set G)
  obtain ⟨e⟩ := component_centralizer_quotient D m hcore z hz
  let R := primeToResidual 3 C
  let em : R ≃* firstCentralizerResidual L z.val :=
    (R.equivMapOfInjective C.subtype C.subtype_injective).trans
      (MulEquiv.subgroupCongr (firstCentralizerResidual_eq L z.val).symm)
  let er := primeToResidualCoreQuotientImage (A := C) 3 2
  have hr : (primeToResidual 3 (C ⧸ pCore 2 C)).map e.toMonoidHom =
      primeToResidual 3 (Equiv.Perm (Fin 3)) :=
    map_primeToResidual_of_surjective 3 e.toMonoidHom e.surjective
  let ee := ((primeToResidual 3 (C ⧸ pCore 2 C)).equivMapOfInjective
    e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr hr)
  have hres : primeToResidual 3 (Equiv.Perm (Fin 3)) = alternatingGroup (Fin 3) := by
    apply le_antisymm
    · exact primeToResidual_three_le_twoResidual.trans
        (Equiv.Perm.twoResidual_eq_alternating (Fin 3)).le
    · apply le_primeToResidual_of_isPGroup
      apply IsPGroup.of_card (n := 1)
      rw [nat_card_alternatingGroup,Nat.card_fin]
      rfl
  rw [← Nat.card_congr (QuotientGroup.congr _ _ em (pCore_map_iso 2 em)).toEquiv,
    Nat.card_congr er.toEquiv,Nat.card_congr ee.toEquiv,hres,
    nat_card_alternatingGroup,Nat.card_fin]
  rfl

/-- Earlier 13.4.4(ii)'s residual identity supplies the cubic section of the
actual centralizer kernel, using the original inclusion into G. -/
theorem centralizer_kernel_residual_core_card_of_firstResidual
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hcore : IsPGroup 2 (centralCore L)) (z : V)
    (hz : z.val ∉ centralizer (L : Set G))
    (hres : let H := centralizer ({z.val} : Set G)
      let K := centralizer ((centralizerOmegaOrbit T z.val).subgroupOf H : Set H)
      ((pResidual 2 K).map K.subtype).map H.subtype = firstCentralizerResidual L z.val) :
    let H := centralizer ({z.val} : Set G)
    let K := centralizer ((centralizerOmegaOrbit T z.val).subgroupOf H : Set H)
    let A := (pResidual 2 K).map K.subtype
    Nat.card (A ⧸ pCore 2 A) = 3 := by
  let H := centralizer ({z.val} : Set G)
  let K := centralizer ((centralizerOmegaOrbit T z.val).subgroupOf H : Set H)
  let A := (pResidual 2 K).map K.subtype
  let e : A ≃* firstCentralizerResidual L z.val :=
    (A.equivMapOfInjective H.subtype H.subtype_injective).trans (MulEquiv.subgroupCongr hres)
  change Nat.card (A ⧸ pCore 2 A) = 3
  rw [Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv]
  exact firstCentralizerResidual_core_quotient_card D m hcore z hz

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable

module
public import CFSG.Quasithin.Defs
public import CFSG.KnownSimple.CarrierCatalogue
public import Theory.Mathieu.M22.Properties.TwoRank
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.CubicResidual.TwoCentralizer
public import Theory.GroupAction.PerfectCentralQuotient
import all CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.FullCubicResidual

/-!
# Cubic centralizers cannot contain the Hermitian nine-space

The actual full residual in a cubic centralizer of J₄ is a quasisimple
M₂₂ cover. Its conjugation action descends faithfully to Aut(M₂₂), whose
two-rank is at most five. The kernel of that action on an elementary
subgroup has order at most two by the native full-residual centralizer
bound. Thus every elementary two-subgroup of a cubic centralizer has order
at most 64, and the full pointwise centralizer of a nine-space is three-free.

The SQTK hypothesis is inherited from the original ordinary covering
component by the chosen-module consumer; no independent K-group assertion
about the model is assumed. Proof-only imports reuse the generic full
cubic-residual theorem while preserving the chapter export boundaries.
Source: Aschbacher--Smith 4.2.13, printed p.612, and 8.2.7, p.718,
refs/quasithin.pdf. Native ATLAS facts retain their imported attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin Sporadic.Mathieu
open CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape
open CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
namespace CFSG.Quasithin.Chapter7.NormalizedSource
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private theorem cubic_residual_model
    (hs : IsSQTK KnownSimple.IsKnownSimple Janko4.Model)
    (x : Janko4.Model) (hx : orderOf x = 3) :
    IsQuasisimple (solvableResidual (centralizer ({x} : Set Janko4.Model))) ∧
      Nonempty (((solvableResidual (centralizer ({x} : Set Janko4.Model))) ⧸
        center (solvableResidual (centralizer ({x} : Set Janko4.Model)))) ≃* M22) := by
  obtain ⟨y,hy,hyq,_,_,hq,⟨eq⟩⟩ := cubic_full_residual_of_cover
    (MonoidHom.id Janko4.Model) Function.surjective_id (by simp) (by simp) hs
  obtain ⟨g,hg⟩ := Janko4.LocalStructure.cubic_cyclic_fusion
    (MonoidHom.id Janko4.Model) Function.surjective_id (by simp)
    x (y : Janko4.Model) hx hyq
  let a := MulAut.conj g
  let C := centralizer ({x} : Set Janko4.Model)
  let D := centralizer ({(y : Janko4.Model)} : Set Janko4.Model)
  have hC : C.map a.toMonoidHom = D := by
    change (centralizer ({x} : Set Janko4.Model)).map a.toMonoidHom = D
    rw [←centralizer_closure,←zpowers_eq_closure,map_centralizer_equiv]
    change centralizer ((zpowers x).map a.toMonoidHom : Set Janko4.Model) = D
    rw [hg,zpowers_eq_closure,centralizer_closure]
  let c : C ≃* D := (a.subgroupMap C).trans (MulEquiv.subgroupCongr hC)
  let e : solvableResidual C ≃* solvableResidual D :=
    (c.subgroupMap _).trans (MulEquiv.subgroupCongr
      (map_solvableResidual_eq c.toMonoidHom c.surjective))
  let := hq
  exact ⟨IsQuasisimple.of_mulEquiv e.symm,⟨(centerQuotientCongr e).trans eq⟩⟩

/-- Elementary subgroups in an actual cubic centralizer have order at most 64. -/
theorem hermitian_janko_cubic_elementary_bound
    (hs : IsSQTK KnownSimple.IsKnownSimple Janko4.Model)
    (x : Janko4.Model) (hx : orderOf x = 3)
    (E : Subgroup Janko4.Model) [IsElementaryAbelian 2 E]
    (hE : E ≤ centralizer ({x} : Set Janko4.Model)) : Nat.card E ≤ 64 := by
  let C := centralizer ({x} : Set Janko4.Model)
  let R := solvableResidual C
  obtain ⟨hr,⟨er⟩⟩ := cubic_residual_model hs x hx
  let := hr
  let Ec := E.subgroupOf C
  let eE : Ec ≃* E := subgroupOfEquivOfLe hE
  let : IsElementaryAbelian 2 Ec := IsElementaryAbelian.subgroupOf hE
  let f : C →* MulAut M22 := (MulAut.centralQuotientAction er).comp
    (MulAut.conjNormal : C →* MulAut R)
  have hk : f.ker = centralizer (R : Set C) := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.centralQuotientAction_injective er),
      MulAut.conjNormal_ker_eq_centralizer]
  let a := f.comp Ec.subtype
  let i := C.subtype.comp Ec.subtype
  have hi : Function.Injective i := C.subtype_injective.comp Ec.subtype_injective
  have haK : IsPGroup 2 (a.ker.map i) :=
    ((IsElementaryAbelian.isPGroup 2 Ec).to_subgroup a.ker).map i
  have hK : a.ker.map i ≤ centralizer (R.map C.subtype : Set Janko4.Model) := by
    rintro _ ⟨u,hu,rfl⟩ _ ⟨r,hr,rfl⟩
    have hh : (u : C) ∈ centralizer (R : Set C) := hk ▸ hu
    exact congrArg C.subtype (hh r hr)
  have hker := Janko4.LocalStructure.cubic_residual_two_centralizer_bound x hx
    (a.ker.map i) haK hK
  rw [card_map_of_injective hi] at hker
  have himg : Nat.card a.range ≤ 32 := by
    let : IsElementaryAbelian 2 a.range := IsElementaryAbelian.of_surjective
      a.rangeRestrict a.rangeRestrict_surjective
    exact (primeRank_le_iff_elementary_card_le (MulAut M22)).mp
      m22_automorphism_twoRank_le_five a.range inferInstance
  have hc := a.ker.card_mul_index
  rw [index_ker,Nat.card_congr eE.toEquiv] at hc
  nlinarith

/-- A native elementary nine-space has three-free full pointwise centralizer. -/
theorem hermitian_janko_large_elementary_centralizer_three_free
    (hs : IsSQTK KnownSimple.IsKnownSimple Janko4.Model)
    (E : Subgroup Janko4.Model) [IsElementaryAbelian 2 E]
    (hE : 64 < Nat.card E) : ¬ 3 ∣ Nat.card (centralizer (E : Set Janko4.Model)) := by
  intro hd
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' 3 hd
  have he : E ≤ centralizer ({(x : Janko4.Model)} : Set Janko4.Model) := by
    intro e he
    exact mem_centralizer_singleton_iff.mpr (x.property e he)
  have hb := hermitian_janko_cubic_elementary_bound hs (x : Janko4.Model)
    ((orderOf_coe x).trans hx) E he
  omega

end CFSG.Quasithin.Chapter7.NormalizedSource

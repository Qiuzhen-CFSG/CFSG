module

public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.SupercriticalSource.Residual
public import CFSG.Quasithin.ChapterA.Section04.Modules
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.PCoreImage

/-!
# Faithful signalizer membership for the actual normal residual

A normal two-perfect subgroup P of H normalizes O₂(H), and their
commutator lies in O₂(P). The A.4.8 module comparison therefore embeds
[P, Ω₁Z(O₂(H))] in the intrinsic V(P). A subgroup U of this omega-center
that P moves makes V(P) nontrivial. Characteristic-two inheritance supplies
F*(P)=O₂(P), giving actual faithful signalizer membership.

The final theorem applies to the literal embedded O²-preimage of a normal
subgroup D of H/O₂(H). Thus the A.4.9 use in this part of the source is
discharged by the already proved A.4.8 comparison and normality.

Source: Aschbacher–Smith 13.3.14(d), printed p.892.
-/

public section
open Subgroup

namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality.SupercriticalSource
open ChapterA.Section04

variable {G : Type*} [Group G] [Finite G]

theorem intrinsic_module_ne_bot_of_normal
    (H P U : Subgroup G) (hPH : P ≤ H) [(P.subgroupOf H).Normal]
    (hP : IsPPerfect 2 P) (hU : U ≤ Stellmacher.omegaOneCenterAmbient (H.pCoreIn 2))
    (hm : ⁅U, P⁆ ≠ ⊥) : intrinsicSignalizerModule P ≠ ⊥ := by
  have hHP : H ≤ normalizer (P : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hPH).mp inferInstance
  have hHQ : H ≤ normalizer (H.pCoreIn 2 : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hPQ := hPH.trans hHQ
  have hQP := (pCoreIn_le 2 H).trans hHP
  have hcore : P.pCoreIn 2 ≤ H.pCoreIn 2 := pCoreIn_mono_of_normalizes hPH hHP
  have hc := commutator_le_pCore_of_mutual_normalization P (H.pCoreIn 2)
    (isPGroup_pCoreIn 2 H) hPQ hQP
  have hle : ⁅U, P⁆ ≤ intrinsicSignalizerModule P := by
    rw [commutator_comm]
    apply (commutator_mono le_rfl hU).trans
    rw [← signalizerModule_eq_commutator_omegaCenter]
    exact signalizerModule_le_intrinsicModule P (H.pCoreIn 2) hP hPQ hcore hc
  exact fun hz => hm (le_bot_iff.mp (hle.trans hz.le))

theorem faithful_signalizer_of_normal
    (H P U : Subgroup G) (hH : H ∈ Chapter1.He G)
    (hPH : P ≤ H) [(P.subgroupOf H).Normal]
    (hP : IsPPerfect 2 P) (hU : U ≤ Stellmacher.omegaOneCenterAmbient (H.pCoreIn 2))
    (hm : ⁅U, P⁆ ≠ ⊥) : IsFaithfulSignalizerType P := by
  have hne : P ≠ ⊥ := by intro he; exact hm (by rw [he, commutator_bot_right])
  have hHe := Chapter1.lemma_1_1_3_1 hH hne hPH
    (inferInstance : (P.subgroupOf H).Normal).isSubnormal
  exact ⟨⟨hne, hP, Theory.GroupTheory.generalizedFitting_eq_pCore_of_selfCentralizing 2
    (Chapter1.mem_He_iff.mp hHe)⟩, intrinsic_module_ne_bot_of_normal H P U hPH hP hU hm⟩

theorem star_residual_faithful
    (H U : Subgroup G) (D : Subgroup (Star H)) [D.Normal]
    (hH : H ∈ Chapter1.He G) (hU : U ≤ Stellmacher.omegaOneCenterAmbient (H.pCoreIn 2))
    (hm : ⁅U, (starResidual H D).map H.subtype⁆ ≠ ⊥) :
    IsFaithfulSignalizerType ((starResidual H D).map H.subtype) := by
  let P := (starResidual H D).map H.subtype
  let : (starResidual H D).Normal := starResidual_normal H D
  let : (P.subgroupOf H).Normal := by
    have he : P.subgroupOf H = starResidual H D := by
      ext x
      change (x : G) ∈ (starResidual H D).map H.subtype ↔ x ∈ starResidual H D
      constructor
      · rintro ⟨y, hy, he⟩
        exact (Subtype.ext he : y = x) ▸ hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    rw [he]
    infer_instance
  let e := (starResidual H D).equivMapOfInjective H.subtype H.subtype_injective
  exact faithful_signalizer_of_normal H P U hH (map_subtype_le _)
    ((starResidual_isPPerfect H D).of_surjective e.toMonoidHom e.surjective) hU hm

end CFSG.Quasithin.Chapter13.Section03.Noncentrality.SupercriticalSource

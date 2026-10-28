module

public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.LocalSubgroups
public import Theory.GroupTheory.SmallNonabelianTwoGroupFiveExclusion
public import Theory.Frattini.QuadraticCentralizer
public import Theory.ElementaryAbelian.Injective
public import Theory.ElementaryAbelian.ExtraspecialEquiv
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Terminal core exclusions for Chapter 11

The elementary branch's dihedral-ten candidate is excluded by the actual
extraspecial two-core and its elementary seed Zα ∩ Qβ. Cardinality transports
the obstruction to the literal quotient of Lβ by its intersection with Qβ.
The two-seed variant first identifies the core by containment and cardinality.

For the nonelementary branch, a commutator bound in Zα puts Φ(Qα) in Qβ
using the centralizer inside the common Sylow subgroup. The second isomorphism
theorem then makes the actual S/Qβ elementary. This is the terminal
contradiction in the Suzuki candidate after its two-seed core identity and
commutator bound have been established.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(11.7)--(11.8), printed pp.174--176. Both statements split on S/Qβ, not S/Qα.
The hypotheses supplying the earlier (11.3)--(11.6) structure remain explicit
here; these local deductions alone do not establish the Chapter 11 profiles.
-/

public section

open Subgroup

namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile

/-- The order-32 extraspecial core with its actual elementary eight excludes
the marked dihedral-ten quotient. P is the finite vertex stabilizer Gβ;
for Qβ ≤ Lβ the quotient below is exactly the printed Lβ/Qβ. -/
theorem beta_quotient_not_dihedralTen
    {P : Type*} [Group P] [Finite P]
    (Zα Lβ : Subgroup P) [IsElementaryAbelian 2 Zα]
    [IsExtraspecial 2 (pCore 2 P)]
    (hcore : Nat.card (pCore 2 P) = 32)
    (hseed : Nat.card (Zα ⊓ pCore 2 P : Subgroup P) = 8)
    (hself : centralizer (pCore 2 P : Set P) ≤ pCore 2 P) :
    ¬ Nonempty ((Lβ ⧸ (pCore 2 P).subgroupOf Lβ) ≃* DihedralGroup 5) := by
  let Q := pCore 2 P
  let E := (Zα ⊓ Q).subgroupOf Q
  let : IsElementaryAbelian 2 (Zα ⊓ Q : Subgroup P) :=
    IsElementaryAbelian.of_injective (inclusion inf_le_left) (inclusion_injective _)
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf inf_le_right
  have hE : Nat.card E = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe
      (show Zα ⊓ Q ≤ Q from inf_le_right)).toEquiv).trans hseed
  have hfive := SmallNonabelianTwoGroup.not_five_dvd_card_of_selfCentralizing_extraspecial
    Q hcore E inferInstance hE hself
  rintro ⟨e⟩
  have hcard : Nat.card (Lβ ⧸ Q.subgroupOf Lβ) = 10 := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  exact hfive ((show 5 ∣ Nat.card (Lβ ⧸ Q.subgroupOf Lβ) by rw [hcard]; decide).trans
    ((Q.subgroupOf Lβ).card_quotient_dvd_card.trans Lβ.card_subgroup_dvd_card))

/-- Apply the dihedral obstruction when the extraspecial group supplied by
(11.3) is the two-seed V: its order identifies it with the literal core first. -/
theorem beta_quotient_not_dihedralTen_of_pairSpan
    {P : Type*} [Group P] [Finite P]
    (Zα Zα₂ Lβ : Subgroup P) [IsElementaryAbelian 2 Zα]
    [IsExtraspecial 2 (pairSpan Zα Zα₂ (pCore 2 P))]
    (hcore : Nat.card (pCore 2 P) = 32)
    (hpair : Nat.card (pairSpan Zα Zα₂ (pCore 2 P)) = 32)
    (hseed : Nat.card (Zα ⊓ pCore 2 P : Subgroup P) = 8)
    (hself : centralizer (pCore 2 P : Set P) ≤ pCore 2 P) :
    ¬ Nonempty ((Lβ ⧸ (pCore 2 P).subgroupOf Lβ) ≃* DihedralGroup 5) := by
  have heq := pairSpan_eq_core_of_card Zα Zα₂ (pCore 2 P) (hpair.trans hcore.symm)
  let : IsExtraspecial 2 (pCore 2 P) :=
    IsExtraspecial.of_mulEquiv (MulEquiv.subgroupCongr heq) inferInstance
  exact beta_quotient_not_dihedralTen Zα Lβ hcore hseed hself

private theorem core_card_of_dihedralTen_quotient
    {P : Type*} [Group P] [Finite P] (L : Subgroup P)
    (hQL : pCore 2 P ≤ L) (S : Sylow 2 L) (hS : Nat.card S = 64)
    (e : (L ⧸ (pCore 2 P).subgroupOf L) ≃* DihedralGroup 5) :
    Nat.card (pCore 2 P) = 32 := by
  let Q := (pCore 2 P).subgroupOf L
  let f := e.toMonoidHom.comp (QuotientGroup.mk' Q)
  have hf : Function.Surjective f :=
    e.surjective.comp (QuotientGroup.mk'_surjective Q)
  have hk : f.ker = Q := by
    ext x
    change e (QuotientGroup.mk' Q x) = 1 ↔ x ∈ Q
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  let T := S.mapSurjective hf
  have hT : Nat.card T = 2 := by
    rw [T.card_eq_multiplicity, DihedralGroup.nat_card]
    decide +kernel
  have hQp : IsPGroup 2 Q := pCore_isPGroup.comap_subtype
  have hQS : Q ≤ (S : Subgroup L) := hQp.le_sylow_of_normal S
  have hcount := (Q.subgroupOf (S : Subgroup L)).card_mul_index
  change Nat.card (Q.subgroupOf (S : Subgroup L)) * Q.relIndex (S : Subgroup L) =
    Nat.card S at hcount
  rw [Nat.card_congr (subgroupOfEquivOfLe hQS).toEquiv, ← hk,
    relIndex_ker] at hcount
  change Nat.card f.ker * Nat.card T = Nat.card S at hcount
  rw [hk, hT, hS] at hcount
  have hQc : Nat.card Q = 32 := by omega
  exact (Nat.card_congr (subgroupOfEquivOfLe hQL).toEquiv).symm.trans hQc

/-- In the binary dihedral candidate, the actual Sylow order 64 and marked
quotient force core order 32. Thus no independent core-order premise is needed.
The source obtains 64 from the earlier order formula with (qα,qβ) = (4,2). -/
theorem beta_quotient_not_dihedralTen_of_sylow64
    {P : Type*} [Group P] [Finite P]
    (Zα Zα₂ Lβ : Subgroup P) [IsElementaryAbelian 2 Zα]
    [IsExtraspecial 2 (pairSpan Zα Zα₂ (pCore 2 P))]
    (hQL : pCore 2 P ≤ Lβ) (S : Sylow 2 Lβ) (hS : Nat.card S = 64)
    (hpair : Nat.card (pairSpan Zα Zα₂ (pCore 2 P)) = 32)
    (hseed : Nat.card (Zα ⊓ pCore 2 P : Subgroup P) = 8)
    (hself : centralizer (pCore 2 P : Set P) ≤ pCore 2 P) :
    ¬ Nonempty ((Lβ ⧸ (pCore 2 P).subgroupOf Lβ) ≃* DihedralGroup 5) := by
  rintro ⟨e⟩
  have hcore := core_card_of_dihedralTen_quotient Lβ hQL S hS e
  exact beta_quotient_not_dihedralTen_of_pairSpan Zα Zα₂ Lβ hcore hpair hseed hself ⟨e⟩

/-- The exact quotient S/Qβ becomes elementary from the quadratic core bound.
The centralizer and normality hypotheses are relative to S. -/
theorem beta_quotient_elementary_of_core_commutator
    {G : Type*} [Group G]
    (Qα Qβ Zα S : Subgroup G) [Finite Qα] [IsElementaryAbelian 2 Zα]
    [(Qβ.subgroupOf S).Normal]
    (hQα : IsPGroup 2 Qα) (hS : S = Qα ⊔ Qβ)
    (hn : Qα ≤ normalizer (Qβ : Set G))
    (hcomm : ⁅Qα, Qβ⁆ ≤ Zα) (hcentral : Qα ≤ centralizer (Zα : Set G))
    (hself : S ⊓ centralizer (Qβ : Set G) ≤ Qβ) :
    IsElementaryAbelian 2 (S ⧸ Qβ.subgroupOf S) := by
  have hphiC := frattini_image_le_centralizer_of_elementary_commutator
    Qα Qβ Zα hQα hcomm hcentral
  have hphiS : (frattini Qα).map Qα.subtype ≤ S :=
    (map_subtype_le _).trans (hS ▸ le_sup_left)
  have hphi : (frattini Qα).map Qα.subtype ≤ Qβ :=
    (le_inf hphiS hphiC).trans hself
  subst S
  exact elementary_sup_quotient_of_frattini_image_le Qα Qβ hQα hn hphi

/-- The two-seed identity and (11.3)'s commutator bound contradict the
nonelementary S/Qβ branch. These are the precise local consequences that
the Suzuki candidate must supply before this exclusion can be applied. -/
theorem nonElementary_beta_excludes_pairSpan_core
    {G : Type*} [Group G]
    (Qα Qβ Zα Zα₂ S : Subgroup G) [Finite Qα] [IsElementaryAbelian 2 Zα]
    [(Qβ.subgroupOf S).Normal]
    (hQα : IsPGroup 2 Qα) (hS : S = Qα ⊔ Qβ)
    (hn : Qα ≤ normalizer (Qβ : Set G))
    (hpair : Qβ = pairSpan Zα Zα₂ Qβ)
    (hcomm : ⁅Qα, pairSpan Zα Zα₂ Qβ⁆ ≤ Zα)
    (hcentral : Qα ≤ centralizer (Zα : Set G))
    (hself : S ⊓ centralizer (Qβ : Set G) ≤ Qβ)
    (hne : ¬ IsElementaryAbelian 2 (S ⧸ Qβ.subgroupOf S)) : False := by
  apply hne
  exact beta_quotient_elementary_of_core_commutator Qα Qβ Zα S hQα hS hn
    (hpair.symm ▸ hcomm) hcentral hself

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile

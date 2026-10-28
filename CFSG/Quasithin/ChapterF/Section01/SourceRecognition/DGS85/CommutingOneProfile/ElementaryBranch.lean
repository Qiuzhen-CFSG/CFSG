module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SeedStructure
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.CoreExclusions
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The seed count and dihedral exclusion in the elementary branch

The original center has order qα qβ² and its intersection with Qβ has
index qβ. Conjugating that seed inside the beta vertex group and using
intersection order qβ gives |V| = qα² qβ. If V is the beta core and
S = Zα Qβ, the subgroup product formula gives |S| = qα² qβ².

At (qα,qβ) = (4,2), this constructs the actual elementary eight and a
nonabelian core of order 32. The existing automorphism obstruction excludes
the literal dihedral-ten quotient. The proof only needs V' nontrivial;
the stronger extraspecial classification is unnecessary for this exclusion.

These are deductions from the earlier seed geometry. Establishing that
geometry and Qα = Zα from Hypothesis B-prime is still required; this module
does not assert full (11.7) or identify a marked unitary amalgam.
Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(11.3), (11.6), and (11.7), printed pp.168--175.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile

private theorem seed_normalizes {G : Type*} [Group G] (Q Z : Subgroup G)
    (hn : Q ≤ normalizer (Z : Set G)) :
    Q ≤ normalizer ((Z ⊓ Q : Subgroup G) : Set G) :=
  (le_inf hn Q.le_normalizer).trans inf_normalizer_le_normalizer_inf

private theorem conjugate_seed_card
    {P : Type*} [Group P] (Q Z Z' : Subgroup P) (g : P)
    (hQ : Q.map (MulAut.conj g).toMonoidHom = Q)
    (hconj : Z.map (MulAut.conj g).toMonoidHom = Z') :
    Nat.card (Z' ⊓ Q : Subgroup P) = Nat.card (Z ⊓ Q : Subgroup P) := by
  have hm : (Z ⊓ Q).map (MulAut.conj g).toMonoidHom = Z' ⊓ Q := by
    rw [map_inf _ _ _ (MulAut.conj g).injective,hconj]
    exact congrArg (Z' ⊓ ·) hQ
  rw [← hm]
  exact card_map_of_injective (MulAut.conj g).injective

/-- The literal pair order from the conjugate seed, its relative index, and
its intersection. The conjugating element preserves the specified beta core. -/
theorem pairSpan_card_of_seed_index
    {P : Type*} [Group P] [Finite P] (Qβ Zα Zα₂ : Subgroup P)
    (g : P) (hQ : Qβ.map (MulAut.conj g).toMonoidHom = Qβ)
    (hconj : Zα.map (MulAut.conj g).toMonoidHom = Zα₂)
    (hn : Qβ ≤ normalizer (Zα : Set P))
    (qα qβ : ℕ) (hqβ : 0 < qβ)
    (hZ : Nat.card Zα = qα * qβ ^ 2)
    (hindex : (Zα ⊓ Qβ).relIndex Zα = qβ)
    (hinter : Nat.card ((Zα ⊓ Qβ) ⊓ (Zα₂ ⊓ Qβ) : Subgroup P) = qβ) :
    Nat.card (Zα ⊓ Qβ : Subgroup P) = qα * qβ ∧
      Nat.card (pairSpan Zα Zα₂ Qβ) = qα ^ 2 * qβ := by
  have hcount := relIndex_mul_relIndex (⊥ : Subgroup P) (Zα ⊓ Qβ) Zα
    bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,hindex,hZ] at hcount
  have hseed : Nat.card (Zα ⊓ Qβ : Subgroup P) = qα * qβ := by
    apply Nat.eq_of_mul_eq_mul_right hqβ
    exact hcount.trans (by ring)
  have hseed' := (conjugate_seed_card Qβ Zα Zα₂ g hQ hconj).trans hseed
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (Zα ⊓ Qβ) (Zα₂ ⊓ Qβ)
    (inf_le_right.trans (seed_normalizes _ _ hn))
  rw [hseed,hseed',hinter] at hprod
  refine ⟨hseed,?_⟩
  apply Nat.eq_of_mul_eq_mul_left hqβ
  exact hprod.symm.trans (by ring)

/-- The order assertion of (11.7)(c) once its preceding core and supplement
identities have been established, using the original seed and conjugation. -/
theorem sylow_card_of_pair_core
    {P : Type*} [Group P] [Finite P] (Qβ Zα Zα₂ S : Subgroup P)
    (g : P) (hQ : Qβ.map (MulAut.conj g).toMonoidHom = Qβ)
    (hconj : Zα.map (MulAut.conj g).toMonoidHom = Zα₂)
    (hn : Qβ ≤ normalizer (Zα : Set P))
    (hcore : Qβ = pairSpan Zα Zα₂ Qβ)
    (hS : S = Zα ⊔ Qβ)
    (qα qβ : ℕ) (hqα : 0 < qα) (hqβ : 0 < qβ)
    (hZ : Nat.card Zα = qα * qβ ^ 2)
    (hindex : (Zα ⊓ Qβ).relIndex Zα = qβ)
    (hinter : Nat.card ((Zα ⊓ Qβ) ⊓ (Zα₂ ⊓ Qβ) : Subgroup P) = qβ) :
    Nat.card S = qα ^ 2 * qβ ^ 2 := by
  obtain ⟨hseed,hpair⟩ := pairSpan_card_of_seed_index Qβ Zα Zα₂ g hQ hconj hn
    qα qβ hqβ hZ hindex hinter
  have hQc : Nat.card Qβ = qα ^ 2 * qβ :=
    (congrArg (fun A : Subgroup P => Nat.card A) hcore).trans hpair
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes Zα Qβ hn
  rw [hZ,hQc,hseed,←hS] at hprod
  apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hqα hqβ)
  exact hprod.symm.trans (by ring)

/-- The binary source seeds have orders eight, intersection two, and product 32.
The opposite seed is obtained by the actual vertex-group conjugation. -/
theorem pairSpan_card_binary
    {P : Type*} [Group P] [Finite P] (Zα Zα₂ : Subgroup P)
    (g : P) (hconj : Zα.map (MulAut.conj g).toMonoidHom = Zα₂)
    (hn : pCore 2 P ≤ normalizer (Zα : Set P))
    (hZ : Nat.card Zα = 16)
    (hindex : (Zα ⊓ pCore 2 P).relIndex Zα = 2)
    (hinter : Nat.card ((Zα ⊓ pCore 2 P) ⊓ (Zα₂ ⊓ pCore 2 P) : Subgroup P) = 2) :
    Nat.card (Zα ⊓ pCore 2 P : Subgroup P) = 8 ∧
      Nat.card (pairSpan Zα Zα₂ (pCore 2 P)) = 32 := by
  simpa using pairSpan_card_of_seed_index (pCore 2 P) Zα Zα₂ g
    (Normal.map_conj_eq (pCore 2 P) g) hconj hn 4 2 (by decide)
    (by norm_num; exact hZ) hindex hinter

/-- The binary dihedral candidate is impossible from the earlier seed
geometry. Only noncommutativity of V is needed; no extraspecial premise,
core order, pair order, or elementary-eight order is added. -/
theorem beta_quotient_not_dihedralTen_of_seed_geometry
    {P : Type*} [Group P] [Finite P]
    (Qα Zα Zα₂ Lβ : Subgroup P) [IsElementaryAbelian 2 Zα]
    (g : P) (hconj : Zα.map (MulAut.conj g).toMonoidHom = Zα₂)
    (hn : pCore 2 P ≤ normalizer (Zα : Set P))
    (hQβ : pCore 2 P = pairSpan Zα Zα₂ (pCore 2 P) ⊔ (Qα ⊓ pCore 2 P))
    (hQα : Qα = Zα)
    (hZ : Nat.card Zα = 16)
    (hindex : (Zα ⊓ pCore 2 P).relIndex Zα = 2)
    (hinter : Nat.card ((Zα ⊓ pCore 2 P) ⊓ (Zα₂ ⊓ pCore 2 P) : Subgroup P) = 2)
    (hnoncomm : ⁅pairSpan Zα Zα₂ (pCore 2 P), pairSpan Zα Zα₂ (pCore 2 P)⁆ ≠ ⊥)
    (hself : centralizer (pCore 2 P : Set P) ≤ pCore 2 P) :
    ¬ Nonempty ((Lβ ⧸ (pCore 2 P).subgroupOf Lβ) ≃* DihedralGroup 5) := by
  have hcore := beta_core_eq_pairSpan_of_alpha_core_eq Qα (pCore 2 P) Zα Zα₂ hQβ hQα
  obtain ⟨hseed,hpair⟩ := pairSpan_card_binary Zα Zα₂ g hconj hn hZ hindex hinter
  have hQc : Nat.card (pCore 2 P) = 32 :=
    (congrArg (fun A : Subgroup P => Nat.card A) hcore).trans hpair
  have hnc : ¬ IsMulCommutative (pCore 2 P) := by
    intro hc
    apply hnoncomm
    rw [←hcore]
    exact commutator_self_eq_bot_iff.mpr hc
  let E := (Zα ⊓ pCore 2 P).subgroupOf (pCore 2 P)
  let : IsElementaryAbelian 2 (Zα ⊓ pCore 2 P : Subgroup P) :=
    IsElementaryAbelian.of_injective (inclusion inf_le_left) (inclusion_injective _)
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf inf_le_right
  have hEc : Nat.card E = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe
      (show Zα ⊓ pCore 2 P ≤ pCore 2 P from inf_le_right)).toEquiv).trans hseed
  have hfive := SmallNonabelianTwoGroup.not_five_dvd_card_of_selfCentralizing
    (pCore 2 P) pCore_isPGroup hnc hQc E inferInstance hEc hself
  rintro ⟨e⟩
  have hcard : Nat.card (Lβ ⧸ (pCore 2 P).subgroupOf Lβ) = 10 := by
    rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card]
  exact hfive ((show 5 ∣ Nat.card (Lβ ⧸ (pCore 2 P).subgroupOf Lβ) by rw [hcard]; decide).trans
    (((pCore 2 P).subgroupOf Lβ).card_quotient_dvd_card.trans Lβ.card_subgroup_dvd_card))

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile

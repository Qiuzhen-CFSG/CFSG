module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.Exhaustive
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.SourceAlternatives

/-!
# Actual FF data for the complete Goldschmidt source

The actual representation retains both source classifiers, its offender
subgroup, and the literal Sylow fixed-space condition. All thirteen original
rows and both corrected field extensions bound the ambient Sylow order.
Odd divisors pass to the normal offender because the quotient is a two-group.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
F.6.18, pp.309–310; B.5.1/B.5.6, pp.99–110; 15.4.18, p.1163.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FullSource
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
universe u v
attribute [local instance] offenderSubgroup_normal

structure ClassifiedAction {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (K : GroupClass.{u}) (ρ : Representation (ZMod 2) D V)
    (G₁ G₂ : Subgroup D) where
  faithful : Function.Injective ρ
  twoCore : pCore 2 D = ⊥
  threePrimeCore : pPrimeCore 3 D = ⊥
  triple : ChapterF.IsGoldschmidtTriple G₁ G₂
  core_nontrivial : pCore 2 G₁ ≠ ⊥ ∨ pCore 2 G₂ ≠ ⊥
  sylow : Sylow 2 D
  intersection : G₁ ⊓ G₂ = (sylow : Subgroup D)
  goldschmidt : FSource.SourceAlternative G₁ G₂ sylow ∨
    FSource.SourceAlternative G₂ G₁ sylow
  ffHypothesis : FFHypothesis K (ρ.comp (offenderSubgroup ρ).subtype)
  ffWitness : IsFFModule (ρ.comp (offenderSubgroup ρ).subtype)
  ffAlternatives : FFAlternatives.ProjectiveLine.AdequateSourceAlternative
    (ρ.comp (offenderSubgroup ρ).subtype)
  quotient_twoGroup : IsPGroup 2 (D ⧸ offenderSubgroup ρ)
  sylow_fixedSpace : ∃ S : Sylow 2 D,
    subspaceKernel ρ (fixedSpace ρ (S : Subgroup D)) ⊤ = (S : Subgroup D)

private theorem extension_card {A B C : Type*} [Group A] [Group B] [Group C]
    (h : FSource.Extension A B C) : Nat.card A = Nat.card B * Nat.card C := by
  obtain ⟨N,_,⟨e⟩,⟨f⟩⟩ := h
  rw [card_eq_card_quotient_mul_card_subgroup N, Nat.card_congr e.toEquiv,
    Nat.card_congr f.toEquiv, Nat.mul_comm]

private theorem alternative_sylow_bound {D : Type u} [Group D] [Finite D]
    {G₁ G₂ : Subgroup D} {S : Sylow 2 D} (r : FSource.Alternative G₁ G₂ S) :
    Nat.card S ≤ 128 := by
  cases r with
  | one hs _ _ _ =>
    rw [Nat.card_congr hs.some.toEquiv]; norm_num [FSource.C]
  | two hm =>
    apply (Nat.card_le_card_of_injective (S : Subgroup D).subtype Subtype.val_injective).trans
    rcases hm with he | ⟨N,_,_,hc,_,⟨e⟩⟩
    · obtain ⟨e⟩ := he
      rw [Nat.card_congr e.toEquiv]
      norm_num [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    · rw [card_eq_card_quotient_mul_card_subgroup N, hc, Nat.card_congr e.toEquiv]
      norm_num [FSource.E4, FSource.C, Nat.card_prod]
  | three _ hs _ _ =>
    rw [Nat.card_congr hs.some.toEquiv, DihedralGroup.nat_card]; norm_num
  | five _ _ _ _ _ _ hs _ _ =>
    rw [Nat.card_congr hs.some.toEquiv, DihedralGroup.nat_card]; norm_num
  | six _ _ _ hs _ _ =>
    rw [Nat.card_congr hs.some.toEquiv, DihedralGroup.nat_card]; norm_num
  | seven _ _ hs _ _ =>
    rw [Nat.card_congr hs.some.toEquiv, DihedralGroup.nat_card]; norm_num
  | four _ _ _ _ _ _ hs _ _ =>
    rw [Nat.card_congr hs.some.toEquiv]; norm_num [FSource.E4, FSource.C, Nat.card_prod]
  | eight _ _ hs _ _ | nine _ _ hs _ _ =>
    rw [Nat.card_congr hs.some.toEquiv, Nat.card_prod, DihedralGroup.nat_card]
    norm_num [FSource.C]
  | ten _ _ _ _ _ _ hs _ _ =>
    rw [Nat.card_congr hs.some.toEquiv]
    norm_num [FSource.W32, FSource.C, RegularWreathProduct.card]
  | eleven _ _ hs _ _ | twelve _ _ hs _ _ =>
    rw [extension_card hs]; norm_num [FSource.C4Square, FSource.E4, FSource.C, Nat.card_prod]
  | thirteen _ _ _ hs _ _ =>
    rw [extension_card hs, DihedralGroup.nat_card]
    norm_num [FSource.C4Square, FSource.C, Nat.card_prod]

private theorem source_sylow_bound {D : Type u} [Group D] [Finite D]
    {G₁ G₂ : Subgroup D} {S : Sylow 2 D} (r : FSource.SourceAlternative G₁ G₂ S) :
    Nat.card S ≤ 128 := by
  rcases r with (r | hr) | hr
  · exact alternative_sylow_bound r
  · obtain ⟨r⟩ := hr
    rw [Nat.card_congr r.sylow.some.toEquiv, DihedralGroup.nat_card]; norm_num
  · obtain ⟨r⟩ := hr
    rw [Nat.card_congr r.sylow.some.toEquiv, Nat.card_prod, DihedralGroup.nat_card]
    norm_num [FSource.C]

variable {D : Type u} [Group D] [Finite D] {K : GroupClass.{u}}
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {G₁ G₂ : Subgroup D}
attribute [local instance] offenderSubgroup_normal

theorem ClassifiedAction.sylow_card_le (h : ClassifiedAction K ρ G₁ G₂)
    (S : Sylow 2 D) : Nat.card S ≤ 128 := by
  rw [Nat.card_congr (S.equiv h.sylow).toEquiv]
  exact h.goldschmidt.elim source_sylow_bound source_sylow_bound

theorem ClassifiedAction.bounded_branch (h : ClassifiedAction K ρ G₁ G₂)
    (hq : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    (c : FFAlternatives.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp (offenderSubgroup ρ).subtype) (generalizedFitting (offenderSubgroup ρ))) :
    Nonempty (QuasisimpleComparison.BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype)) := by
  obtain ⟨hm,ha⟩ := QuasisimpleComparison.projectiveLine_bounded_actor h.sylow_card_le
    (offenderSubgroup ρ).subtype Subtype.val_injective _ hq c
  exact ⟨⟨hq,c,hm,ha⟩⟩

theorem ClassifiedAction.odd_dvd_offender_card_iff
    (h : ClassifiedAction K ρ G₁ G₂) {m : ℕ} (hm : Odd m) :
    m ∣ Nat.card (offenderSubgroup ρ) ↔ m ∣ Nat.card D := by
  constructor
  · exact fun hd => hd.trans (offenderSubgroup ρ).card_subgroup_dvd_card
  · intro hd
    obtain ⟨k,hk⟩ := h.quotient_twoGroup.exists_card_eq
    have he : Nat.card D = Nat.card (offenderSubgroup ρ) * 2 ^ k := by
      rw [← hk, ← Subgroup.index_eq_card, Subgroup.card_mul_index]
    rw [he] at hd
    exact ((Nat.coprime_two_right.mpr hm).pow_right k).dvd_of_dvd_mul_right hd

theorem ClassifiedAction.rankOne_not_odd_prime_cube (h : ClassifiedAction K ρ G₁ G₂)
    (ha : QuasisimpleComparison.ActorPruning.RankOneActorModel (offenderSubgroup ρ))
    {p : ℕ} (hp : p.Prime) (hne : p ≠ 2) : ¬ p ^ 3 ∣ Nat.card D := by
  intro hd
  exact ha.not_odd_prime_cube hp hne
    ((h.odd_dvd_offender_card_iff ((hp.odd_of_ne_two hne).pow)).mpr hd)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FullSource

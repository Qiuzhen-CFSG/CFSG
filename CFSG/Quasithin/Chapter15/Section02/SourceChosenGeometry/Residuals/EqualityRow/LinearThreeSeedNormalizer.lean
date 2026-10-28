module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.LinearThreeSeedFactors
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EscapingReductions
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.Seeds
public import CFSG.Quasithin.Chapter1.Section01Inheritance

/-!
# The canonical-seed normalizer argument on the original plane

A two-perfect seed inside NI with an S₃ quotient lies outside MI when
C_M(V) is three-prime. If the seed mutually normalizes the opposite cubic
factor, the four original generators form mutually normalizing conjugates.
Characteristic two gives their join a nontrivial two-core. The join with T
contains H, hence lies in its unique maximal two-local overgroup Mc,
contradicting the seed's escape.

The seed remains two-perfect, not a two-group, and both NI and MI retain
the original embeddings. This supplies the canonical-seed consumer of the
actual residual pair without a partner residual identity.
Source: Aschbacher--Smith, 15.2.22, printed pp.1114--1115,
refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.ResidualInput
open SmallActionsSource
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Index two transports S-invariance to the second factor. -/
private theorem pair_second_normalized {A S K : Subgroup G} {t : G}
    (p : ResidualPair A S K t) (hSA : S ≤ A) (hi : S.relIndex A = 2) :
    S ≤ normalizer (p.K₂ : Set G) := by
  rw [← p.conjugate]
  exact normalizes_conjugate_of_normalizes
    (((normal_subgroupOf_iff_le_normalizer hSA).mp (normal_of_index_eq_two hi)) p.t_mem)
    p.normalized

omit [Finite G] in
private def pairAsSplit {A S K : Subgroup G} {t : G}
    (p : ResidualPair A S K t) (hSA : S ≤ A) (hi : S.relIndex A = 2) :
    SmallActionSplit A S K where
  H₁ := p.K₁ ⊔ S
  H₂ := p.K₂ ⊔ S
  K₁ := p.K₁
  K₂ := p.K₂
  t := t
  t_mem := p.t_mem
  t_not_mem := p.t_not_mem
  K_sup_S := by rw [sup_sup_sup_comm, sup_idem, p.span]
  K₁_sup_K₂ := p.span
  K₁_le := p.first.1
  K₂_le := p.second.1
  K₁_conj := p.conjugate
  S_normalizes_K₁ := p.normalized
  S_normalizes_K₂ := pair_second_normalized p hSA hi

variable {T : Sylow 2 G} {M Mc V H B I Y : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (r : ResidualInput hsource H B)
include r

/-- A two-perfect subgroup of NI lying in MI centralizes V by 15.2.14(5). -/
theorem seed_le_module_centralizer_of_le_MI
    (s : Seed M I (smallActionS T (⁅V,B⁆ : Subgroup G)) Y) (hY : Y ≤ Mc ⊓ I) :
    Y ≤ M ⊓ centralizer (V : Set G) := by
  have hYA : Y ≤ M ⊓ Mc := le_inf (s.le_NI.trans inf_le_left) (hY.trans inf_le_left)
  have hm := embedded_pResidual_mono 2 hYA
  rw [(pResidual_eq_top_iff 2 Y).mpr s.perfect, ← MonoidHom.range_eq_map, range_subtype] at hm
  exact hm.trans r.partner_intersection_residual_le_module_centralizer

/-- In 15.2.22, the three-prime centralizer forces Y₁ outside MI.
Thus the missing containment hypothesis of 15.2.21(3) is derived when
needed, without ever treating Y₁ as a two-group. -/
theorem seed_not_le_MI (s : Seed M I (smallActionS T (⁅V,B⁆ : Subgroup G)) Y)
    (hC : IsSmallActionThreePrime (M ⊓ centralizer (V : Set G))) :
    ¬ Y ≤ Mc ⊓ I := by
  intro hY
  have hCcard : Nat.Coprime 3 (Nat.card (M ⊓ centralizer (V : Set G) : Subgroup G)) := by
    have hh := primeToResidual_index_coprime (G := (M ⊓ centralizer (V : Set G) : Subgroup G)) 3
    change primeToResidual 3 (M ⊓ centralizer (V : Set G) : Subgroup G) = ⊥ at hC
    rwa [hC, index_bot] at hh
  have hYcard := hCcard.coprime_dvd_right
    (card_dvd_of_le (r.seed_le_module_centralizer_of_le_MI s hY))
  have hScard : Nat.Coprime 3 (Nat.card (smallActionS T (⁅V,B⁆ : Subgroup G))) := by
    obtain ⟨n, hn⟩ := (T.isPGroup'.to_le
      (show smallActionS T (⁅V,B⁆ : Subgroup G) ≤ (T : Subgroup G) from inf_le_left)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hprod := hYcard.mul_right hScard
  rw [card_mul_eq_card_inf_mul_card_sup_of_normalizes Y (smallActionS T (⁅V,B⁆ : Subgroup G))
    s.normalized] at hprod
  have hq := hprod.coprime_dvd_right
    (dvd_mul_left (Nat.card (Y ⊔ smallActionS T (⁅V,B⁆ : Subgroup G) : Subgroup G))
      (Nat.card (Y ⊓ smallActionS T (⁅V,B⁆ : Subgroup G) : Subgroup G)))
  have hquot := hq.coprime_dvd_right
    (card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 (Y ⊔ smallActionS T (⁅V,B⁆ : Subgroup G) : Subgroup G)))
      (QuotientGroup.mk'_surjective _))
  obtain ⟨e⟩ := s.quotient
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin] at hquot
  norm_num at hquot
/-- The local normalizer argument of 15.2.22: a nontrivial S-invariant X
and its mutually normalizing conjugate generate a subgroup of Mc whenever
they contain K. Nontriviality of the core is proved using characteristic two. -/
theorem conjugate_pair_le_partner (hI : PlaneEscapes Mc (⁅V,B⁆ : Subgroup G) I)
    (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup G} (hX : X ≠ ⊥) (hXI : X ≤ I)
    (hSX : smallActionS T (⁅V,B⁆ : Subgroup G) ≤ normalizer (X : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htS : t ∉ smallActionS T (⁅V,B⁆ : Subgroup G))
    (hpair : X.map (MulAut.conj t).toMonoidHom ≤ normalizer (X : Set G))
    (hK : smallActionK H ≤ X ⊔ X.map (MulAut.conj t).toMonoidHom) :
    X ⊔ X.map (MulAut.conj t).toMonoidHom ≤ Mc := by
  let S := smallActionS T (⁅V,B⁆ : Subgroup G)
  let D := X ⊔ X.map (MulAut.conj t).toMonoidHom
  have hSI : S ≤ I :=
    (le_sup_right.trans (r.residual_sup_planeCentralizer_le hI)).trans inf_le_right
  have hIHe : I ∈ Chapter1.He G := by
    apply Chapter1.mem_He_iff.mpr
    simpa only [hfit] using centralizer_generalizedFitting_le I
  have hXSHe : X ⊔ S ∈ Chapter1.He G :=
    Chapter1.lemma_1_1_4_4 (fun he => hX (bot_unique (le_sup_left.trans_eq he)))
      (sup_le hXI hSI) hIHe
      (inf_le_left.trans ((r.core_le_plane hI).trans le_sup_right))
  have hXnorm : (X.subgroupOf (X ⊔ S)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le X.le_normalizer hSX)
  have hXHe : X ∈ Chapter1.He G :=
    Chapter1.lemma_1_1_3_1 hXSHe hX le_sup_left hXnorm.isSubnormal
  have hXcore : X.pCoreIn 2 ≠ ⊥ := by
    intro he
    apply hX
    change X ⊓ centralizer (X.pCoreIn 2 : Set G) ≤ X.pCoreIn 2 at hXHe
    have hc : centralizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
      centralizer_eq_top_iff_subset.mpr (show (⊥ : Subgroup G) ≤ center G from bot_le)
    rw [he, hc, inf_top_eq] at hXHe
    exact bot_unique hXHe
  have hTD : (T : Subgroup G) ≤ normalizer (D : Set G) := by
    simpa only [inv_inv] using
      index_two_normalizes_pair S (T : Subgroup G) X inf_le_left
        (r.escape_index hI).2 t⁻¹ ((T : Subgroup G).inv_mem ht)
        (by simpa only [inv_mem_iff] using htS) hSX
  have hcoreD : X.pCoreIn 2 ≤ D.pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left (sup_le X.le_normalizer hpair)
  have hcoreDT : D.pCoreIn 2 ≤ (D ⊔ (T : Subgroup G)).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left (sup_le D.le_normalizer hTD)
  have hne : pCore 2 (D ⊔ (T : Subgroup G) : Subgroup G) ≠ ⊥ := by
    intro he
    apply hXcore
    apply bot_unique
    simpa only [pCoreIn, he, Subgroup.map_bot] using hcoreD.trans hcoreDT
  obtain ⟨N, hN, hDN⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot
    (D ⊔ (T : Subgroup G)) hne
  have hHN : H ≤ N := by
    rw [← r.residual_join]
    exact (sup_le_sup_right hK _).trans hDN
  have hNMc : N = Mc :=
    source_chosen_HStar_unique r.outside r.two_overgroups N hN hHN
  exact (le_sup_left.trans hDN).trans_eq hNMc

/-- Expand the normalizer step on the actual four generators Y₁,K₁,Y₁ᵗ,K₂.
The two same-family commutator relations are retained as local geometric
inputs; no normalizer bound or contradiction is assumed. -/
theorem not_commutator_le_inf_of_conjugate_pair
    (hI : PlaneEscapes Mc (⁅V,B⁆ : Subgroup G) I) (hfit : generalizedFitting I = pCore 2 I)
    (split : SmallActionSplit (T : Subgroup G) (smallActionS T (⁅V,B⁆ : Subgroup G)) (smallActionK H))
    {Y : Subgroup G} (hYI : Y ≤ I) (hYout : ¬ Y ≤ Mc ⊓ I)
    (hSY : smallActionS T (⁅V,B⁆ : Subgroup G) ≤ normalizer (Y : Set G))
    (hYY : ⁅Y, Y.map (MulAut.conj split.t).toMonoidHom⁆ ≤
      Y ⊓ Y.map (MulAut.conj split.t).toMonoidHom)
    (hKK : ⁅split.K₁, split.K₂⁆ ≤ split.K₁ ⊓ split.K₂) :
    ¬ ⁅Y, split.K₂⁆ ≤ Y ⊓ split.K₂ := by
  intro hYK
  let f := (MulAut.conj split.t).toMonoidHom
  have ht2 : split.t ^ 2 ∈ smallActionS T (⁅V,B⁆ : Subgroup G) :=
    ((smallActionS T (⁅V,B⁆ : Subgroup G)).subgroupOf (T : Subgroup G)).sq_mem_of_index_two
      (r.escape_index hI).2 ⟨split.t, split.t_mem⟩
  have hK₂conj : split.K₂.map f = split.K₁ := by
    rw [← split.K₁_conj]
    change (split.K₁.conjBy split.t).conjBy split.t = split.K₁
    rw [conjBy_conjBy, ← pow_two]
    exact mem_normalizer_iff_map_conj_eq.mp (split.S_normalizes_K₁ ht2)
  have hYtK : ⁅Y.map f, split.K₁⁆ ≤ Y.map f ⊓ split.K₁ := by
    have hm := map_mono (f := f) hYK
    rwa [map_commutator, map_inf _ _ _ (MulAut.conj split.t).injective, hK₂conj] at hm
  let X := Y ⊔ split.K₁
  have hXmap : X.map f = Y.map f ⊔ split.K₂ := by
    rw [show X = Y ⊔ split.K₁ from rfl, Subgroup.map_sup, split.K₁_conj]
  have hpair : X.map f ≤ normalizer (X : Set G) := by
    rw [hXmap]
    apply sup_le
    · exact (le_inf
        (le_normalizer_iff_commutator_le_left.mpr (hYY.trans inf_le_left))
        (le_normalizer_iff_commutator_le_right.mpr (hYtK.trans inf_le_right))).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · exact (le_inf
        (le_normalizer_iff_commutator_le_left.mpr (hYK.trans inf_le_left))
        (le_normalizer_iff_commutator_le_left.mpr (hKK.trans inf_le_left))).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hXI : X ≤ I := sup_le hYI (split.K₁_le.trans
    ((le_sup_left.trans (r.residual_sup_planeCentralizer_le hI)).trans inf_le_right))
  have hSX : smallActionS T (⁅V,B⁆ : Subgroup G) ≤ normalizer (X : Set G) :=
    (le_inf hSY split.S_normalizes_K₁).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hXne : X ≠ ⊥ := by
    intro he
    apply hYout
    have hY : Y ≤ ⊥ := le_sup_left.trans_eq he
    exact hY.trans bot_le
  have hK : smallActionK H ≤ X ⊔ X.map f := by
    rw [← split.K₁_sup_K₂]
    exact sup_le (le_sup_right.trans le_sup_left)
      (le_sup_right.trans (hXmap.ge.trans le_sup_right))
  have hle := r.conjugate_pair_le_partner hI hfit hXne hXI hSX
    split.t_mem split.t_not_mem hpair hK
  exact hYout (le_inf ((le_sup_left.trans le_sup_left).trans hle) hYI)
/-- The actual pair's normality discharges the residual-factor commutator
in the conjugate normalizer argument. -/
theorem commutator_exclusion_of_residualPair
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hfit : generalizedFitting I = pCore 2 I) {t : G}
    (p : ResidualPair (T : Subgroup G) (smallActionS T ⁅V,B⁆) (smallActionK H) t)
    {Y : Subgroup G} (seed : Seed M I (smallActionS T ⁅V,B⁆) Y)
    (hC : IsSmallActionThreePrime (M ⊓ centralizer (V : Set G)))
    (hYY : ⁅Y,Y.map (MulAut.conj t).toMonoidHom⁆ ≤
      Y ⊓ Y.map (MulAut.conj t).toMonoidHom) :
    ¬ ⁅Y,p.K₂⁆ ≤ Y ⊓ p.K₂ := by
  have hKK : ⁅p.K₁,p.K₂⁆ ≤ p.K₁ ⊓ p.K₂ :=
    le_inf
      (le_normalizer_iff_commutator_le_left.mp
        (p.second.1.trans ((normal_subgroupOf_iff_le_normalizer p.first.1).mp p.first.2.1)))
      (le_normalizer_iff_commutator_le_right.mp
        (p.first.1.trans ((normal_subgroupOf_iff_le_normalizer p.second.1).mp p.second.2.1)))
  exact r.not_commutator_le_inf_of_conjugate_pair hI hfit
    (pairAsSplit p inf_le_left (r.escape_index hI).2)
    (seed.le_NI.trans inf_le_right) (r.seed_not_le_MI seed hC) seed.normalized hYY hKK

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.ResidualInput

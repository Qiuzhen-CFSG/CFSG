module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActions
public import CFSG.Quasithin.Chapter1.Section01Inheritance
public import Theory.GroupTheory.IndexTwoConjugateSpan

/-!
# The conjugate-pair normalizer argument in 15.2.22

Let X = ⟨Y₁,K₁⟩. The two same-family commutator relations together
with the putative [Y₁,K₂] ≤ Y₁ ∩ K₂ make Xᵗ normalize X. The index-two
condition on S makes T normalize XXᵗ. Characteristic two passes from I
to XS, and then to its normal subgroup X, so O₂(X) is nontrivial.
Its image survives in O₂(XXᵗT), giving a genuine two-local overgroup.

Because this overgroup contains the original H = KT, 15.2.12(3) puts
it in Mc, contradicting Y₁ outside MI. This uses the already proved
uniqueness over H in place of the source's uniqueness over Y₁Y₁ᵗT.
All normality is relative; Xᵗ need not lie in I.

The same-family relations and the marked split remain explicit local
inputs, to be constructed in the full source proof. No normalizer bound
or contradiction callback is assumed. ComponentModels applies the result
to the actual binary component calculation.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.2.22, printed pp.1114--1115; refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The local normalizer argument of 15.2.22: a nontrivial S-invariant X
and its mutually normalizing conjugate generate a subgroup of Mc whenever
they contain K. Nontriviality of the core is proved using characteristic two. -/
theorem conjugate_pair_le_partner (hI : PlaneEscapes Mc ZS I)
    (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup G} (hX : X ≠ ⊥) (hXI : X ≤ I)
    (hSX : smallActionS T ZS ≤ normalizer (X : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htS : t ∉ smallActionS T ZS)
    (hpair : X.map (MulAut.conj t).toMonoidHom ≤ normalizer (X : Set G))
    (hK : smallActionK H ≤ X ⊔ X.map (MulAut.conj t).toMonoidHom) :
    X ⊔ X.map (MulAut.conj t).toMonoidHom ≤ Mc := by
  let S := smallActionS T ZS
  let D := X ⊔ X.map (MulAut.conj t).toMonoidHom
  have hSI : S ≤ I :=
    (le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right
  have hIHe : I ∈ Chapter1.He G := by
    apply Chapter1.mem_He_iff.mpr
    simpa only [hfit] using centralizer_generalizedFitting_le I
  have hXSHe : X ⊔ S ∈ Chapter1.He G :=
    Chapter1.lemma_1_1_4_4 (fun he => hX (bot_unique (le_sup_left.trans_eq he)))
      (sup_le hXI hSI) hIHe
      (inf_le_left.trans ((d.core_le_plane hI).trans le_sup_right))
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
        (d.escape_index hI).2 t⁻¹ ((T : Subgroup G).inv_mem ht)
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
    rw [← d.residual_sup_sylow]
    exact (sup_le_sup_right hK _).trans hDN
  have hNMc : N = Mc := by
    apply Set.mem_singleton_iff.mp
    rw [← d.local_unique]
    exact ⟨hN, hHN⟩
  exact (le_sup_left.trans hDN).trans_eq hNMc

/-- Expand the normalizer step on the actual four generators Y₁,K₁,Y₁ᵗ,K₂.
The two same-family commutator relations are retained as local geometric
inputs; no normalizer bound or contradiction is assumed. -/
theorem not_commutator_le_inf_of_conjugate_pair
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (split : SmallActionSplit (T : Subgroup G) (smallActionS T ZS) (smallActionK H))
    {Y : Subgroup G} (hYI : Y ≤ I) (hYout : ¬ Y ≤ Mc ⊓ I)
    (hSY : smallActionS T ZS ≤ normalizer (Y : Set G))
    (hYY : ⁅Y, Y.map (MulAut.conj split.t).toMonoidHom⁆ ≤
      Y ⊓ Y.map (MulAut.conj split.t).toMonoidHom)
    (hKK : ⁅split.K₁, split.K₂⁆ ≤ split.K₁ ⊓ split.K₂) :
    ¬ ⁅Y, split.K₂⁆ ≤ Y ⊓ split.K₂ := by
  intro hYK
  let f := (MulAut.conj split.t).toMonoidHom
  have ht2 : split.t ^ 2 ∈ smallActionS T ZS :=
    ((smallActionS T ZS).subgroupOf (T : Subgroup G)).sq_mem_of_index_two
      (d.escape_index hI).2 ⟨split.t, split.t_mem⟩
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
    ((le_sup_left.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right))
  have hSX : smallActionS T ZS ≤ normalizer (X : Set G) :=
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
  have hle := conjugate_pair_le_partner d hI hfit hXne hXI hSX
    split.t_mem split.t_not_mem hpair hK
  exact hYout (le_inf ((le_sup_left.trans le_sup_left).trans hle) hYI)
end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource

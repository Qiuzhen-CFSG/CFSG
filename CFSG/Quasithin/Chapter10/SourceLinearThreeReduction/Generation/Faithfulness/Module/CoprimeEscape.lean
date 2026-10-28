module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Escape
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Module.Coprimality

/-!
# Coprime escaping elementary Hall kernels

The proved 4.4.13 escape construction selects an elementary abelian odd
subgroup inside the literal Hall kernel. Applying the original orbit-section
coprimality theorem records the exact prime-to-|L/O₂(L)| conclusion needed
by the later module argument. The subgroup, action, and normalizer maps are
those of the source setup; no A₅ marking or fixed-seed irreducibility is used.

Source: Aschbacher--Smith 4.4.13(1) and 10.2.3(2), printed pp.623--625,745.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 ChapterB ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

theorem source_hstar_hall_kernel_escaping_coprime
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {n : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP n)
    (hk : d.witness.abelianGroup ⊓
      (sectionCentralizer (localOrbit T L)).subgroupOf H ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧
      Nat.Coprime p (Nat.card (L ⧸ pCore 2 L)) ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ d.witness.abelianGroup.map H.subtype ∧
      A ≤ sectionCentralizer (localOrbit T L) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ D.maximalLocal := by
  obtain ⟨p,A,hp,ho,hA,hAe,hAY,hAC,hAT,hout⟩ :=
    source_hstar_hall_kernel_escaping_elementary D hH hlarge hP d hk
  let : Fact p.Prime := ⟨hp⟩
  let := hAe
  let : Nontrivial A := A.nontrivial_iff_ne_bot.mpr hA
  have hAp : IsPGroup p A := IsElementaryAbelian.isPGroup p A
  obtain ⟨k,hk,hcard⟩ := hAp.nontrivial_iff_card.mp inferInstance
  have hodd : Odd (Nat.card A) := hcard ▸ ho.pow
  have hcop := source_nonnormal_odd_sectionKernel_coprime D hn A hodd hAC
  have hd : p ∣ Nat.card A := hcard ▸ dvd_pow_self p (Nat.ne_of_gt hk)
  exact ⟨p,A,hp,ho,hcop.coprime_dvd_left hd,hA,hAe,hAY,hAC,hAT,hout⟩
end CFSG.Quasithin.Chapter10

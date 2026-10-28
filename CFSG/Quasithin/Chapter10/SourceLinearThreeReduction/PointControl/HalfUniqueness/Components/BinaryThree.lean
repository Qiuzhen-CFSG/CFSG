module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.QuotientRank
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.LowCubicModels
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BenderSylowOvergroups
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.LowCubic
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.BinaryThreeSection

/-!
# Excluding strict containing components in the binary-three row

Cubic rank at most one reduces the constrained C.2.7 quotient to binary
SL₂ or SL₃. The first has no proper nonsolvable full-Sylow overgroup; the
second cannot place the original SL₃(2) section in a proper parabolic.

In the nonconstrained case, module choice removes the odd core and makes
the component quasisimple. The original moved quotient gives two-rank at
least three. The actual Theorem C catalogue then leaves Bender models,
binary PSL₃, or J₁. Full-Sylow solvability excludes Bender; the same parabolic
obstruction excludes PSL₃; elementary Sylow two-subgroups exclude J₁.
All maps start from the literal conjugate of L in the containing component.

The containing-pair applications retain the same exchanger, half-join and
relative normality. They complete both enlargement cases for an actual
binary-three quotient, conditional on the still-unproved component
distinctness. The other quotient rows, distinctness, the binary-three
normalizer and final uniqueness assembly remain with
qt-d-10-nona5-half-sylow-unique. ModuleChoiceAt is the only independent source
input used here; its final discharge remains with qt-d-10-nona5-point-control
using qt-d-10-nona5-point-selection.

Source: Aschbacher--Smith 10.2.6, printed pp.748--749,
using A.3.12 and C.2.7, pp.47--48 and 145--147.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {H K : Subgroup G} {s : G}

namespace RankedEnlargement
variable (E : RankedEnlargement D H s K)
include E

/-- The literal binary-three section excludes every binary linear-three containing quotient. -/
theorem not_linear_three_of_binary_three_quotient
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (dK : (K ⧸ pCore 2 K) ≃* PSL(3,F)) : False := by
  obtain ⟨S,_,hlocal⟩ := E.local_sylow
  let B := (L.map (MulAut.conj s).toMonoidHom).subgroupOf K
  let eB : L ≃* B := ((MulAut.conj s).subgroupMap L).trans
    (subgroupOfEquivOfLe E.strict.le).symm
  let i : L →* K := B.subtype.comp eB.toMonoidHom
  have hi : Function.Injective i := B.subtype_injective.comp eB.injective
  let q : K →* PSL(3,F) := dK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := dK.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 K := by
    ext x
    change dK (QuotientGroup.mk' (pCore 2 K) x) = 1 ↔ x ∈ pCore 2 K
    rw [dK.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  let f := q.comp i
  have hf : IsPGroup 2 f.ker := by
    change IsPGroup 2 (q.ker.comap i)
    rw [hk]
    exact pCore_isPGroup.comap_of_injective i hi
  let π := dL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hπ : Function.Surjective π := dL.surjective.comp (QuotientGroup.mk'_surjective _)
  let P := B ⊔ (S : Subgroup K)
  have hSP : (S.mapSurjective hq : Subgroup PSL(3,F)) ≤ P.map q := map_mono le_sup_right
  have hfP : f.range ≤ P.map q := by
    rintro _ ⟨l,rfl⟩
    exact mem_map_of_mem q (show i l ∈ P from (show B ≤ P from le_sup_left) (eB l).property)
  let := Chapter1.mem_L_isPerfect D.maximal.1
  have hm := Matrix.PSL3.LinearThree.sylow_overgroup_eq_top_of_binary_three_quotient
    F π hπ f hf hn hF (S.mapSurjective hq) (P.map q) hSP hfP
  have hkerP : q.ker ≤ P := by
    rw [hk]
    exact (pCore_isPGroup.le_sylow_of_normal S).trans le_sup_right
  have hP : P = ⊤ := by
    have hh := congrArg (Subgroup.comap q) hm
    simpa only [Subgroup.comap_map_eq_self hkerP,Subgroup.comap_top] using hh
  have hB : B.IsCComponent := by
    change (B.subgroupOf P).IsCComponent at hlocal
    rw [hP] at hlocal
    simpa only [map_subgroupOf_eq_of_le le_top] using
      hlocal.map_subtype (show (⊤ : Subgroup K).IsSubnormal from .top)
  have htop : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using E.component.2.subgroupOf_of_le le_rfl E.component.1
  have heB := hB.eq_of_le htop le_top
  exact E.strict.ne (le_antisymm E.strict.le (subgroupOf_eq_top.mp heB))

/-- The full C.2.7 comparison excludes the constrained binary-three enlargement. -/
theorem not_constrained_of_binary_three_quotient
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)) :
    generalizedFitting K ≠ pCore 2 K := by
  intro hfit
  have h3 : 3 ∣ Nat.card (L ⧸ pCore 2 L) := by
    rw [Nat.card_congr dL.toEquiv,Matrix.PSL3Two.card_SL]
    decide
  have hr := E.ranks 3 (by decide) (by decide) h3
  obtain ⟨F,hF⟩ := source_low_cubic_coreQuotient_linear (E.c27_input hfit) hr
  rcases hF with hF | hF
  · obtain ⟨e⟩ := hF
    exact E.not_binary_rank_one e
  · obtain ⟨e⟩ := hF
    have hz : center SL(3,F.Carrier) = ⊥ := by
      apply (eq_bot_iff_card _).mpr
      rw [←Nat.card_congr (centerCongr e).toEquiv,
        source_rank_one_coreQuotient_center (E.c27_input hfit) hr,card_bot]
    let d : SL(3,F.Carrier) ≃* PSL(3,F.Carrier) :=
      MulEquiv.ofBijective (Matrix.PSL3.projection F.Carrier) ⟨
        (MonoidHom.ker_eq_bot_iff _).mp (by rw [Matrix.PSL3.projection_ker,hz]),
        Matrix.PSL3.projection_surjective F.Carrier⟩
    exact E.not_linear_three_of_binary_three_quotient dL F.degree_pos F.card_eq (e.trans d)

/-- The original order-four section cannot occur in the elementary Sylow model J₁. -/
theorem not_janko_one_of_binary_three_quotient
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (dK : (K ⧸ pCore 2 K) ≃* Janko1.Model) : False := by
  let B := (L.map (MulAut.conj s).toMonoidHom).subgroupOf K
  let eB : L ≃* B := ((MulAut.conj s).subgroupMap L).trans
    (subgroupOfEquivOfLe E.strict.le).symm
  let i : L →* K := B.subtype.comp eB.toMonoidHom
  have hi : Function.Injective i := B.subtype_injective.comp eB.injective
  let q : K →* Janko1.Model := dK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := dK.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 K := by
    ext x
    change dK (QuotientGroup.mk' (pCore 2 K) x) = 1 ↔ x ∈ pCore 2 K
    rw [dK.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  let f := q.comp i
  have hf : IsPGroup 2 f.ker := by
    change IsPGroup 2 (q.ker.comap i)
    rw [hk]
    exact pCore_isPGroup.comap_of_injective i hi
  let π := dL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  apply Matrix.SpecialLinearGroup.no_binary_three_quotient_of_two_subgroup_exponent
    (π := π) (f := f) _ (dL.surjective.comp (QuotientGroup.mk'_surjective _)) hf
  intro P hP x
  obtain ⟨S,hPS⟩ := hP.exists_le_sylow
  let := Janko1.SylowTwo.elementary S
  apply Subtype.ext
  exact elemPow_eq_one_of_isElementaryAbelian (x : Janko1.Model) (hPS x.property)

/-- Both Fitting cases of the strict binary-three enlargement are impossible. -/
theorem impossible_of_binary_three_quotient
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)) : False := by
  let : IsQuasisimple K := E.quasisimple_of_nonconstrained hchoice hmany hn hna
    (E.not_constrained_of_binary_three_quotient dL)
  have h2 : 3 ≤ primeRank 2 (K ⧸ pCore 2 K) :=
    quasisimple_overgroup_quotient_twoRank D E.strict.le
  have ho : pPrimeCore 2 K = ⊥ := by
    have hh := E.component.2.subnormal.pPrimeCore_eq_bot
      (oddCore_eq_bot_of_moduleChoice hchoice hmany D hn hna E.half_le) (K.subgroupOf H)
    have heq := pPrimeCore_map_iso 2 (subgroupOfEquivOfLe E.component.1)
    rw [hh] at heq
    simpa only [Subgroup.map_bot] using heq.symm
  have hz : center K = pCore 2 K := IsQuasisimple.center_eq_pCore ho
  let qk : (K ⧸ pCore 2 K) ≃* (K ⧸ center K) :=
    QuotientGroup.quotientMulEquivOfEq hz.symm
  have hsqtk : IsSQTK KnownSimple.IsKnownSimple (K ⧸ pCore 2 K) := by
    have hs := D.simpleQTKE.twoLocal_sqtk E.maximal.1
    have hKsq : IsSQTK KnownSimple.IsKnownSimple K := ⟨
      hs.stronglyQuasithin.of_injective (inclusion E.component.1) (inclusion_injective _),
      hs.isKGroup.of_injective (inclusion E.component.1) (inclusion_injective _)⟩
    refine ⟨?_,hKsq.isKGroup.quotient _⟩
    intro p hp hop
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p hop _ pCore_isPGroup).trans
      (hKsq.stronglyQuasithin p hp hop)
  let : IsSimpleGroup (K ⧸ pCore 2 K) :=
    (MulEquiv.isSimpleGroup_congr qk).mpr IsQuasisimple.simple
  have hmodel : Chapter1.Section02.LocalModels.TheoremCModel (K ⧸ pCore 2 K) :=
    ChapterA.Section03.SourceComponents.sourceTheoremC_to_local
      (Group.IsPerfect.not_isMulCommutative (K ⧸ pCore 2 K))
      (ChapterA.Section02.theoremC_knownSimple (G := K ⧸ pCore 2 K) inferInstance
        (Group.IsPerfect.not_isMulCommutative (K ⧸ pCore 2 K))
        hsqtk.stronglyQuasithin hsqtk.isKGroup)
  have h3 : 3 ∣ Nat.card (L ⧸ pCore 2 L) := by
    rw [Nat.card_congr dL.toEquiv,Matrix.PSL3Two.card_SL]
    decide
  have hr := (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans
    (E.ranks 3 (by decide) (by decide) h3)
  rcases ChapterA.Section03.SourceEmbeddings.models_of_three_le_twoRank_low_threeRank
    hmodel h2 hr with hb | hm | hm
  · obtain ⟨S,_,hlocal⟩ := E.local_sylow
    have htop : (⊤ : Subgroup K).IsCComponent := by
      simpa only [subgroupOf_self] using E.component.2.subgroupOf_of_le le_rfl E.component.1
    have hproper : ∀ (S' : Sylow 2 K) (P : Subgroup K),
        (S' : Subgroup K) ≤ P → P ≠ ⊤ → Group.IsSolvable P := by
      intro S' P hSP hneP
      exact isSolvable_proper_sylow_overgroup_of_twoCore_quotient
        (G := K) (fun Q' P' hQ' hneQ' =>
          ChapterA.Section03.SourceEmbeddings.bender_solvable_proper_sylow_overgroup
            hb Q' P' hQ' hneQ') S' P hSP hneP
    have heB := ChapterA.Section03.SourceEmbeddings.eq_of_solvable_sylow_overgroups
      S hlocal htop le_top (isSolvable_proper_sylow_overgroup_of_equiv topEquiv hproper)
    exact E.strict.ne (le_antisymm E.strict.le (subgroupOf_eq_top.mp heB))
  · obtain ⟨n,hnn,F,_,_,hF,⟨e⟩⟩ := hm
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    exact E.not_linear_three_of_binary_three_quotient dL (by omega) hF e
  · obtain ⟨e⟩ := hm
    exact E.not_janko_one_of_binary_three_quotient dL e

end RankedEnlargement

/-- The constrained exclusion applied to the original strict pair member. -/
theorem ContainingPair.exists_nonconstrained_of_binary_three_quotient
    {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}
    (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) (hne : K₁ ≠ K₂)
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)) :
    ∃ (s : G) (K : Subgroup G), RankedEnlargement D H s K ∧
      generalizedFitting K ≠ pCore 2 K := by
  obtain ⟨s,K,E⟩ := C.exists_rankedEnlargement hn hne
  exact ⟨s,K,E,E.not_constrained_of_binary_three_quotient dL⟩

/-- The binary-three row on the literal containing pair and its original exchanger. -/
theorem ContainingPair.impossible_of_distinct_binary_three_quotient
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}
    (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hne : K₁ ≠ K₂) (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)) : False := by
  obtain ⟨s,K,E⟩ := C.exists_rankedEnlargement hn hne
  exact E.impossible_of_binary_three_quotient hchoice hmany hn hna dL

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness

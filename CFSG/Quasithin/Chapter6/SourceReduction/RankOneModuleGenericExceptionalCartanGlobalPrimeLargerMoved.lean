module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeLargerInvariant
public import Theory.GroupTheory.PResidual.NormalizerLift
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.CComponentCommutation

/-!
# Excluding the larger-Sylow actual-component branch

Let I be the common component over the selected actual H-component R.
The original and changed Sylows have the same stabilizer T₀ on I.
The common two-core lies in T₀ and normalizes R. Distinct conjugates
of I commute modulo that core; lifting normalizers shows that the
changed-Sylow conjugates of R normalize R. Thus R is a component in
its changed local group, with its literal embedding and nonzero core.

The changed Sylow moves R, but the source extension has a normal
component strictly containing R. The full-Sylow invariant-container
exclusion now gives a contradiction. No equality of the original and
changed residuals, or additional model recognition, is required.
The original selected pair consequently retains only the zero-core
and larger-Sylow parabolic alternatives.

Source: Aschbacher–Smith 1.2.1–8 and 5.2.2, printed pp.504–507,
648–649, refs/quasithin.pdf.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
public noncomputable section
variable {G : Type*} [Group G] [Finite G]

private theorem perfect_twoPerfect (R : Subgroup G) [Group.IsPerfect R] : IsPPerfect 2 R := by
  intro N hn htwo
  let := hn
  by_contra he
  let : Nontrivial (R ⧸ N) := QuotientGroup.nontrivial_iff.mpr he
  let : Group.IsPerfect (R ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent (R ⧸ N) := htwo.isNilpotent
  exact Group.IsPerfect.not_isSolvable (R ⧸ N) inferInstance

private theorem orbit_normalizes_of_component_stabilizer
    (hQ : IsSQTK KnownSimple.IsKnownSimple (G ⧸ pCore 2 G))
    {R I S : Subgroup G} [Group.IsPerfect R]
    (hI : I.IsCComponent) (hRI : R ≤ I)
    (hcore : pCore 2 G ≤ normalizer (R : Set G))
    (hstab : S ⊓ normalizer (I : Set G) ≤ normalizer (R : Set G)) :
    conjugateSpanBy R S ≤ normalizer (R : Set G) := by
  let q := QuotientGroup.mk' (pCore 2 G)
  rw [conjugateSpanBy_eq_iSup_conj]
  apply iSup_le
  intro s
  by_cases he : I.map (MulAut.conj (s : G)).toMonoidHom = I
  · have hfix := mem_normalizer_iff_map_conj_eq.mp
      (hstab ⟨s.property,mem_normalizer_iff_map_conj_eq.mpr he⟩)
    change R.map (MulAut.conj (s : G)).toMonoidHom = R at hfix
    rw [hfix]
    exact R.le_normalizer
  · have hc := ChapterA.Section03.CComponentCommutation.proposition_1_2_1_two hQ
      (hI.map_equiv (MulAut.conj (s : G))) hI he
    have hcR : ⁅R.map (MulAut.conj (s : G)).toMonoidHom,R⁆ ≤ pCore 2 G :=
      (commutator_mono (map_mono hRI) hRI).trans (hc.1.trans hc.2)
    have hcq : ⁅(R.map (MulAut.conj (s : G)).toMonoidHom).map q,R.map q⁆ = ⊥ := by
      rw [←map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
      exact hcR
    have hnq := (commutator_eq_bot_iff_le_centralizer.mp hcq).trans
      (Subgroup.centralizer_le_normalizer _)
    exact (map_le_iff_le_comap.mp hnq).trans
      (normalizer_comap_map_le_of_pGroup_kernel q R (perfect_twoPerfect R)
        (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
        (by rw [QuotientGroup.ker_mk']; exact hcore))

omit [Finite G] in
private theorem component_in_join_of_orbit_normalizes
    {R S : Subgroup G} (hR : (⊤ : Subgroup R).IsCComponent)
    (hn : conjugateSpanBy R S ≤ normalizer (R : Set G)) :
    (R.subgroupOf (R ⊔ S)).IsCComponent := by
  let J := R ⊔ S
  let V := conjugateSpanBy R S
  have hRV : R ≤ V := le_conjugateSpanBy R S
  have hVJ : V ≤ J := conjugateSpanBy_le le_sup_left
    ((show S ≤ J from le_sup_right).trans J.le_normalizer)
  have hJN : J ≤ normalizer (V : Set G) :=
    sup_le (hRV.trans V.le_normalizer) (le_normalizer_conjugateSpanBy R S)
  have hVN : (V.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer hJN
  have hRN : ((R.subgroupOf J).subgroupOf (V.subgroupOf J)).Normal := by
    apply normal_subgroupOf_of_le_normalizer
    rw [←subgroupOf_normalizer_eq (show R ≤ J from le_sup_left)]
    exact subgroupOf_mono J hn
  have hsub : (R.subgroupOf J).IsSubnormal := IsSubnormal.step _ _
    (subgroupOf_mono J hRV) hVN.isSubnormal hRN
  let e := (subgroupOfEquivOfLe (show R ≤ J from le_sup_left)).symm
  have htop : (⊤ : Subgroup (R.subgroupOf J)).IsCComponent := by
    simpa only [map_top_of_surjective e.toMonoidHom e.surjective] using hR.map_equiv e
  simpa only [←MonoidHom.range_eq_map,range_subtype] using htop.map_subtype hsub


/-- The common-component stabilizers transfer the selected right component
into the local family of the changed full Sylow. -/
theorem LocalData.changedSylow_right_component_of_common_stabilizers
    {T U : Sylow 2 G} {L W H A B D R I : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hTU : normalizingSylow T R ≤ (U : Subgroup G))
    (hRI : R ≤ I)
    (hIX : I ≤ normalizer (normalizingSylow T R : Set G) ⊔ H)
    (hI : (I.subgroupOf (normalizer (normalizingSylow T R : Set G) ⊔ H)).IsCComponent)
    (hTN : (T : Subgroup G) ⊓ normalizer (I : Set G) = normalizingSylow T R)
    (hUN : (U : Subgroup G) ⊓ normalizer (I : Set G) = normalizingSylow T R) :
    (R.subgroupOf (R ⊔ (U : Subgroup G))).IsCComponent := by
  let X := normalizer (normalizingSylow T R : Set G) ⊔ H
  have hTX : (T : Subgroup G) ≤ X :=
    (show (T : Subgroup G) ≤ H from hH.1.1.2).trans le_sup_right
  have hUX : (U : Subgroup G) ≤ X :=
    (d.overgroup_two_subgroup_normalizes hH.1.1.2 c hd hz U.isPGroup' hTU).trans le_sup_left
  have hRX : R ≤ X := hRI.trans hIX
  have hQ := Chapter3.sqtk_of_mem_H h.qtke (d.common_normal_overgroup h hH c hd hz).1
  have hQbar : IsSQTK KnownSimple.IsKnownSimple (X ⧸ pCore 2 X) := by
    refine ⟨?_,hQ.isKGroup.quotient _⟩
    intro q hq ho
    let : Fact q.Prime := ⟨hq⟩
    exact (primeRank_quotient_le_of_isTwoGroup q ho (pCore 2 X) pCore_isPGroup).trans
      (hQ.stronglyQuasithin q hq ho)
  let : Group.IsNilpotent (pCore 2 X) := pCore_isNilpotent
  have hcoreI : pCore 2 X ≤ (normalizer (I : Set G)).subgroupOf X := by
    rw [subgroupOf_normalizer_eq hIX,←normalizer_cComponent_quotient hI (pCore 2 X)]
    simpa only [QuotientGroup.ker_mk'] using MonoidHom.ker_le_comap
      (QuotientGroup.mk' (pCore 2 X))
      (normalizer ((I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X)) : Set _))
  have hcoreT : pCore 2 X ≤ (T : Subgroup G).subgroupOf X :=
    pCore_isPGroup.le_sylow_of_normal (T.subtype hTX)
  have hcoreR : pCore 2 X ≤ normalizer (R.subgroupOf X : Set X) := by
    rw [←subgroupOf_normalizer_eq hRX]
    intro x hx
    exact (show normalizingSylow T R ≤ normalizer (R : Set G) from inf_le_right)
      (hTN ▸ (show (x : G) ∈ (T : Subgroup G) ⊓ normalizer (I : Set G) from
        ⟨hcoreT hx,hcoreI hx⟩))
  have hstab : (U : Subgroup G).subgroupOf X ⊓ normalizer (I.subgroupOf X : Set X) ≤
      normalizer (R.subgroupOf X : Set X) := by
    rw [←subgroupOf_normalizer_eq hIX,←subgroupOf_normalizer_eq hRX]
    intro x hx
    exact (show normalizingSylow T R ≤ normalizer (R : Set G) from inf_le_right)
      (hUN ▸ (show (x : G) ∈ (U : Subgroup G) ⊓ normalizer (I : Set G) from hx))
  let : Group.IsPerfect R := Chapter1.mem_L_isPerfect (d.right_mem_local_family h hH)
  let e := subgroupOfEquivOfLe hRX
  let : Group.IsPerfect (R.subgroupOf X) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hnX := orbit_normalizes_of_component_stabilizer hQbar hI
    (subgroupOf_mono X hRI) hcoreR hstab
  rw [←subgroupOf_normalizer_eq hRX] at hnX
  have hn := map_mono (f := X.subtype) hnX
  rw [map_conjugateSpanBy,map_subgroupOf_eq_of_le hRX,map_subgroupOf_eq_of_le hUX] at hn
  have htop : (⊤ : Subgroup R).IsCComponent := by
    simpa only [subgroupOf_self] using
      d.right_component.subgroupOf_of_le (le_refl R) (show R ≤ R ⊔ normalizingSylow T R from le_sup_left)
  exact component_in_join_of_orbit_normalizes htop (hn.trans (map_comap_le _ _))

/-- The selected actual H-component cannot occur at a larger ambient
changed Sylow. The argument keeps the common component's stabilizers and
uses the normal overcomponent in the literal source extension. -/
theorem LocalData.largerSylow_actual_component_impossible
    {T U : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hC : (R.subgroupOf H).IsCComponent)
    (P : Sylow 2 (extension T L H B D R))
    (hTP : normalizingSylow T R ≤
      (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype)
    (hU : (U : Subgroup G) =
      (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype) : False := by
  let X := normalizer (normalizingSylow T R : Set G) ⊔ H
  let E := extension T L H B D R
  have hTU : normalizingSylow T R ≤ (U : Subgroup G) := hTP.trans_eq hU.symm
  have hUX : (U : Subgroup G) ≤ X :=
    (d.overgroup_two_subgroup_normalizes hH.1.1.2 c hd hz U.isPGroup' hTU).trans le_sup_left
  obtain ⟨I,hRI,hIX,hI,hTI,hu,_⟩ :=
    d.changedSylow_common_orbit_strict h hH c hd hz P hTP hU
  have hm := d.common_component_not_normalized h hH c hd hz hC hRI.le hIX hI
  obtain ⟨hTN,_,_,hUm,hUN⟩ := d.changedSylow_moved_common_intersections h hH c hd hz
    hTU hIX hI hTI hm
  have hRX : R ≤ X := hRI.le.trans hIX
  have hRcomp := d.changedSylow_right_component_of_common_stabilizers h hH c hd hz
    hTU hRI.le hIX hI hTN hUN
  have hRlocal : R ∈ Chapter1.L G (U : Subgroup G) := by
    refine ⟨hRcomp,⟨U.subtype le_sup_right,map_subgroupOf_eq_of_le le_sup_right⟩,?_⟩
    have hc : (R ⊔ (P : Subgroup E).map E.subtype).pCoreIn 2 ≠ ⊥ :=
      (d.changedSylow_overgroups h hH c hd hz P hTP).1.1
    rw [hU]
    exact hc
  have hmove : R < conjugateSpanBy R (U : Subgroup G) := by
    apply lt_of_le_of_ne (le_conjugateSpanBy R _)
    intro he
    have hnR : (U : Subgroup G) ≤ normalizer (R : Set G) :=
      he.symm ▸ le_normalizer_conjugateSpanBy R (U : Subgroup G)
    have huniq : ∀ J : Subgroup X, J.IsCComponent → R.subgroupOf X ≤ J →
        J = I.subgroupOf X := by
      intro J hJ hRJ
      have hmapJ : ((J.map X.subtype).subgroupOf X).IsCComponent := by
        change (J.map X.subtype |>.comap X.subtype).IsCComponent
        rw [comap_map_eq_self_of_injective X.subtype_injective]
        exact hJ
      have hRmap : R ≤ J.map X.subtype := by
        simpa only [map_subgroupOf_eq_of_le hRX] using map_mono (f := X.subtype) hRJ
      have hEq := hu (J.map X.subtype) (map_subtype_le _) hmapJ hRmap
      apply map_injective X.subtype_injective
      rw [map_subgroupOf_eq_of_le (show I ≤ X from hIX)]
      exact hEq
    have hnI := cComponent_le_normalizer_of_unique hI (subgroupOf_mono X hRI.le) huniq
      (S := (U : Subgroup G).subgroupOf X) (by
        rw [←subgroupOf_normalizer_eq hRX]
        exact subgroupOf_mono X hnR)
    rw [←subgroupOf_normalizer_eq hIX] at hnI
    apply hUm
    intro u huU
    exact hnI (show (⟨u,hUX huU⟩ : X) ∈ (U : Subgroup G).subgroupOf X from huU)
  obtain ⟨K,hRK,hKE,hK,hKn,_⟩ := d.extension_overcomponent h hH c hd hz
  have hUE : (U : Subgroup G) ≤ E := hU ▸ map_subtype_le _
  have hKlocal : K ∈ Chapter1.L G (U : Subgroup G) :=
    Chapter1.mem_L_of_cComponent (d.extension_core_ne_bot hz)
      ⟨U.subtype hUE,map_subgroupOf_eq_of_le hUE⟩ hKE hK
  have hUK : (U : Subgroup G) ≤ normalizer (K : Set G) :=
    hUE.trans ((normal_subgroupOf_iff_le_normalizer hKE).mp hKn)
  exact LargerInvariant.normalized_chain_impossible h.qtke U hRlocal hKlocal hRK.le hUK hmove

/-- On the same original prime pair, every nonzero-core case is now a
larger-Sylow selected parabolic. The actual-component branch is excluded,
while the original field and the full linear cover remain explicit. -/
theorem source_prime_pair_zero_or_larger_parabolic
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    ∃ R : Subgroup G, LocalData T L H B D R ∧ SelectedSourceModels H R ∧
      (((generated L H D R).pCoreIn 2 = ⊥ ∧
        ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)) ∨
       ((generated L H D R).pCoreIn 2 ≠ ⊥ ∧
        ¬ D ≤ normalizer (R : Set G) ∧
        (normalizingSylow T R).relIndex (T : Subgroup G) = 2 ∧
        (ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 → p = 5 ∧ n ≠ 2) ∧
        ∃ P : Sylow 2 (extension T L H B D R),
          let T₁ := (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype
          normalizingSylow T R < T₁ ∧
          T₁ ≤ normalizer ((D ⊔ normalizingSylow T R : Subgroup G) : Set G) ∧
          ∃ U : Sylow 2 G, (U : Subgroup G) = T₁ ∧
            ¬ (R.subgroupOf H).IsCComponent ∧
            ∃ f : ℕ, 1 < f ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2 ^ f) ∧
              (ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
               Chapter1.Section02.LocalModels.IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
               ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f)))) := by
  obtain ⟨R,d,hs,hcases⟩ := source_prime_pair_zero_or_largerSylow h hH hgen hthree c hd
  refine ⟨R,d,hs,?_⟩
  rcases hcases with hz | ⟨hz,hD,hi,hA5,P,hlt,hDT,U,hU,hr⟩
  · exact .inl hz
  rcases hr with ⟨hC,_⟩ | ⟨hC,hpar⟩
  · exact (d.largerSylow_actual_component_impossible h hH c hd hz hC P hlt.le hU).elim
  · exact .inr ⟨hz,hD,hi,hA5,P,hlt,hDT,U,hU,hC,hpar⟩

end
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime

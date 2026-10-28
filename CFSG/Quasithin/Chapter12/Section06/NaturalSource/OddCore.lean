module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.PointThreeRank
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.F9
public import Theory.GroupTheory.OddPrimeCoreInvolution
public import CFSG.Quasithin.Chapter12.Section06.Nonabelian.Components.Selection
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs.TheoremC
public import Theory.GroupTheory.CComponent.QuasisimpleSupplement

/-!
# The original three-core exclusion and component selection

The point stabilizer in L maps into C_{H*}(V*) through H → H/O₂(H).
Its two-group kernel preserves three-rank, so that centralizer has rank
two. An involution fixing an elementary abelian group of order nine centralizes every
normal three-subgroup in a group of three-rank at most two. Applied to
each element of the original V*, this proves [O₃(H*),V*]=1.

The same original quotient inherits SQTK. Genuine Theorems A and C give
even order for each component's simple quotient. F.9's exact centralizer
preimage proves V* centralizes the actual Sylow image, and V ≤ O₂(M)
follows by relative normality of L in M. Thus the existing component
selection now needs only centralization of the p-cores for p>3, besides
the contrary-nonabelian branch and the earlier geometry. That remaining
odd-prime assertion, the component exclusions and the abelian-span theorem
are not established here.

Source: Aschbacher--Smith, proof of 12.6.26, printed p.832. The selected
C-component and its ordinary star image use the original H and quotient.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- The actual two-core quotient inherits the full SQTK hypothesis from the point centralizer. -/
theorem SourceHypothesis.original_star_sqtk
    (hz : z ≠ 1) {H : Subgroup G}
    (hH : H ∈ (D.fullSetup hZ T z).Hz) : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
  have ho : orderOf (z : G) = 2 := orderOf_eq_prime_iff.mpr
    ⟨elemPow_eq_one_of_isElementaryAbelian _ z.property,fun he => hz (Subtype.ext he)⟩
  have hGz : IsSQTK KnownSimple.IsKnownSimple (D.fullSetup hZ T z).Gz := by
    rw [(D.fullSetup hZ T z).Gz_eq]
    exact S.source.simpleQTKE.involution_centralizer_sqtk ho
  have hHSQ : IsSQTK KnownSimple.IsKnownSimple H :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hH.2.1)).mp (hGz.subgroup (H.subgroupOf _))
  refine ⟨?_,hHSQ.isKGroup.quotient (pCore 2 H)⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  rw [primeRank_quotient_eq_of_isTwoGroup p ho (pCore 2 H) pCore_isPGroup]
  exact hHSQ.stronglyQuasithin p hp ho

/-- Three-rank is at most two on the original intrinsic two-core quotient. -/
theorem SourceHypothesis.original_star_three_rank
    (hz : z ≠ 1) {H : Subgroup G}
    (hH : H ∈ (D.fullSetup hZ T z).Hz) : primeRank 3 (H ⧸ pCore 2 H) ≤ 2 := by
  exact (S.original_star_sqtk D hZ z hz hH).stronglyQuasithin 3 (by decide) (by decide)

/-- The exact centralizer of V* has three-rank two, using the image of C_L(z). -/
theorem SourceHypothesis.original_star_point_centralizer_three_rank
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ V ≤ H.pCoreIn 2) :
    primeRank 3 (centralizer (Nonabelian.Setup.star H V : Set (H ⧸ pCore 2 H))) = 2 := by
  let E := D.fullSetup hZ T z
  let C := L ⊓ E.Gz
  let h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  have hTG : (T : Subgroup G) ≤ normalizer (E.Gz : Set G) :=
    hTz.trans (normalizer_le_normalizer_centralizer _)
  have hTC : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    (le_inf S.chosen.sylow_normalizes_component hTG).trans inf_normalizer_le_normalizer_inf
  have hCH : C ≤ H :=
    (le_embedded_pResidual_sup_sylow_of_normalizes T C hTC).trans h.local_le
  let j : C →* H := inclusion hCH
  let f : C →* (H ⧸ pCore 2 H) := (QuotientGroup.mk' (pCore 2 H)).comp j
  have hp : IsPGroup 2 f.ker := by
    change IsPGroup 2 ((QuotientGroup.mk' (pCore 2 H)).ker.comap j)
    rw [QuotientGroup.ker_mk']
    exact (pCore_isPGroup (p := 2) (G := H)).comap_of_injective j (inclusion_injective hCH)
  let B := centralizer (Nonabelian.Setup.star H V : Set (H ⧸ pCore 2 H))
  have hb (c : C) : f c ∈ B := by
    change j c ∈ B.comap (QuotientGroup.mk' (pCore 2 H))
    have he : B.comap (QuotientGroup.mk' (pCore 2 H)) = (normalizer (V : Set G)).subgroupOf H :=
      h.star_centralizer_preimage (E.perpendicular_index hz) hn
    rw [he]
    exact S.chosen.normalizes c.property.1
  let g : C →* B := f.codRestrict B hb
  have hc : Nat.Coprime 3 (Nat.card g.ker) := by
    have he : g.ker = f.ker := MonoidHom.ker_codRestrict _ _ _
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    rw [he,hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  apply le_antisymm
  · exact (Theory.GroupTheory.primeRank_le_of_injective 3 B.subtype B.subtype_injective).trans
      (S.original_star_three_rank D hZ z hz hH)
  · exact (S.original_point_three_rank D hZ z hz hTz).symm.le.trans
      (primeRank_le_of_coprime_ker 3 g hc)

/-- The O₃(H*) exclusion in 12.6.26, with the original V and quotient map. -/
theorem SourceHypothesis.original_star_three_core_centralized
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz) :
    Nonabelian.Setup.star H V ≤ centralizer (pCore 3 (H ⧸ pCore 2 H) : Set (H ⧸ pCore 2 H)) := by
  let E := D.fullSetup hZ T z
  let h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  by_cases hn : V ≤ H.pCoreIn 2
  · have he : Nonabelian.Setup.star H V = ⊥ := by
      by_contra he
      exact (h.star_module_ne_bot_iff_not_le_core.mp he) hn
    rw [he]
    exact bot_le
  · have hr := S.original_star_three_rank D hZ z hz hH
    have hrc := S.original_star_point_centralizer_three_rank D hZ z hz hTV hTz hbound hH hn
    intro t ht
    have ht2 : t ^ 2 = 1 := by
      obtain ⟨v,hv,rfl⟩ := ht
      have hv2 : v ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian v.val hv)
      rw [←map_pow,hv2,map_one]
    apply involution_centralizes_pCore_of_centralizer_rank (by decide : Odd 3) hr t ht2
    exact hrc.symm.le.trans
      (primeRank_mono 3 (centralizer_le (Set.singleton_subset_iff.mpr ht)))

/-- Every component of the actual star group has even simple quotient, by genuine A and C. -/
theorem SourceHypothesis.original_star_component_even
    (hz : z ≠ 1) {H : Subgroup G}
    (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (J : Subgroup (H ⧸ pCore 2 H)) (hJ : IsComponent (H ⧸ pCore 2 H) J) :
    2 ∣ Nat.card (J ⧸ center J) := by
  let := hJ.2
  let : CommGroup (center J) := IsMulCommutative.instCommGroup
  have he := (ChapterA.Section03.SourceComponents.source_model_inputs_on_cComponent_of_theoremC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    (S.original_star_sqtk D hZ z hz hH) J hJ.isCComponent).2
  have hr : solvableRadical J = center J := le_antisymm
    IsQuasisimple.solvableRadical_le_center
    (le_solvableRadical (center J) inferInstance inferInstance)
  rw [hr] at he
  exact even_iff_two_dvd.mp he

/-- Select the original moved C-component after centralization of the remaining
p-cores for p>3. The three-core, Sylow centrality, evenness and V ≤ O₂(M)
premises of the selection theorem are all discharged here. -/
theorem SourceHypothesis.original_selectedComponent_of_large_odd_cores
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (hother : ∀ p : ℕ, p.Prime → 3 < p →
      Nonabelian.Setup.star H V ≤ centralizer (pCore p (H ⧸ pCore 2 H) : Set (H ⧸ pCore 2 H))) :
    Nonempty ((D.fullSetup hZ T z).SelectedComponent H) := by
  let E := D.fullSetup hZ T z
  let h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  have hC := S.original_perpendicular_centralizer D hZ z hz hTV hTz hbound
  have hVn := (E.nonabelian_inputs h hC hn).2.1
  have hF : Nonabelian.Setup.star H V ≤ centralizer (fittingSubgroup (H ⧸ pCore 2 H) : Set (H ⧸ pCore 2 H)) := by
    apply subgroup_le_centralizer_fitting_of_le_centralizer_pCores
    intro p
    have hp := Nat.prime_of_mem_primeFactors p.val.property
    by_cases h2 : p.val.val = 2
    · rw [h2,pCore_quotient_pCore_eq_bot 2]
      intro a _ b hb
      rw [mem_bot.mp hb]
      simp
    by_cases h3 : p.val.val = 3
    · rw [h3]
      exact S.original_star_three_core_centralized D hZ z hz hTV hTz hbound hH
    exact hother p.val.val hp (by have := hp.two_le; omega)
  have hcentral : Nonabelian.Setup.star H V ≤ centralizer (E.Tstar H h.T_le_H : Set (H ⧸ pCore 2 H)) := by
    apply le_centralizer_iff.mpr
    rintro _ ⟨t,ht,rfl⟩
    have he : (centralizer (Nonabelian.Setup.star H V : Set (H ⧸ pCore 2 H))).comap
        (QuotientGroup.mk' (pCore 2 H)) = (normalizer (V : Set G)).subgroupOf H :=
      h.star_centralizer_preimage (E.perpendicular_index hz) hVn
    change t ∈ (centralizer (Nonabelian.Setup.star H V : Set (H ⧸ pCore 2 H))).comap
      (QuotientGroup.mk' (pCore 2 H))
    rw [he]
    exact hTV ht
  have hVM : V ≤ (M L).pCoreIn 2 := S.chosen.le_componentCore.trans
    (pCoreIn_mono_of_normalizes L.le_normalizer (le_refl (M L)))
  exact E.selectedComponent_of_nonabelian h hC hn h.T_le_H hVM hF hcentral
    (S.original_star_component_even D hZ z hz hH)
end CFSG.Quasithin.Chapter12.Section06

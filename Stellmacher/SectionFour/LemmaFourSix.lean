module
public import Stellmacher.SectionFour.LemmaFourFive
public import Stellmacher.SectionFour.OutsideMember
public import Stellmacher.SectionFour.BaumannPartner
public import Stellmacher.SectionFour.BaumannLineConfiguration
public import Stellmacher.SectionFour.CommonCoreNormalizerContradiction
public import Theory.GroupTheory.Commutator.NormalizerLinePermutation
public import Theory.GroupTheory.Commutator.LineTransitivity
public import Theory.GroupTheory.LineStabilizerOddSupplement
public import Theory.GroupTheory.Commutator.LineOrbitNormalizer

/-!
# Stellmacher (4.6): a starred subgroup outside the core normalizer

Under the Section Four hypotheses and two-family cover, the family starred
over C = C_G(omega_1 Z(S)) is not contained in the family over M = N_G(D).
The conclusion remains the source's noncontainment assertion.

Assuming containment gives the critical-partner Baumann configuration.
Its proved natural-line configuration retains the original module V,
identifies V with the partner two-core, and provides pairwise disjoint
four-element modules, their order-two commutator lines, and the Sylow
coordinates. The selected module spans V under S and commutes with its
odd conjugates by (2.5). Injective subtype transport carries this exact
family to the ambient group. Automorphisms induced by N_G(B) permute the
lines, and the selected-module spanning equality makes S transitive.

A compatible odd Hall supplement U of C lies in the selected line's
stabilizer. Self and cross-coordinate commutators show that its conjugates
of the selected module lie in V; the literal C=US factorization and
S-spanning then force C to normalize V. The actual partner-core equality
V=O_2(M) gives the common-core normalizer contradiction, using the two
supplied distinct maximal two-local overgroups. This avoids assuming an
unproved equality N_G(O_2(M))=M and supplies the prerequisite for (4.7).

Source: refs/latex/stellmacher-n-group.tex, statement and proof (4.6),
Journal of Algebra 190 (1997), journal p26.
-/

open scoped Pointwise
namespace Stellmacher.SectionFour
universe u

private theorem le_normalizer_core
    {G : Type*} [Group G] (K : Subgroup G) :
    K ≤ Subgroup.normalizer (twoCoreAmbient K : Set G) := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp
  rw [subgroupOf_map_subtype_eq]
  infer_instance

/-- Stellmacher (4.6), with the source's noncontainment conclusion. -/
public theorem lemma_four_six
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (h : Hypotheses G S)
    (hcover : SectionThree.PSet (⊤ : Subgroup G) (S : Subgroup G) =
      SectionThree.PSet (cSubgroup S) (S : Subgroup G) ∪
        SectionThree.PSet (mSubgroup S) (S : Subgroup G)) :
    ¬ SectionThree.PStarSet (cSubgroup S) (S : Subgroup G) ⊆
      SectionThree.PSet (mSubgroup S) (S : Subgroup G) := by
  intro hstar
  obtain ⟨P, Pstar, E, hPC, hPstar, hpair, _hcore, hE, hSyl,
    hsolv, hchar, hEP, _hPE, hBS, _hBN, _hcomm, _hres⟩ :=
    exists_baumann_configuration S h hcover hstar
  obtain ⟨SP, hsec, hSPmap, hV⟩ := original_partner_sectionTwo_data
    S h.even_order P Pstar E hpair hPC.1.1 hEP hsolv hchar hE hSyl
  let B := twoCoreAmbient (cSubgroup S) ⊓ Subgroup.centralizer
    (omegaOneCenterAmbient (elementaryAbelianMaxJ (twoCoreAmbient (cSubgroup S))) : Set G)
  let BN := B.subgroupOf Pstar
  let VN := SectionTwo.vSubgroup SP
  let V := VN.map Pstar.subtype
  have hSPstar : (S : Subgroup G) ≤ Pstar := hSPmap ▸ Subgroup.map_subtype_le _
  have hBP : B ≤ Pstar := hBS.trans hSPstar
  have hBNmap : BN.map Pstar.subtype = B := Subgroup.map_subgroupOf_eq_of_le hBP
  have hQ : pCore 2 Pstar = VN := by
    rw [partner_core_eq_v S h.even_order P Pstar E hpair hPC.1.1 hEP hsolv hchar hE hSyl]
    exact hV.symm
  have hVcore : V = twoCoreAmbient Pstar := by
    change VN.map Pstar.subtype = (pCore 2 Pstar).map Pstar.subtype
    rw [hQ]
  obtain ⟨n, WN, TN, i, hWNB, hVNgen, hWNdisj, hRleN, hTNB, hBNgen,
      hlinesN, hVNspan, hodd⟩ := baumann_line_configuration
    S h.even_order P Pstar E B hpair hPC.1.1 hEP hsolv hchar hE hSyl rfl hBS
      SP hsec hSPmap hV
  change VN = ⨆ j, WN j at hVNgen
  change BN = VN ⊔ ⨆ j, TN j at hBNgen
  change VN = ⨆ s : SP, (WN i).map (MulAut.conj (s : Pstar)).toMonoidHom at hVNspan
  let W (j : Fin n) := (WN j).map Pstar.subtype
  let T (j : Fin n) := (TN j).map Pstar.subtype
  let R (j : Fin n) := ⁅W j, B⁆
  have hWB (j : Fin n) : W j ≤ B := by
    rw [← hBNmap]
    exact Subgroup.map_mono (hWNB j)
  have hTB (j : Fin n) : T j ≤ B := by
    rw [← hBNmap]
    exact Subgroup.map_mono (hTNB j)
  have hVgen : V = ⨆ j, W j := by
    change VN.map Pstar.subtype = _
    rw [hVNgen, Subgroup.map_iSup]
  have hVB : V ≤ B := by rw [hVgen]; exact iSup_le hWB
  have hWdisj : Pairwise fun j k => Disjoint (W j) (W k) := by
    intro j k hjk
    exact Subgroup.disjoint_map Pstar.subtype_injective (hWNdisj hjk)
  have hRmap (j : Fin n) : (⁅WN j, BN⁆).map Pstar.subtype = R j := by
    rw [Subgroup.map_commutator, hBNmap]
  have hRle (j : Fin n) : R j ≤ W j := by
    rw [← hRmap]
    exact Subgroup.map_mono (hRleN j)
  have hRcard (j : Fin n) : Nat.card (R j) = 2 := by
    rw [← hRmap, Subgroup.card_map_of_injective Pstar.subtype_injective]
    exact (hlinesN j).2
  have hlocal (j : Fin n) : ⁅V, T j⁆ = R j := by
    change ⁅VN.map Pstar.subtype, (TN j).map Pstar.subtype⁆ = R j
    rw [← Subgroup.map_commutator, (hlinesN j).1, hRmap]
  have hBgen : B = V ⊔ ⨆ j, T j := by
    rw [← hBNmap, hBNgen, Subgroup.map_sup, Subgroup.map_iSup]
  have hcentral : B ⊓ Subgroup.centralizer (V : Set G) ≤ V := by
    rintro g ⟨hgB, hgC⟩
    let gP : Pstar := ⟨g, hBP hgB⟩
    have hg : gP ∈ Subgroup.centralizer (VN : Set Pstar) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hgC v
        (Subgroup.mem_map_of_mem Pstar.subtype hv))
    have hcent : Subgroup.centralizer (VN : Set Pstar) ≤ VN := by rw [← hQ]; exact hchar
    exact Subgroup.mem_map_of_mem Pstar.subtype (hcent hg)
  have hSC : (S : Subgroup G) ≤ cSubgroup S := by
    obtain ⟨Q, hQmap⟩ := hPC.1.2.1
    rw [← hQmap]
    exact (Subgroup.map_subtype_le _).trans hPC.1.1
  have hCB : cSubgroup S ≤ Subgroup.normalizer (B : Set G) :=
    (le_normalizer_core (cSubgroup S)).trans
      (normalizer_le_normalizer_baumann (twoCoreAmbient (cSubgroup S)))
  have hSB : (S : Subgroup G) ≤ Subgroup.normalizer (B : Set G) := hSC.trans hCB
  have hSV : (S : Subgroup G) ≤ Subgroup.normalizer (V : Set G) := by
    rw [hVcore]
    exact hSPstar.trans (le_normalizer_core Pstar)
  let e : SP ≃* S := ((SP : Subgroup Pstar).equivMapOfInjective
    Pstar.subtype Pstar.subtype_injective).trans (MulEquiv.subgroupCongr hSPmap)
  have hVspan : V = ⨆ s : S, (W i).map (MulAut.conj (s : G)).toMonoidHom := by
    change VN.map Pstar.subtype = _
    rw [hVNspan, Subgroup.map_iSup]
    rw [← e.toEquiv.iSup_comp (g := fun s : S =>
      (W i).map (MulAut.conj (s : G)).toMonoidHom)]
    apply iSup_congr
    intro s
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hperm : ∀ c ∈ cSubgroup S, ∃ j,
      (R i).map (MulAut.conj c).toMonoidHom = R j := by
    intro c hc
    exact Subgroup.normalizer_maps_commutator_line B V W T hVB hWB hTB hVgen
      hcentral hBgen hRcard (fun j => (hlocal j).le) c (hCB hc) i
  have htrans : ∀ j, ∃ s ∈ S, (R i).map (MulAut.conj s).toMonoidHom = R j := by
    intro j
    obtain ⟨s, hs⟩ := Subgroup.exists_conjugate_commutator_line_of_spanning
      B V (W i) (T j) (S : Subgroup G) hSB (hTB j) (hRcard i)
        (by rw [hlocal j]; exact hRcard j) hVspan
    exact ⟨s, s.property, hs.trans (hlocal j)⟩
  have hCsolv : Group.IsSolvable (cSubgroup S) := by
    let N := Subgroup.normalizer (twoCoreAmbient (cSubgroup S) : Set G)
    have hCN : cSubgroup S ≤ N := le_normalizer_core _
    have hNlocal : IsTwoLocal N := ⟨twoCoreAmbient (cSubgroup S),
      twoCore_cSubgroup_ne_bot S h.even_order,
      (pCore_isPGroup (p := 2) (G := cSubgroup S)).map (cSubgroup S).subtype, rfl⟩
    let _ : Group.IsSolvable N := (h.local_solvable_characteristicTwo N hNlocal (hSC.trans hCN)).1
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hCN)
  obtain ⟨U, hUC, hUodd, hUS⟩ := Subgroup.exists_odd_stabilizer_supplement
    (cSubgroup S) hCsolv S hSC R i hperm htrans
  have hUB : U ≤ Subgroup.normalizer (B : Set G) := (hUC.trans inf_le_left).trans hCB
  have hself := hodd U hUodd hUB
  have hCV : cSubgroup S ≤ Subgroup.normalizer (V : Set G) :=
    Subgroup.line_family_odd_orbit_normalizes B V (S : Subgroup G) (cSubgroup S) U W i
      hWB hVgen hWdisj hRle hcentral hSV hVspan
      (le_inf hUB (hUC.trans inf_le_right)) (fun u hu => hself ⟨u, hu⟩) hUS
  have hcoreeq := partner_core_eq_m_core S h P Pstar E hPstar hpair hPC.1.1
    hEP hsolv hchar hE hSyl
  apply four_six_contradiction_of_core_normalized_by_c S h hcover
  rwa [← hcoreeq, ← hVcore]

end Stellmacher.SectionFour

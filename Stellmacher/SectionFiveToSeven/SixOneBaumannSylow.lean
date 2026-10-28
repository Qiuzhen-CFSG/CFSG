module

public import Stellmacher.SectionFiveToSeven.PFamilyBridge
public import Stellmacher.SectionFiveToSeven.HypothesisTwoSectionThree
public import Stellmacher.SectionFiveToSeven.Result5_3
public import Stellmacher.SectionThree.NormalClosureCentralizerSylow
public import Stellmacher.SectionTwo.CoreCentralizerCriterion
public import Stellmacher.SectionTwo.LemmaTwoThree
public import Stellmacher.BaumannMap
public import Stellmacher.UniqueMaximalContainingTransport

/-!
# The Baumann Sylow subgroup in the first local normal closure

Under Hypothesis Two, this module proves the Sylow assertion used in the
noncentral branch of Stellmacher (6.1): B(S) is a Sylow two-subgroup of its
P₁-conjugate closure L₁. The statement retains the branch hypothesis that
J(S) does not lie in O₂(P₁).

The alternatives in (5.1) force P₁ to act nontrivially on Ω₁(Z(S)). In
alternative (b), simultaneous centralization by P₁ and P₂ would put this
nontrivial two-subgroup in the trivial core of their join. The centralizer
Sylow consequence of (3.3), together with (5.3), therefore applies to the
normal closure of Ω₁(Z(S)) inside P₁. Transferring its Sylow witness through
the subgroup-image equivalence gives precisely the core-centralizer equality
required by (2.3). That theorem produces the native Baumann Sylow witness.

Injective omega-center and Baumann transport identify the native subgroups
with the original S and B(S). Mapping the native normal closure gives the
literal P₁-conjugate closure in H, and mapping its Sylow witness finishes.
The native-data companion retains this same exact Sylow witness, the core
equality, noncentral Thompson action, and unique maximal containment needed
for factor selection. Noncentrality follows by contradiction from J(S)≰O₂(P₁);
unique maximal containment is transported through the subgroup lattice.

P₁ is not required to be normal in H, and the join P₁ ∨ P₂ is not identified
with H. All intermediate normal closures use their stated acting group.

Source: B. Stellmacher, *2-Local structure of N-groups*, Journal of Algebra
190 (1997), (6.1), journal p.30; the scan in refs/files/stellmacher-n-group.pdf
is PDF page20. This is the explicit native transfer for the cited applications
of (5.3), (3.3), and (2.3).
-/

namespace Stellmacher.SectionsFiveToSeven
universe u
variable {H : Type u} [Group H]

private theorem closure_map_subtype (X P : Subgroup H) (hXP : X ≤ P) :
    (Subgroup.normalClosure (X.subgroupOf P : Set P)).map P.subtype =
      conjugateClosure X P := by
  rw [Subgroup.normalClosure, MonoidHom.map_closure, conjugateClosure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hy
    obtain ⟨a, ha⟩ := isConj_iff.mp hconj
    refine ⟨a, ⟨z, hz⟩, ?_⟩
    exact congrArg Subtype.val ha.symm
  · rintro ⟨a, z, rfl⟩
    let zP : P := ⟨z, hXP z.property⟩
    refine ⟨a * zP * a⁻¹, ?_, rfl⟩
    exact Group.mem_conjugatesOfSet_iff.mpr ⟨zP, z.property, isConj_iff.mpr ⟨a, rfl⟩⟩

private theorem omega_le (S : Subgroup H) : omegaOneCenter S ≤ S :=
  Subgroup.map_subtype_le _

private theorem sylow_centralizes_omega (S : Subgroup H) :
    S ≤ Subgroup.centralizer (omegaOneCenter S : Set H) := by
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨zS, ⟨zC, _hz, rfl⟩, rfl⟩ := hz
  exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp zC.property) ⟨s, hs⟩).symm

private theorem omega_ne [Finite H] (S : Subgroup H) (hSp : IsPGroup 2 S) (hSne : S ≠ ⊥) :
    omegaOneCenter S ≠ ⊥ := by
  let _ : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).2 hSne
  let _ : Nontrivial (Subgroup.center S) := hSp.center_nontrivial
  have hcenterP : IsPGroup 2 (Subgroup.center S) := hSp.to_subgroup (Subgroup.center S)
  obtain ⟨n, hn, hcard⟩ := hcenterP.nontrivial_iff_card.mp inferInstance
  have hdvd : 2 ∣ Nat.card (Subgroup.center S) := by
    rw [hcard]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn)
  have hinner := omega₁_map_subtype_ne_bot (G := S) (Subgroup.center S) 2 hdvd
  intro hz
  apply hinner
  apply (Subgroup.map_eq_bot_iff_of_injective
    (H := (omega₁ (G := Subgroup.center S) (p := 2)).map (Subgroup.center S).subtype)
    (f := S.subtype) S.subtype_injective).mp
  exact hz

private theorem normalIn_of_centralizes (X P : Subgroup H)
    (hXP : X ≤ P) (hPX : P ≤ Subgroup.centralizer (X : Set H)) : NormalIn X P := by
  refine ⟨hXP, (Subgroup.normal_subgroupOf_iff_le_normalizer hXP).mpr ?_⟩
  exact hPX.trans (Subgroup.centralizer_le_normalizer _)

private theorem not_centralizes_omega [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (h : HypothesisTwo H S0 S P1 P2) :
    ¬ P1 ≤ Subgroup.centralizer (omegaOneCenter S : Set H) := by
  intro hP1
  have hSP1 : S ≤ P1 := h.fiveOne.P1_mem.1.2.1.1
  have hSP2 : S ≤ P2 := h.fiveOne.P2_mem.1.2.1.1
  have hn1 : NormalIn (omegaOneCenter S) P1 :=
    normalIn_of_centralizes _ _ ((omega_le S).trans hSP1) hP1
  cases h.fiveOne.alternative with
  | a _ hn _ => exact hn hn1
  | c _ _ _ hn _ _ _ _ _ _ _ _ _ => exact hn hn1
  | b hS hP2 =>
    have hP2c : P2 ≤ Subgroup.centralizer (omegaOneCenter S : Set H) := hP2.1.1.1
    let J := P1 ⊔ P2
    let Z := omegaOneCenter S
    have hZJ : Z ≤ J := (omega_le S).trans (hSP1.trans le_sup_left)
    have hJc : J ≤ Subgroup.centralizer (Z : Set H) := sup_le hP1 hP2c
    have hZn : (Z.subgroupOf J).Normal := (normalIn_of_centralizes Z J hZJ hJc).2
    have hSp : IsPGroup 2 S := h.sectionThreeHypotheses.nontrivial_two_subgroup.2
    have hZp : IsPGroup 2 Z := hSp.to_le (omega_le S)
    have hZpJ : IsPGroup 2 (Z.subgroupOf J) :=
      hZp.of_equiv (Subgroup.subgroupOfEquivOfLe hZJ).symm
    have hZcore : Z.subgroupOf J ≤ pCore 2 J := le_sSup ⟨hZn, hZpJ⟩
    have hZbot : Z = ⊥ := by
      apply le_bot_iff.mp
      have hm := Subgroup.map_mono (f := J.subtype) hZcore
      rw [Subgroup.map_subgroupOf_eq_of_le hZJ] at hm
      exact hm.trans (le_of_eq h.fiveOne.join_twoCore_eq_bot)
    exact omega_ne S hSp h.fiveOne.S_nontrivial hZbot

/-- Exact native Section Two inputs for the first local member in (6.1). -/
public theorem sixOne_native_local_data [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (h : HypothesisTwo H S0 S P1 P2)
    (hJ : ¬ elementaryAbelianMaxJ S ≤ twoCoreIn P1)
    (T : Sylow 2 P1) (hTm : (T : Subgroup P1).map P1.subtype = S) :
    SectionTwo.Hypotheses P1 ∧
    pCore 2 P1 = (T : Subgroup P1) ⊓
      Subgroup.centralizer (SectionTwo.vSubgroup T : Set P1) ∧
    (¬ SectionTwo.vSubgroup T ≤ Subgroup.centralizer
      (elementaryAbelianMaxJ (T : Subgroup P1) : Set P1)) ∧
    IsUniqueMaximalContaining (T : Subgroup P1) (⊤ : Subgroup P1) := by
  obtain ⟨hsolv, hchar, _⟩ := lemma_five_three S0 S P1 P2 h
  have hSP1 : S ≤ P1 := h.fiveOne.P1_mem.1.2.1.1
  have hTne : (T : Subgroup P1) ≠ ⊥ := by
    intro hb
    apply h.fiveOne.S_nontrivial
    rw [← hTm, hb, Subgroup.map_bot]
  have hdvd : 2 ∣ Nat.card T := T.isPGroup'.card_eq_or_dvd.resolve_left
    (fun hc => hTne (Subgroup.card_eq_one.mp hc))
  have heven : Even (Nat.card P1) := even_iff_two_dvd.mpr
    (hdvd.trans (Subgroup.card_subgroup_dvd_card (T : Subgroup P1)))
  have hsec : SectionTwo.Hypotheses P1 := ⟨hsolv, heven, hchar⟩
  have hZP : SectionTwo.zSubgroup T = (omegaOneCenter S).subgroupOf P1 := by
    apply Subgroup.map_injective P1.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le ((omega_le S).trans hSP1)]
    change (omegaOneCenterAmbient (T : Subgroup P1)).map P1.subtype = omegaOneCenter S
    rw [← omegaOneCenterAmbient_map_injective P1.subtype P1.subtype_injective, hTm]
    rfl
  let V := SectionTwo.vSubgroup T
  let C : Subgroup P1 := Subgroup.centralizer (V : Set P1)
  have hSyl := SectionThree.twoCore_sylow_normalClosure_centralizer
    S h.sectionThreeHypotheses P1 (omegaOneCenter S)
    ((pFamily_iff_pSet _ _ _).mp h.fiveOne.P1_mem) hsolv (omega_le S)
    (sylow_centralizes_omega S) (not_centralizes_omega S0 S P1 P2 h)
  rw [← hZP] at hSyl
  change IsSylowSubgroupIn (twoCoreIn P1) (C.map P1.subtype) at hSyl
  obtain ⟨TC, hTC⟩ := hSyl
  let e : C ≃* C.map P1.subtype :=
    C.equivMapOfInjective P1.subtype P1.subtype_injective
  let TC' : Sylow 2 C := TC.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hTC' : (TC' : Subgroup C).map C.subtype = pCore 2 P1 := by
    apply Subgroup.map_injective P1.subtype_injective
    rw [Subgroup.map_map]
    change ((TC : Subgroup (C.map P1.subtype)).map e.symm.toMonoidHom).map
      (P1.subtype.comp C.subtype) = (pCore 2 P1).map P1.subtype
    rw [Subgroup.map_map]
    have he : (P1.subtype.comp C.subtype).comp e.symm.toMonoidHom =
        (C.map P1.subtype).subtype := by
      ext x
      exact congrArg (fun y : C.map P1.subtype => (y : H)) (e.apply_symm_apply x)
    rw [he]
    exact hTC
  have hcore := SectionTwo.twoCore_eq_sylow_centralizer_of_sylow_control
    T V le_rfl ⟨TC', hTC'⟩
  refine ⟨hsec, hcore, ?_, ?_⟩
  · intro hcent
    apply hJ
    have hJcore : elementaryAbelianMaxJ (T : Subgroup P1) ≤ pCore 2 P1 := by
      rw [hcore]
      exact le_inf (sSup_le fun _ hA => hA.1)
        (Subgroup.le_centralizer_iff.mp hcent)
    have hmap := Subgroup.map_mono (f := P1.subtype) hJcore
    rw [← elementaryAbelianMaxJ_map_injective P1.subtype P1.subtype_injective,
      hTm] at hmap
    exact hmap
  · apply native_uniqueMaximalContaining
    rw [hTm]
    exact ((pFamily_iff_pSet _ _ _).mp h.fiveOne.P1_mem).2

/-- In the noncentral branch of (6.1), the actual Baumann subgroup is Sylow
in its normal closure under the first amalgam member. -/
public theorem sixOne_baumann_sylow [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (h : HypothesisTwo H S0 S P1 P2)
    (_hJ : ¬ elementaryAbelianMaxJ S ≤ twoCoreIn P1) :
    IsSylowTwoIn (baumannIn S) (sectionSixL (baumannIn S) P1) := by
  obtain ⟨hSP1, T, hTm⟩ := h.fiveOne.P1_mem.1.2.1
  obtain ⟨hsec, hcore, _, _⟩ := sixOne_native_local_data S0 S P1 P2 h _hJ T hTm
  let B : Subgroup P1 := (T : Subgroup P1) ⊓ Subgroup.centralizer
    (omegaOneCenterAmbient (elementaryAbelianMaxJ (T : Subgroup P1)) : Set P1)
  have hBm : B.map P1.subtype = baumannIn S := by
    rw [baumann_map_injective P1.subtype P1.subtype_injective, hTm]
    rfl
  let L := Subgroup.normalClosure (B : Set P1)
  obtain ⟨R, hR⟩ := SectionTwo.lemma_two_three hsec T hcore B L rfl rfl
  have hBL : baumannIn S ≤ P1 := hBm ▸ Subgroup.map_subtype_le B
  have hBsub : (baumannIn S).subgroupOf P1 = B := by
    rw [← hBm]
    exact Subgroup.comap_map_eq_self_of_injective P1.subtype_injective _
  have hLm : L.map P1.subtype = sectionSixL (baumannIn S) P1 := by
    dsimp only [L]
    rw [← hBsub]
    exact closure_map_subtype (baumannIn S) P1 hBL
  let f : L →* H := P1.subtype.comp L.subtype
  have hfrange : f.range = sectionSixL (baumannIn S) P1 := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hLm
  let R' : Sylow 2 f.range := R.mapSurjective f.rangeRestrict_surjective
  have hRmap : (R' : Subgroup f.range).map f.range.subtype = baumannIn S := by
    rw [Sylow.coe_mapSurjective, Subgroup.map_map]
    change (R : Subgroup L).map f = baumannIn S
    rw [show f = P1.subtype.comp L.subtype from rfl, ← Subgroup.map_map, hR, hBm]
  rw [← hfrange]
  exact ⟨hRmap ▸ Subgroup.map_subtype_le (R' : Subgroup f.range), R', hRmap⟩

end Stellmacher.SectionsFiveToSeven

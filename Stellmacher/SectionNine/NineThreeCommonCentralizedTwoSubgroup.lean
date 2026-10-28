module
public import Stellmacher.SectionNine.NineThreeNormalizedGeometry
public import Stellmacher.SectionNine.NineTwoAmbientSetup
public import Stellmacher.SectionFiveToSeven.FiveTwoCentralizerSubnormal
public import Stellmacher.SectionFiveToSeven.FiveTwoFullCommutatorOddQuotient
public import Stellmacher.SectionFiveToSeven.Result7_8.GeometricActorCommutator
public import Theory.GroupTheory.PGroup.SubnormalConjugateCore
public import Stellmacher.BaumannMap

/-!
# No nontrivial two-subgroup centralizes the normalized extraction pair and Baumann group

For the actual normalized two-extraction configuration of (9.3), any
two-subgroup centralized by both extracted groups and B(T) is trivial.
The subgroup need not have a specified mixed-commutator form, and it need
not lie in the initial center. All extracted and residual witnesses remain
those of the supplied configuration.

If I is nontrivial, its ambient centralizer contains B(S) and both extracted
groups. The full commutator F of the actual second residual with B(S) is
subnormal in this centralizer by (5.2), applied through the true two-local
normalizer, and F/O₂(F) is an odd-prime group. The actual second residual
conjugator compares the initial and old neighboring centers modulo O₂(C).
Critical minimality puts the old center in the terminal core. Consequently
a two-group normalized by the first extracted group contains the initial
center, making their commutator a two-group. This contradicts the prescribed
actor property of that unchanged extraction.

This exposes exactly the centralizer argument used for R₁ in Stellmacher
(9.3), Journal of Algebra 190 (1997), pp.49–50,
`refs/files/stellmacher-n-group.pdf`. It also applies to the full intersection
of the two new centers in the subsequent native Thompson-action argument.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem map_conjugate
    {G H : Type u} [Group G] [Group H] (f : G →* H) (A : Subgroup G) (x : G) :
    (A.conjBy x).map f = (A.map f).conjBy (f x) := by
  change (A.map (MulAut.conj x).toMonoidHom).map f =
    (A.map f).map (MulAut.conj (f x)).toMonoidHom
  rw [Subgroup.map_map,Subgroup.map_map]
  congr 1
  ext a
  simp [MulAut.conj_apply]

public theorem nine_three_normalized_common_two_subgroup_bot
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first)
    (config : NineThreeNormalizedGeometry ctx first second)
    (I : Subgroup G) (hIp : IsPGroup 2 I)
    (hIB : I ≤ Subgroup.centralizer (baumannIn T : Set G))
    (hEI : first.E.map (MulAut.conj config.g⁻¹).toMonoidHom ⊔
      second.E.map (MulAut.conj config.g⁻¹).toMonoidHom ≤
        Subgroup.centralizer (I : Set G)) : I = ⊥ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hbLocal : 1 < cp.length := hb
  let c := MulAut.conj config.g⁻¹
  let d := Γ.act config.g cp.a'
  let r := Γ.act config.g second.l
  let V := VAt Γ cp.firstStep
  let E1 := first.E.map c.toMonoidHom
  let E2 := second.E.map c.toMonoidHom
  let R1 := I
  have hEpair : E1 ⊔ E2 ≤ Subgroup.centralizer (R1 : Set G) := hEI
  have hZaV : ZAt Γ cp.a ≤ V := (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1
  have hVp : IsPGroup 2 V :=
    ((lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hb).1.isPGroup
  have hR1p : IsPGroup 2 R1 := hIp
  by_contra hR1ne
  let RH := R1.map embedding
  let C := Subgroup.centralizer (RH : Set H)
  let BH := baumannIn S
  let E1H := E1.map embedding
  let E2H := E2.map embedding
  let VH := V.map embedding
  let ZaH := (ZAt Γ cp.a).map embedding
  let ZrH := (ZAt Γ r).map embedding
  let R := (twoResidualAmbient E2).map embedding
  let F := ⁅R,BH⁆
  have hRHne : RH ≠ ⊥ := fun he => hR1ne
    ((Subgroup.map_eq_bot_iff_of_injective R1 ctx.embedding_injective).mp he)
  have hBmap : (baumannIn T).map embedding = BH := by
    rw [show (baumannIn T).map embedding = baumannIn (T.map embedding) from
      baumann_map_injective embedding ctx.embedding_injective T,ctx.map_S]
  have hBC : BH ≤ C := by
    have hR1B : R1 ≤ Subgroup.centralizer (baumannIn T : Set G) :=
      hIB
    have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (Subgroup.le_centralizer_iff.mp hR1B)
    have hm := congrArg (Subgroup.map embedding) hc
    rw [Subgroup.map_commutator,Subgroup.map_bot,hBmap] at hm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hm
  have hEsC : E1H ⊔ E2H ≤ C := by
    have hm := congrArg (Subgroup.map embedding)
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hEpair)
    rw [Subgroup.map_commutator,Subgroup.map_sup,Subgroup.map_bot] at hm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hm
  have hE1C : E1H ≤ C := le_sup_left.trans hEsC
  have hE2C : E2H ≤ C := le_sup_right.trans hEsC
  have hRE2 : R ≤ E2H := Subgroup.map_mono (Subgroup.map_subtype_le _)
  have hRF : R ≤ F := by
    have hm := Subgroup.map_mono (f := embedding) config.residual_baumann
    rw [Subgroup.map_commutator,hBmap] at hm
    exact hm
  have hFB : F = ⁅F,BH⁆ :=
    le_antisymm (Subgroup.commutator_mono hRF le_rfl)
      (Subgroup.le_normalizer_iff_commutator_le_left.mp
        (Subgroup.normalizer_commutator_ge_right R BH))
  have hFC : F ≤ C := (Subgroup.commutator_le_sup _ _).trans (sup_le (hRE2.trans hE2C) hBC)
  obtain ⟨_,hmapGa,hmapP,_⟩ := nine_two_ambient_setup ctx
  have hE2P : E2H ≤ P2 := by
    rw [← hmapP]
    exact Subgroup.map_mono config.second_geometry.group_le
  have hBP : BH ≤ P2 := inf_le_left.trans ctx.hypothesisTwo.fiveOne.P2_mem.1.2.1.1
  have hFP : F ≤ P2 := (Subgroup.commutator_le_sup _ _).trans (sup_le (hRE2.trans hE2P) hBP)
  have homega : (omegaOneCenter T).map embedding = omegaOneCenter S := by
    rw [← ctx.map_S]
    exact (omegaOneCenterAmbient_map_injective embedding ctx.embedding_injective T).symm
  have hnext := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).next_center
  have hcomm : ⁅P2,omegaOneCenter S⁆ = ⊥ := by
    rw [← hmapP,← homega,← Subgroup.map_commutator]
    have hc : ⁅GAt Γ cp.firstStep,omegaOneCenter T⁆ = ⊥ := by
      apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      apply Subgroup.le_centralizer_iff.mpr
      rw [← hnext.1,hnext.2]
      exact (omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _)
    rw [hc,Subgroup.map_bot]
  have hlocal := fiveTwo_centralizer_subnormal_characteristicTwo ctx.hypothesisTwo hcomm
    F hFP hFB RH hRHne (hR1p.map embedding) (sup_le hBC hFC)
  obtain ⟨p,hp,hp2,hFp⟩ := fiveTwo_full_commutator_odd_quotient ctx.hypothesisTwo hcomm F hFP hFB
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let y := config.second_geometry.x
  have hyR : embedding y ∈ R := Subgroup.mem_map_of_mem embedding config.second_geometry.residual_mem
  have hyF : embedding y⁻¹ ∈ F := by rw [map_inv]; exact F.inv_mem (hRF hyR)
  have hZaConj : ZaH.conjBy (embedding y⁻¹) = ZrH := by
    have hZa : ZAt Γ cp.a = (ZAt Γ r).conjBy y := by
      rw [← config.second_new_vertex]
      change z Γ (Γ.act y⁻¹ r) = _
      rw [z_act,inv_inv]
      rfl
    have hh : (ZAt Γ cp.a).conjBy y⁻¹ = ZAt Γ r := by rw [hZa,Subgroup.conjBy_inv]
    rw [← map_conjugate,hh]
  have hZrV : ZAt Γ r ≤ V := by
    have hr : r ∈ neighborhood Γ cp.firstStep := by
      obtain ⟨_,_,hr,_,_,_⟩ := nine_three_second_center_inputs ctx hb first second
      apply (mem_neighborhood_iff_adjacent Γ).mpr
      rw [← config.fixes_firstStep]
      exact adjacent_act Γ config.g ((mem_neighborhood_iff_adjacent Γ).mp hr)
    change z Γ r ≤ v Γ cp.firstStep
    rw [v,Γ.vAt_def]
    exact le_sSup ⟨r,hr,rfl⟩
  have hVH : VH ≤ E1H := Subgroup.map_mono (by
    have he : E1 = V ⊔ V.conjBy config.first_geometry.x := config.first_geometry.generated
    rw [he]
    exact le_sup_left)
  have hVC : VH ≤ C := hVH.trans hE1C
  have hZaVH : ZaH ≤ VH := Subgroup.map_mono hZaV
  have hZrVH : ZrH ≤ VH := Subgroup.map_mono hZrV
  have hZaBound : ZaH ≤ ZrH ⊔ (pCore 2 C).map C.subtype := by
    have hh := subnormal_conjugate_le_sup_pCore_in p 2 hp2 C F hFC hlocal.2.2 hFp
      VH ZaH hVC (hVp.map embedding) hZaVH (embedding y⁻¹) hyF (hZaConj ▸ hZrVH)
    rwa [hZaConj] at hh
  have hZrQd : ZAt Γ r ≤ QAt Γ d := by
    have hold : ZAt Γ second.l ≤ QAt Γ cp.a' := by
      apply critical_minimality Γ cp
      obtain ⟨_,he⟩ := second.second
      rw [he]
      have hd := path_distance_le Γ cp 2 cp.length (by omega) le_rfl
      simpa only [cp.path_end] using lt_of_le_of_lt hd (by have := cp.length_pos; omega)
    change z Γ (Γ.act config.g second.l) ≤ q Γ (Γ.act config.g cp.a')
    rw [z_act,q_act]
    exact Subgroup.map_mono hold
  let Q := (QAt Γ d).map embedding ⊓ C
  let O := (pCore 2 C).map C.subtype
  let M := Q ⊔ O
  have hZrQ : ZrH ≤ Q := le_inf (Subgroup.map_mono hZrQd) (hZrVH.trans hVC)
  have hZaM : ZaH ≤ M := hZaBound.trans (sup_le_sup_right hZrQ O)
  have hQp : IsPGroup 2 Q := by
    have hdcore : IsPGroup 2 (QAt Γ d) := by
      change IsPGroup 2 (q Γ d)
      rw [q,Γ.twoCoreAt_def]
      exact (pCore_isPGroup (p := 2)).map _
    exact (hdcore.map embedding).to_le inf_le_left
  have hOp : IsPGroup 2 O := (pCore_isPGroup (p := 2)).map _
  have hOC : NormalIn O C := ⟨Subgroup.map_subtype_le _,twoCoreIn_normal C⟩
  have hQO : Q ≤ Subgroup.normalizer O := inf_le_right.trans
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hOC.1).mp hOC.2)
  have hMp : IsPGroup 2 M := hQp.to_sup_of_normal_right' hOp hQO
  have hE1Gd : E1H ≤ (GAt Γ d).map embedding := Subgroup.map_mono config.first_geometry.group_le
  have hE1Q : E1H ≤ Subgroup.normalizer Q := by
    have hnormal := (stabilizer_le_normalizer_q Γ d)
    have hm : (GAt Γ d).map embedding ≤ Subgroup.normalizer ((QAt Γ d).map embedding) := by
      rintro z ⟨a,ha,rfl⟩
      exact Subgroup.le_normalizer_map embedding (Subgroup.mem_map_of_mem embedding (hnormal ha))
    exact (le_inf (hE1Gd.trans hm) (hE1C.trans C.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hE1O : E1H ≤ Subgroup.normalizer O := hE1C.trans
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hOC.1).mp hOC.2)
  have hE1M : E1H ≤ Subgroup.normalizer M :=
    (le_inf hE1Q hE1O).trans (Subgroup.normalizer_inf_normalizer_le_normalizer_sup Q O)
  have hcM : ⁅ZaH,E1H⁆ ≤ M := (Subgroup.commutator_mono hZaM le_rfl).trans
    (Subgroup.le_normalizer_iff_commutator_le_left.mp hE1M)
  have hcp : IsPGroup 2 (⁅ZAt Γ cp.a,E1⁆ : Subgroup G) := by
    have hm : IsPGroup 2 ((⁅ZAt Γ cp.a,E1⁆ : Subgroup G).map embedding) := by
      rw [Subgroup.map_commutator]
      exact hMp.to_le hcM
    exact hm.of_equiv ((⁅ZAt Γ cp.a,E1⁆ : Subgroup G).equivMapOfInjective
      embedding ctx.embedding_injective).symm
  exact geometric_actor_commutator_not_two Γ d (Γ.act config.g first.l) V E1
    (first.A0.map c.toMonoidHom) config.first_actor config.first_geometry hVp
    (ZAt Γ cp.a) hZaV config.first_actor_initial hcp

end Stellmacher.SectionNine

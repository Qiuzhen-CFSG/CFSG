module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.Statements
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.BaumannCentralizing
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.ThetaObstruction
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalControl
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Action
public import Theory.GroupTheory.ElementaryThompsonFrattini
public import Theory.GroupTheory.SylowNormalGenerationFrattini
public import Theory.GroupTheory.Commutator.SylowNormalGeneration

/-!
# Thompson arguments for an outside overgroup

Both complete local alternatives imply C_T(V) ≤ R ≤ S. In the centralizing
case of 15.3.5, Baumann heredity gives the first alternative of (10).
J(S) is a nontrivial characteristic subgroup of Baum(S), so its normalizer
is controlled by characteristic-normalizer generation. The Thompson
Frattini argument then forces J(I) outside M. Containment of the actual
action kernel carries this conclusion to I/C_I(U_I).

The noncentral image calculation retains the action kernel: equality
of the images of J(T) and S implies S = J(S) C_T(V), not J(T) = S.
The actual S₃ or S₃ × S₃ section in (5) gives Sylow normal generation
through the two-core and Frattini subgroup. Since Y₊ is two-perfect,
this proves Y₊=[Y₊,J(S)], completing the second branch.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.5 and 15.3.11(10)–(11), printed pp.1122–1124.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.OutsideStructure
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The kernel of the action on V stabilizes each of its marked planes. -/
theorem action_kernel_le_plane_stabilizer (d : CharacteristicTwo.LocalData G) :
    (d.T : Subgroup G) ⊓ centralizer (d.V : Set G) ≤ d.S :=
  le_inf inf_le_left (inf_le_right.trans
    ((centralizer_le (d.action.plane_le 1)).trans (Subgroup.centralizer_le_normalizer _)))

omit [Finite G] in
/-- Both full alternatives in (5) give exactly the two core containments
used in the proof of (10), including the rank-one centralizer convention. -/
theorem core_containments_of_local_alternatives (d : CharacteristicTwo.LocalData G)
    (I : Subgroup G) (hlocal : RankTwoCase d I ∨ RankOneCase d I) :
    (d.T : Subgroup G) ⊓ centralizer (d.V : Set G) ≤ d.R ∧ d.R ≤ d.S := by
  have hCS := action_kernel_le_plane_stabilizer d
  rcases hlocal with htwo | hone
  · rw [htwo.2.2.2.2.1]
    exact ⟨le_rfl, hCS⟩
  · rw [hone.2.2.2]
    exact ⟨le_inf hCS (inf_le_right.trans (centralizer_le (d.action.plane_le _))), inf_le_left⟩

omit [Finite G] in
private theorem le_sup_action_kernel (d : CharacteristicTwo.LocalData G)
    (A B : Subgroup G) (hAT : A ≤ (d.T : Subgroup G)) (hBT : B ≤ (d.T : Subgroup G))
    (himage : d.action.image A ≤ d.action.image B) :
    A ≤ B ⊔ ((d.T : Subgroup G) ⊓ centralizer (d.V : Set G)) := by
  intro a ha
  have him : d.action.actor ⟨a, d.sylow_le (hAT ha)⟩ ∈ d.action.image B :=
    himage (mem_map_of_mem d.action.actor ha)
  obtain ⟨b, hb, he⟩ := him
  have hk : b⁻¹ * (⟨a, d.sylow_le (hAT ha)⟩ : d.M) ∈ d.action.actor.ker := by
    change d.action.actor _ = 1
    rw [map_mul, map_inv, he, inv_mul_cancel]
  rw [d.action.ker_actor] at hk
  have hc : (b : G)⁻¹ * a ∈ (d.T : Subgroup G) ⊓ centralizer (d.V : Set G) :=
    ⟨d.T.inv_mem (hBT hb) |> fun hi => d.T.mul_mem hi (hAT ha), hk⟩
  have hm : (b : G) * ((b : G)⁻¹ * a) ∈
      B ⊔ ((d.T : Subgroup G) ⊓ centralizer (d.V : Set G)) := mul_mem_sup hb hc
  simpa only [mul_inv_cancel_left] using hm

/-- The noncentral equality in 15.3.5 is an equality of action images.
Keeping its kernel gives the actual supplement needed for the commutator step. -/
theorem thompson_supplement_of_action_image (d : CharacteristicTwo.LocalData G)
    (himage : d.action.image (elementaryAbelianMaxJ (d.T : Subgroup G)) =
      d.action.image d.S) :
    elementaryAbelianMaxJ d.S = elementaryAbelianMaxJ (d.T : Subgroup G) ∧
      d.S = elementaryAbelianMaxJ d.S ⊔
        ((d.T : Subgroup G) ⊓ centralizer (d.V : Set G)) := by
  have hJT : elementaryAbelianMaxJ (d.T : Subgroup G) ≤ (d.T : Subgroup G) :=
    sSup_le fun _ hA => hA.1
  have hCS := action_kernel_le_plane_stabilizer d
  have hJS : elementaryAbelianMaxJ (d.T : Subgroup G) ≤ d.S :=
    (le_sup_action_kernel d _ _ hJT inf_le_left himage.le).trans (sup_le le_rfl hCS)
  have hJeq := elementaryAbelianMaxJ_eq_of_intermediate (d.T : Subgroup G) d.S hJS inf_le_left
  refine ⟨hJeq, ?_⟩
  rw [hJeq]
  exact le_antisymm (le_sup_action_kernel d _ _ inf_le_left hJT himage.ge) (sup_le hJS hCS)

omit [Finite G] in
private theorem thompson_le_baumann (S : Subgroup G) :
    elementaryAbelianMaxJ S ≤ ChapterB.baumann S := by
  refine le_inf (sSup_le fun _ hA => hA.1) ?_
  intro j hj e he
  exact ((mem_omegaOneCenterAmbient_iff _ _).mp he).2.2 j hj |>.symm

/-- Normalizer control of J(S), together with the Sylow hypothesis, forces
the global Thompson subgroup outside M by the genuine Frattini argument. -/
theorem thompson_outside_of_normalizer_control (I S M : Subgroup G)
    (hSyl : ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = S)
    (hI : ¬ I ≤ M) (hN : normalizer (elementaryAbelianMaxJ S : Set G) ≤ M) :
    ¬ elementaryAbelianMaxJ I ≤ M := by
  obtain ⟨P, hP⟩ := hSyl
  have hmap : (elementaryAbelianMaxJ (P : Subgroup I)).map I.subtype =
      elementaryAbelianMaxJ S := by
    rw [← elementaryAbelianMaxJ_map_injective I.subtype I.subtype_injective, hP]
  have hNP : normalizer (elementaryAbelianMaxJ (P : Subgroup I) : Set I) ≤
      M.subgroupOf I := by
    intro i hi
    apply hN
    rw [← hmap]
    exact le_normalizer_map I.subtype (mem_map_of_mem I.subtype hi)
  intro hJ
  apply hI
  have hJG : elementaryAbelianMaxJ (⊤ : Subgroup I) ≤ M.subgroupOf I := by
    intro j hj
    apply hJ
    have hm := mem_map_of_mem I.subtype hj
    rw [← elementaryAbelianMaxJ_map_injective I.subtype I.subtype_injective,
      ← MonoidHom.range_eq_map, range_subtype] at hm
    exact hm
  intro i hi
  have htop : (⊤ : Subgroup I) ≤ M.subgroupOf I := by
    rw [← elementaryAbelianMaxJ_frattini P]
    exact sup_le hNP hJG
  exact htop (show (⟨i, hi⟩ : I) ∈ (⊤ : Subgroup I) from trivial)

/-- Clauses (10i) and (11) in the centralizing branch. The displayed
Baumann and fixed-center inputs are the actual conclusions of 15.3.5(1);
the core bounds are deduced from the full alternatives of (5). -/
theorem lemma_15_3_11_centralizing (d : CharacteristicTwo.LocalData G) (I : Subgroup G)
    (hI : I ∈ d.Hplus)
    (hSyl : ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = d.S)
    (hC : I ⊓ centralizer (d.UI I : Set G) ≤ d.MI I)
    (hlocal : RankTwoCase d I ∨ RankOneCase d I)
    (hBR : ChapterB.baumann (d.T : Subgroup G) =
      ChapterB.baumann ((d.T : Subgroup G) ⊓ centralizer (d.V : Set G)))
    (hE : d.V ≤ ChapterB.thompsonAlpha (d.T : Subgroup G))
    (hB : (ChapterB.baumann (d.T : Subgroup G)).characteristicNormalizerClosure ≤ d.M) :
    ThompsonAlternative d I ∧
      ¬ d.starImage I (elementaryAbelianMaxJ I) ≤ d.starImage I d.M := by
  obtain ⟨hCR, hRS⟩ := core_containments_of_local_alternatives d I hlocal
  have hBS : ChapterB.baumann (d.T : Subgroup G) ≤ d.S := by
    rw [hBR]
    exact inf_le_left.trans (hCR.trans hRS)
  have hJeq := elementaryAbelianMaxJ_eq_of_intermediate (d.T : Subgroup G) d.S
    ((thompson_le_baumann _).trans hBS) inf_le_left
  have hJne : elementaryAbelianMaxJ d.S ≠ ⊥ := by
    intro he
    have hVJ : d.V ≤ elementaryAbelianMaxJ (d.T : Subgroup G) :=
      hE.trans (fun _ hx => ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1)
    have hV : d.V = ⊥ := le_bot_iff.mp (hVJ.trans_eq (hJeq.symm.trans he))
    have hc := card_eq_one.mpr hV
    rw [d.action.card_vector] at hc
    norm_num at hc
  have hBaum := ChapterB.lemma_B_2_3_4 (d.T : Subgroup G) d.S hBS inf_le_left
  have hN : normalizer (elementaryAbelianMaxJ d.S : Set G) ≤ d.M := by
    apply (normalizer_maxJ_le_characteristicNormalizerClosure d.S (ChapterB.baumann d.S)
      (thompson_le_baumann _) inf_le_left hJne).trans
    rwa [← hBaum]
  have hout := thompson_outside_of_normalizer_control I d.S d.M hSyl hI.2 hN
  refine ⟨Or.inl (lemma_15_3_11_10_centralizing d I hI hBR hB hCR hRS), ?_⟩
  intro him
  have hker : (d.starMap I).ker ≤ d.M.subgroupOf I := by
    rw [CharacteristicTwo.LocalData.starMap, localActionMap, QuotientGroup.ker_mk']
    exact fun x hx => (hC ⟨x.property, hx⟩).1
  have hpre : (elementaryAbelianMaxJ I).subgroupOf I ≤
      d.M.subgroupOf I ⊔ (d.starMap I).ker := map_le_map_iff.mp him
  rw [sup_eq_left.mpr hker] at hpre
  apply hout
  intro j hj
  have hjI : j ∈ I := (show elementaryAbelianMaxJ I ≤ I from sSup_le fun _ hA => hA.1) hj
  exact hpre (show (⟨j, hjI⟩ : I) ∈ (elementaryAbelianMaxJ I).subgroupOf I from hj)

/-- Each Sylow subgroup normally generates Y₊S. This follows from the
literal symmetric-group sections in (5), with Frattini nongeneration in
the rank-two case and the two-core kernel retained in both cases. -/
theorem local_sylow_normal_generation (d : CharacteristicTwo.LocalData G) (I : Subgroup G)
    (hlocal : RankTwoCase d I ∨ RankOneCase d I) (P : Sylow 2 ↥(d.Yplus ⊔ d.S)) :
    normalClosure (P : Set ↥(d.Yplus ⊔ d.S)) = ⊤ := by
  let H := d.Yplus ⊔ d.S
  have hRP : pCore 2 H ≤ (P : Subgroup H) := pCore_isPGroup.le_sylow_of_normal P
  rcases hlocal with htwo | hone
  · obtain ⟨e⟩ := htwo.2.1
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (coreFrattiniSubgroup H))
    apply normalClosure_sylow_eq_top_of_frattini_image P (pCore 2 H) hRP f
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
      _ (symmetric_product_involutions_generate (Fin 3) (Fin 3))
    intro x hx
    change e (QuotientGroup.mk' (coreFrattiniSubgroup H) x) = 1 at hx
    exact (QuotientGroup.eq_one_iff x).mp (e.map_eq_one_iff.mp hx)
  · obtain ⟨e⟩ := hone.2.1
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
    apply normalClosure_sylow_eq_top_of_frattini_image P (pCore 2 H) hRP f
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
      _ (symmetric_involutions_generate (Fin 3))
    intro x hx
    change e (QuotientGroup.mk' (pCore 2 H) x) = 1 at hx
    change QuotientGroup.mk' (pCore 2 H) x ∈ frattini (H ⧸ pCore 2 H)
    rw [e.map_eq_one_iff.mp hx]
    exact one_mem _

omit [Finite G] in
private theorem restrict_sylow_image (H I S : Subgroup G) (hHI : H ≤ I) (hSH : S ≤ H)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S) :
    ∃ Q : Sylow 2 H, (Q : Subgroup H).map H.subtype = S := by
  let f : H →* I := inclusion hHI
  have hPr : (P : Subgroup I) ≤ f.range := by
    intro x hx
    have hxS : (x : G) ∈ S := hP ▸ mem_map_of_mem I.subtype hx
    exact ⟨⟨x, hSH hxS⟩, rfl⟩
  let Q := P.comapOfInjective f (inclusion_injective hHI) hPr
  have hmap : (Q : Subgroup H).map f = (P : Subgroup I) := map_comap_eq_self hPr
  refine ⟨Q, ?_⟩
  calc
    (Q : Subgroup H).map H.subtype = ((Q : Subgroup H).map f).map I.subtype := by
      rw [map_map]
      rfl
    _ = S := by rw [hmap, hP]

private theorem chosen_isPPerfect (d : CharacteristicTwo.LocalData G) : IsPPerfect 2 d.Yplus := by
  rw [← chosen_residual_eq d.M d.Mc d.S d.V₁ d.Yplus d.choice]
  intro N hN hp
  have h := BenderSuzuki.External.hktPResidual_le N hN hp
  rw [twoResidualAmbient_has_top_twoResidual] at h
  exact top_unique h

/-- The noncentral branch of (10) follows from the genuine equality of
action images, the full local alternatives, and clause (4). No commutator
identity or Thompson containment is used as an input. -/
theorem lemma_15_3_11_noncentral_commutator (d : CharacteristicTwo.LocalData G) (I : Subgroup G)
    (hI : I ∈ d.Hplus)
    (hSyl : ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = d.S)
    (hN : I ⊓ normalizer (d.Yplus : Set G) = d.MI I)
    (hlocal : RankTwoCase d I ∨ RankOneCase d I)
    (himage : d.action.image (elementaryAbelianMaxJ (d.T : Subgroup G)) = d.action.image d.S) :
    d.Yplus = ⁅d.Yplus, elementaryAbelianMaxJ d.S⁆ := by
  let H := d.Yplus ⊔ d.S
  let Y := d.Yplus.subgroupOf H
  let A := (elementaryAbelianMaxJ d.S).subgroupOf H
  have hYH : d.Yplus ≤ H := le_sup_left
  have hJH : elementaryAbelianMaxJ d.S ≤ H :=
    (show elementaryAbelianMaxJ d.S ≤ d.S from sSup_le fun _ hA => hA.1).trans le_sup_right
  have hSn : d.S ≤ normalizer (d.Yplus : Set G) := by
    intro s hs
    exact (hN.ge ⟨d.sylow_le hs.1,
      (show d.S ≤ I from le_sup_right.trans hI.1.2) hs⟩).2
  let : Y.Normal := normal_subgroupOf_of_le_normalizer (sup_le d.Yplus.le_normalizer hSn)
  have hY : IsPPerfect 2 Y :=
    (chosen_isPPerfect d).of_surjective (subgroupOfEquivOfLe hYH).symm.toMonoidHom
      (subgroupOfEquivOfLe hYH).symm.surjective
  obtain ⟨P, hP⟩ := hSyl
  obtain ⟨Q, hQ⟩ := restrict_sylow_image H I d.S hI.1.2 le_sup_right P hP
  have hgen : Y ⊔ (Q : Subgroup H) = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hYH, hQ, ← MonoidHom.range_eq_map, range_subtype]
  have hA : (Q : Subgroup H) ≤ normalizer (A : Set H) := by
    rw [← subgroupOf_normalizer_eq hJH]
    intro q hq
    exact ambient_normalizes_thompson d.S (hQ ▸ mem_map_of_mem H.subtype hq)
  have hcover : (Q : Subgroup H) ≤ A ⊔ pCore 2 H := by
    apply (map_le_map_iff_of_injective H.subtype_injective).mp
    rw [Subgroup.map_sup, hQ, map_subgroupOf_eq_of_le hJH]
    exact (thompson_supplement_of_action_image d himage).2.le.trans
      (sup_le_sup_left (core_containments_of_local_alternatives d I hlocal).1 _)
  have hcomm := eq_commutator_of_sylow_normal_generation Q Y A (pCore 2 H) hgen hY hA
    (pCore_isPGroup.le_sylow_of_normal Q) hcover (local_sylow_normal_generation d I hlocal Q)
  have hm := congrArg (map H.subtype) hcomm
  rwa [map_commutator, map_subgroupOf_eq_of_le hYH, map_subgroupOf_eq_of_le hJH] at hm

/-- Both requested clauses in the noncentral branch, using the already
proved theta obstruction in the actual centralizer quotient. -/
theorem lemma_15_3_11_noncentral (d : CharacteristicTwo.LocalData G) (I : Subgroup G)
    (hI : I ∈ d.Hplus)
    (hSyl : ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = d.S)
    (hC : I ⊓ centralizer (d.UI I : Set G) ≤ d.MI I)
    (hN : I ⊓ normalizer (d.Yplus : Set G) = d.MI I)
    (hlocal : RankTwoCase d I ∨ RankOneCase d I)
    (hθ : theta (d.MI I) = d.Yplus)
    (himage : d.action.image (elementaryAbelianMaxJ (d.T : Subgroup G)) = d.action.image d.S) :
    ThompsonAlternative d I ∧
      ¬ d.starImage I (elementaryAbelianMaxJ I) ≤ d.starImage I d.M := by
  have hc := lemma_15_3_11_noncentral_commutator d I hI hSyl hN hlocal himage
  have hout := lemma_15_3_11_11_of_commutator d I hI hSyl hC hθ hN hc
  exact ⟨Or.inr ⟨hc, hout.1⟩, hout.2⟩

/-- Clauses (10) and (11), from the complete earlier Thompson dichotomy
15.3.5 and the separate clauses (1),(2),(4),(5),(6) of 15.3.11.
The parent supplies those source inputs; neither the full Conclusions
record nor either of the present conclusions is a hypothesis. -/
theorem lemma_15_3_11_10_11 (d : CharacteristicTwo.LocalData G) (I : Subgroup G)
    (hI : I ∈ d.Hplus)
    (hSyl : ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = d.S)
    (hC : I ⊓ centralizer (d.UI I : Set G) ≤ d.MI I)
    (hN : I ⊓ normalizer (d.Yplus : Set G) = d.MI I)
    (hlocal : RankTwoCase d I ∨ RankOneCase d I)
    (hθ : d.Yplus = theta (d.MI I))
    (h35 :
      (⁅d.V, elementaryAbelianMaxJ (d.T : Subgroup G)⁆ = ⊥ ∧
        ChapterB.baumann (d.T : Subgroup G) =
          ChapterB.baumann ((d.T : Subgroup G) ⊓ centralizer (d.V : Set G)) ∧
        d.V ≤ ChapterB.thompsonAlpha (d.T : Subgroup G) ∧
        (ChapterB.baumann (d.T : Subgroup G)).characteristicNormalizerClosure ≤ d.M) ∨
      (d.action.image (ChapterB.baumann (d.T : Subgroup G)) =
          d.action.image (elementaryAbelianMaxJ (d.T : Subgroup G)) ∧
        d.action.image (elementaryAbelianMaxJ (d.T : Subgroup G)) = d.action.image d.S ∧
        Nonempty (d.action.image d.S ≃* OrthogonalPlaneVector) ∧
        ChapterB.thompsonAlpha (d.T : Subgroup G) ⊓ d.V = d.ZS ∧
        Nonempty (d.ZS ≃* OrthogonalPlaneVector))) :
    ThompsonAlternative d I ∧
      ¬ d.starImage I (elementaryAbelianMaxJ I) ≤ d.starImage I d.M := by
  rcases h35 with hc | hn
  · exact lemma_15_3_11_centralizing d I hI hSyl hC hlocal hc.2.1 hc.2.2.1 hc.2.2.2
  · exact lemma_15_3_11_noncentral d I hI hSyl hC hN hlocal hθ.symm hn.2.1

end CFSG.Quasithin.Chapter15.Section03.OutsideStructure
end

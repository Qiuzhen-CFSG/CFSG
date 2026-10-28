module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalAlternating

/-!
# The escaping S₅ preimage in the original four-space overgroup

In the contrary order-four branch, extend a five-letter permutation to an
even seven-letter permutation by correcting its sign on the complementary
pair. Sylow conjugacy positions this S₅ around the image of the original T.
Its full preimage in L₀ has index 21 and nontrivial two-core.

Every element of M intersected with L₀ preserves Z_S = U intersected with V.
A group of order five preserving a four-subgroup of a group of order sixteen
acts trivially, by fixed-point counting. Thus the faithful S₅ image on U
forces its original preimage outside M. The full centralizer of U has
exponent dividing four: its action on V has displacement in the fixed plane
Z_S, so its squares lie in C_M(V) = V. This identifies the preimage's
literal two-core quotient as S₅, with O₂(Y) = C_Y(U).

Source: Aschbacher--Smith, 6.2.11, printed p.686. The index-five intersection
with M, H-star minimality and generation parameter two remain to be proved.
No LocalAnalysis or later identification is assumed. The signed embedding
adapts the existing four-letter construction in
`Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.NaturalFixed`.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Equiv Equiv.Perm
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalQuotientAction
private def signPair : ℤˣ →* Perm (Fin 2) where
  toFun s := if s = 1 then 1 else swap 0 1
  map_one' := by simp
  map_mul' a b := by
    rcases Int.units_eq_one_or a with rfl | rfl <;>
      rcases Int.units_eq_one_or b with rfl | rfl <;> decide
private def fiveLetterExtension : Perm (Fin 5) →* Perm (Fin 7) :=
  (Equiv.permCongrHom (finSumFinEquiv : Fin 5 ⊕ Fin 2 ≃ Fin 7)).toMonoidHom.comp
    ((sumCongrHom (Fin 5) (Fin 2)).comp
      ((MonoidHom.id (Perm (Fin 5))).prod (signPair.comp sign)))
private theorem fiveLetterExtension_even (σ : Perm (Fin 5)) :
    fiveLetterExtension σ ∈ alternatingGroup (Fin 7) := by
  rw [mem_alternatingGroup]
  change sign ((finSumFinEquiv : Fin 5 ⊕ Fin 2 ≃ Fin 7).permCongr
    (Equiv.sumCongr σ (signPair (sign σ)))) = 1
  rw [sign_permCongr, sign_sumCongr]
  rcases Int.units_eq_one_or (sign σ) with h | h <;> rw [h] <;> decide
private def fiveEmbedding : Perm (Fin 5) →* alternatingGroup (Fin 7) :=
  fiveLetterExtension.codRestrict _ fiveLetterExtension_even
private theorem fiveEmbedding_injective : Function.Injective fiveEmbedding := by
  intro σ τ h
  have hp := (Equiv.permCongrHom finSumFinEquiv).injective (congrArg Subtype.val h)
  have hq := sumCongrHom_injective hp
  exact congrArg Prod.fst hq

private theorem seven_sylow_symmetric_five (S : Sylow 2 (alternatingGroup (Fin 7))) :
    ∃ B : Subgroup (alternatingGroup (Fin 7)), (S : Subgroup _) ≤ B ∧
      B.index = 21 ∧ Nonempty (B ≃* Perm (Fin 5)) := by
  let A7 := alternatingGroup (Fin 7)
  let B := fiveEmbedding.range
  have hc : Nat.card B = 120 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective fiveEmbedding_injective).toEquiv,
      Nat.card_perm, Nat.card_fin]
    norm_num [Nat.factorial]
  let Q : Sylow 2 B := default
  have hQcard : Nat.card ((Q : Subgroup B).map B.subtype) = 8 := by
    rw [card_map_of_injective B.subtype_injective, Q.card_eq_multiplicity, hc]
    decide +kernel
  let Q7 : Sylow 2 A7 := Sylow.ofCard ((Q : Subgroup B).map B.subtype) (by
    rw [hQcard, nat_card_alternatingGroup, Nat.card_fin]
    decide +kernel)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A7 Q7 S
  let e := MulAut.conj g
  let C := B.map e.toMonoidHom
  have hS : (S : Subgroup A7) = ((Q : Subgroup B).map B.subtype).map e.toMonoidHom := by
    have hh := congrArg (fun Q : Sylow 2 A7 => (Q : Subgroup A7)) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hh
    exact hh.symm
  refine ⟨C, ?_, ?_, ⟨(e.subgroupMap B).symm.trans
    (MonoidHom.ofInjective fiveEmbedding_injective).symm⟩⟩
  · rw [hS]
    exact map_mono (map_subtype_le _)
  · have hh := C.card_mul_index
    rw [card_map_of_injective e.injective, hc, nat_card_alternatingGroup] at hh
    norm_num [Nat.factorial] at hh
    omega

private theorem no_five_on_sixteen_plane {E : Type*} [Group E] [Finite E]
    (hE : Nat.card E = 16) (B : Subgroup (MulAut E)) (W : Subgroup E)
    (hW : Nat.card W = 4) (hBW : ∀ b ∈ B, ∀ x, x ∈ W ↔ b x ∈ W) :
    ¬ 5 ∣ Nat.card B := by
  classical
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  intro hd
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := B) 5 hd
  let A := zpowers b
  have hA : IsPGroup 5 A := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hb]; decide)
  let : IsInvariant A E W := ⟨fun a x => hBW a.val.val a.val.property x⟩
  have hmW := hA.card_modEq_card_fixedPoints W
  change Nat.card W % 5 = Nat.card (FixedPoints.subgroup A W) % 5 at hmW
  have hleW := (FixedPoints.subgroup A W).card_le_card_group
  rw [hW] at hmW hleW
  have hcW : Nat.card (FixedPoints.subgroup A W) = 4 := by omega
  have htopW : FixedPoints.subgroup A W = ⊤ :=
    eq_top_of_card_eq _ (hcW.trans hW.symm)
  have hWF : W ≤ FixedPoints.subgroup A E := by
    intro x hx a
    have hh : (⟨x,hx⟩ : W) ∈ FixedPoints.subgroup A W := htopW ▸ mem_top _
    exact congrArg Subtype.val (hh a)
  have hlow : 4 ≤ Nat.card (FixedPoints.subgroup A E) := by
    rw [← hW]
    exact Nat.le_of_dvd Nat.card_pos (card_dvd_of_le hWF)
  have hm := hA.card_modEq_card_fixedPoints E
  change Nat.card E % 5 = Nat.card (FixedPoints.subgroup A E) % 5 at hm
  rw [hE] at hm
  have hdiv : Nat.card (FixedPoints.subgroup A E) ∣ 2 ^ 4 := by
    rw [show 2 ^ 4 = 16 by decide, ← hE]
    exact (FixedPoints.subgroup A E).card_subgroup_dvd_card
  obtain ⟨k,hk,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  have hcard : Nat.card (FixedPoints.subgroup A E) = 16 := by
    interval_cases k <;> norm_num only [Nat.reducePow] at he <;> omega
  have htop : FixedPoints.subgroup A E = ⊤ := eq_top_of_card_eq _ (hcard.trans hE.symm)
  have hb1 : b = 1 := by
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    have hx : x ∈ FixedPoints.subgroup A E := htop ▸ mem_top x
    exact hx ⟨b, mem_zpowers b⟩
  rw [hb1, orderOf_one] at hb
  contradiction

variable {G : Type*} [Group G] [Finite G] {P : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- The full preimage of a positioned five-letter subgroup, retaining its
actual kernel on the original closure. -/
theorem four_symmetric_five_preimage
    (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hNL : normalizer (layer L R : Set G) ≤ normalizer (L : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    ∃ Y : Subgroup G, (P : Subgroup G) ≤ Y ∧ Y ≤ fourOvergroup (P : Subgroup G) L z ∧
      Y.relIndex (fourOvergroup (P : Subgroup G) L z) = 21 ∧
      Y ∈ Chapter1.HOver G (P : Set G) ∧
      ∃ f : Y →* Perm (Fin 5), Function.Surjective f ∧
        f.ker = (centralizer (sourceClosure (P : Subgroup G) L R z : Set G)).subgroupOf Y := by
  classical
  let X := fourOvergroup (P : Subgroup G) L z
  have hPX : (P : Subgroup G) ≤ X := hP.trans le_sup_right
  obtain ⟨q, hq, hker⟩ := four_overgroup_alternating_quotient h hnatural hz ho hP hplane hNL hcard
  let S := (P.subtype hPX).mapSurjective hq
  obtain ⟨B, hSB, hBi, ⟨eB⟩⟩ := seven_sylow_symmetric_five S
  let J := B.comap q
  let Y := J.map X.subtype
  have hYX : Y ≤ X := map_subtype_le J
  have hPY : (P : Subgroup G) ≤ Y := by
    intro x hx
    refine ⟨⟨x, hPX hx⟩, ?_, rfl⟩
    exact hSB (mem_map_of_mem q (show (⟨x, hPX hx⟩ : X) ∈ P.subtype hPX from hx))
  have hYJ : Y.subgroupOf X = J := J.comap_map_eq_self_of_injective X.subtype_injective
  have hYindex : Y.relIndex X = 21 := by
    change (Y.subgroupOf X).index = 21
    rw [hYJ, index_comap_of_surjective _ hq, hBi]
  let b : Y →* B := (q.comp (inclusion hYX)).codRestrict B (by
    intro y
    have hy : inclusion hYX y ∈ J := by
      rw [← hYJ]
      exact y.property
    exact hy)
  have hb : Function.Surjective b := by
    intro b0
    obtain ⟨x, hx⟩ := hq b0.val
    have hxJ : x ∈ J := by change q x ∈ B; rw [hx]; exact b0.property
    exact ⟨⟨x.val, mem_map_of_mem X.subtype hxJ⟩, Subtype.ext hx⟩
  have hUY : sourceClosure (P : Subgroup G) L R z ≤ Y := by
    have hc := pCoreIn_le_sylow (Centralizer z) (P.subtype hP)
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hP] at hc
    exact ((local_closure_core h hnatural hz ho hP).1.trans hc).trans hPY
  have hYH : Y ∈ Chapter1.HOver G (P : Set G) := by
    refine ⟨?_, hPY⟩
    change Y.pCoreIn 2 ≠ ⊥
    have hu : sourceClosure (P : Subgroup G) L R z ≤ Y.pCoreIn 2 :=
      le_pCoreIn_of_normalizes
        (by
          let := four_closure_elementary h hnatural hz ho hP hplane hcard
          exact IsElementaryAbelian.isPGroup 2 _)
        hUY (hYX.trans (four_generated_overgroup_normalizes_closure h hnatural hz ho hP hplane hNL hcard))
    intro he
    have hu0 := bot_unique (he ▸ hu)
    have hc := four_closure_card h hnatural hz ho hP hplane hcard
    rw [hu0, card_bot] at hc
    contradiction
  refine ⟨Y, hPY, hYX, hYindex, hYH, eB.toMonoidHom.comp b, eB.surjective.comp hb, ?_⟩
  rw [MonoidHom.ker_comp_of_injective _ _ eB.injective]
  ext y
  change b y = 1 ↔ (y : G) ∈ centralizer (sourceClosure (P : Subgroup G) L R z : Set G)
  have he : b y = 1 ↔ q (inclusion hYX y) = 1 := Subtype.ext_iff
  rw [he, ← MonoidHom.mem_ker, hker]
  rfl

/-- Within the actual four-space overgroup, every element of M preserves
the source plane. This uses both original normal subgroups U and V. -/
theorem four_maximal_intersection_normalizes_plane
    (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hNL : normalizer (layer L R : Set G) ≤ normalizer (L : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    M ⊓ fourOvergroup (P : Subgroup G) L z ≤ normalizer (ZS (P : Subgroup G) L R : Set G) := by
  have hm : M ≤ normalizer (layer L R : Set G) := by
    rw [← (four_component_and_maximal_core_eq_layer h hnatural hz ho hP hplane hNL hcard).2]
    exact M.le_normalizer.trans (normalizer_le_normalizer_characteristic_image M (pCore 2 M))
  have hu := four_generated_overgroup_normalizes_closure h hnatural hz ho hP hplane hNL hcard
  have hi := (four_intersection_geometry h hnatural hz ho hP hplane hcard).2.2.1
  rw [← hi]
  exact (inf_le_inf hm hu).trans inf_normalizer_le_normalizer_inf


/-- A five-letter quotient with the actual U-centralizer kernel cannot lie
in M: a quintic action on sixteen cannot preserve the original four-plane. -/
theorem four_symmetric_preimage_not_le
    (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hNL : normalizer (layer L R : Set G) ≤ normalizer (L : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4)
    {Y : Subgroup G} (hYX : Y ≤ fourOvergroup (P : Subgroup G) L z)
    (f : Y →* Perm (Fin 5)) (hf : Function.Surjective f)
    (hfker : f.ker = (centralizer (sourceClosure (P : Subgroup G) L R z : Set G)).subgroupOf Y) :
    ¬ Y ≤ M := by
  intro hYM
  let U := sourceClosure (P : Subgroup G) L R z
  let W := (ZS (P : Subgroup G) L R).subgroupOf U
  have hSU : ZS (P : Subgroup G) L R ≤ U :=
    (ZS_le_sourceClosure_intersection h hz).trans inf_le_left
  have hYU := hYX.trans (four_generated_overgroup_normalizes_closure h hnatural hz ho hP hplane hNL hcard)
  let b : Y →* MulAut U := U.normalizerMonoidHom.comp (inclusion hYU)
  have hker : b.ker = f.ker := by
    rw [hfker]
    ext y
    change U.normalizerMonoidHom (inclusion hYU y) = 1 ↔ (y : G) ∈ centralizer (U : Set G)
    rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker]
    rfl
  have hc : Nat.card b.range = 120 := by
    have hh := congrArg Subgroup.index hker
    rw [index_ker, index_ker, MonoidHom.range_eq_top.mpr hf, card_top,
      Nat.card_perm, Nat.card_fin] at hh
    exact hh.trans (by decide)
  have hYW : Y ≤ normalizer (ZS (P : Subgroup G) L R : Set G) :=
    (le_inf hYM hYX).trans (four_maximal_intersection_normalizes_plane h hnatural hz ho hP hplane hNL hcard)
  have hBW : ∀ a ∈ b.range, ∀ x : U, x ∈ W ↔ a x ∈ W := by
    rintro a ⟨y,rfl⟩ x
    exact mem_normalizer_iff.mp (hYW y.property) x.val
  have hn := no_five_on_sixteen_plane (four_closure_card h hnatural hz ho hP hplane hcard)
    b.range W ((Nat.card_congr (subgroupOfEquivOfLe hSU).toEquiv).trans
      (h.natural_ZS_geometry hnatural).2.1) hBW
  rw [hc] at hn
  exact hn (by decide)

/-- The actual escaping S₅ preimage in the source overgroup, before proving
its minimality outside M and its generation parameter. -/
theorem four_exists_escaping_symmetric_five
    (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hNL : normalizer (layer L R : Set G) ≤ normalizer (L : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    ∃ Y : Subgroup G, (P : Subgroup G) ≤ Y ∧ Y ≤ fourOvergroup (P : Subgroup G) L z ∧
      Y.relIndex (fourOvergroup (P : Subgroup G) L z) = 21 ∧
      Y ∈ Chapter1.HOver G (P : Set G) ∧ ¬ Y ≤ M ∧
      ∃ f : Y →* Perm (Fin 5), Function.Surjective f ∧
        f.ker = (centralizer (sourceClosure (P : Subgroup G) L R z : Set G)).subgroupOf Y := by
  obtain ⟨Y,hPY,hYX,hi,hY,f,hf,hk⟩ :=
    four_symmetric_five_preimage h hnatural hz ho hP hplane hNL hcard
  exact ⟨Y,hPY,hYX,hi,hY,four_symmetric_preimage_not_le h hnatural hz ho hP hplane hNL hcard hYX f hf hk,
    f,hf,hk⟩

/-- In the order-four branch the full ambient centralizer of U is a
2-group. Its action on V has displacement in the fixed plane Z_S, so
its squares centralize V and its fourth powers are trivial. -/
theorem four_closure_centralizer_isPGroup
    (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hNL : normalizer (layer L R : Set G) ≤ normalizer (L : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    IsPGroup 2 (centralizer (sourceClosure (P : Subgroup G) L R z : Set G)) := by
  let U := sourceClosure (P : Subgroup G) L R z
  let V := layer L R
  let S := ZS (P : Subgroup G) L R
  let K := centralizer (U : Set G)
  let := h.layer_elementary
  have hSU : S ≤ U := (ZS_le_sourceClosure_intersection h hz).trans inf_le_left
  have hKM : K ≤ M := (centralizer_le hSU).trans hnatural.2.2.2.1
  have hcore : M.pCoreIn 2 = V :=
    (four_component_and_maximal_core_eq_layer h hnatural hz ho hP hplane hNL hcard).2
  have hMN : M ≤ normalizer (V : Set G) := by
    rw [← hcore]
    exact M.le_normalizer.trans (normalizer_le_normalizer_characteristic_image M (pCore 2 M))
  have hVK : V ≤ normalizer (K : Set G) :=
    ((layer_le_involution_centralizer h hz).trans (closure_normalized _ _ _ _)).trans
      (normalizer_le_normalizer_centralizer U)
  have hcomm : ⁅K,V⁆ ≤ S := by
    change ⁅K,V⁆ ≤ ZS (P : Subgroup G) L R
    rw [← four_layer_centralizer_closure h hnatural hz ho hP hplane hcard]
    exact le_inf (le_normalizer_iff_commutator_le_right.mp (hKM.trans hMN))
      (le_normalizer_iff_commutator_le_left.mp hVK)
  have hself : M ⊓ centralizer (V : Set G) ≤ V := by
    rw [← hcore]
    exact Chapter1.twoLocal_mem_He_of_sylow_le P (h.simpleQTKE.evenCharacteristic P)
      h.maximal.1 h.sylow_le
  intro c
  have hcV : (c : G) ^ 2 ∈ V := by
    apply hself
    refine ⟨M.pow_mem (hKM c.property) 2, ?_⟩
    intro v hv
    let d := (c : G) * v * (c : G)⁻¹ * v⁻¹
    have hd : d ∈ S := hcomm (commutator_mem_commutator c.property hv)
    have hd2 : d * d = 1 := by
      simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) d (show d ∈ V from hd.1)
    have hcd : (c : G) * d = d * (c : G) := (c.property d (hSU hd)).symm
    have hcv : (c : G) * v * (c : G)⁻¹ = d * v := by dsimp [d]; group
    have hs : (c : G)^2 * v * ((c : G)^2)⁻¹ = v := by
      calc
        _ = (c : G) * ((c : G) * v * (c : G)⁻¹) * (c : G)⁻¹ := by rw [pow_two]; group
        _ = (c : G) * (d * v) * (c : G)⁻¹ := by rw [hcv]
        _ = d * ((c : G) * v * (c : G)⁻¹) := by rw [← mul_assoc, hcd]; group
        _ = d * (d * v) := by rw [hcv]
        _ = v := by rw [← mul_assoc, hd2, one_mul]
    exact (mul_inv_eq_iff_eq_mul.mp hs).symm
  refine ⟨2, ?_⟩
  apply Subtype.ext
  change (c : G) ^ 4 = 1
  have hh := elemPow_eq_one_of_isElementaryAbelian (p := 2) ((c : G)^2) hcV
  exact (pow_mul (c : G) 2 2).trans hh


private theorem five_twoCore : pCore 2 (Perm (Fin 5)) = ⊥ := by
  by_contra hn
  have hnt : Nontrivial (pCore 2 (Perm (Fin 5))) := (nontrivial_iff_ne_bot _).mpr hn
  have hle := Perm.alternatingGroup_le_of_normal (by simp : 5 ≤ Nat.card (Fin 5)) hnt
  have hdiv : 60 ∣ Nat.card (pCore 2 (Perm (Fin 5))) := by
    have hc : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
      decide
    exact hc ▸ card_dvd_of_le hle
  obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := Perm (Fin 5))).exists_card_eq
  have hthree : 3 ∣ 2 ^ k := hk ▸ (dvd_trans (by decide : 3 ∣ 60) hdiv)
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hthree)

/-- The escaping preimage has the source's literal two-core quotient S₅.
Its kernel is the centralizer of U in the original ambient group. -/
theorem four_exists_escaping_symmetric_core_quotient
    (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hNL : normalizer (layer L R : Set G) ≤ normalizer (L : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    ∃ Y : Subgroup G, (P : Subgroup G) ≤ Y ∧ Y ≤ fourOvergroup (P : Subgroup G) L z ∧
      Y.relIndex (fourOvergroup (P : Subgroup G) L z) = 21 ∧
      Y ∈ Chapter1.HOver G (P : Set G) ∧ ¬ Y ≤ M ∧
      Nonempty ((Y ⧸ pCore 2 Y) ≃* Perm (Fin 5)) ∧
      Y.pCoreIn 2 = Y ⊓ centralizer (sourceClosure (P : Subgroup G) L R z : Set G) := by
  obtain ⟨Y,hPY,hYX,hi,hY,hout,f,hf,hk⟩ :=
    four_exists_escaping_symmetric_five h hnatural hz ho hP hplane hNL hcard
  have hkp : IsPGroup 2 f.ker := by
    rw [hk]
    exact (four_closure_centralizer_isPGroup h hnatural hz ho hP hplane hNL hcard).comap_subtype
  have hcore : f.ker = pCore 2 Y := by
    simpa only [five_twoCore, MonoidHom.comap_bot] using f.comap_pCore_of_ker_isPGroup hf hkp
  refine ⟨Y,hPY,hYX,hi,hY,hout,?_,?_⟩
  · exact ⟨(QuotientGroup.quotientMulEquivOfEq hcore.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩
  · rw [pCoreIn, ← hcore, hk, subgroupOf_map_subtype, inf_comm]

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalQuotientAction

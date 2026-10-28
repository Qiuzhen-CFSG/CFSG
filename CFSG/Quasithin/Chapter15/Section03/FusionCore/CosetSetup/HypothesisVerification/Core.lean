module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.Reductions
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.SubnormalSupplement
public import Theory.GroupTheory.PCoreRestriction

/-!
# The relative normal core in the verification of F.9.1

The normal core is taken inside H before taking its two-residual. Its
quotient-centralizer condition implies normalization of Z_S, hence containment
in M by 15.3.46(5). The product C_M(Z) = C_M(V)T then makes the action of
this core on V a two-group, so its two-residual centralizes V.

The local inputs in the statements below are explicit earlier conclusions;
these calculations do not yet assert all of 15.3.48 or F.9.1. In particular,
the extraspecial branch must retain C_Y(V) ≤ H when placing L₁ in H.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.48,
printed pp.1141–1142; Hypothesis F.9.1, printed pp.317–318.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup

variable {G : Type*} [Group G]

private theorem twoResidualSubgroup_eq_pResidual [Finite G] (A : Subgroup G) :
    Stellmacher.twoResidualSubgroup A = pResidual 2 A := by
  unfold Stellmacher.twoResidualSubgroup pResidual
  congr 1
  ext N
  constructor
  · rintro ⟨hN, n, hn⟩
    let := hN
    exact ⟨hN, IsPGroup.iff_card.mpr ⟨n, by simpa [Subgroup.index_eq_card] using hn⟩⟩
  · rintro ⟨hN, hp⟩
    let := hN
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
    exact ⟨hN, n, by simpa [Subgroup.index_eq_card] using hn⟩

private theorem twoResidualAmbient_eq_pResidual [Finite G] (A : Subgroup G) :
    Stellmacher.twoResidualAmbient A = (pResidual 2 A).map A.subtype := by
  rw [Stellmacher.twoResidualAmbient, twoResidualSubgroup_eq_pResidual]

/-- Embedding the relative core and then taking its residual gives exactly
the source's embedded residual. -/
theorem centralizerCoreResidual_eq_residual_image [Finite G]
    (H A Z : Subgroup G) [(Z.subgroupOf H).Normal] :
    centralizerCoreResidual H A Z =
      Stellmacher.twoResidualAmbient ((centralizerCore H A Z).map H.subtype) := by
  simp only [centralizerCoreResidual, twoResidualAmbient_eq_pResidual]
  exact map_embedded_pResidual 2 (centralizerCore H A Z) H.subtype

/-- The residual of the relative normal core is normal in H, not necessarily
in the ambient group. -/
theorem centralizerCoreResidual_normal [Finite G]
    (H A Z : Subgroup G) [(Z.subgroupOf H).Normal] :
    ((centralizerCoreResidual H A Z).subgroupOf H).Normal := by
  rw [centralizerCoreResidual, ← comap_subtype, comap_map_eq_self_of_injective H.subtype_injective,
    twoResidualAmbient_eq_pResidual]
  exact ConjAct.normal_of_characteristic_of_normal

/-- The embedded normal-core residual has no nontrivial two-group quotient. -/
theorem centralizerCoreResidual_isPPerfect [Finite G]
    (H A Z : Subgroup G) [(Z.subgroupOf H).Normal] :
    IsPPerfect 2 (centralizerCoreResidual H A Z) := by
  rw [centralizerCoreResidual_eq_residual_image, twoResidualAmbient_eq_pResidual]
  exact isPPerfect_embedded_pResidual 2 _

/-- Centralizing A/Z implies normalizing A when Z ≤ A. This uses the actual
relative quotient centralizer and does not assume normality of A in H. -/
theorem quotientCentralizer_image_le_normalizer
    (H A Z : Subgroup G) [(Z.subgroupOf H).Normal]
    (hAH : A ≤ H) (hZA : Z ≤ A) :
    (quotientCentralizer H A Z).map H.subtype ≤ normalizer (A : Set G) := by
  apply le_normalizer_iff.mpr
  rintro x ⟨x, hx, rfl⟩ a ha
  have hc := hZA ((mem_quotientCentralizer_iff H A Z hAH x).mp hx a ha)
  have he : (x : G) * a * (x : G)⁻¹ = ⁅a, (x : G)⁆⁻¹ * a := by
    simp only [commutatorElement_def]
    group
  change (x : G) * a * (x : G)⁻¹ ∈ A
  rw [he]
  exact A.mul_mem (A.inv_mem hc) ha

/-- The normal core lies in M by 15.3.46(5), before taking any residual. -/
theorem centralizerCore_image_le
    (M H A Z : Subgroup G) [(Z.subgroupOf H).Normal]
    (hAH : A ≤ H) (hZA : Z ≤ A) (hAM : normalizer (A : Set G) ≤ M) :
    (centralizerCore H A Z).map H.subtype ≤ M :=
  (map_mono (quotientCentralizer H A Z).normalCore_le).trans
    ((quotientCentralizer_image_le_normalizer H A Z hAH hZA).trans hAM)

/-- The centralizer factorization of 15.3.7 proves X ≤ C_M(V). Neither this
bound nor the vanishing of X is an input. -/
theorem centralizerCoreResidual_le_centralizer [Finite G]
    (M H V A Z : Subgroup G) (T : Sylow 2 G) [(Z.subgroupOf H).Normal]
    (hAH : A ≤ H) (hZA : Z ≤ A) (hAM : normalizer (A : Set G) ≤ M)
    (hM : M ≤ normalizer (V : Set G)) (hTM : (T : Subgroup G) ≤ M)
    (hHZ : H ≤ centralizer (Z : Set G))
    (hfactor : ∀ x ∈ M ⊓ centralizer (Z : Set G),
      ∃ c ∈ M ⊓ centralizer (V : Set G), ∃ t ∈ (T : Subgroup G), c * t = x) :
    centralizerCoreResidual H A Z ≤ M ⊓ centralizer (V : Set G) := by
  have hKM := centralizerCore_image_le M H A Z hAH hZA hAM
  have hKH : (centralizerCore H A Z).map H.subtype ≤ H := map_subtype_le _
  rw [centralizerCoreResidual_eq_residual_image]
  have hr := residual_centralizes_of_two_supplement
    ((centralizerCore H A Z).map H.subtype) V (T : Subgroup G)
    (hKM.trans hM) (hTM.trans hM) T.isPGroup' (fun x hx => by
      obtain ⟨c, hc, t, ht, he⟩ := hfactor x ⟨hKM hx, hHZ (hKH hx)⟩
      exact ⟨c, hc.2, t, ht, he⟩)
  exact hr.trans (inf_le_inf_right _ hKM)

/-- The same product calculation places L₁=O²(C_Y(Z)) in C_Y(V). -/
theorem localL1_le_centralizer [Finite G]
    (M Y V Z : Subgroup G) (T : Sylow 2 G)
    (hYM : Y ≤ M) (hM : M ≤ normalizer (V : Set G))
    (hTM : (T : Subgroup G) ≤ M)
    (hfactor : ∀ x ∈ M ⊓ centralizer (Z : Set G),
      ∃ c ∈ M ⊓ centralizer (V : Set G), ∃ t ∈ (T : Subgroup G), c * t = x) :
    localL1 Y Z ≤ Y ⊓ centralizer (V : Set G) := by
  have hr := residual_centralizes_of_two_supplement
    (Y ⊓ centralizer (Z : Set G)) V (T : Subgroup G)
    (inf_le_left.trans (hYM.trans hM)) (hTM.trans hM) T.isPGroup'
    (fun x hx => by
      obtain ⟨c, hc, t, ht, he⟩ := hfactor x ⟨hYM hx.1, hx.2⟩
      exact ⟨c, hc.2, t, ht, he⟩)
  exact hr.trans (inf_le_inf_right _ inf_le_left)

/-- The first commutator bound in the source proof follows from normality
of Y in M and invariance of V. -/
theorem centralizerCoreResidual_commutator_le [Finite G]
    (M Y H V A Z : Subgroup G) (T : Sylow 2 G) [(Z.subgroupOf H).Normal]
    (hAH : A ≤ H) (hZA : Z ≤ A) (hAM : normalizer (A : Set G) ≤ M)
    (hM : M ≤ normalizer (V : Set G)) (hTM : (T : Subgroup G) ≤ M)
    (hHZ : H ≤ centralizer (Z : Set G))
    (hfactor : ∀ x ∈ M ⊓ centralizer (Z : Set G),
      ∃ c ∈ M ⊓ centralizer (V : Set G), ∃ t ∈ (T : Subgroup G), c * t = x)
    (hYM : Y ≤ M) (hMY : M ≤ normalizer (Y : Set G)) :
    ⁅Y, centralizerCoreResidual H A Z⁆ ≤ Y ⊓ centralizer (V : Set G) := by
  have hX := centralizerCoreResidual_le_centralizer M H V A Z T
    hAH hZA hAM hM hTM hHZ hfactor
  apply le_inf
  · exact le_normalizer_iff_commutator_le_left.mp ((hX.trans inf_le_left).trans hMY)
  · exact (commutator_mono le_rfl (hX.trans inf_le_right)).trans
      (le_normalizer_iff_commutator_le_right.mp
        ((hYM.trans hM).trans (normalizer_le_normalizer_centralizer _)))

/-- A T-invariant subgroup has its two-core inside the Sylow group T. -/
theorem core_le_sylow_of_invariant (Y : Subgroup G) (T : Sylow 2 G)
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G)) : Y.pCoreIn 2 ≤ T := by
  have hTQ := hTY.trans (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y))
  have hp : IsPGroup 2 (Y.pCoreIn 2 ⊔ (T : Subgroup G) : Subgroup G) :=
    (isPGroup_pCoreIn 2 Y).to_sup_of_normal_left' T.isPGroup' hTQ
  exact le_sup_left.trans_eq (T.is_maximal' hp le_sup_right)

private theorem core_ne_bot_of_normal (H X : Subgroup G) (hXH : X ≤ H)
    (hHX : H ≤ normalizer (X : Set G))
    (hchar : H ⊓ centralizer (H.pCoreIn 2 : Set G) ≤ H.pCoreIn 2)
    (hX : X ≠ ⊥) : pCore 2 X ≠ ⊥ := by
  intro hbot
  have hQbot : X.pCoreIn 2 = ⊥ := by simp [pCoreIn, hbot]
  have hHQ : H ≤ normalizer (H.pCoreIn 2 : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hc : ⁅X, H.pCoreIn 2⁆ ≤ X ⊓ H.pCoreIn 2 :=
    le_inf (le_normalizer_iff_commutator_le_left.mp ((pCoreIn_le 2 H).trans hHX))
      (le_normalizer_iff_commutator_le_right.mp (hXH.trans hHQ))
  have hc0 : ⁅X, H.pCoreIn 2⁆ = ⊥ := le_bot_iff.mp
    ((hc.trans (inf_pCoreIn_le_of_le 2 hXH)).trans_eq hQbot)
  have hXQ : X ≤ H.pCoreIn 2 :=
    (le_inf hXH (commutator_eq_bot_iff_le_centralizer.mp hc0)).trans hchar
  have hp : IsPGroup 2 X := (isPGroup_pCoreIn 2 H).to_le hXQ
  have hXX : X ≤ X.pCoreIn 2 := le_pCoreIn_of_normalizes hp le_rfl X.le_normalizer
  exact hX (le_bot_iff.mp (hXX.trans_eq hQbot))

/-- The missing local-overgroup justification: a nontrivial normal subgroup
of H has nontrivial characteristic two-core when H has characteristic two. -/
theorem normalizer_has_twoLocal_of_normal (H X : Subgroup G) (hXH : X ≤ H)
    (hHX : H ≤ normalizer (X : Set G))
    (hchar : H ⊓ centralizer (H.pCoreIn 2 : Set G) ≤ H.pCoreIn 2) (hX : X ≠ ⊥) :
    ∃ L : Subgroup G, IsTwoLocal L ∧ normalizer (X : Set G) ≤ L :=
  exists_twoLocal_overgroup_normalizer X (pCore 2 X)
    (core_ne_bot_of_normal H X hXH hHX hchar hX) pCore_isPGroup

private theorem normalizes_of_residual_commutator
    (X Q Y : Subgroup G) (hX : IsPPerfect 2 X) (hQ : IsPGroup 2 Q)
    (hQX : Q ≤ normalizer (X : Set G)) (hYQ : Y ≤ normalizer (Q : Set G))
    (hcomm : ⁅Y, X⁆ ≤ X ⊔ Q) : Y ≤ normalizer (X : Set G) := by
  have hXK : X ≤ X ⊔ Q := le_sup_left
  have hQK : Q ≤ X ⊔ Q := le_sup_right
  let : (X.subgroupOf (X ⊔ Q)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le X.le_normalizer hQX)
  have hXperf : IsPPerfect 2 (X.subgroupOf (X ⊔ Q)) :=
    hX.of_surjective (subgroupOfEquivOfLe hXK).symm.toMonoidHom
      (subgroupOfEquivOfLe hXK).symm.surjective
  have htop : X.subgroupOf (X ⊔ Q) ⊔ Q.subgroupOf (X ⊔ Q) = ⊤ := by
    apply (map_injective (X ⊔ Q).subtype_injective)
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hXK, map_subgroupOf_eq_of_le hQK,
      ← MonoidHom.range_eq_map, range_subtype]
  have he : (pResidual 2 (X ⊔ Q : Subgroup G)).map (X ⊔ Q).subtype = X := by
    rw [pResidual_eq_of_isPPerfect_sup _ _ hXperf hQ.comap_subtype htop,
      map_subgroupOf_eq_of_le hXK]
  have hYK : Y ≤ normalizer ((X ⊔ Q : Subgroup G) : Set G) := by
    apply le_normalizer_iff.mpr
    intro y hy a ha
    have hconj : X ⊔ Q ≤ (X ⊔ Q).comap (MulAut.conj y).toMonoidHom := by
      apply sup_le
      · intro x hx
        change y * x * y⁻¹ ∈ X ⊔ Q
        have hc := hcomm (commutator_mem_commutator hy hx)
        have hh := (X ⊔ Q).mul_mem hc (hXK hx)
        simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using hh
      · intro q hq
        exact hQK ((hYQ hy q).mp hq)
    exact hconj ha
  rw [← he]
  exact hYK.trans (normalizer_le_normalizer_characteristic_image _ _)

/-- The commutator bound normalizes XO₂(Y); its two-residual is X, so YT
normalizes X. The bound remains an explicit premise of this intermediate step. -/
theorem centralizerCoreResidual_normalized_of_commutator [Finite G]
    (Y H A Z : Subgroup G) (T : Sylow 2 G) [(Z.subgroupOf H).Normal]
    (hTH : (T : Subgroup G) ≤ H) (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hcomm : ⁅Y, centralizerCoreResidual H A Z⁆ ≤
      centralizerCoreResidual H A Z ⊔ Y.pCoreIn 2) :
    Y ⊔ (T : Subgroup G) ≤ normalizer (centralizerCoreResidual H A Z : Set G) := by
  have hXH : centralizerCoreResidual H A Z ≤ H := map_subtype_le _
  have hHX := (normal_subgroupOf_iff_le_normalizer hXH).mp
    (centralizerCoreResidual_normal H A Z)
  have hQH := (core_le_sylow_of_invariant Y T hTY).trans hTH
  exact sup_le
    (normalizes_of_residual_commutator _ _ Y (centralizerCoreResidual_isPPerfect H A Z)
      (isPGroup_pCoreIn 2 Y) (hQH.trans hHX)
      (Y.le_normalizer.trans (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y)))
      hcomm)
    (hTH.trans hHX)

/-- Uniqueness kills the normal-core residual after the branch-specific
commutator bound has been proved. Nontriviality supplies a two-local overgroup
through the characteristic two-core of X, not through an assumed localness. -/
theorem centralizerCoreResidual_eq_bot_of_commutator [Finite G]
    (M Y H A Z : Subgroup G) (T : Sylow 2 G) [(Z.subgroupOf H).Normal]
    (hTH : (T : Subgroup G) ≤ H) (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hchar : H ⊓ centralizer (H.pCoreIn 2 : Set G) ≤ H.pCoreIn 2)
    (hunique : Chapter4.UniqueMaximalOvergroup (Y ⊔ (T : Subgroup G)) M)
    (houtside : ¬ H ≤ M)
    (hcomm : ⁅Y, centralizerCoreResidual H A Z⁆ ≤
      centralizerCoreResidual H A Z ⊔ Y.pCoreIn 2) :
    centralizerCoreResidual H A Z = ⊥ := by
  by_contra hX
  have hXH : centralizerCoreResidual H A Z ≤ H := map_subtype_le _
  have hHX := (normal_subgroupOf_iff_le_normalizer hXH).mp
    (centralizerCoreResidual_normal H A Z)
  have hYX := centralizerCoreResidual_normalized_of_commutator Y H A Z T hTH hTY hcomm
  obtain ⟨N, hN, hXN⟩ := normalizer_has_twoLocal_of_normal H
    (centralizerCoreResidual H A Z) hXH hHX hchar hX
  obtain ⟨K, hNK, hK⟩ := Finite.exists_le_maximal hN
  have hKM := hunique.2.2 K hK (hYX.trans (hXN.trans hNK))
  exact houtside ((hHX.trans (hXN.trans hNK)).trans_eq hKM)

/-- Vanishing of the residual makes the actual relative normal core a
normal two-subgroup of H. -/
theorem centralizerCore_le_twoCore_of_residual_eq_bot [Finite G]
    (H A Z : Subgroup G) [(Z.subgroupOf H).Normal]
    (hX : centralizerCoreResidual H A Z = ⊥) : centralizerCore H A Z ≤ pCore 2 H := by
  let K := centralizerCore H A Z
  have hres : Stellmacher.twoResidualAmbient K = ⊥ :=
    ((Stellmacher.twoResidualAmbient K).map_eq_bot_iff_of_injective H.subtype_injective).mp hX
  rw [twoResidualAmbient_eq_pResidual] at hres
  have hr : pResidual 2 K = ⊥ :=
    ((pResidual 2 K).map_eq_bot_iff_of_injective K.subtype_injective).mp hres
  have hp : IsPGroup 2 K :=
    ((isPGroup_quotient_pResidual (G := K) 2).of_equiv
      (QuotientGroup.quotientMulEquivOfEq hr)).of_equiv QuotientGroup.quotientBot
  exact le_sSup ⟨inferInstance, hp⟩

/-- F.9.1(a)'s normal-core bound in the ordinary alternative of 15.3.7.
All residual and commutator containments are derived from the local inputs. -/
theorem centralizerCore_le_twoCore_of_ordinary [Finite G]
    (M Y H V A Z : Subgroup G) (T : Sylow 2 G) [(Z.subgroupOf H).Normal]
    (hAH : A ≤ H) (hZA : Z ≤ A) (hAM : normalizer (A : Set G) ≤ M)
    (hM : M ≤ normalizer (V : Set G)) (hTM : (T : Subgroup G) ≤ M)
    (hHZ : H ≤ centralizer (Z : Set G))
    (hfactor : ∀ x ∈ M ⊓ centralizer (Z : Set G),
      ∃ c ∈ M ⊓ centralizer (V : Set G), ∃ t ∈ (T : Subgroup G), c * t = x)
    (hYM : Y ≤ M) (hMY : M ≤ normalizer (Y : Set G))
    (hTH : (T : Subgroup G) ≤ H)
    (hchar : H ⊓ centralizer (H.pCoreIn 2 : Set G) ≤ H.pCoreIn 2)
    (hunique : Chapter4.UniqueMaximalOvergroup (Y ⊔ (T : Subgroup G)) M)
    (houtside : ¬ H ≤ M) (hordinary : Y ⊓ centralizer (V : Set G) = Y.pCoreIn 2) :
    centralizerCore H A Z ≤ pCore 2 H := by
  apply centralizerCore_le_twoCore_of_residual_eq_bot
  apply centralizerCoreResidual_eq_bot_of_commutator M Y H A Z T hTH
    (hTM.trans hMY) hchar hunique houtside
  have hc := centralizerCoreResidual_commutator_le M Y H V A Z T
    hAH hZA hAM hM hTM hHZ hfactor hYM hMY
  exact (hc.trans_eq hordinary).trans le_sup_right

end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup

end

module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeCommonNormal
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalSmallGenerationTorus
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLocalCartan
public import Theory.GroupTheory.CyclicQuotientCharacteristic
public import Theory.GroupTheory.SylowSmallIndexModels
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Theory.SpecificGroups.SL2.BinaryProjective
public import Theory.GroupTheory.SylowPrimeIndexSelfNormalizer
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The actual left prime-actor group in original 5.2.2

Put U=T∩L, S=O₂(N_G(L)∩H), and take the selected prime subgroup D
of the original Hall Cartan. The cyclic quotient N_L(U)/U makes UD
characteristic in N_L(U). Therefore TB normalizes DS. The literal
intersection UD∩S=U gives [DS:S]=|D|, so S is Sylow in DS.

The original common-normal theorem excludes normality of S in DS.
The existing prime-index theorem then gives its exact Borel S and the
concrete quotient S₃, D₁₀ or Sz(2). These are proved before imposing
the zero-core condition on the rank-two generated group.

The final constructor removes all left-side premises from LocalData,
and its application verifies genuine F.1.1 on the original (DS,L₂) pair.
The right-factor geometry remains an explicit source obligation owned by
qt-d-1222-rankone-cartan-local-to-global, as do the subsequent zero-core
model exclusions and changed-Sylow analysis. This is not full 5.2.2.

Source: Aschbacher--Smith, 5.1.5, 5.1.11 and 5.2.2,
printed pp.631,634--635,647--648 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A prime actor with zero join core forces the original left factor outside H. -/
theorem CartanPrimeActor.left_not_le_hstar
    {T : Sylow 2 G} {L H A B D : Subgroup G} {p : ℕ}
    (hd : CartanPrimeActor A H p D) (c : CartanPair T L H A B)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ¬ L ≤ H := by
  intro hLH
  have hDH : D ≤ H := hd.le_cartan.trans (c.left_le.trans (inf_le_left.trans hLH))
  exact hH.1.1.1 (by simpa only [sup_eq_right.mpr hDH] using hd.zero_core)

private theorem cartan_subgroup_preimage_characteristic
    {T : Sylow 2 G} {L H A B D : Subgroup G} {n : ℕ}
    (c : CartanPair T L H A B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) :
    ((((T : Subgroup G) ⊓ L) ⊔ D).subgroupOf (localBorel T L)).Characteristic := by
  let C := localBorel T L
  let U := (T : Subgroup G) ⊓ L
  have hUC : U ≤ C := le_inf inf_le_right U.le_normalizer
  obtain ⟨P, hP⟩ := exists_sylow_localBorel T L hTL
  have hPU : (P : Subgroup C) = U.subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [hP, map_subgroupOf_eq_of_le hUC]
  have hUN : (U.subgroupOf C).Normal := normal_subgroupOf_of_le_normalizer inf_le_right
  let : (U.subgroupOf C).Characteristic := by
    rw [← hPU]
    exact P.characteristic_of_normal (by simpa only [hPU] using hUN)
  obtain ⟨F, _, _, _, _, ⟨e⟩⟩ := c.left_equiv_units hpsl hTL
  let : IsCyclic A := isCyclic_of_injective e.toMonoidHom e.injective
  let : IsCyclic (A.subgroupOf C) :=
    isCyclic_of_surjective (subgroupOfEquivOfLe c.left_le).symm
      (subgroupOfEquivOfLe c.left_le).symm.surjective
  have hsup : U.subgroupOf C ⊔ A.subgroupOf C = ⊤ := by
    rw [← subgroupOf_sup hUC c.left_le, c.left_sup_intersection hTL]
    exact subgroupOf_self C
  let : IsCyclic (C ⧸ U.subgroupOf C) :=
    isCyclic_quotient_of_cyclic_supplement _ _ hsup
  exact characteristic_of_cyclic_quotient (U.subgroupOf C) _
    (subgroupOf_mono C le_sup_left)

/-- The original Borel normalizer preserves each prime-torus preimage. -/
theorem cartan_subgroup_preimage_normalized
    {T : Sylow 2 G} {L H A B D : Subgroup G} {n : ℕ}
    (c : CartanPair T L H A B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) (hDA : D ≤ A) :
    normalizer (localBorel T L : Set G) ≤
      normalizer ((((T : Subgroup G) ⊓ L) ⊔ D : Subgroup G) : Set G) := by
  let : ((((T : Subgroup G) ⊓ L) ⊔ D).subgroupOf (localBorel T L)).Characteristic :=
    cartan_subgroup_preimage_characteristic c hTL hpsl
  have hh := normalizer_le_normalizer_characteristic_image (localBorel T L)
    ((((T : Subgroup G) ⊓ L) ⊔ D).subgroupOf (localBorel T L))
  have hUC : (T : Subgroup G) ⊓ L ≤ localBorel T L :=
    le_inf inf_le_right ((T : Subgroup G) ⊓ L).le_normalizer
  simpa only [map_subgroupOf_eq_of_le (sup_le hUC (hDA.trans c.left_le))] using hh

/-- The actual overlap TB normalizes DS before any normalization of L₂. -/
theorem Input.prime_left_normalized
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    (T : Subgroup G) ⊔ B ≤ normalizer ((D ⊔ Global.sourceS L H : Subgroup G) : Set G) := by
  let U := (T : Subgroup G) ⊓ L
  let S := Global.sourceS L H
  have hSL := sourceS_intersection_left h.linear h.sylow_normalizes hH.1.1.2
    (CartanPrimeActor.left_not_le_hstar hd c hH)
  have hUS : U ≤ S := hSL.ge.trans inf_le_left
  have he : D ⊔ S = (U ⊔ D) ⊔ S := by
    exact le_antisymm (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
      (sup_le (sup_le (hUS.trans le_sup_right) le_sup_left) le_sup_right)
  have hnorm : (T : Subgroup G) ⊔ B ≤ normalizer ((U ⊔ D : Subgroup G) : Set G) := by
    rw [c.sylow_sup_right h.sylow_normalizes hH.1.1.2]
    exact (intersection_normalizes_localBorel h.linear h.sylow_normalizes hH.1.1.2
      (CartanPrimeActor.left_not_le_hstar hd c hH)).trans
      (cartan_subgroup_preimage_normalized c h.sylow_normalizes h.linear hd.le_cartan)
  rw [he]
  apply le_trans _ (normalizer_inf_normalizer_le_normalizer_sup _ _)
  refine le_inf hnorm ?_
  rw [c.sylow_sup_right h.sylow_normalizes hH.1.1.2]
  exact Global.intersection_normalizes_sourceS L H

private theorem prime_left_card
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    Nat.card (D ⊔ Global.sourceS L H : Subgroup G) = p * Nat.card (Global.sourceS L H) := by
  let U := (T : Subgroup G) ⊓ L
  let S := Global.sourceS L H
  have hST := Global.sourceS_le_sylow h.sylow_normalizes hH.1.1.2
  have hSL : S ⊓ L = U := sourceS_intersection_left h.linear h.sylow_normalizes hH.1.1.2
    (CartanPrimeActor.left_not_le_hstar hd c hH)
  have hUS : U ≤ S := hSL.ge.trans inf_le_left
  have hDU : D ≤ normalizer (U : Set G) := hd.le_cartan.trans (c.left_le.trans inf_le_right)
  have hDL : D ≤ L := hd.le_cartan.trans (c.left_le.trans inf_le_left)
  have hKS : (U ⊔ D) ⊓ S = U := by
    apply le_antisymm
    · rw [← hSL]
      exact le_inf inf_le_right (inf_le_left.trans (sup_le inf_le_right hDL))
    · exact le_inf le_sup_left hUS
  have he : (U ⊔ D) ⊔ S = D ⊔ S := by
    exact le_antisymm (sup_le (sup_le (hUS.trans le_sup_right) le_sup_left) le_sup_right)
      (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  have hSN : S ≤ normalizer ((U ⊔ D : Subgroup G) : Set G) := by
    have hc := intersection_normalizes_localBorel h.linear h.sylow_normalizes hH.1.1.2
      (CartanPrimeActor.left_not_le_hstar hd c hH)
    exact (hST.trans (le_inf h.sylow_normalizes hH.1.1.2)).trans
      (hc.trans (cartan_subgroup_preimage_normalized c h.sylow_normalizes h.linear hd.le_cartan))
  have hodd : ¬ 2 ∣ Nat.card D := by rcases hd.prime with rfl | rfl <;> rw [hd.card] <;> decide
  obtain ⟨k,hk⟩ := (T.isPGroup'.to_le (show U ≤ (T : Subgroup G) from inf_le_left)).exists_card_eq
  have hdis : Disjoint U D := disjoint_of_coprime_natCard (by
    rw [hk]
    exact (Nat.prime_two.coprime_iff_not_dvd.mpr hodd).pow_left k)
  have hm := card_mul_eq_card_inf_mul_card_sup_of_normalizes (U ⊔ D) S hSN
  rw [card_sup_eq_mul_of_normalizes_of_disjoint U D hDU hdis, hKS, he, mul_assoc] at hm
  exact (Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := U)) hm).symm.trans
    (by rw [hd.card])

/-- The literal source S has index p in DS. -/
theorem Input.prime_left_index
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    (Global.sourceS L H).relIndex (D ⊔ Global.sourceS L H) = p := by
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) (Global.sourceS L H)
    (D ⊔ Global.sourceS L H) bot_le le_sup_right
  simp only [relIndex_bot_left] at hc
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Global.sourceS L H))
  rw [hc, prime_left_card h hH c hd]
  exact Nat.mul_comm _ _

/-- The same S is Sylow in the left prime-actor group. -/
theorem Input.prime_left_sylow
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    ∃ P : Sylow 2 (D ⊔ Global.sourceS L H : Subgroup G),
      (P : Subgroup (D ⊔ Global.sourceS L H : Subgroup G)).map
        (D ⊔ Global.sourceS L H : Subgroup G).subtype = Global.sourceS L H := by
  let S := Global.sourceS L H
  have hS : IsPGroup 2 S := pCore_isPGroup.map _
  have hSP : IsPGroup 2 (S.subgroupOf (D ⊔ S)) :=
    hS.of_equiv (subgroupOfEquivOfLe (show S ≤ D ⊔ S from le_sup_right)).symm
  have hi : ¬ 2 ∣ (S.subgroupOf (D ⊔ S)).index := by
    change ¬ 2 ∣ S.relIndex (D ⊔ S)
    rw [Input.prime_left_index h hH c hd]
    rcases hd.prime with rfl | rfl <;> decide
  exact ⟨hSP.toSylow hi, by
    rw [IsPGroup.toSylow_coe, map_subgroupOf_eq_of_le le_sup_right]⟩

/-- The actual left Borel is S, by prime index and source nonnormality. -/
theorem Input.prime_left_borel
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hSK : Global.sourceS L H ⊓ residual H = (T : Subgroup G) ⊓ residual H) :
    ChapterF.Source.borel (D ⊔ Global.sourceS L H) (Global.sourceS L H) =
      Global.sourceS L H := by
  let S := Global.sourceS L H
  let J := D ⊔ S
  have hSJ : S ≤ J := le_sup_right
  obtain ⟨P,hP⟩ := Input.prime_left_sylow h hH c hd
  have hP' : (P : Subgroup J) = S.subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [hP, map_subgroupOf_eq_of_le hSJ]
  have hindex : P.index.Prime := by
    rw [hP']
    change (S.relIndex J).Prime
    rw [Input.prime_left_index h hH c hd]
    rcases hd.prime with rfl | rfl <;> decide
  have hnot : ¬ (P : Subgroup J) ≤ pCore 2 J := by
    intro hPc
    have he : (P : Subgroup J) = pCore 2 J := le_antisymm hPc (pCore_isPGroup.le_sylow_of_normal P)
    have hn : (S.subgroupOf J).Normal := by rw [← hP', he]; infer_instance
    have hn' := (normal_subgroupOf_iff_le_normalizer hSJ).mp hn
    exact zero_core_not_normalizes_sourceS h hH hSK hd.zero_core (le_sup_left.trans hn')
  have hn := P.normalizer_eq_of_prime_index_not_le_core hindex hnot
  change normalizer ((P : Subgroup J) : Set J) = _ at hn
  rw [hP'] at hn
  have hh := congrArg (Subgroup.map J.subtype) hn
  rw [← subgroupOf_normalizer_eq hSJ, subgroupOf_map_subtype,
    map_subgroupOf_eq_of_le hSJ] at hh
  change J ⊓ normalizer ((S ⊓ J : Subgroup G) : Set G) = S
  rw [inf_eq_left.mpr hSJ, inf_comm]
  exact hh

/-- Nonnormality and index three or five give the concrete rank-one quotient. -/
theorem Input.prime_left_quotient
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hSK : Global.sourceS L H ⊓ residual H = (T : Subgroup G) ⊓ residual H) :
    ChapterF.Source.IsRankOneModel
      ((D ⊔ Global.sourceS L H : Subgroup G) ⧸ pCore 2 (D ⊔ Global.sourceS L H : Subgroup G)) := by
  let S := Global.sourceS L H
  let J := D ⊔ S
  obtain ⟨P,hP⟩ := Input.prime_left_sylow h hH c hd
  have hP' : (P : Subgroup J) = S.subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [hP, map_subgroupOf_eq_of_le le_sup_right]
  have hi : P.index = 3 ∨ P.index = 5 := by
    rw [hP']
    change S.relIndex J = 3 ∨ S.relIndex J = 5
    rw [Input.prime_left_index h hH c hd]
    exact hd.prime
  have hproper : pCore 2 J < (P : Subgroup J) := by
    refine lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal P) ?_
    intro he
    have hn : (S.subgroupOf J).Normal := by rw [← hP', ← he]; infer_instance
    have hn' := (normal_subgroupOf_iff_le_normalizer
      (show S ≤ J from le_sup_right)).mp hn
    exact zero_core_not_normalizes_sourceS h hH hSK hd.zero_core (le_sup_left.trans hn')
  rcases sylow_small_index_core_quotient P hi hproper with hh | hh | ⟨e⟩
  · exact .dihedral hh
  · exact .suzuki 0 hh
  · apply ChapterF.Source.IsRankOneModel.linear 1 (by decide)
    refine ⟨ZMod 2, inferInstance, inferInstance, by simp, ?_⟩
    exact ⟨e.some.trans (SLTwoPermThree.sl2Two_equiv_perm_three.some.symm.trans
      Matrix.SpecialLinearGroup.sl2TwoEquivPSL2Two)⟩

/-- The genuinely remaining right-side source geometry of 5.1.10--11.
There is no left-index, left-model, left-Borel or whole-Cartan-normalization
field. Its construction remains with this consolidated source owner. -/
structure RightData (T : Sylow 2 G) (L H B L₂ : Subgroup G) : Prop where
  right_le_residual : L₂ ≤ residual H
  right_outside : ¬ L₂ ≤ normalizer (L : Set G)
  right_generate : L₂ ⊔ (T : Subgroup G) = H
  right_nonsolvable : ¬ Group.IsSolvable L₂
  right_component : (L₂.subgroupOf (L₂ ⊔ normalizingSylow T L₂)).IsCComponent
  index_le_two : (normalizingSylow T L₂).relIndex (T : Subgroup G) ≤ 2
  S_intersection_residual : Global.sourceS L H ⊓ residual H = (T : Subgroup G) ⊓ residual H
  S_normalizes_right : Global.sourceS L H ≤ normalizer (L₂ : Set G)
  B_normalizes_right : B ≤ normalizer (L₂ : Set G)
  right_sylow : ∃ P : Sylow 2 L₂,
    (P : Subgroup L₂).map L₂.subtype = Global.sourceS L H ⊓ L₂
  right_quotient : ChapterF.Source.IsRankOneModel (L₂ ⧸ pCore 2 L₂)
  right_borel : ChapterF.Source.borel L₂ (Global.sourceS L H) =
    (Global.sourceS L H ⊓ L₂) ⊔ (B ⊓ L₂)

/-- Construct the original local-pair interface from the right geometry;
all five left-side clauses are proved here on the literal DS. -/
theorem RightData.localData
    {T : Sylow 2 G} {L W H A B D L₂ : Subgroup G} {n p : ℕ}
    (d : RightData T L H B L₂) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    LocalData T L H B D L₂ :=
  { right_le_residual := d.right_le_residual
    right_outside := d.right_outside
    right_generate := d.right_generate
    right_nonsolvable := d.right_nonsolvable
    right_component := d.right_component
    index_le_two := d.index_le_two
    S_intersection_residual := d.S_intersection_residual
    S_intersection_left := sourceS_intersection_left h.linear h.sylow_normalizes hH.1.1.2
      (CartanPrimeActor.left_not_le_hstar hd c hH)
    S_normalizes_right := d.S_normalizes_right
    B_normalizes_right := d.B_normalizes_right
    TB_normalizes_left := Input.prime_left_normalized h hH c hd
    right_sylow := d.right_sylow
    right_quotient := d.right_quotient
    right_borel := d.right_borel
    left_sylow := Input.prime_left_sylow h hH c hd
    left_quotient := fun _ => Input.prime_left_quotient h hH c hd d.S_intersection_residual
    left_borel := fun _ => Input.prime_left_borel h hH c hd d.S_intersection_residual }

/-- The exact genuine F.1.1 consumer, without left-model or left-Borel
callbacks. The right geometry and original zero-core branch remain explicit. -/
theorem RightData.hypothesisF11
    {T : Sylow 2 G} {L W H A B D L₂ : Subgroup G} {n p : ℕ}
    (d : RightData T L H B L₂) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D L₂).pCoreIn 2 = ⊥) :
    ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H, L₂] (Global.sourceS L H) :=
  (d.localData h hH c hd).hypothesisF11 h hH c hd hz

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime

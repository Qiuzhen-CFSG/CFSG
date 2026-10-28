module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.BinaryLinearModels
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.EvenCharacteristic
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.ExceptionalOvercomponentsAlternatingSeven

/-!
# A₇ sections exclude the binary four- and five-space containing models

For PSL₄(2), the smaller quotient already has the full odd part of the
ambient order. Its normalizer contains a full Sylow two-subgroup, so its
index is both odd and a divisor of eight. Simplicity then contradicts
the specified A₇ quotient.

For PSL₅(2), a proper full-Sylow join lies in a maximal subspace
parabolic. Its literal two-core quotient is either S₃ × PSL₃(2), whose
order excludes the A₇ section, or PSL₄(2), handled above. The final
consumer transports the original local X ≤ K and its normalization
through the actual two-core quotient of K.

Source: Aschbacher–Smith A.3.12(4–5), pp.47–48, and 1.2.8, pp.506–507.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.Section02.ExceptionalOvercomponents.AlternatingSevenBinary
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

private theorem section_map (B : Subgroup G) [Group.IsPerfect B]
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7)))
    (f : G →* H) [Group.IsSolvable f.ker] :
    Nonempty (((B.map f) ⧸ pCore 2 (B.map f)) ≃* alternatingGroup (Fin 7)) := by
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (B ⧸ pCore 2 B) := h.some.isSimpleGroup
  let g := f.subgroupMap B
  let : Group.IsSolvable g.ker := by
    change Group.IsSolvable (f.subgroupMap B).ker
    rw [Subgroup.ker_subgroupMap]
    exact Group.isSolvable_of_isSolvable_injective
      (f := B.subtype.subgroupComap f.ker) (fun a b he => Subtype.ext (Subtype.ext
        (congrArg (fun x : f.ker => (x : G)) he)))
  exact ⟨(PerfectCoreTwoExtension.solvableKernelQuotientEquiv g
    (f.subgroupMap_surjective B)).symm.trans h.some⟩

private theorem local_section_map {S B : Subgroup G} (hB : B ∈ localCComponents S)
    (hSB : S ≤ normalizer (B : Set G))
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7)))
    (f : G →* H) [Group.IsSolvable f.ker] :
    B.map f ∈ localCComponents (S.map f) ∧
      S.map f ≤ normalizer (B.map f : Set H) ∧
      Nonempty (((B.map f) ⧸ pCore 2 (B.map f)) ≃* alternatingGroup (Fin 7)) := by
  let := Exceptional.local_perfect hB
  exact ⟨localCComponents_map_of_solvable_ker hB f,
    (map_mono hSB).trans (le_normalizer_map f), section_map B h f⟩

omit [Group H] [Finite H] [Finite G] in
private theorem section_card {B : Subgroup G}
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7))) :
    Nat.card (B ⧸ pCore 2 B) = 2520 := by
  rw [Nat.card_congr h.some.toEquiv, nat_card_alternatingGroup]
  norm_num

omit [Group H] [Finite H] [Finite G] in
private theorem model_of_top_section [IsSimpleGroup G] (B : Subgroup G)
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7))) (ht : B = ⊤) :
    Nonempty (G ≃* alternatingGroup (Fin 7)) := by
  let eB : B ≃* G := (MulEquiv.subgroupCongr ht).trans topEquiv
  let : IsSimpleGroup B := eB.isSimpleGroup
  have hc : pCore 2 B = ⊥ := by
    rcases (inferInstance : (pCore 2 B).Normal).eq_bot_or_eq_top with hc | hc
    · exact hc
    · have hh := section_card h
      simp [hc] at hh
  let q : B ≃* B ⧸ pCore 2 B := QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hc.symm)
  exact ⟨eB.symm.trans (q.trans h.some)⟩

omit [Group H] [Finite H] in
private noncomputable def binaryProjectiveEquiv {n : ℕ}
    (hm : ClassicalGroup.IsPSL G n 2) : G ≃* PSL(n,ZMod 2) :=
  Classical.choice <| by
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let := Fintype.ofFinite F
    let k : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
      simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
    exact ⟨e.trans (Atlas.fieldEquivPSL n k)⟩

private theorem binary_card (n : ℕ) [NeZero n] :
    Nat.card PSL(n,ZMod 2) = ∏ i : Fin n, (2^n-2^i.val) := by
  have h := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) n
  simpa only [Nat.card_zmod, show 2-1=1 from rfl, Nat.gcd_one_right,mul_one] using h

omit [Group H] [Finite H] in
/-- A full Sylow cannot normalize an A₇ two-core section in PSL₄(2). -/
theorem not_binaryFour (S : Sylow 2 G) (B : Subgroup G)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7)))
    (hm : ClassicalGroup.IsPSL G 4 2) : False := by
  let e := binaryProjectiveEquiv hm
  let : IsSimpleGroup PSL(4,ZMod 2) := Atlas.psl_simple_high_rank 4 (by decide)
  let : IsSimpleGroup G := e.isSimpleGroup
  have hc : Nat.card G = 20160 := by
    rw [Nat.card_congr e.toEquiv, binary_card]
    decide
  let N := normalizer (B : Set G)
  have hd : 2520 ∣ Nat.card N := (section_card h ▸ card_quotient_dvd_card (pCore 2 B)).trans
    (card_dvd_of_le B.le_normalizer)
  obtain ⟨k,hk⟩ := hd
  have he := N.card_mul_index
  rw [hc,hk] at he
  have hi : N.index ∣ 8 := ⟨k, by nlinarith⟩
  have hodd : ¬ 2 ∣ N.index := fun h => S.not_dvd_index (h.trans (index_dvd_of_le hn))
  have hone : N.index = 1 :=
    Nat.eq_one_of_dvd_coprimes
      ((Nat.prime_two.coprime_iff_not_dvd.mpr hodd).pow_left 3) hi (dvd_refl _)
  let : B.Normal := normalizer_eq_top_iff.mp (index_eq_one.mp hone)
  rcases (inferInstance : B.Normal).eq_bot_or_eq_top with hb | hb
  · have hd : 2520 ∣ Nat.card B := section_card h ▸ card_quotient_dvd_card (pCore 2 B)
    simp [hb] at hd
  · obtain ⟨a⟩ := model_of_top_section B h hb
    have hh := Nat.card_congr a.toEquiv
    rw [hc,nat_card_alternatingGroup] at hh
    norm_num at hh

open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
open BinaryLinear.FiveFlagGeometry.MaximalOvergroups
private instance : Finite (LinearGroup 5) :=
  Finite.of_injective (fun g : LinearGroup 5 => (g : Space 5 → Space 5)) DFunLike.coe_injective

private theorem no_section_maximal_parabolic
    (S : Sylow 2 (LinearGroup 5)) (B : Subgroup (LinearGroup 5))
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup (LinearGroup 5)) ≤ normalizer (B : Set _))
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7)))
    (b : FiveBasis) (i : Fin 4) (hBP : B ≤ flagStabilizer b {i})
    (hSP : (S : Subgroup (LinearGroup 5)) ≤ flagStabilizer b {i}) : False := by
  let P := flagStabilizer b {i}
  let D := B.subgroupOf P
  let T := S.subtype hSP
  have hl : D ∈ localCComponents T := local_restrict hB hBP
  have hnorm : (T : Subgroup P) ≤ normalizer (D : Set P) := by
    intro s hs
    apply mem_normalizer_iff.mpr
    intro x
    exact mem_normalizer_iff.mp (hn hs) (x : LinearGroup 5)
  let eD : D ≃* B := subgroupOfEquivOfLe hBP
  have hD : Nonempty ((D ⧸ pCore 2 D) ≃* alternatingGroup (Fin 7)) :=
    ⟨(QuotientGroup.congr _ _ eD (pCore_map_iso 2 eD)).trans h.some⟩
  let q := QuotientGroup.mk' (pCore 2 P)
  let : Group.IsNilpotent (pCore 2 P) := pCore_isNilpotent
  let : Group.IsSolvable q.ker := by rw [QuotientGroup.ker_mk']; infer_instance
  obtain ⟨hl',hn',hD'⟩ := local_section_map hl hnorm hD q
  let U := T.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 P))
  rcases singleton_quotient_models b i with hsmall | hfour
  · have hd : 2520 ∣ Nat.card (P ⧸ pCore 2 P) :=
      (section_card hD' ▸ card_quotient_dvd_card (pCore 2 (D.map q))).trans
        (D.map q).card_subgroup_dvd_card
    rw [Nat.card_congr hsmall.some.toEquiv,Nat.card_prod,Nat.card_perm,Nat.card_fin,
      binary_card] at hd
    exact (by decide : ¬ 2520 ∣ Nat.factorial 3 * (∏ i : Fin 3, (2^3-2^i.val))) hd
  · exact not_binaryFour U (D.map q) hn' hD'
      ⟨ZMod 2,inferInstance,inferInstance,Nat.card_zmod 2,hfour⟩

private theorem not_linearFive (S : Sylow 2 (LinearGroup 5))
    (B : Subgroup (LinearGroup 5)) (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup (LinearGroup 5)) ≤ normalizer (B : Set _))
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7))) : False := by
  let e := projectiveEquivLinear (by decide : 0 < 5)
  let : IsSimpleGroup PSL(5,ZMod 2) := Atlas.psl_simple_high_rank 5 (by decide)
  let : IsSimpleGroup (LinearGroup 5) := e.symm.isSimpleGroup
  by_cases ht : B ⊔ (S : Subgroup (LinearGroup 5)) = ⊤
  · let : B.Normal := normalizer_eq_top_iff.mp
      (top_unique (ht ▸ sup_le le_normalizer hn))
    have hb : B = ⊤ := by
      rcases (inferInstance : B.Normal).eq_bot_or_eq_top with hb | hb
      · exact (hB.ne_bot (by simp [hb])).elim
      · exact hb
    obtain ⟨a⟩ := model_of_top_section B h hb
    have hc : Nat.card (LinearGroup 5) = 9999360 := by
      rw [← Nat.card_congr e.toEquiv, binary_card]
      decide
    have hh := Nat.card_congr a.toEquiv
    rw [hc,nat_card_alternatingGroup] at hh
    norm_num at hh
  · obtain ⟨b,cuts,hcuts⟩ := isFlagParabolic_of_sylow_le S
      (B ⊔ (S : Subgroup (LinearGroup 5))) le_sup_right
    have hnonempty : cuts.Nonempty := by
      by_contra hh
      have he : cuts = ∅ := Set.not_nonempty_iff_eq_empty.mp hh
      exact ht (hcuts.trans (he ▸ flagStabilizer_empty b))
    obtain ⟨i,hi⟩ := hnonempty
    have hle : B ⊔ (S : Subgroup (LinearGroup 5)) ≤ flagStabilizer b {i} :=
      hcuts.le.trans ((flag_le_iff b _ _).mpr (Set.singleton_subset_iff.mpr hi))
    exact no_section_maximal_parabolic S B hB hn h b i
      (le_sup_left.trans hle) (le_sup_right.trans hle)

omit [Group H] [Finite H] in
/-- Both binary higher-linear containing rows are excluded for the actual
Sylow-normalized local A₇ section. -/
theorem not_binaryFour_or_Five (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S) (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7)))
    {n : ℕ} (hn' : n = 4 ∨ n = 5) (hm : ClassicalGroup.IsPSL G n 2) : False := by
  rcases hn' with rfl | rfl
  · exact not_binaryFour S B hn h hm
  · let e := (binaryProjectiveEquiv hm).trans (projectiveEquivLinear (by decide : 0 < 5))
    let : Group.IsSolvable e.toMonoidHom.ker := by
      rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective]
      infer_instance
    obtain ⟨hl,hn',hs⟩ := local_section_map hB hn h e.toMonoidHom
    exact not_linearFive (S.mapSurjective e.surjective) (B.map e.toMonoidHom) hl hn' hs

end CFSG.Quasithin.Chapter1.Section02.ExceptionalOvercomponents.AlternatingSevenBinary

namespace CFSG.Quasithin.Chapter1.Section02.ExceptionalOvercomponents.AlternatingSevenBinary
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem not_model_of_local_overcomponent
    {n : ℕ}
    (hexclude : ∀ {V : Type u} [Group V] [Finite V] (S : Sylow 2 V) (B : Subgroup V),
      B ∈ localCComponents S → (S : Subgroup V) ≤ normalizer (B : Set V) →
      Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7)) → ClassicalGroup.IsPSL V n 2 → False)
    (T : Sylow 2 G) {X K : Subgroup G}
    (hX : X ∈ L G (T : Subgroup G))
    (hn : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hK : K ∈ L G (T : Subgroup G)) (hXK : X ≤ K)
    (h : Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 7)))
    (e : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) n 2) : False := by
  let H := K ⊔ (T : Subgroup G)
  have hXH : X ≤ H := hXK.trans le_sup_left
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  have hx : X.subgroupOf H ∈ L H (S : Subgroup H) :=
    (mem_LIn_iff_subgroupOf le_sup_right hXH).mp ⟨hXH,hX⟩
  have hn' : (S : Subgroup H) ≤ normalizer (X.subgroupOf H : Set H) := by
    intro s hs
    apply mem_normalizer_iff.mpr
    intro x
    exact mem_normalizer_iff.mp (hn hs) (x : G)
  let q := QuotientGroup.mk' (pCore 2 H)
  let Sbar := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  have hb : (X.subgroupOf H).map q ∈ localCComponents Sbar :=
    mem_L_map_twoCore_mem_localCComponents hx
  have hnb : (Sbar : Subgroup (H ⧸ pCore 2 H)) ≤
      normalizer ((X.subgroupOf H).map q : Set _) :=
    (map_mono hn').trans (le_normalizer_map q)
  let eX := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hXH)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hXH))
  have hk : IsPGroup 2 (q.subgroupMap (X.subgroupOf H)).ker := by
    rw [ker_subgroupMap, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let eB := MonoidHom.quotientPCoreEquivOfSurjective
    (q.subgroupMap (X.subgroupOf H)) (q.subgroupMap_surjective _) hk
  have hm : Nonempty ((((X.subgroupOf H).map q) ⧸ pCore 2 ((X.subgroupOf H).map q)) ≃*
      alternatingGroup (Fin 7)) := ⟨eB.symm.trans (eX.trans h.some)⟩
  let := pCore_isNilpotent (p := 2) (G := H)
  have hC := hK.1.map_quotient (pCore 2 H)
  have hBC : (X.subgroupOf H).map q ≤ (K.subgroupOf H).map q :=
    map_mono (comap_mono hXK)
  obtain ⟨P,_,hl,hs⟩ := exists_local_sylow_normalizing Sbar hb hC.subnormal hBC hnb
  let er := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hBC)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hBC))
  let eK := QuotientGroup.congr _ _ (subgroupOfEquivOfLe (show K ≤ H from le_sup_left))
    (pCore_map_iso 2 (subgroupOfEquivOfLe (show K ≤ H from le_sup_left)))
  exact hexclude P _ hl hs ⟨er.trans hm.some⟩
    (e.of_mulEquiv ((cComponentTwoCoreQuotientEquiv hK.1).symm.trans eK))

/-- The actual overcomponent quotient cannot be either binary higher-linear model. -/
theorem local_overcomponent_not_binaryFour_or_Five
    (T : Sylow 2 G) {X K : Subgroup G}
    (hX : X ∈ L G (T : Subgroup G))
    (hn : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hK : K ∈ L G (T : Subgroup G)) (hXK : X ≤ K)
    (h : Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 7)))
    {n : ℕ} (hn' : n = 4 ∨ n = 5) :
    ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) n 2 := by
  intro hm
  exact not_model_of_local_overcomponent
    (fun S B hl hs he hmodel => not_binaryFour_or_Five S B hl hs he hn' hmodel)
    T hX hn hK hXK h hm

end CFSG.Quasithin.Chapter1.Section02.ExceptionalOvercomponents.AlternatingSevenBinary

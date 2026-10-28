module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.ExceptionalOvercomponentsAlternatingSevenBinary
public import Theory.Alternating.Aut
/-!
# Transport and faithful Sylow control for the actual A₇ section

The perfect local section survives solvable kernels. When its two-core is
trivial, even characteristic makes the full Sylow actor faithful on A₇,
so its order divides sixteen. The final transfer retains the literal
X/O₂(X) and K/O₂(K) in the original local-family consumer.
Source: Aschbacher–Smith A.3.12, pp.47–48, and 1.2.8, pp.506–507.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02.ExceptionalOvercomponents.AlternatingSevenSection
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
universe u v
variable {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
theorem section_map (B : Subgroup G) [Group.IsPerfect B]
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

theorem local_section_map {S B : Subgroup G} (hB : B ∈ localCComponents S)
    (hSB : S ≤ normalizer (B : Set G))
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7)))
    (f : G →* H) [Group.IsSolvable f.ker] :
    B.map f ∈ localCComponents (S.map f) ∧
      S.map f ≤ normalizer (B.map f : Set H) ∧
      Nonempty (((B.map f) ⧸ pCore 2 (B.map f)) ≃* alternatingGroup (Fin 7)) := by
  let := Exceptional.local_perfect hB
  exact ⟨localCComponents_map_of_solvable_ker hB f,
    (map_mono hSB).trans (le_normalizer_map f), section_map B h f⟩

omit [Group H] [Finite H] in
theorem sylow_card_dvd_of_core_eq_bot (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7)))
    (hc : pCore 2 B = ⊥) (hE : IsEvenCharacteristicAt S) : Nat.card S ∣ 16 := by
  let eB : B ≃* alternatingGroup (Fin 7) :=
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm.trans h.some
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup B := eB.isSimpleGroup
  let := Exceptional.local_perfect hB
  have hz : center B = ⊥ :=
    (inferInstance : (center B).Normal).eq_bot_or_eq_top.resolve_right
      (fun ht => Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp ht))
  let : IsQuasisimple B :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩
  have hf := sylow_centralizer_eq_bot_of_evenCharacteristic S hE hB hn
  let f := B.normalizerMonoidHom.comp (inclusion hn)
  have hinj : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro a ha
    apply Subtype.ext
    apply mem_bot.mp
    rw [← hf]
    refine ⟨a.property, ?_⟩
    change inclusion hn a ∈ B.normalizerMonoidHom.ker at ha
    rw [normalizerMonoidHom_ker] at ha
    exact ha
  let c : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
    MulEquiv.ofBijective MulAut.conjNormal
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by decide) (by decide))
  have hAut : Nat.card (MulAut B) = 16 * 315 := by
    rw [Nat.card_congr (MulAut.congr eB).toEquiv, ← Nat.card_congr c.toEquiv,
      Nat.card_perm, Nat.card_fin]
    norm_num
  have hd : Nat.card S ∣ 16 * 315 := hAut ▸ card_dvd_of_injective f hinj
  have hcop : Nat.Coprime (Nat.card S) 315 := by
    obtain ⟨m,hm⟩ := S.isPGroup'.exists_card_eq
    rw [hm]
    exact (by decide : Nat.Coprime 2 315).pow_left m
  exact hcop.dvd_of_dvd_mul_right hd

omit [Group H] [Finite H] in
/-- Restrict the same local section and full Sylow actor to the literal
containing two-core quotient. The returned section is its actual image. -/
theorem local_overcomponent_pair
    (T : Sylow 2 G) {X K : Subgroup G}
    (hX : X ∈ L G (T : Subgroup G))
    (hn : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hK : K ∈ L G (T : Subgroup G)) (hXK : X ≤ K)
    (h : Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 7))) :
    ∃ (S : Sylow 2 (K ⧸ pCore 2 K)) (B : Subgroup (K ⧸ pCore 2 K)),
      B ∈ localCComponents S ∧
      (S : Subgroup (K ⧸ pCore 2 K)) ≤ normalizer (B : Set _) ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7)) := by
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
  let f := (cComponentTwoCoreQuotientEquiv hK.1).symm.trans eK
  let : Group.IsSolvable f.toMonoidHom.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr f.injective]
    infer_instance
  obtain ⟨hl',hs',hm'⟩ := local_section_map hl hs ⟨er.trans hm.some⟩ f.toMonoidHom
  exact ⟨P.mapSurjective f.surjective,_,hl',hs',hm'⟩

omit [Group H] [Finite H] in
theorem not_model_of_local_overcomponent
    {M : Type*} [Group M]
    (hexclude : ∀ {V : Type u} [Group V] [Finite V] (S : Sylow 2 V) (B : Subgroup V),
      B ∈ localCComponents S → (S : Subgroup V) ≤ normalizer (B : Set V) →
      Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7)) → (V ≃* M) → False)
    (T : Sylow 2 G) {X K : Subgroup G}
    (hX : X ∈ L G (T : Subgroup G))
    (hn : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hK : K ∈ L G (T : Subgroup G)) (hXK : X ≤ K)
    (h : Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 7)))
    (e : (K ⧸ pCore 2 K) ≃* M) : False := by
  obtain ⟨S,B,hl,hs,hm⟩ := local_overcomponent_pair T hX hn hK hXK h
  exact hexclude S B hl hs hm e

end CFSG.Quasithin.Chapter1.Section02.ExceptionalOvercomponents.AlternatingSevenSection

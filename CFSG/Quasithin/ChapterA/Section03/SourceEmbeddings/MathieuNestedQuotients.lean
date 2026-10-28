module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BinaryNestedQuotients
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.MathieuTwentyFour

/-!
# Nested local components in the native Mathieu group

For a full-Sylow-normalized local component with nontrivial two-core,
the native normal-elementary catalogue gives a common octad, trio or
sextet stabilizer. The octad's actual binary-four quotient gives the
possible degrees three and four. In the trio, perfection kills the S₃
factor, and the literal affine kernel bounds the core quotient by 168.
The sextet order has no factor seven.

Consequently, a strict enlargement of a local PSL₃(2) component with
nontrivial two-core has PSL₄(2) two-core quotient. The original inclusion,
Sylow action and intrinsic core quotients are retained. The Section09
Mathieu consumer applies this to the actual image in JT/O₂(JT), excluding
all nontrivial-core plane enlargements there. The trivial-core case is
not asserted to be excluded by this theorem.

Source: Aschbacher--Smith, 12.9.3, printed pp.858--859, and A.3.12,
printed pp.47--48; the native local geometry is GLS3 Table 5.3e.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.MathieuNested
open BinaryIntrinsic BinaryNested BinaryLinear.OuterCyclic
open LinearFourCore PairOvergroups PairOvergroups.QuotientConstruction

private instance (n : ℕ) : Finite (LinearGroup n) :=
  Finite.of_injective (fun g : LinearGroup n => (g : (Fin n → ZMod 2) → (Fin n → ZMod 2))) DFunLike.coe_injective

private theorem perfect_of_local {X : Type*} [Group X] {B S : Subgroup X}
    (hB : B ∈ localCComponents S) : Group.IsPerfect B := by
  let := hB.perfect
  exact Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ S from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show B ≤ B ⊔ S from le_sup_left)).surjective

private theorem three_card {X : Type*} [Group X]
    (h : ClassicalGroup.IsPSL X 3 2) : Nat.card X = 168 := by
  obtain ⟨k,_,_,hk,⟨e⟩⟩ := h
  let := Fintype.ofFinite k
  let f : k ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hk)
  let a := ((e.trans (Atlas.fieldEquivPSL 3 f)).trans
    (projectiveEquivLinear (by decide))).trans (slEquivLinear 3).symm
  rw [Nat.card_congr a.toEquiv, Matrix.PSL3Two.card_SL]

private theorem quotient_card_dvd {X : Type*} [Group X] [Finite X]
    (A : Subgroup X) : Nat.card (A ⧸ pCore 2 A) ∣ Nat.card (X ⧸ pCore 2 X) := by
  let q := QuotientGroup.mk' (pCore 2 X)
  have hk : IsPGroup 2 (q.subgroupMap A).ker := by
    rw [ker_subgroupMap]
    have hq : IsPGroup 2 q.ker := by
      rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
    exact hq.comap_subtype
  let e := (q.subgroupMap A).pCoreQuotientEquiv (q.subgroupMap_surjective A) hk
  rw [Nat.card_congr e.toEquiv]
  exact (card_quotient_dvd_card _).trans (A.map q).card_subgroup_dvd_card

private theorem seed_octad_models (S : Sylow 2 (octadStabilizer seedOctad))
    (B : Subgroup (octadStabilizer seedOctad)) (hl : B ∈ localCComponents S) :
    Nat.card (B ⧸ pCore 2 B) ≤ 168 ∨ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2 := by
  classical
  let a : seedOctad.val ≃ Fin 8 := Fintype.equivFinOfCardEq (by
    rw [←Nat.card_eq_fintype_card,seed_card])
  let e := (a.altCongrHom.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.symm).trans
    (projectiveEquivLinear (by decide : 0 < 4))
  let q := e.toMonoidHom.comp alternatingAction
  have hq : Function.Surjective q := e.surjective.comp alternatingAction_surjective
  have hk : q.ker = pCore 2 (octadStabilizer seedOctad) := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,seed_core_eq_kernel]
    ext x
    change alternatingAction x = 1 ↔ action seedOctad x = 1
    simp only [Subtype.ext_iff,alternatingAction_coe,Subgroup.coe_one]
  have hp : IsPGroup 2 q.ker := hk ▸ pCore_isPGroup
  let : Group.IsNilpotent q.ker := hp.isNilpotent
  have hb := Chapter1.Section02.localCComponents_map_of_solvable_ker hl q
  obtain ⟨m,hm,hm4,⟨d⟩⟩ := local_twoCore_quotient 4 (by decide)
    (S.mapSurjective hq) (B.map q) hb
  have hkb : IsPGroup 2 (q.subgroupMap B).ker := by
    rw [ker_subgroupMap]; exact hp.comap_subtype
  let b := (q.subgroupMap B).pCoreQuotientEquiv (q.subgroupMap_surjective B) hkb
  have hmodel : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) m 2 :=
    ⟨ZMod 2,inferInstance,inferInstance,Nat.card_zmod 2,
      ⟨b.trans (d.trans (projectiveEquivLinear (by omega)).symm)⟩⟩
  rcases (show m = 3 ∨ m = 4 by omega) with rfl | rfl
  · exact Or.inl (three_card hmodel).le
  · exact Or.inr hmodel

private theorem transport_models {X Y : Type*} [Group X] [Group Y] [Finite X]
    (e : X ≃* Y) (S : Sylow 2 X) (B : Subgroup X) (hl : B ∈ localCComponents S)
    (hmodels : ∀ (T : Sylow 2 Y) (D : Subgroup Y), D ∈ localCComponents T →
      Nat.card (D ⧸ pCore 2 D) ≤ 168 ∨ ClassicalGroup.IsPSL (D ⧸ pCore 2 D) 4 2) :
    Nat.card (B ⧸ pCore 2 B) ≤ 168 ∨ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2 := by
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot e.injective]; infer_instance
  let b := e.subgroupMap B
  let q := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  rcases hmodels (S.mapSurjective e.surjective) (B.map e.toMonoidHom)
      (Chapter1.Section02.localCComponents_map_of_solvable_ker hl e.toMonoidHom) with hc | hm
  · exact Or.inl ((Nat.card_congr q.toEquiv).trans_le hc)
  · exact Or.inr (hm.of_mulEquiv q)

private theorem octad_models (O : Octad) (S : Sylow 2 (octadStabilizer O))
    (B : Subgroup (octadStabilizer O)) (hl : B ∈ localCComponents S) :
    Nat.card (B ⧸ pCore 2 B) ≤ 168 ∨ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2 := by
  obtain ⟨g,hg⟩ := exists_smul_octad_eq O seedOctad
  let e : octadStabilizer O ≃* octadStabilizer seedOctad :=
    MulAction.stabilizerEquivStabilizer (G := M24) hg.symm
  exact transport_models e S B hl seed_octad_models

private theorem symmetricThree_solvable : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
  rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]

private theorem trio_card (B : Subgroup (trioStabilizer standardTrio))
    [Group.IsPerfect B] : Nat.card (B ⧸ pCore 2 B) ≤ 168 := by
  let f := affineQuotient affineCoverage
  let g := (MonoidHom.snd (Equiv.Perm (Fin 3)) (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))).comp f
  let s := ((MonoidHom.fst (Equiv.Perm (Fin 3))
    (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))).comp f).comp B.subtype
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := symmetricThree_solvable
  have hs : s = 1 := by
    apply MonoidHom.range_eq_bot_iff.mp
    apply bot_unique
    have hm := map_solvableResidual_le s
    simpa only [solvableResidual_eq_top,solvableResidual_eq_bot,
      ←MonoidHom.range_eq_map] using hm
  have hk : IsPGroup 2 (g.subgroupMap B).ker := by
    let j : (g.subgroupMap B).ker →* f.ker :=
      { toFun := fun x => ⟨x.val.val,Prod.ext (DFunLike.congr_fun hs x.val)
          (congrArg Subtype.val x.property)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact (affineQuotient_kernel_isPGroup affineCoverage).of_injective j
      (fun x y hxy => Subtype.ext (Subtype.ext (congrArg (fun z : f.ker => z.val) hxy)))
  let e := (g.subgroupMap B).pCoreQuotientEquiv (g.subgroupMap_surjective B) hk
  rw [Nat.card_congr e.toEquiv]
  exact (Nat.le_of_dvd Nat.card_pos (card_quotient_dvd_card _)).trans
    ((card_le_card_group _).trans_eq Matrix.PSL3Two.card_SL)

private theorem candidate_models (k : Fin 2) (S : Sylow 2 (EvenCandidates.localGroup k))
    (B : Subgroup (EvenCandidates.localGroup k)) (hl : B ∈ localCComponents S)
    (hseven : 7 ∣ Nat.card (B ⧸ pCore 2 B)) :
    Nat.card (B ⧸ pCore 2 B) ≤ 168 ∨ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2 := by
  fin_cases k
  · apply transport_models EvenCatalogue.NormalSeeds.trioNormalizerEquiv S B hl
    intro T D hd
    let := perfect_of_local hd
    exact Or.inl (trio_card D)
  · exfalso
    have hd := (hseven.trans (card_quotient_dvd_card (pCore 2 B))).trans B.card_subgroup_dvd_card
    change 7 ∣ Nat.card (EvenCandidates.localGroup 1) at hd
    rw [Nat.card_congr EvenCatalogue.NormalSeeds.sextetNormalizerEquiv.toEquiv,
      SextetCore.stabilizer_card] at hd
    norm_num at hd

private noncomputable def markedSylow : Sylow 2 M24 :=
  Sylow.ofCard SylowNormalizer.candidate (by
    rw [SylowNormalizer.candidate_card,m24_order]
    decide +kernel)

private theorem fixed_models (B : Subgroup M24)
    (hl : B ∈ localCComponents markedSylow)
    (hn : (markedSylow : Subgroup M24) ≤ normalizer (B : Set M24))
    (hc : pCore 2 B ≠ ⊥) (hseven : 7 ∣ Nat.card (B ⧸ pCore 2 B)) :
    Nat.card (B ⧸ pCore 2 B) ≤ 168 ∨ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2 := by
  obtain ⟨N,hN,hBN,hSN⟩ := FiveLocalFF.SolvableQuotients.exists_maximal_two_local markedSylow B hn hc
  obtain ⟨R,hR,hnR,heR,hNR⟩ := exists_normal_elementary_normalizer_of_sylow_le markedSylow hN hSN
  obtain ⟨i,hi⟩ := MainConverse.M24Even.normalElementaryCatalogue R hR hnR heR
  have he : N = EvenCatalogue.localGroup i := by rw [hNR,hi]; rfl
  rw [he] at hBN hSN
  rcases EvenCatalogue.normalizerOvergroups i with ⟨O,hO⟩ | ⟨k,hk⟩
  · have hBO := hBN.trans hO
    let e := subgroupOfEquivOfLe hBO
    let q := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
    rcases octad_models O (markedSylow.subtype (hSN.trans hO))
      (B.subgroupOf (octadStabilizer O)) (local_restrict hl hBO) with hd | hm
    · exact Or.inl ((Nat.card_congr q.symm.toEquiv).trans_le hd)
    · exact Or.inr (hm.of_mulEquiv q.symm)
  · have hBK := hBN.trans hk
    let e := subgroupOfEquivOfLe hBK
    let q := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
    have h7 : 7 ∣ Nat.card ((B.subgroupOf (EvenCandidates.localGroup k)) ⧸
        pCore 2 (B.subgroupOf (EvenCandidates.localGroup k))) :=
      (Nat.card_congr q.toEquiv).symm ▸ hseven
    rcases candidate_models k (markedSylow.subtype (hSN.trans hk))
      (B.subgroupOf (EvenCandidates.localGroup k)) (local_restrict hl hBK) h7 with hd | hm
    · exact Or.inl ((Nat.card_congr q.symm.toEquiv).trans_le hd)
    · exact Or.inr (hm.of_mulEquiv q.symm)

/-- The actual octad, trio and sextet quotient maps bound a normalized M₂₄
local component with nontrivial two-core and a factor seven in its core quotient. -/
theorem local_models_of_core_ne_bot {G : Type*} [Group G] [Finite G]
    (e : G ≃* M24) (S : Sylow 2 G) (B : Subgroup G)
    (hl : B ∈ localCComponents S) (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hc : pCore 2 B ≠ ⊥) (hseven : 7 ∣ Nat.card (B ⧸ pCore 2 B)) :
    Nat.card (B ⧸ pCore 2 B) ≤ 168 ∨ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2 := by
  let Q := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M24 Q markedSylow
  let f := e.trans (MulAut.conj g)
  have hS : (S : Subgroup G).map f.toMonoidHom = (markedSylow : Subgroup M24) := by
    have he := congrArg (fun P : Sylow 2 M24 => (P : Subgroup M24)) hg
    change ((S : Subgroup G).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom = _ at he
    have hf : f.toMonoidHom = (MulAut.conj g).toMonoidHom.comp e.toMonoidHom := by ext x; rfl
    rw [hf,←map_map]
    exact he
  let : Group.IsSolvable f.toMonoidHom.ker := by
    rw [f.toMonoidHom.ker_eq_bot f.injective]; infer_instance
  have hl' := Chapter1.Section02.localCComponents_map_of_solvable_ker hl f.toMonoidHom
  have hn' := (map_mono (f := f.toMonoidHom) hn).trans (B.le_normalizer_map f.toMonoidHom)
  rw [hS] at hl' hn'
  have hc' : pCore 2 (B.map f.toMonoidHom) ≠ ⊥ := by
    intro hz
    apply hc
    apply (map_eq_bot_iff_of_injective (f := (f.subgroupMap B).toMonoidHom) _
      (f.subgroupMap B).injective).mp
    rw [pCore_map_iso]
    exact hz
  let b := f.subgroupMap B
  let q := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  have h7 : 7 ∣ Nat.card (B.map f.toMonoidHom ⧸ pCore 2 (B.map f.toMonoidHom)) :=
    (Nat.card_congr q.toEquiv) ▸ hseven
  rcases fixed_models (B.map f.toMonoidHom) hl' hn' hc' h7 with hd | hm
  · exact Or.inl ((Nat.card_congr q.toEquiv).trans_le hd)
  · exact Or.inr (hm.of_mulEquiv q)

/-- A strict enlargement of an original local PSL₃(2) section in M₂₄,
with nontrivial two-core, has the literal PSL₄(2) two-core quotient. -/
theorem strict_three_models_of_core_ne_bot {G : Type*} [Group G] [Finite G]
    (e : G ≃* M24) (S : Sylow 2 G) {B D : Subgroup G}
    (hB : B ∈ localCComponents S) (hD : D ∈ localCComponents S)
    (hBD : B < D) (hnD : (S : Subgroup G) ≤ normalizer (D : Set G))
    (hc : pCore 2 D ≠ ⊥) (hBm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 3 2) :
    ClassicalGroup.IsPSL (D ⧸ pCore 2 D) 4 2 := by
  let b := subgroupOfEquivOfLe hBD.le
  have hb := quotient_card_dvd (B.subgroupOf D)
  rw [Nat.card_congr (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).toEquiv,
    three_card hBm] at hb
  have hseven : 7 ∣ Nat.card (D ⧸ pCore 2 D) := (by decide : 7 ∣ 168).trans hb
  rcases local_models_of_core_ne_bot e S D hD hnD hc hseven with hd | hm
  · have he := local_eq_of_twoCore_card_le S hB hD hBD.le
      (hd.trans_eq (three_card hBm).symm)
    exact (hBD.ne he).elim
  · exact hm

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.MathieuNested

module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryNatural
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveDeletedCenter
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BinaryIntrinsicQuotients
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.CarrierSieve
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SporadicSieve
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2
public import GorensteinWalter.PGL2Cardinality
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8

/-!
# Carrier selection for the proper unitary quotient image

Write K = O²(H), Q = O₂(K), R = O₂(J). The actual image B of
K → J/R is a centerless natural SL₂(2^m) block with elementary two-core
of order 2^(2m). Its elementary rank forces J/R to be quasisimple by the
genuine A.3.6 theorem. Since B is centerless, the literal central quotient
is injective on B; perfectness prevents that proper image becoming full.
The natural module, full two-core and original full Sylow all survive.

Theorem C now supplies actual carriers. The elementary core excludes the
odd and small alternating families, while the full-Sylow local condition
excludes Bender and higher binary-linear groups. The latter uses their
actual flag-Levi quotient calculation and exact order separation from
PSL₂(2^m). The normalized elementary core reduces the sporadics to M₂₂,
M₂₃, M₂₄, J₄, Held and Rudvalis. A G₂ containing carrier is impossible:
its actual local parabolic core has order q^5, whereas the original core
has order q^2; the quotient isomorphism identifies these field orders.

The companion applies this sieve to the literal Chapter12 overcomponent,
including both unitary orientations and the degree-two extension. The
remaining carrier comparisons, (S)L₃ selection, natural R-action and
second-parabolic contradiction remain required. This does not prove
unitary maximality or the final ambient GlobalExit, and does not assume
the general conditional A.3.12 embedding interface.

Source: Aschbacher–Smith 5.2.8, printed pp.652–653, using A.3.6 and
A.3.12, printed pp.43–48 (`refs/quasithin.pdf`). The imported binary
matrix and exceptional-isomorphism results retain LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryEmbedding
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
open BinaryLinear BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] [Finite G]

private theorem binary_quotient_not_psl2 (d : ℕ) (hd : 3 ≤ d) (hd5 : d ≤ 5)
    {m : ℕ} (hm : 1 < m) (h : ClassicalGroup.IsPSL (LinearGroup d) 2 (2^m)) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := h
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hcard : Nat.card (LinearGroup d) = 2^m * ((2^m)^2-1) := by
    rw [Nat.card_congr (e.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm).toEquiv,
      GorensteinWalter.sl2_card_formula,hF]
  have hc : Nat.card (LinearGroup d) = ∏ i : Fin d, (2^d - 2^i.val) := by
    rw [←Nat.card_congr (matrixEquivLinear d).toEquiv,Matrix.card_GL_field]
    simp
  have hb : m ≤ 7 := by
    by_contra! hlarge
    have hpow : 256 ≤ 2^m := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hlarge
    have hbound : 16776960 ≤ 2^m * ((2^m)^2-1) := by
      have hh : 65535 ≤ (2^m)^2-1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hpow 2) 1
      exact Nat.mul_le_mul hpow hh
    rw [←hcard,hc] at hbound
    interval_cases d <;> norm_num [Fin.prod_univ_succ] at hbound
  rw [hc] at hcard
  interval_cases d <;> interval_cases m <;> norm_num [Fin.prod_univ_succ] at hcard

private theorem not_binary_containing
    (S : Sylow 2 G) (B : Subgroup G) (hB : B ∈ localCComponents S)
    {m : ℕ} (hm : 1 < m) (hb : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^m))
    {d : ℕ} (hd : d = 4 ∨ d = 5) (h : ClassicalGroup.IsPSL G d 2) : False := by
  obtain ⟨F,_,_,hF,⟨a⟩⟩ := h
  let := Fintype.ofFinite F
  let k : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  let e := (a.trans (Atlas.fieldEquivPSL d k)).trans
    (projectiveEquivLinear (by rcases hd with rfl | rfl <;> decide))
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective]
    infer_instance
  have hlocal := Chapter1.Section02.localCComponents_map_of_solvable_ker hB e.toMonoidHom
  obtain ⟨r,hr,hrd,⟨j⟩⟩ := BinaryIntrinsic.local_twoCore_quotient d
    (by rcases hd with rfl | rfl <;> omega)
    (S.mapSurjective (f := e.toMonoidHom) e.surjective) (B.map e.toMonoidHom) hlocal
  let eb := B.equivMapOfInjective e.toMonoidHom e.injective
  let eq := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  obtain ⟨K,_,_,hK,⟨b⟩⟩ := hb
  exact binary_quotient_not_psl2 r hr (hrd.trans (by rcases hd with rfl | rfl <;> omega)) hm
    ⟨K,inferInstance,inferInstance,hK,⟨j.symm.trans (eq.symm.trans b)⟩⟩

private theorem small_alternating_rank {d : ℕ} (hd : d ≤ 7) :
    primeRank 2 (alternatingGroup (Fin d)) ≤ 3 := by
  let P : Sylow 2 (alternatingGroup (Fin d)) := Classical.choice inferInstance
  rw [P.primeRank_eq]
  apply (primeRank_le_iff_elementary_card_le P).mpr
  intro E _
  apply E.card_le_card_group.trans
  rw [P.card_eq_multiplicity]
  interval_cases d
  · have hc : Nat.card (alternatingGroup (Fin 0)) = 1 := Nat.card_unique
    rw [hc]; simp
  · have hc : Nat.card (alternatingGroup (Fin 1)) = 1 := Nat.card_unique
    rw [hc]; simp
  all_goals rw [nat_card_alternatingGroup,Nat.card_fin]; decide +kernel


private theorem core_card_separation
    {X : Type*} [Group X] [Finite X] {F : Type*} [Field F] [Finite F] [CharP F 2]
    {m a : ℕ} (ha : a ≠ 2)
    (hm : ClassicalGroup.IsPSL (X ⧸ pCore 2 X) 2 (2^m))
    (hcore : Nat.card (pCore 2 X) = (2^m)^2)
    (e : (X ⧸ pCore 2 X) ≃* PSL(2,F))
    (hcard : Nat.card (pCore 2 X) = Nat.card F ^ a) : False := by
  obtain ⟨K,_,_,hK,⟨b⟩⟩ := hm
  let := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hK)
  have hfield : 2^m = Nat.card F := hK.symm.trans (binary_psl_field_card_eq (b.symm.trans e))
  rw [hfield] at hcore
  exact ha (Nat.pow_right_injective (Finite.one_lt_card (α := F)) (hcard.symm.trans hcore))

private theorem not_g2_model {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hq : 2 < Nat.card F) (S : Sylow 2 (Atlas.G2.Model F))
    (B : Subgroup (Atlas.G2.Model F)) (hB : B ∈ localCComponents S)
    (hproper : B ≠ ⊤) {m : ℕ}
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^m))
    (hc : Nat.card (pCore 2 B) = (2^m)^2) : False := by
  obtain ⟨g,hg⟩ := FiveLocalFF.G2.local_placement hq S B hB hproper
  let a := B.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have hcore := LocalCoreTransport.core_card 2 a
  rw [hc] at hcore
  rcases hg with hg | hg
  · have e : (B ⧸ pCore 2 B) ≃* PSL(2,F) := aq.trans (by
      rw [hg]
      exact Atlas.G2.LieParabolicSetup.local₁CoreQuotientEquivPSL)
    have hcard : Nat.card (pCore 2 B) = Nat.card F ^ 5 := by
      rw [hg,Atlas.G2.LieParabolicSetup.card_local₁_pCore] at hcore
      exact hc.trans hcore
    exact core_card_separation (by decide : 5 ≠ 2) hm hc e hcard
  · have e : (B ⧸ pCore 2 B) ≃* PSL(2,F) := aq.trans (by
      rw [hg]
      exact Atlas.G2.LieParabolicSetup.local₂CoreQuotientEquivPSL)
    have hcard : Nat.card (pCore 2 B) = Nat.card F ^ 5 := by
      rw [hg,Atlas.G2.LieParabolicSetup.card_local₂_pCore] at hcore
      exact hc.trans hcore
    exact core_card_separation (by decide : 5 ≠ 2) hm hc e hcard

private theorem not_g2_containing
    (S : Sylow 2 G) (B : Subgroup G) (hB : B ∈ localCComponents S)
    (hproper : B ≠ ⊤) {m : ℕ}
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^m))
    (hc : Nat.card (pCore 2 B) = (2^m)^2)
    {f : ℕ} (hf : 2 ≤ f) (h : ClassificationModels.IsG2At G (2^f)) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := h
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let a := B.equivMapOfInjective e.toMonoidHom e.injective
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have hcore := LocalCoreTransport.core_card 2 a
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective]
    infer_instance
  have hlocal := Chapter1.Section02.localCComponents_map_of_solvable_ker hB e.toMonoidHom
  have hne : B.map e.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hproper
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [ht,map_top_of_surjective e.toMonoidHom e.surjective]
  obtain ⟨K,_,_,hK,⟨b⟩⟩ := hm
  apply not_g2_model (S := S.mapSurjective (f := e.toMonoidHom) e.surjective)
    (B := B.map e.toMonoidHom) ?_ hlocal hne
    ⟨K,inferInstance,inferInstance,hK,⟨aq.symm.trans b⟩⟩ (hcore.symm.trans hc)
  rw [hF]
  exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) hf)

/-- Actual carriers remaining after the elementary-core and full-Sylow sieve.
Every alternative includes a model isomorphism. -/
@[expose] def RemainingModels (X : Type*) [Group X] : Prop :=
  ((∃ f, ChapterA.Section02.IsTheoremCRankTwoModel X f) ∨
    ∃ name : ClassificationModels.SporadicName,
      (name = .m22 ∨ name = .m23 ∨ name = .m24 ∨ name = .j4 ∨
        name = .he ∨ name = .ru) ∧ Nonempty (X ≃* name.Carrier)) ∧
    ¬ ∃ f, 2 ≤ f ∧ ClassificationModels.IsG2At X (2^f)

private theorem simple_sieve [IsQuasisimple G]
    (S : Sylow 2 G) (B E : Subgroup G)
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤)
    {m : ℕ} (hm : 1 < m) (hb : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^m))
    (hcore : Nat.card (pCore 2 B) = (2^m)^2)
    (hE : IsElementaryAbelian 2 E) (hc : 16 ≤ Nat.card E)
    (hEn : (S : Subgroup G) ≤ normalizer (E : Set G))
    (hmodel : ChapterA.Section02.IsTheoremCModel G) :
    RemainingModels G := by
  refine ⟨?_,fun ⟨f,hf,hg⟩ => not_g2_containing S B hB hproper hb hcore hf hg⟩
  cases hmodel with
  | odd h => exact (FiveLocalFF.CarrierSieve.not_odd_model E hE hc h).elim
  | bender h => exact (FiveLocalFF.CarrierSieve.not_bender_model S B hB hproper h).elim
  | rank_two f h => exact .inl ⟨f,h⟩
  | sporadic h => exact .inr (FiveLocalFF.SporadicSieve.six_carriers S E hE hEn hc h)
  | linear_binary d hd h => exact (not_binary_containing S B hB hm hb hd h).elim
  | alternating d hd he =>
    obtain ⟨e⟩ := he
    by_cases hd8 : d = 8
    · subst d
      have hbin : ClassicalGroup.IsPSL G 4 2 :=
        ⟨ZMod 2,inferInstance,inferInstance,Nat.card_zmod 2,
          ⟨e.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two⟩⟩
      exact (not_binary_containing S B hB hm hb (.inl rfl) hbin).elim
    · have hr : primeRank 2 G ≤ 3 := by
        rw [primeRank_equiv 2 e]
        exact small_alternating_rank (by omega)
      have hbound := (primeRank_le_iff_elementary_card_le G).mp hr E hE
      norm_num at hbound
      omega


/-- The centerless natural image survives the literal central quotient.
The genuine A.3.6 and Theorem C catalogues then give the reduced carriers. -/
theorem center_quotient_models
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hO : pCore 2 G = ⊥)
    (htop : (⊤ : Subgroup G).IsCComponent)
    (S : Sylow 2 G) (B : Subgroup G) (hB : B ∈ localCComponents S)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hproper : B ≠ ⊤) {m : ℕ} (hb : ChapterC.IsL2EvenBlock B m)
    (hel : IsElementaryAbelian 2 (pCore 2 B))
    (hc : Nat.card (pCore 2 B) = (2^m)^2) (hz : center B = ⊥) :
    IsQuasisimple G ∧
      RemainingModels (G ⧸ center G) := by
  let E := B.pCoreIn 2
  have hE : IsElementaryAbelian 2 E := by
    let := hel
    exact IsElementaryAbelian.map B.subtype
  have hEc : 16 ≤ Nat.card E := by
    have hpow : 4 ≤ 2^m := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hb.1
    have hec : Nat.card E = Nat.card (pCore 2 B) :=
      (Nat.card_congr ((pCore 2 B).equivMapOfInjective B.subtype B.subtype_injective).toEquiv).symm
    rw [hec,hc]
    nlinarith
  have hr : 4 ≤ primeRank 2 G := by
    by_contra! hh
    have hh' : primeRank 2 G ≤ 3 := by omega
    have hh'' := (primeRank_le_iff_elementary_card_le G).mp hh' E hE
    norm_num at hh''
    omega
  let : IsQuasisimple (⊤ : Subgroup G) :=
    NoncentralFitting.quasisimple_of_two_le_two_rank hG hO htop (by
      rw [primeRank_equiv 2 (topEquiv (G := G))]
      omega)
  let : IsQuasisimple G := IsQuasisimple.of_mulEquiv (topEquiv (G := G))
  refine ⟨inferInstance,?_⟩
  let q := QuotientGroup.mk' (center G)
  let f := q.comp B.subtype
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro x hx
    have hxz : (x : G) ∈ center G := (QuotientGroup.eq_one_iff _).mp hx
    have hxb : x ∈ center B := mem_center_iff.mpr (fun y =>
      Subtype.ext (mem_center_iff.mp hxz y))
    simpa only [hz,mem_bot] using hxb
  let e : B ≃* B.map q := MulEquiv.ofBijective (q.subgroupMap B)
    ⟨fun x y hh => hf (congrArg Subtype.val hh),q.subgroupMap_surjective B⟩
  let SB := S.mapSurjective (QuotientGroup.mk'_surjective (center G))
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    exact Group.isSolvable_of_comm fun a b => IsMulCommutative.is_comm.comm a b
  have hlocal : B.map q ∈ localCComponents SB :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hB q
  have hne : B.map q ≠ ⊤ := by
    intro hh
    apply hproper
    apply eq_top_of_sup_center_eq_top B
    have hcomap := congrArg (Subgroup.comap q) hh
    simpa only [comap_map_eq,q,QuotientGroup.ker_mk',comap_top] using hcomap
  have hbq := ChapterC.IsL2EvenBlock.of_mulEquiv hb e
  obtain ⟨F,_,_,hF,hpsl,_⟩ := hbq.2.2
  let ecore := (e.subgroupMap (pCore 2 B)).trans
    (MulEquiv.subgroupCongr (pCore_map_iso 2 e))
  have hcore : IsElementaryAbelian 2 (pCore 2 (B.map q)) := by
    let := hel
    exact IsElementaryAbelian.of_injective ecore.symm.toMonoidHom ecore.symm.injective
  let D := (B.map q).pCoreIn 2
  have hD : IsElementaryAbelian 2 D := by
    let := hcore
    exact IsElementaryAbelian.map (B.map q).subtype
  have hDc : 16 ≤ Nat.card D := by
    have hec := Nat.card_congr ((pCore 2 (B.map q)).equivMapOfInjective
      (B.map q).subtype (B.map q).subtype_injective).toEquiv
    change 16 ≤ Nat.card ((pCore 2 (B.map q)).map (B.map q).subtype)
    rw [←hec,←Nat.card_congr ecore.toEquiv,hc]
    have hp : 4 ≤ 2^m := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hb.1
    nlinarith
  let : IsSimpleGroup (G ⧸ center G) := IsQuasisimple.simple
  have hSBq : (SB : Subgroup (G ⧸ center G)) ≤ normalizer (B.map q : Set _) :=
    (map_mono hSB).trans (le_normalizer_map q)
  have hDn : (SB : Subgroup (G ⧸ center G)) ≤ normalizer (D : Set _) :=
    hSBq.trans (normalizer_le_normalizer_characteristic_image (B.map q) (pCore 2 (B.map q)))
  let : IsQuasisimple (G ⧸ center G) := IsQuasisimple.of_surjective q
    (QuotientGroup.mk'_surjective (center G))
  have hcq : Nat.card (pCore 2 (B.map q)) = (2^m)^2 :=
    (Nat.card_congr ecore.symm.toEquiv).trans hc
  exact simple_sieve SB (B.map q) D hlocal hne hb.1 hpsl hcq hD hDc hDn
    (quasisimple_center_quotient_theoremC_model hG)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryEmbedding

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
section Unitary
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B (residual H))
  (h : Input KnownSimple.IsKnownSimple T L W n)
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
  (he : (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm).reverse)) ∨
    (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)))
include d h hH hp m hm he

/-- The actual overcomponent quotient is quasisimple. Its literal central
quotient lies in the remaining rank-two or six sporadic carriers, after
excluding the odd, alternating, Bender, higher binary-linear and G₂ families. -/
theorem Preparation.unitary_overcomponent_central_quotient_models
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hKJ : residual H < J)
    (hQR : ¬ (residual H).pCoreIn 2 ≤ J.pCoreIn 2) :
    IsQuasisimple (J ⧸ pCore 2 J) ∧
      UnitaryEmbedding.RemainingModels
        ((J ⧸ pCore 2 J) ⧸ center (J ⧸ pCore 2 J)) := by
  obtain ⟨hsq,htop,hproper,S,hS,hlocal,hnorm⟩ :=
    d.unitary_overcomponent_embedding_context h hH hp m hm he hJ hKJ
  obtain ⟨hb,hcore,hcenter⟩ :=
    d.unitary_overcomponent_proper_image_block h hH hp m hm he hJ hKJ.le hQR
  have hel := (d.unitary_overcomponent_quotient_image h hH hp m hm he hJ hKJ.le).2.2.1
  have hc := (d.unitary_overcomponent_proper_quotient_core h hH hp m hm he hJ hKJ.le hQR).1
  exact UnitaryEmbedding.center_quotient_models hsq (pCore_quotient_pCore_eq_bot 2)
    htop (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 J))) _
    hlocal hnorm hproper hb hel hc hcenter

end Unitary

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.Alternating.ProperComponents.PrimitiveRecognition.EightKernel
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Quotients
public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.BinaryLinear.FourTwoLocalFive
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.MaximalLevi
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.Residuals.FlagTypes
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Higher binary linear exclusions for local alternating-five sections

A local C-component whose two-core quotient is alternating of degree five
has order divisible by five. In dimension four, a proper full-Sylow join
lies in a subspace parabolic, whose order is prime to five. In dimension
five, a proper full-Sylow join with a factor five is an endpoint parabolic;
its actual two-core quotient is simple PSL₄(2). The C-component image is
then the whole quotient, contradicting the supplied alternating-five section.
The whole-group joins are excluded by simplicity and group orders.

The image consumer retains both the literal quotient map and the original
smaller two-core, using a two-group restricted kernel to transport the section.
No quasisimplicity assumption on the smaller local C-component is required.

Source: the higher binary linear rows of Aschbacher–Smith A.3.12(4–5),
printed pp.47–48, in the local-section application of 10.2.9, printed pp.751–752.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.BinaryLinear
open ChapterB.ComponentRecognition.SylowOvergroups
open _root_.BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
open BinaryLinear.FiveFlagGeometry.MaximalOvergroups

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem five_dvd_section (B : Subgroup G)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) : 5 ∣ Nat.card B := by
  have hd := card_quotient_dvd_card (pCore 2 B)
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup] at hd
  norm_num at hd
  exact (by decide : 5 ∣ 60).trans hd

omit [Finite G] in
private theorem simple_not_five_section [IsSimpleGroup G]
    (hc : Nat.card G ≠ 60) (B : Subgroup G) (hB : B.IsCComponent)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) : False := by
  have hBt : B = ⊤ := (hB.subnormal.eq_bot_or_top_of_isSimpleGroup
    (inferInstance : IsSimpleGroup G)).resolve_left hB.ne_bot
  let d : B ≃* G := (MulEquiv.subgroupCongr hBt).trans topEquiv
  let : IsSimpleGroup B := d.isSimpleGroup
  have hp : pCore 2 B = ⊥ := by
    rcases (inferInstance : (pCore 2 B).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · have hh : Nat.card (B ⧸ pCore 2 B) = 60 := by
        rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
        norm_num
      rw [h] at hh
      simp at hh
  let q : B ≃* B ⧸ pCore 2 B := QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hp.symm)
  apply hc
  rw [← Nat.card_congr d.toEquiv, Nat.card_congr (q.trans e).toEquiv,
    nat_card_alternatingGroup]
  norm_num

private theorem binary_card (n : ℕ) [NeZero n] :
    Nat.card PSL(n, ZMod 2) = ∏ i : Fin n, (2 ^ n - 2 ^ i.val) := by
  have h := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) n
  simpa only [Nat.card_zmod, show 2 - 1 = 1 from rfl, Nat.gcd_one_right, mul_one] using h

private instance : Finite (LinearGroup 4) :=
  Finite.of_injective (fun g : LinearGroup 4 => (g : Space 4 → Space 4)) DFunLike.coe_injective

private instance : Finite (LinearGroup 5) :=
  Finite.of_injective (fun g : LinearGroup 5 => (g : Space 5 → Space 5)) DFunLike.coe_injective

private theorem not_section_linearFour (S : Sylow 2 (LinearGroup 4))
    (B : Subgroup (LinearGroup 4)) (hB : B ∈ localCComponents S)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) : False := by
  let e := projectiveEquivLinear (by decide : 0 < 4)
  let : IsSimpleGroup PSL(4, ZMod 2) := Atlas.psl_simple_high_rank 4 (by decide)
  let : IsSimpleGroup (LinearGroup 4) := e.symm.isSimpleGroup
  let J := B ⊔ (S : Subgroup (LinearGroup 4))
  by_cases hj : J = ⊤
  · have hl : B.IsCComponent := by
      have hh : (B.subgroupOf J).IsCComponent := hB
      rw [hj] at hh
      simpa only [map_subgroupOf_eq_of_le le_top] using hh.map_subtype .top
    apply simple_not_five_section (B := B) _ hl eB
    rw [← Nat.card_congr e.toEquiv, binary_card]
    decide
  · obtain ⟨W, hW, hWt, hJP⟩ := exists_invariant_subspace S J le_sup_right hj
    exact BinaryLinear.FourTwoLocalFive.five_not_dvd_parabolic W hW hWt
      ((five_dvd_section B eB).trans (card_dvd_of_le (le_sup_left.trans hJP)))

private theorem not_section_linearFive (S : Sylow 2 (LinearGroup 5))
    (B : Subgroup (LinearGroup 5)) (hB : B ∈ localCComponents S)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) : False := by
  let e := projectiveEquivLinear (by decide : 0 < 5)
  let : IsSimpleGroup PSL(5, ZMod 2) := Atlas.psl_simple_high_rank 5 (by decide)
  let : IsSimpleGroup (LinearGroup 5) := e.symm.isSimpleGroup
  let J := B ⊔ (S : Subgroup (LinearGroup 5))
  have hl : (B.subgroupOf J).IsCComponent := hB
  by_cases hj : J = ⊤
  · have hl' : B.IsCComponent := by
      rw [hj] at hl
      simpa only [map_subgroupOf_eq_of_le le_top] using hl.map_subtype .top
    apply simple_not_five_section (B := B) _ hl' eB
    rw [← Nat.card_congr e.toEquiv, binary_card]
    decide
  · obtain ⟨b, cuts, hcuts⟩ := isFlagParabolic_of_sylow_le S J le_sup_right
    have hproper : flagStabilizer b cuts ≠ ⊤ := hcuts ▸ hj
    have hfive : 5 ∣ Nat.card (flagStabilizer b cuts) := by
      rw [← hcuts]
      exact (five_dvd_section B eB).trans (card_dvd_of_le le_sup_left)
    have hq : Nonempty ((J ⧸ pCore 2 J) ≃* PSL(4, ZMod 2)) := by
      let d := MulEquiv.subgroupCongr hcuts
      let dq := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
      rcases cuts_eq_singleton_end_of_five_dvd b cuts hproper hfive with h | h
      · exact ⟨dq.trans (h.symm ▸ lineQuotientEquiv b)⟩
      · exact ⟨dq.trans (h.symm ▸ hyperplaneQuotientEquiv b)⟩
    obtain ⟨a⟩ := hq
    let : IsSimpleGroup PSL(4, ZMod 2) := Atlas.psl_simple_high_rank 4 (by decide)
    let : IsSimpleGroup (J ⧸ pCore 2 J) := a.isSimpleGroup
    let : Group.IsNilpotent (pCore 2 J) := pCore_isNilpotent
    have him := hl.map_quotient (pCore 2 J)
    let c := cComponentTwoCoreQuotientEquiv hl
    let d : B.subgroupOf J ≃* B := subgroupOfEquivOfLe le_sup_left
    let dquot := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
    let m := c.symm.trans (dquot.trans eB)
    have htop : (B.subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) = ⊤ :=
      (him.subnormal.eq_bot_or_top_of_isSimpleGroup
        (inferInstance : IsSimpleGroup (J ⧸ pCore 2 J))).resolve_left him.ne_bot
    let k := (MulEquiv.subgroupCongr htop).trans (topEquiv.trans a)
    have hc := Nat.card_congr (k.symm.trans m).toEquiv
    have hn : Nat.card PSL(4, ZMod 2) ≠ Nat.card (alternatingGroup (Fin 5)) := by
      rw [binary_card, nat_card_alternatingGroup, Nat.card_fin]
      decide
    exact hn hc

private theorem not_section_of_equiv {H : Type*} [Group H] [Finite H]
    (hH : ∀ (S : Sylow 2 H) (B : Subgroup H), B ∈ localCComponents S →
      ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) → False)
    (a : G ≃* H) (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) : False := by
  let : Group.IsSolvable a.toMonoidHom.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr a.injective]
    infer_instance
  let d := B.equivMapOfInjective a.toMonoidHom a.injective
  let dq := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
  apply hH (S.mapSurjective (f := a.toMonoidHom) a.surjective)
    (B.map a.toMonoidHom) _ (dq.symm.trans eB)
  exact Chapter1.Section02.localCComponents_map_of_solvable_ker hB a.toMonoidHom

/-- No full-Sylow local C-component in PSL₄(2) has two-core quotient A₅. -/
theorem not_section_psl_four (S : Sylow 2 PSL(4, ZMod 2))
    (B : Subgroup PSL(4, ZMod 2)) (hB : B ∈ localCComponents S)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) : False :=
  not_section_of_equiv not_section_linearFour (projectiveEquivLinear (by decide)) S B hB eB

/-- No full-Sylow local C-component in PSL₅(2) has two-core quotient A₅. -/
theorem not_section_psl_five (S : Sylow 2 PSL(5, ZMod 2))
    (B : Subgroup PSL(5, ZMod 2)) (hB : B ∈ localCComponents S)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) : False :=
  not_section_of_equiv not_section_linearFive (projectiveEquivLinear (by decide)) S B hB eB

/-- Both higher binary linear containing rows are excluded while retaining
the original smaller two-core. -/
theorem not_section_binary_linear (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    {d : ℕ} (hd : d = 4 ∨ d = 5) (hm : ClassicalGroup.IsPSL G d 2) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let k : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  let a := e.trans (Atlas.fieldEquivPSL d k)
  rcases hd with rfl | rfl
  · exact not_section_of_equiv not_section_psl_four a S B hB eB
  · exact not_section_of_equiv not_section_psl_five a S B hB eB

/-- The literal reduced-action image cannot be either higher binary linear
model. The restricted two-kernel preserves the supplied A₅ marking. -/
theorem image_excluded {M : Type*} [Group M] [Finite M]
    (f : G →* M) (hf : Function.Surjective f) (hks : Group.IsSolvable f.ker)
    (S : Sylow 2 G) (L : Subgroup G) (hL : L ∈ localCComponents S)
    (hk : IsPGroup 2 (f.subgroupMap L).ker)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {d : ℕ} (hd : d = 4 ∨ d = 5) (hm : ClassicalGroup.IsPSL M d 2) : False := by
  let : Group.IsSolvable f.ker := hks
  let eq := ((f.subgroupMap L).pCoreQuotientEquiv (f.subgroupMap_surjective L) hk).symm.trans e
  exact not_section_binary_linear (S.mapSurjective hf) (L.map f)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hL f) eq hd hm

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.BinaryLinear

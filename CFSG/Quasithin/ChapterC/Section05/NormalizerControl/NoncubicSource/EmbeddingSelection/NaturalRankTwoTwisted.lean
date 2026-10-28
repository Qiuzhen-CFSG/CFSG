module

public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.NaturalRankTwo
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.ReeLocal
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Triality
public import Theory.SpecificGroups.Triality.BinaryMovedElementary
public import Theory.SpecificGroups.Triality.SylowComponentUnique
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ExceptionalRestrictions.Conjugation

/-!
# Excluding twisted rank-two carriers for a centerless natural block

The actual Ree local placement gives either a Suzuki quotient, excluded by
its three-free order, or an SL₂ quotient whose field is the block's field.
The latter residual has two-core of order q¹¹, incompatible with q².
For triality over q > 2, the two residual quotients recover fields q³ and q,
while the corresponding cores have orders q⁹ and q¹¹. Neither is a natural
block with its full two-core. At q = 2, full-Sylow component uniqueness
normalizes the block; its nonzero moved elementary core contradicts the
proved arms-radical bound. This endpoint uses no perfectness assertion for
the entire binary arms factor.

Together with the preceding six model cases, these exclusions recognize
PSL₃ over the original field from the rank-two alternative. They retain
the genuine local component, actual isomorphisms and relative quotients.
The Chapter 10 application is NaturalTerminal/OddRecognition; the genuine
A.3.12 embedding remains with qt-d-10-nona5-moving-hall-three.
Source: Aschbacher–Smith A.3.12, pp.47–48, F.1.12(I)(4–5), pp.263–264,
and 10.2.3(4), p.747. All concrete model calculations reuse existing proofs.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin CFSG.Quasithin.ChapterC
open CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
open CFSG.Quasithin.ChapterA.Section03
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection.NaturalRankTwo
variable {G X : Type*} [Group G] [Finite G] [Group X] [Finite X]

omit [Finite X] in
private theorem transport_local (e : G ≃* X) (S : Sylow 2 G) (J : Subgroup G)
    (hl : J ∈ localCComponents S) :
    J.map e.toMonoidHom ∈ localCComponents
      (S.mapSurjective (f := e.toMonoidHom) e.surjective : Subgroup X) := by
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective]
    infer_instance
  exact Chapter1.Section02.localCComponents_map_of_solvable_ker hl e.toMonoidHom

omit [Finite G] [Finite X] in
private theorem transport_proper (e : G ≃* X) (J : Subgroup G) (h : J ≠ ⊤) :
    J.map e.toMonoidHom ≠ ⊤ := by
  intro he
  apply h
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [map_top_of_surjective e.toMonoidHom e.surjective]
  exact he

private theorem core_card_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nat.card (pCore 2 A) = Nat.card (pCore 2 B) :=
  Nat.card_congr ((e.subgroupMap (pCore 2 A)).trans
    (MulEquiv.subgroupCongr (pCore_map_iso 2 e))).toEquiv

/-- Neither actual Ree parabolic residual is a centerless full-core natural block. -/
theorem not_ree (S : Sylow 2 G) (J : Subgroup G)
    (ht : (⊤ : Subgroup G).IsCComponent)
    (hl : J ∈ localCComponents S) (hp : J ≠ ⊤)
    {n : ℕ} (h : IsL2EvenBlock J n) (hc : pCore 2 J = blockU J) (hz : center J = ⊥)
    {m : ℕ} (hm : 1 ≤ m) : ¬ Chapter1.Section02.LocalModels.IsReeF4At G m := by
  rintro ⟨d,⟨a⟩⟩
  let e := a.trans d.modelEquiv
  have ht' : (⊤ : Subgroup (ReeF4.Model m)).IsCComponent := by
    simpa only [map_top_of_surjective e.toMonoidHom e.surjective] using ht.map_equiv e
  obtain ⟨g,s,hg⟩ := ReeLocal.local_placement hm ht'
    (S.mapSurjective (f := e.toMonoidHom) e.surjective) (J.map e.toMonoidHom)
    (transport_local e S J hl) (transport_proper e J hp)
  let b := ((e.subgroupMap J).trans
    ((MulAut.conj g).subgroupMap (J.map e.toMonoidHom))).trans (MulEquiv.subgroupCongr hg)
  let q := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  open ReeF4.Parabolics in
  cases s with
  | suzuki =>
    obtain ⟨F,_,_,_,hps,_⟩ := h.2.2
    exact binary_not_suzuki hps m (by omega) ⟨q.trans (suzukiLocalQuotientEquiv m)⟩
  | linear =>
    have hf := quotient_field_card h (q.trans ((linearLocalQuotientEquiv m).trans
      (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := ReeF4.CoefficientField m)).symm))
    rw [ReeF4.field_card] at hf
    have hn := Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hf
    have hh := core_card_equiv b
    rw [core_card h hc hz,card_local_pCore_linear,←pow_mul] at hh
    have he := Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hh
    omega

/-- The two triality residuals have cores too large for their natural quotient field. -/
theorem not_triality_nonbinary (S : Sylow 2 G) (J : Subgroup G)
    (hl : J ∈ localCComponents S)
    {n : ℕ} (h : IsL2EvenBlock J n) (hc : pCore 2 J = blockU J) (hz : center J = ⊥)
    {f : ℕ} (hf : 2 ≤ f) : ¬ Triality.Standard.IsTrialityGroupAt (2^f) G := by
  intro hm
  open Triality.Standard Triality.Standard.Parabolics in
  have hf0 : 0 < f := by omega
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff G f hf0).mp hm
  let A := J.map e.toMonoidHom
  have hcore : pCore 2 A ≠ ⊥ := by
    intro he
    have hh := core_card_equiv (e.subgroupMap J)
    change Nat.card (pCore 2 J) = Nat.card (pCore 2 A) at hh
    rw [he,card_bot,core_card h hc hz] at hh
    have hn := h.1
    have hp : 1 < 2^(2*n) := Nat.one_lt_pow (by omega) (by decide)
    omega
  have hq : 2 < 2^f := lt_of_lt_of_le (by decide : 2 < 2^2)
    (Nat.pow_le_pow_right (by decide) hf)
  obtain ⟨g,s,hg⟩ := FiveLocalFF.Triality.local_placement f hf0 hq
    (S.mapSurjective (f := e.toMonoidHom) e.surjective) A (transport_local e S J hl) hcore
  let b := ((e.subgroupMap J).trans ((MulAut.conj g).subgroupMap A)).trans
    (MulEquiv.subgroupCongr hg)
  let q := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  open Triality.Standard Triality.Standard.Parabolics in
  cases s with
  | arms =>
    have hh := quotient_field_card h (q.trans ((localFactorArmsQuotientEquivPSL2 _ rfl).trans
      (Theory.PSL2.sl2QuotientEquiv _).symm))
    rw [card_extensionField] at hh
    change (2^f)^3 = 2^n at hh
    rw [←pow_mul] at hh
    have hn := Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hh
    have hk := core_card_equiv b
    rw [core_card h hc hz,localFactor_arms_twoCore_card _ rfl] at hk
    change 2^(2*n) = (2^f)^9 at hk
    rw [←pow_mul] at hk
    have he := Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hk
    omega
  | central =>
    have hh := quotient_field_card h (q.trans ((localFactorCentralQuotientEquivPSL2 _ rfl).trans
      (Theory.PSL2.sl2QuotientEquiv _).symm))
    rw [card_baseField] at hh
    change 2^f = 2^n at hh
    have hn := Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hh
    have hk := core_card_equiv b
    rw [core_card h hc hz,localFactor_central_twoCore_card _ rfl] at hk
    change 2^(2*n) = (2^f)^11 at hk
    rw [←pow_mul] at hk
    have he := Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hk
    omega

/-- At field order two the moved elementary block core contradicts the actual arms radical. -/
theorem not_triality_binary (S : Sylow 2 G) (J : Subgroup G)
    (hl : J ∈ localCComponents S) (hp : J ≠ ⊤)
    {n : ℕ} (h : IsL2EvenBlock J n) :
    ¬ Triality.Standard.IsTrialityGroupAt 2 G := by
  intro hm
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff G 1 Nat.zero_lt_one).mp
    (show Triality.Standard.IsTrialityGroupAt (2^1) G from hm)
  let := hl.perfect
  let d := subgroupOfEquivOfLe (show J ≤ J ⊔ (S : Subgroup G) from le_sup_left)
  let : Group.IsPerfect J := Group.IsPerfect.ofSurjective (f := d.toMonoidHom) d.surjective
  have hns : ¬ Group.IsSolvable J := by
    intro hs
    let := hs
    exact hl.not_isSolvable (Group.isSolvable_of_isSolvable_injective
      (f := d.toMonoidHom) d.injective)
  have hnorm : (S : Subgroup G) ≤ normalizer (J : Set G) :=
    SylowOvergroupComponentUnique.normalizes_local_component S (K := ⊤) hl .top le_top
      (by rw [normalizer_eq_top]; exact le_top)
      (.of_equiv ((topEquiv (G := G)).trans e)
        (Triality.Standard.binary_sylow_overgroup_component_unique 1 Nat.zero_lt_one))
  let E := (blockU J).map J.subtype
  let : IsElementaryAbelian 2 (blockU J) := h.2.1.elementary
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map J.subtype
  have hE : E ≠ ⊥ := by
    intro he
    exact h.2.1.blockU_ne_bot ((map_eq_bot_iff_of_injective _ J.subtype_injective).mp he)
  have hm : ⁅E,J⁆ = E := by
    have hh := congrArg (map J.subtype) (ExceptionalRestrictions.short_commutator h.2.1)
    simpa only [map_commutator,← MonoidHom.range_eq_map,range_subtype] using hh
  exact Triality.Standard.BinaryLocalSections.no_moved_elementary e S J E hp hns hnorm
    (map_subtype_le _) hE hm

/-- All genuine binary triality parameters are excluded. -/
theorem not_triality (S : Sylow 2 G) (J : Subgroup G)
    (hl : J ∈ localCComponents S) (hp : J ≠ ⊤)
    {n : ℕ} (h : IsL2EvenBlock J n) (hc : pCore 2 J = blockU J) (hz : center J = ⊥)
    {f : ℕ} (hf : 1 ≤ f) : ¬ Triality.Standard.IsTrialityGroupAt (2^f) G := by
  by_cases he : f = 1
  · subst f
    exact not_triality_binary S J hl hp h
  · exact not_triality_nonbinary S J hl h hc hz (by omega)

/-- The full rank-two list now recognizes the original field, without exceptional callbacks. -/
theorem recognize (S : Sylow 2 G) (J : Subgroup G)
    (ht : (⊤ : Subgroup G).IsCComponent)
    (hl : J ∈ localCComponents S) (hp : J ≠ ⊤)
    {n : ℕ} (h : IsL2EvenBlock J n) (hc : pCore 2 J = blockU J) (hz : center J = ⊥)
    (ho : Odd n)
    (hr : Chapter1.Section02.LocalModels.RankTwoTheoremC (⊤ : Subgroup G)) :
    ClassicalGroup.IsPSL G 3 (2^n) := by
  rcases rank_two_alternatives S J hl hp h hc hz ho hr with ha | ⟨f,hf,htw⟩ | ⟨m,hm,he⟩
  · exact ha
  · exact (not_triality S J hl hp h hc hz hf htw).elim
  · exact (not_ree S J ht hl hp h hc hz hm he).elim

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection.NaturalRankTwo

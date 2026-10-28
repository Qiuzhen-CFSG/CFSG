module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.SplitOrRee
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Triality
public import Theory.SpecificGroups.Triality.BinaryLocalSections
public import Theory.SpecificGroups.Triality.SylowComponentUnique

/-!
# Both triality fields in relative-component embeddings

Pass the original full-Sylow local component through the containing
component's actual two-core quotient. Properness survives that map.
For nonbinary triality, full-Sylow overgroup placement puts the smaller
component in a root parabolic; perfectness and rank-one rigidity identify
its local residual. The two residual quotients are PSL₂(q) and PSL₂(q³).
Their two-adic orders determine the original field exactly.

At q = 2, the central parabolic is solvable. The marked arm-quotient
calculation instead supplies PSL₂(8), so this endpoint is retained in the
cube-field row. No nontrivial-core or nonbinary-carrier premise is added.
The applications preserve both flag normalizers and arbitrary nontrivial
U ≤ V₁ with its original Sylow-normalizer condition.

The preceding flag quotient and pointwise action come from
qt-d-1222-natural-flag-cartan, with final discharge in
qt-d-1222-natural-local-geometry. Refinement.Triality applies this field
matching to the literal Cartan sieve. The relative-components owner
retains the remaining carriers, second-component equality and triangle.
Source: Aschbacher--Smith A.3.12(2) and 11.1.1, printed pp.47--48,761,
combined manuscript of 1 March 2004; the imported triality root geometry
uses the genuine graph-field D₄ carrier and GLS3 §§2.3--2.6.
-/

open Subgroup Theory.GroupTheory
open CFSG.Quasithin CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.ChapterA.Section03
open CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding
public noncomputable section
variable {G : Type*} [Group G] [Finite G]
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics

private theorem triality_perfect_le_local (P : Parameters) (a : Node)
    (B : Subgroup (Carrier P)) [Group.IsPerfect B] (hp : P.prime = 2)
    (hB : B ≤ parabolic P a) : B ≤ localFactor P a := by
  let Y := B.subgroupOf (parabolic P a)
  let : Group.IsPerfect Y := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hB).symm.toMonoidHom) (subgroupOfEquivOfLe hB).symm.surjective
  let : IsCyclic (parabolic P a ⧸ (localFactor P a).subgroupOf (parabolic P a)) :=
    parabolic_quotient_isCyclic P hp a
  let : CommGroup (parabolic P a ⧸ (localFactor P a).subgroupOf (parabolic P a)) :=
    IsCyclic.commGroup
  have h := le_of_isPerfect_of_solvable_quotient Y
    ((localFactor P a).subgroupOf (parabolic P a))
  intro x hx
  exact h (show (⟨x,hB hx⟩ : parabolic P a) ∈ Y from hx)

private theorem triality_local_placement {m : ℕ} (hm : 1 < m)
    (S : Sylow 2 (BinaryCarrier m (by omega))) (B : Subgroup (BinaryCarrier m (by omega)))
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤)
    (htop : (⊤ : Subgroup (BinaryCarrier m (by omega))).IsCComponent) :
    ∃ (g : BinaryCarrier m (by omega)) (a : Node),
      B.map (MulAut.conj g).toMonoidHom = localFactor (binaryParameters m (by omega)) a := by
  let P := binaryParameters m (by omega : 0 < m)
  have hq : 2 < P.q := by
    change 2 < 2 ^ m
    exact (by norm_num : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) hm
  have hjoin : B ⊔ (S : Subgroup (Carrier P)) ≠ ⊤ := by
    intro he
    change (B.subgroupOf (B ⊔ (S : Subgroup (Carrier P)))).IsCComponent at hB
    rw [he] at hB
    exact hproper (le_antisymm le_top (subgroupOf_eq_top.mp (htop.eq_top_of_isCComponent hB)))
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Carrier P) S (unipotentSylow P rfl)
  let a := MulAut.conj g
  let S' := S.mapSurjective (f := a.toMonoidHom) a.surjective
  let B' := B.map a.toMonoidHom
  have hS : (S' : Subgroup (Carrier P)) = unipotent P := congrArg Sylow.toSubgroup hg
  let : Group.IsSolvable a.toMonoidHom.ker := by
    rw [a.toMonoidHom.ker_eq_bot_iff.mpr a.injective]
    infer_instance
  have hl : B' ∈ localCComponents S' := localCComponents_map_of_solvable_ker hB a.toMonoidHom
  let := hl.perfect
  let : Group.IsPerfect B' := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show B' ≤ B' ⊔ (S' : Subgroup (Carrier P)) from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe le_sup_left).surjective
  have hp : (B ⊔ (S : Subgroup (Carrier P))).map a.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hjoin
    apply map_injective (f := a.toMonoidHom) a.injective
    rw [ht,map_top_of_surjective _ a.surjective]
  have hU : unipotent P ≤ (B ⊔ (S : Subgroup (Carrier P))).map a.toMonoidHom := by
    rw [← hS]
    exact map_mono (show (S : Subgroup (Carrier P)) ≤ B ⊔ (S : Subgroup (Carrier P)) from le_sup_right)
  obtain ⟨b,hb⟩ := OddSupplement.le_parabolic m (by omega) _ hU hp
  have hBP : B' ≤ parabolic P b := (map_mono le_sup_left).trans hb
  have hSP : (S' : Subgroup (Carrier P)) ≤ parabolic P b := (map_mono le_sup_right).trans hb
  have hBK : B' ≤ localFactor P b := triality_perfect_le_local P b B' rfl hBP
  have hSK := sylow_le_localFactor P b S' hSP
  let := localFactor_isPerfect P rfl hq b
  refine ⟨g,b,?_⟩
  cases b with
  | arms =>
    apply SourceEmbeddings.FiveLocalFF.local_eq_of_sl2_core_quotient (localFactor P .arms) ?_
      ((localFactorArmsQuotientEquivPSL2 P rfl).trans (Theory.PSL2.sl2QuotientEquiv _).symm)
      S' B' hl hBK hSK
    rw [card_extensionField]
    exact lt_of_lt_of_le hq (Nat.le_pow (by decide))
  | central =>
    apply SourceEmbeddings.FiveLocalFF.local_eq_of_sl2_core_quotient (localFactor P .central) ?_
      ((localFactorCentralQuotientEquivPSL2 P rfl).trans (Theory.PSL2.sl2QuotientEquiv _).symm)
      S' B' hl hBK hSK
    simpa only [card_baseField] using hq

private theorem triality_parameter {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (S : Sylow 2 (BinaryCarrier m hm)) (B : Subgroup (BinaryCarrier m hm))
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤)
    (hsmall : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2 ^ n))
    (htop : (⊤ : Subgroup (BinaryCarrier m hm)).IsCComponent) : n = m ∨ n = 3 * m := by
  by_cases hm1 : m = 1
  · subst m
    let := hB.perfect
    let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ (S : Subgroup _) from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).surjective
    let := htop.perfect
    let : Group.IsPerfect (BinaryCarrier 1 hm) := Group.IsPerfect.ofSurjective
      (f := (topEquiv (G := BinaryCarrier 1 hm)).toMonoidHom) topEquiv.surjective
    have hnorm : (S : Subgroup (BinaryCarrier 1 hm)) ≤ normalizer (B : Set (BinaryCarrier 1 hm)) :=
      SylowOvergroupComponentUnique.normalizes_local_component S (K := ⊤) hB .top le_top
        (by rw [normalizer_eq_top]; exact le_top)
        (.of_equiv topEquiv (binary_sylow_overgroup_component_unique 1 hm))
    have hns : ¬ Group.IsSolvable B := by
      intro hs
      let := hs
      exact hB.not_isSolvable (Group.isSolvable_of_isSolvable_injective
        (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ (S : Subgroup _) from le_sup_left)).toMonoidHom)
        (subgroupOfEquivOfLe le_sup_left).injective)
    obtain ⟨_,_,_,e,_⟩ := BinaryLocalSections.marked_arm_quotient (MulEquiv.refl _) S B hproper hns hnorm
    have he : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2 ^ (3 * 1)) :=
      ⟨ExtensionField (binaryParameters 1 hm),inferInstance,inferInstance,
        (by rw [card_extensionField]; rfl),⟨e.trans (localFactorArmsQuotientEquivPSL2 _ rfl)⟩⟩
    exact .inr ((binary_two_valuation hn hsmall).symm.trans (binary_two_valuation (by decide) he))
  · obtain ⟨g,a,hg⟩ := triality_local_placement (by omega : 1 < m) S B hB hproper htop
    let e := ((MulAut.conj g).subgroupMap B).trans (MulEquiv.subgroupCongr hg)
    let eq := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
    cases a with
    | arms =>
      have he : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2 ^ (3 * m)) :=
        ⟨ExtensionField (binaryParameters m hm),inferInstance,inferInstance,
          (by rw [card_extensionField]; change (2 ^ m) ^ 3 = 2 ^ (3 * m); rw [← pow_mul,Nat.mul_comm]),
          ⟨eq.trans (localFactorArmsQuotientEquivPSL2 _ rfl)⟩⟩
      exact .inr ((binary_two_valuation hn hsmall).symm.trans (binary_two_valuation (by omega) he))
    | central =>
      have he : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2 ^ m) :=
        ⟨GaloisField 2 m,inferInstance,inferInstance,GaloisField.card 2 m (by omega),
          ⟨eq.trans (localFactorCentralQuotientEquivPSL2 _ rfl)⟩⟩
      exact .inl ((binary_two_valuation hn hsmall).symm.trans (binary_two_valuation hm he))

/-- A proper triality containing component has the same field or the exact
cubic subfield. This includes the binary carrier ³D₄(2). -/
theorem proper_triality_parameters
    (P : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents P) (hK : K.IsCComponent) (hBK : B < K)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hsmall : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2 ^ n))
    (hmodel : IsTrialityGroupAt (2 ^ m) (K ⧸ pCore 2 K)) : n = m ∨ n = 3 * m := by
  obtain ⟨e⟩ := (isTrialityGroupAt_binary_iff _ m hm).mp hmodel
  obtain ⟨R,C,hl,hp,hs,ht⟩ := model_local_image P hB hK hBK hsmall e
  exact triality_parameter hn hm R C hl hp hs ht

/-- The parameter relation in the original relative group, with the same
full Sylow and literal core quotients. -/
theorem relative_triality_parameters
    {H B K P : Subgroup G}
    (hP : Chapter1.IsSylowIn 2 P H)
    (hB : B ∈ Chapter1.L G P) (hK : Source.ComponentIn H K) (hBK : B < K)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hsmall : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2 ^ n))
    (hmodel : IsTrialityGroupAt (2 ^ m) (K ⧸ pCore 2 K)) : n = m ∨ n = 3 * m := by
  obtain ⟨P₀,hP₀⟩ := hP
  have hPH : P ≤ H := hP₀ ▸ map_subtype_le (P₀ : Subgroup H)
  have hBH : B ≤ H := hBK.le.trans hK.1
  have hlocal : B.subgroupOf H ∈ localCComponents P₀ := by
    have hh := (Chapter1.mem_LIn_iff_subgroupOf hPH hBH).mp ⟨hBH,hB⟩
    have he : P.subgroupOf H = (P₀ : Subgroup H) := by
      rw [← hP₀]
      exact comap_map_eq_self_of_injective H.subtype_injective _
    rw [he] at hh
    exact hh.1
  have hlt : B.subgroupOf H < K.subgroupOf H := by
    refine lt_of_le_of_ne (comap_mono hBK.le) ?_
    intro hh
    apply hBK.ne
    simpa only [map_subgroupOf_eq_of_le hBH,map_subgroupOf_eq_of_le hK.1] using
      congrArg (map H.subtype) hh
  let b := subgroupOfEquivOfLe hBH
  let k := subgroupOfEquivOfLe hK.1
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  let kq := QuotientGroup.congr _ _ k (pCore_map_iso 2 k)
  obtain ⟨e⟩ := (isTrialityGroupAt_binary_iff _ m hm).mp hmodel
  have ht : IsTrialityGroupAt (2 ^ m) (K.subgroupOf H ⧸ pCore 2 (K.subgroupOf H)) :=
    (isTrialityGroupAt_binary_iff _ m hm).mpr ⟨kq.trans e⟩
  exact proper_triality_parameters P₀ hlocal hK.2 hlt hn hm (hsmall.of_mulEquiv bq) ht

/-- Both triality branches of 11.1.1, including the cube-field row at q = 8.
The carrier premise is an actual equivalence to genuine graph-field D₄. -/
theorem relative_component_alternative_of_triality
    {H B K P : Subgroup G}
    (hP : Chapter1.IsSylowIn 2 P H)
    (hB : B ∈ Chapter1.L G P) (hK : Source.ComponentIn H K) (hBK : B ≤ K)
    {n : ℕ} (hn : 1 < n)
    (hsmall : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2 ^ n))
    (hmodel : _root_.Triality.IsQTKETrialityModel (K ⧸ pCore 2 K)) :
    ComponentAlternative B K n := by
  by_cases he : B = K
  · exact .equal he
  obtain ⟨m,hm,hmodel⟩ := (_root_.Triality.isQTKETrialityModel_iff_fieldOrder _).mp hmodel
  rcases relative_triality_parameters hP hB hK (lt_of_le_of_ne hBK he) (by omega) hm
    hsmall hmodel with hnm | hnm
  · exact .lie (.triality (hnm.symm ▸ hmodel))
  · exact .lie (.trialityCube m (by omega) hnm hmodel)

open CFSG.Quasithin.Chapter12.Section02
variable {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- Apply the triality field comparison to each original flag normalizer. -/
theorem flag_component_alternative_of_triality (i : Fin 2)
    (hm : ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2 ^ S.field.degree))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi i.castSucc : Set G)) K)
    (hLK : f.Li i ≤ K)
    (hmodel : _root_.Triality.IsQTKETrialityModel (K ⧸ pCore 2 K)) :
    ComponentAlternative (f.Li i) K S.field.degree := by
  have hT : (T : Subgroup G) ≤ normalizer (f.Vi i.castSucc : Set G) := f.invariant i.castSucc
  have hs : Chapter1.IsSylowIn 2 (T : Subgroup G)
      (normalizer (f.Vi i.castSucc : Set G)) :=
    ⟨T.subtype hT,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hT]⟩
  exact relative_component_alternative_of_triality hs (flag_mem_local_of_model D S f i hm)
    hK hLK S.nonbinary hm hmodel

/-- The same two source branches for arbitrary nontrivial U ≤ V₁, retaining
its original Sylow-normalizer hypothesis and full point preimage. -/
theorem subspace_component_alternative_of_triality
    (U : Subgroup G) (hU : U ≠ ⊥) (hUV : U ≤ f.Vi 0)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (U : Set G))
      (normalizer (U : Set G)))
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (U : Set G)) K)
    (hLK : f.Li 0 ≤ K)
    (hmodel : _root_.Triality.IsQTKETrialityModel (K ⧸ pCore 2 K)) :
    ComponentAlternative (f.Li 0) K S.field.degree := by
  let : IsElementaryAbelian 2 (f.Vi 0) :=
    D.centralQuotientPreimage_elementary (c.binarySubspace (f.space 0))
  have htwo : IsPGroup 2 U := (IsElementaryAbelian.isPGroup 2 (f.Vi 0)).to_le hUV
  have hUL : f.Li 0 ≤ normalizer (U : Set G) :=
    (hfix.trans (centralizer_le hUV)).trans (Subgroup.centralizer_le_normalizer _)
  let P := (T : Subgroup G) ⊓ normalizer (U : Set G)
  have hUP : U ≤ P := le_inf
    (hUV.trans ((D.centralQuotientPreimage_le _).trans D.le_sylow)) U.le_normalizer
  have hcore : U ≤ (f.Li 0 ⊔ P).pCoreIn 2 :=
    le_pCoreIn_of_normalizes htwo (hUP.trans le_sup_right) (sup_le hUL inf_le_right)
  have hlocal := flag_mem_local_of_model D S f 0 hm
  have hlocalP : f.Li 0 ∈ Chapter1.L G P :=
    ⟨hlocal.1.subgroupOf_of_le le_sup_left (sup_le_sup_left inf_le_left _),
      hSyl.restrict le_sup_right (sup_le hUL inf_le_right),
      fun he => hU (bot_unique (he ▸ hcore))⟩
  exact relative_component_alternative_of_triality hSyl hlocalP hK hLK S.nonbinary hm hmodel

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding

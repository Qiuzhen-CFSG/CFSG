module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryNormalizer
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryCore
public import Theory.SpecificGroups.SL2.LineBorelResidual
public import CFSG.Quasithin.ChapterG.Section02.CentralClosureConsequences

/-!
# The natural central line satisfies G.2.1

The full stabilizer of a field line acts irreducibly on the natural plane
modulo that line, even among additive subgroups. Its two-perfect Borel
image lifts through the literal residual O²(N_L(Z_S)). This proves the
invariant-subgroup interval required by G.2.1. The original Hypothesis
6.1.1 supplies relative Sylow subgroups and characteristic two.

The natural line spans V_L under L. Applying G.2.2 and the established
normalizer-closure identity gives Φ(U) ≤ Z_S, U ≤ O₂(N_G(Z_S)), and
[U,O₂(N_G(Z_S))] ≤ Z_S. These are the earlier inputs to G.2.3 in 6.1.21.
The initial natural action and escaping nonabelianness still belong to
qt-d-1222-rankone-recognition-natural; neither is asserted here.

Source: Aschbacher–Smith, 6.1.20–21, printed pp.675–676, and G.2.1–2,
printed p.332.
-/

public noncomputable section

open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups Pointwise
open Matrix.SpecialLinearGroup
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open ConjugateFixedSpaces

private theorem standard_interval {F : Type*} [Field F]
    (A : AddSubgroup (Fin 2 → F)) (hline : ∀ t : F, ![t, 0] ∈ A)
    (hinv : ∀ g ∈ rankOneBorel F, ∀ v ∈ A, g.val *ᵥ v ∈ A) :
    (∀ v ∈ A, v 1 = 0) ∨ A = ⊤ := by
  by_cases h : ∀ v ∈ A, v 1 = 0
  · exact Or.inl h
  right
  push Not at h
  obtain ⟨v, hv, hv1⟩ := h
  apply top_unique
  intro w _
  by_cases hw : w 1 = 0
  · have he : w = ![w 0, 0] := by ext i; fin_cases i <;> simp [hw]
    rw [he]
    exact hline _
  let a := v 1 / w 1
  have ha : a ≠ 0 := div_ne_zero hv1 hw
  have hz := hinv (diag2 a ha) (diag_mem_rankOneBorel a ha) v hv
  have he : (diag2 a ha).val *ᵥ v + ![w 0 - a * v 0, 0] = w := by
    ext i
    fin_cases i <;> simp [diag2_coe', dotProduct, Fin.sum_univ_two, a, hv1]
  exact he ▸ A.add_mem hz (hline _)

private theorem line_interval {F : Type*} [Field F] [Finite F]
    (P : Submodule F (Fin 2 → F)) (hP : Module.finrank F P = 1)
    (A : AddSubgroup (Fin 2 → F)) (hPA : P.toAddSubgroup ≤ A)
    (hinv : ∀ g ∈ MulAction.stabilizer SL(2,F) (P : Set (Fin 2 → F)),
      ∀ v ∈ A, g.val *ᵥ v ∈ A) : A = P.toAddSubgroup ∨ A = ⊤ := by
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Submodule.isAtom_iff_finrank_eq_one.mpr hP).ne_bot
  obtain ⟨a, ha⟩ := Matrix.SL2.exists_mulVec_eq F (![1,0] : Fin 2 → F) z
    (by intro he; have := congrFun he 0; simp at this) hz0
  let e := Matrix.SpecialLinearGroup.toLin' a
  have he (t : F) : e ![t,0] = t • z := by
    have ht : (![t,0] : Fin 2 → F) = t • ![1,0] := by ext i; fin_cases i <;> simp
    rw [ht, e.map_smul]
    exact congrArg (t • ·) ha
  have hmem (v : Fin 2 → F) : e v ∈ P ↔ v 1 = 0 := by
    rw [eq_span_singleton_of_mem_of_finrank_eq_one hP hz hz0, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨t, ht⟩
      have hv : ![t,0] = v := e.injective ((he t).trans ht)
      simpa using congrFun hv.symm 1
    · intro hv
      refine ⟨v 0, ?_⟩
      rw [← he]
      congr 1
      ext i; fin_cases i <;> simp [hv]
  let A' := A.comap e.toAddEquiv.toAddMonoidHom
  have hline (t : F) : ![t,0] ∈ A' := hPA ((hmem _).mpr (by simp))
  have hstable (b : SL(2,F)) (hb : b ∈ rankOneBorel F) :
      a * b * a⁻¹ ∈ MulAction.stabilizer SL(2,F) (P : Set (Fin 2 → F)) := by
    rw [MulAction.mem_stabilizer_set' (Set.toFinite _)]
    intro v hv
    have hv0 : (e.symm v) 1 = 0 := (hmem _).mp (by simpa using hv)
    have hb0 := (mem_rankOneBorel_iff b).mp hb
    have hprod : (a * b * a⁻¹).val *ᵥ v = e (b.val *ᵥ e.symm v) := by
      change ((a * b * a⁻¹) • v) = a • (b • (a⁻¹ • v))
      simp only [mul_smul]
    change (a * b * a⁻¹).val *ᵥ v ∈ P
    rw [hprod, hmem]
    simp [mulVec, dotProduct, Fin.sum_univ_two, hb0, hv0]
  have hinv' : ∀ b ∈ rankOneBorel F, ∀ v ∈ A', b.val *ᵥ v ∈ A' := by
    intro b hb v hv
    have hh := hinv (a * b * a⁻¹) (hstable b hb) (e v) hv
    have heq : (a * b * a⁻¹).val *ᵥ e v = e (b.val *ᵥ v) := by
      change (a * b * a⁻¹) • (a • v) = a • (b • v)
      simp only [mul_smul, inv_smul_smul]
    change e (b.val *ᵥ v) ∈ A
    exact heq ▸ hh
  rcases standard_interval A' hline hinv' with hzero | hfull
  · left
    apply le_antisymm _ hPA
    intro v hv
    have hh : e.symm v ∈ A' := by change e (e.symm v) ∈ A; simpa using hv
    have hp := (hmem _).mpr (hzero _ hh)
    simpa using hp
  · right
    apply top_unique
    intro v _
    have hh : e.symm v ∈ A' := hfull ▸ AddSubgroup.mem_top _
    change e (e.symm v) ∈ A at hh
    simpa using hh


variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}

/-- The actual two-residual of the central-line normalizer is irreducible
on the subgroup interval from the line to the natural layer. -/
theorem natural_escape_invariant_interval
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n) :
    ZS (T : Subgroup G) L V ≠ layer L V ∧
      ∀ A : Subgroup G, ZS (T : Subgroup G) L V ≤ A → A ≤ layer L V →
        (naturalEscapeSetup (T : Subgroup G) L V).L₁ ≤ normalizer (A : Set G) →
        A = ZS (T : Subgroup G) L V ∨ A = layer L V := by
  have hcard := (hnatural.sylow_intersection_geometry T h.sylow_normalizes_L).1
  change Nat.card (ZS (T : Subgroup G) L V) = 2 ^ n at hcard
  constructor
  · intro he
    rw [he, hnatural.card] at hcard
    have he := Nat.pow_right_injective (by decide : 1 < 2) hcard
    have := h.n_gt_one
    omega
  intro A hZA hAB hKA
  obtain ⟨F, _, _, _, hF, e, f, hf⟩ := hnatural
  let B := layer L V
  let Z := ZS (T : Subgroup G) L V
  let P := sylowSpace (T : Subgroup G) e
  let q₀ : L →* SL(2,F) := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq₀ : Function.Surjective q₀ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  change ∀ (l : L) (v : B), (f.symm (Multiplicative.ofAdd
    ((q₀ l).val *ᵥ (f v).toAdd)) : G) = (l : G) * (v : G) * (l : G)⁻¹ at hf
  have hP : P.toAddSubgroup = coordinateSpace f Z :=
    AddSubgroup.ext (mem_sylowSpace_iff (T : Subgroup G) e f hf)
  have hc : Nat.card P = Nat.card F := by
    change Nat.card P.toAddSubgroup = Nat.card F
    rw [hP, coordinateSpace_card f (show Z ≤ B from inf_le_left), hF]
    exact hcard
  have hd : Module.finrank F P = 1 := by
    apply Nat.pow_right_injective (Finite.one_lt_card (α := F))
    change Nat.card F ^ Module.finrank F P = Nat.card F ^ 1
    rw [← Module.natCard_eq_pow_finrank, hc, pow_one]
  let J := MulAction.stabilizer SL(2,F) (P : Set (Fin 2 → F))
  have hstab (l : L) : q₀ l ∈ J ↔ (l : G) ∈ normalizer (Z : Set G) := by
    rw [MulAction.mem_stabilizer_set' (Set.toFinite _)]
    constructor
    · intro hl
      apply mem_normalizer_fintype
      intro z hz
      let v : B := ⟨z, (show Z ≤ B from inf_le_left) hz⟩
      have hv : (f v).toAdd ∈ P := by
        change (f v).toAdd ∈ P.toAddSubgroup
        rw [hP]
        simpa [v] using hz
      have hh := hl hv
      change (q₀ l).val *ᵥ (f v).toAdd ∈ P.toAddSubgroup at hh
      rw [hP] at hh
      change (f.symm (Multiplicative.ofAdd ((q₀ l).val *ᵥ (f v).toAdd)) : G) ∈ Z at hh
      rwa [hf l v] at hh
    · intro hl v hv
      have hz : (f.symm (Multiplicative.ofAdd v) : G) ∈ Z := by
        exact (show v ∈ coordinateSpace f Z from hP ▸ hv)
      have hh := (mem_normalizer_iff.mp hl _).mp hz
      rw [← hf l (f.symm (Multiplicative.ofAdd v)), f.apply_symm_apply] at hh
      change (q₀ l).val *ᵥ v ∈ P.toAddSubgroup
      rw [hP]
      exact hh
  let K := L ⊓ normalizer (Z : Set G)
  let q : K →* J := (q₀.comp (inclusion (show K ≤ L from inf_le_left))).codRestrict J
    (fun k => (hstab ⟨k, k.property.1⟩).mpr k.property.2)
  have hq : Function.Surjective q := by
    intro s
    obtain ⟨l, hl⟩ := hq₀ s
    exact ⟨⟨l, l.property, (hstab l).mp (hl ▸ s.property)⟩, Subtype.ext hl⟩
  have hperfect : IsPPerfect 2 J := lineStabilizer_isPPerfect P hd (by
    rw [hF]
    change 2 ^ 2 ≤ 2 ^ n
    exact Nat.pow_le_pow_right (by decide : 0 < 2) h.n_gt_one)
  have hres : (pResidual 2 K).map q = ⊤ := by
    rw [map_pResidual_of_surjective 2 q hq, (pResidual_eq_top_iff 2 J).mpr hperfect]
  have hPA : P.toAddSubgroup ≤ coordinateSpace f A := by
    rw [hP]
    exact fun v hv => hZA hv
  have hinv : ∀ s ∈ J, ∀ v ∈ coordinateSpace f A, s.val *ᵥ v ∈ coordinateSpace f A := by
    intro s hs v hv
    have hs' : (⟨s,hs⟩ : J) ∈ (pResidual 2 K).map q := hres ▸ mem_top _
    obtain ⟨k, hk, hks⟩ := hs'
    have hkactor : (k : G) ∈ (naturalEscapeSetup (T : Subgroup G) L V).L₁ :=
      mem_map_of_mem K.subtype hk
    have hconj := (mem_normalizer_iff.mp (hKA hkactor) _).mp hv
    rw [← hf ⟨k,k.property.1⟩ (f.symm (Multiplicative.ofAdd v)), f.apply_symm_apply] at hconj
    have he : q₀ ⟨k,k.property.1⟩ = s := congrArg Subtype.val hks
    change (f.symm (Multiplicative.ofAdd ((q₀ ⟨k,k.property.1⟩).val *ᵥ v)) : G) ∈ A at hconj
    rw [he] at hconj
    exact hconj
  rcases line_interval P hd (coordinateSpace f A) hPA hinv with hzero | hfull
  · left
    apply le_antisymm _ hZA
    intro x hx
    have hh : (f ⟨x,hAB hx⟩).toAdd ∈ coordinateSpace f A := by simpa using hx
    rw [hzero, hP] at hh
    simpa using hh
  · right
    apply le_antisymm hAB
    intro x hx
    have hh : (f ⟨x,hx⟩).toAdd ∈ coordinateSpace f A := hfull ▸ AddSubgroup.mem_top _
    simpa using hh

/-- Every genuine Hypothesis 6.1.1 supplies the relative Sylow, residual,
normalization and characteristic-two assumptions in G.2.1. -/
theorem natural_escape_G2_base (h : Hypothesis611 κ T L M V n) :
    (naturalEscapeSetup (T : Subgroup G) L V).BaseHypothesis := by
  refine {
    elementary := h.layer_elementary
    point_ne_bot := h.ZS_ne_bot
    point_le := inf_le_left
    residual := (pResidual_eq_top_iff 2 L).mpr h.local_mem.2.2.1
    V_le_T := h.layer_le_T
    T_normalizes_point := h.sylow_normalizes_ZS
    T_normalizes_V := h.sylow_normalizes_layer
    T_normalizes_L := h.sylow_normalizes_L
    sylow_LT := h.local_mem.1.prop.2.1
    H_le := le_rfl
    local_le := sup_le ((map_subtype_le _).trans inf_le_right) h.sylow_normalizes_ZS
    sylow_H := ?_
    characteristic_two := h.source_lemma_6_1_9_3 }
  refine ⟨T.subtype h.sylow_normalizes_ZS, ?_⟩
  exact map_subgroupOf_eq_of_le h.sylow_normalizes_ZS

/-- The actual natural action discharges the remaining G.2.1 module clauses. -/
theorem natural_escape_G2_hypothesis
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n) :
    (naturalEscapeSetup (T : Subgroup G) L V).Hypothesis := by
  obtain ⟨hne, hirr⟩ := natural_escape_invariant_interval h hnatural
  refine { natural_escape_G2_base h with
    local_normalizes_V := ?_
    quotient_nonzero := hne
    irreducible := fun A hZA hAB hn => hirr A hZA hAB (le_sup_left.trans hn) }
  exact sup_le ((map_subtype_le _).trans (inf_le_left.trans
    (normalizer_commutator_ge_right V L))) h.sylow_normalizes_layer

/-- The source point generates the whole original natural module under L. -/
theorem natural_escape_point_span
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n) :
    (naturalEscapeSetup (T : Subgroup G) L V).VL = layer L V := by
  have hle : conjugateSpanBy (ZS (T : Subgroup G) L V) L ≤ layer L V :=
    conjugateSpanBy_le inf_le_left (normalizer_commutator_ge_right V L)
  exact (hnatural.invariant_subgroup _ hle (le_normalizer_conjugateSpanBy _ _)).resolve_left
    (fun he => h.ZS_ne_bot (bot_unique ((le_conjugateSpanBy _ _).trans_eq he)))

/-- The full normalizer closure has the G.2.2 Frattini bound and is central
modulo Z_S under its full normalizer's two-core, on the literal escaping U. -/
theorem natural_escape_frattini_and_normalizer_core
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hE : ChapterE.Section06.HypothesisE61 κ T M (layer L V))
    (hNS : normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L V : Set G) : Subgroup G) : Set G) ≤ M) :
    (frattini (Escape.U (T : Subgroup G) L V)).map (Escape.U (T : Subgroup G) L V).subtype ≤
        ZS (T : Subgroup G) L V ∧
      Escape.U (T : Subgroup G) L V ≤ (Escape.H (T : Subgroup G) L V).pCoreIn 2 ∧
      ⁅Escape.U (T : Subgroup G) L V, (Escape.H (T : Subgroup G) L V).pCoreIn 2⁆ ≤
        ZS (T : Subgroup G) L V := by
  have d := natural_escape_G2_hypothesis h hnatural
  have hU : (naturalEscapeSetup (T : Subgroup G) L V).U = Escape.U (T : Subgroup G) L V :=
    natural_escape_normalizer_span h hE hNS
  have hphi := d.frattini_U_le_point
  have hcore := d.U_le_core
  have hcomm := d.commutator_U_core_le_point
  rw [hU] at hphi hcore hcomm
  exact ⟨hphi, hcore, hcomm⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

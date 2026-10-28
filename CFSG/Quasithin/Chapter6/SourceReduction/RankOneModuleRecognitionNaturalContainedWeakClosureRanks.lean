module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFusionModelRecognition
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedWeakClosure
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateCentralizers

/-!
# The exact local minimum for a natural SL₂ layer

In natural coordinates every automizer is semilinear. A nonidentity linear
actor has an F-fixed space of dimension at most one; a nontrivial field
twist has at most |F| fixed vectors by the two-copy injection. Thus every
involution has binary fixed codimension at least n. A Sylow subgroup of
the actual normal SL₂ image attains n, giving the exact local minimum.

The quotient and vector markings are the original natural-module ones.
This proves the local equality in source 6.1.10(2) and equality of the
local centralizers for subgroups of corank less than n. E.6.12 then reduces
the global-r lower bound to excluding r=1; the companion RanksGlobal module
discharges that last step by hyperplane transitivity.
Source: Aschbacher--Smith, printed p.670 (PDF p.687).
-/

public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition

private theorem semilinear_fixed_card_le
    {F H : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F] [Group H]
    (ρ : Representation (ZMod 2) H (Fin 2 → F)) (hρ : Function.Injective ρ)
    {a : H} (ha : a ≠ 1)
    (hs : ∃ σ : F ≃+* F, ∀ c v, ρ a (c • v) = σ c • ρ a v) :
    Nat.card (fixedSpace ρ (zpowers a)) ≤ Nat.card F := by
  obtain ⟨σ,hσ⟩ := hs
  by_cases hid : σ = 1
  · have hlin (c : F) (v : Fin 2 → F) : ρ a (c • v) = c • ρ a v := by
      rw [hσ,hid]
      rfl
    let X : Submodule F (Fin 2 → F) := {
      carrier := {v | ρ a v = v}
      zero_mem' := map_zero (ρ a)
      add_mem' := by
        intro v w hv hw
        exact (map_add (ρ a) v w).trans (congrArg₂ (· + ·) hv hw)
      smul_mem' := by
        intro c v hv
        exact (hlin c v).trans (congrArg (c • ·) hv) }
    have hne : X ≠ ⊤ := by
      intro hX
      apply ha
      apply hρ
      rw [map_one]
      apply LinearMap.ext
      intro v
      exact (show v ∈ X from hX ▸ Submodule.mem_top)
    have hdim : Module.finrank F X ≤ 1 := by
      have hh := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hne)
      simp only [Module.finrank_pi,Fintype.card_fin,finrank_top] at hh
      omega
    calc
      Nat.card (fixedSpace ρ (zpowers a)) ≤ Nat.card X :=
        Nat.card_le_card_of_injective
          (fun v : fixedSpace ρ (zpowers a) => (⟨v,v.property ⟨a,mem_zpowers a⟩⟩ : X))
          (fun _ _ hh => Subtype.ext (congrArg (fun z : X => (z : Fin 2 → F)) hh))
      _ = Nat.card F ^ Module.finrank F X := Module.natCard_eq_pow_finrank
      _ ≤ Nat.card F ^ 1 := Nat.pow_le_pow_right Nat.card_pos hdim
      _ = Nat.card F := pow_one _
  · exact Representation.SL2NaturalOffenders.fixedSpace_card_le_of_nontrivial_coefficient
      ρ (zpowers a) ⟨a,mem_zpowers a⟩ σ hid hσ

private theorem semilinear_fixedCodim_ge
    {F H : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F] [Group H]
    (ρ : Representation (ZMod 2) H (Fin 2 → F)) (hρ : Function.Injective ρ)
    {a : H} (ha : a ≠ 1)
    (hs : ∃ σ : F ≃+* F, ∀ c v, ρ a (c • v) = σ c • ρ a v) :
    Module.finrank (ZMod 2) F ≤ fixedCodim ρ (zpowers a) := by
  have hc := semilinear_fixed_card_le ρ hρ ha hs
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ (zpowers a)),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F),Nat.card_zmod] at hc
  have hd := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
  have hh := fixedCodim_add_finrank ρ (zpowers a)
  simp only [Module.finrank_pi_fintype,Fin.sum_univ_two] at hh
  omega

variable {G : Type*} [Group G] [Finite G] {L B : Subgroup G} [IsElementaryAbelian 2 B]

/-- The local parameter is the actual field degree of a normal natural SL₂ layer. -/
theorem natural_localM_eq {n : ℕ}
    (hnatural : IsNaturalModule L B n)
    (hNL : normalizer (B : Set G) ≤ normalizer (L : Set G)) :
    ChapterE.localM B = n := by
  obtain ⟨F,_,_,_,hF,e,f,hf⟩ := hnatural
  let : Algebra (ZMod 2) F := ZMod.algebra _ 2
  obtain ⟨j,E,hE⟩ := NaturalAction.marking e f hf
  let C := ChapterE.inducedAutomizer B L
  let : C.Normal := NaturalAction.induced_normal hNL
  let τ : Representation (ZMod 2) (ChapterE.Automizer B) (Fin 2 → F) :=
    E.conjRingEquiv.toMonoidHom.comp (ChapterE.automizerRepresentation B)
  have hτ : Function.Injective τ :=
    E.conjRingEquiv.injective.comp (ChapterE.automizerRepresentation_injective B)
  have hnat : ∀ (g : C) v, τ (g : ChapterE.Automizer B) v =
      Matrix.mulVec (j g).val v := by
    intro g v
    change E (ChapterE.automizerRepresentation B g (E.symm v)) = _
    rw [hE,E.apply_symm_apply]
  have hdim : Module.finrank (ZMod 2) F = n := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
    rw [Nat.card_zmod,hF] at hh
    exact (Nat.pow_right_injective (by decide : 2 ≤ 2) hh).symm
  have hcod (A : Subgroup (ChapterE.Automizer B)) :
      fixedCodim (ChapterE.automizerRepresentation B) A = fixedCodim τ A := by
    simpa only [Subgroup.map_id] using
      fixedCodim_map_equivariant (ChapterE.automizerRepresentation B) τ (MonoidHom.id _) E
        (fun a v => by
          change E (ChapterE.automizerRepresentation B a v) =
            E (ChapterE.automizerRepresentation B a (E.symm (E v)))
          rw [E.symm_apply_apply]) A
  apply le_antisymm
  · let P : Sylow 2 C := default
    have hP := Representation.SL2NaturalOffenders.Ratios.sylowImage_offender C j τ hnat P
    calc
      ChapterE.localM B ≤ fixedCodim (ChapterE.automizerRepresentation B)
          ((P : Subgroup C).map C.subtype) := ChapterE.moduleM_le_fixedCodim _ hP.1
      _ = fixedCodim τ ((P : Subgroup C).map C.subtype) := hcod _
      _ = Module.finrank (ZMod 2) F :=
        Representation.SL2NaturalOffenders.Ratios.sylowImage_fixedCodim C j τ hnat P
      _ = n := hdim
  · apply le_csInf ⟨_,Set.mem_insert _ _⟩
    rintro k (rfl | ⟨a,ha,rfl⟩)
    · have hh := E.finrank_eq
      simp only [Module.finrank_pi_fintype,Fin.sum_univ_two,hdim] at hh
      omega
    · rw [hcod,← hdim]
      exact semilinear_fixedCodim_ge τ hτ (fun he => by simp [he] at ha)
        (Representation.SL2NaturalOffenders.normalizer_semilinear C j τ hnat a)

omit [Finite G] in
/-- Every nonidentity actual automizer moves at least n binary dimensions. -/
theorem natural_automizer_fixedCodim_ge {n : ℕ}
    (hnatural : IsNaturalModule L B n)
    (hNL : normalizer (B : Set G) ≤ normalizer (L : Set G))
    {a : ChapterE.Automizer B} (ha : a ≠ 1) :
    n ≤ fixedCodim (ChapterE.automizerRepresentation B) (zpowers a) := by
  obtain ⟨F,_,_,_,hF,e,f,hf⟩ := hnatural
  let : Algebra (ZMod 2) F := ZMod.algebra _ 2
  obtain ⟨j,E,hE⟩ := NaturalAction.marking e f hf
  let C := ChapterE.inducedAutomizer B L
  let : C.Normal := NaturalAction.induced_normal hNL
  let τ : Representation (ZMod 2) (ChapterE.Automizer B) (Fin 2 → F) :=
    E.conjRingEquiv.toMonoidHom.comp (ChapterE.automizerRepresentation B)
  have hτ : Function.Injective τ :=
    E.conjRingEquiv.injective.comp (ChapterE.automizerRepresentation_injective B)
  have hnat : ∀ (g : C) v, τ (g : ChapterE.Automizer B) v =
      Matrix.mulVec (j g).val v := by
    intro g v
    change E (ChapterE.automizerRepresentation B g (E.symm v)) = _
    rw [hE,E.apply_symm_apply]
  have hdim : Module.finrank (ZMod 2) F = n := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
    rw [Nat.card_zmod,hF] at hh
    exact (Nat.pow_right_injective (by decide : 2 ≤ 2) hh).symm
  have hcod : fixedCodim (ChapterE.automizerRepresentation B) (zpowers a) =
      fixedCodim τ (zpowers a) := by
    simpa only [Subgroup.map_id] using
      fixedCodim_map_equivariant (ChapterE.automizerRepresentation B) τ (MonoidHom.id _) E
        (fun a v => by
          change E (ChapterE.automizerRepresentation B a v) =
            E (ChapterE.automizerRepresentation B a (E.symm (E v)))
          rw [E.symm_apply_apply]) (zpowers a)
  rw [hcod, ← hdim]
  exact semilinear_fixedCodim_ge τ hτ ha
    (Representation.SL2NaturalOffenders.normalizer_semilinear C j τ hnat a)

/-- Small-corank subgroups have the same local centralizer as the full layer. -/
theorem natural_local_centralizer_eq_of_corank_lt
    {κ : GroupClass} {T : Sylow 2 G} {M U : Subgroup G} {n : ℕ}
    (hnatural : IsNaturalModule L B n)
    (hNL : normalizer (B : Set G) ≤ normalizer (L : Set G))
    (hE : ChapterE.Section06.HypothesisE61 κ T M B)
    (hUB : U ≤ B) (hsmall : ChapterE.subgroupCorank B U < n) :
    M ⊓ centralizer (U : Set G) = M ⊓ centralizer (B : Set G) := by
  have hm := natural_localM_eq hnatural hNL
  have hUne : U ≠ ⊥ := ChapterE.Section06.nontrivial_of_corank_lt_localM
    (hm.symm ▸ hsmall)
  let A := M ⊓ centralizer (U : Set G)
  have hAN : A ≤ normalizer (B : Set G) := hE.localCentralizer_le_normalizer hUne hUB
  have hzero : ChapterE.inducedAutomizer B A = ⊥ := by
    apply eq_bot_iff.mpr
    intro a ha
    by_contra hn
    have hane : a ≠ 1 := by simpa only [mem_bot] using hn
    have hlo := natural_automizer_fixedCodim_ge hnatural hNL hane
    have hmid := ChapterE.fixedCodim_mono (ChapterE.automizerRepresentation B)
      (zpowers_le.mpr ha)
    have hhi : fixedCodim (ChapterE.automizerRepresentation B)
        (ChapterE.inducedAutomizer B A) ≤ ChapterE.subgroupCorank B U := by
      rw [ChapterE.fixedCodim_inducedAutomizer B A hAN]
      exact ChapterE.Section06.subgroupCorank_antitone
        (le_inf hUB (le_centralizer_iff.mpr (show A ≤ centralizer (U : Set G) from inf_le_right)))
    exact (not_lt_of_ge (hlo.trans (hmid.trans hhi))) hsmall
  exact le_antisymm (le_inf inf_le_left
    ((ChapterE.inducedAutomizer_eq_bot_iff hAN).mp hzero))
    (inf_le_inf_left M (centralizer_le hUB))

/-- Once hyperplanes are controlled, the natural local estimate globalizes. -/
theorem natural_globalR_ge_of_one_lt
    {T : Sylow 2 G} {M : Subgroup G} {n : ℕ}
    (hnatural : IsNaturalModule L B n)
    (hNL : normalizer (B : Set G) ≤ normalizer (L : Set G))
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M B)
    (hr : 1 < ChapterE.globalR B) : (n : ℕ∞) ≤ ChapterE.globalR B := by
  apply le_iInf
  intro U
  apply le_iInf
  rintro ⟨hUB, he⟩
  by_contra hn
  have hsmall : ChapterE.subgroupCorank B U < n := by
    exact_mod_cast lt_of_not_ge hn
  have hm := natural_localM_eq hnatural hNL
  have hUne := ChapterE.Section06.nontrivial_of_corank_lt_localM (hm.symm ▸ hsmall)
  exact he (centralizer_le_normalizer_of_local_equality hE hr hUne hUB
    (natural_local_centralizer_eq_of_corank_lt hnatural hNL hE hUB hsmall))

variable {κ : GroupClass} {T : Sylow 2 G} {M V : Subgroup G} {n : ℕ}

omit [IsElementaryAbelian 2 B] in
/-- Source 6.1.10's local minimum, before the independent global-r bound. -/
theorem natural_layer_localM_eq
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hE : ChapterE.Section06.HypothesisE61 κ T M (layer L V)) :
    letI := h.layer_elementary; ChapterE.localM (layer L V) = n := by
  let := h.layer_elementary
  exact natural_localM_eq hnatural
    (hE.normalizer_le.trans ((normal_subgroupOf_iff_le_normalizer h.L_le).mp h.L_normal))

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

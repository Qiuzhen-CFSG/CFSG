module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.AlternatingOrbitHeads
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.ComponentFixedFreeAt

/-!
# Guarded paired alternating-six orbit heads

The two fixed lines generate the actual component orbits. Their trivial
fixed spaces remove constants, and the marked fifteen-point permutation
theorem produces both inequivalent natural quotient maps with a common
parabolic and Sylow marking. AlternatingHeadBudgetAt adds their movement.
The original component, full quotient and Structural1222At are retained.
Source: Aschbacher--Smith 13.4.7(1iv), printed p.901, using G.5.3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}
open Theory.SpecificGroups.SymmetricSix BinaryDuadModule BinaryAlternatingSix
open Representation Representation.BinaryOffender
omit [Finite G] in
private theorem fixed_orbit_generator (F C P : Subgroup G)
    [IsElementaryAbelian 2 (conjugateSpanBy F C)]
    (hF : Nat.card F = 2) (hFP : F ≤ centralizer (P : Set G)) :
    let U := conjugateSpanBy F C
    let ρ := Representation.elementaryRepresentation (p := 2)
      (U.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy F C)))
    ∃ w : Additive U, (∀ a : P.subgroupOf C, ρ a w = w) ∧
      Submodule.span (ZMod 2) (Set.range (fun c : C => ρ c w)) = ⊤ := by
  let U := conjugateSpanBy F C
  let actor := U.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy F C))
  let ρ := Representation.elementaryRepresentation (p := 2) actor
  obtain ⟨v,hv,huniq⟩ := (Nat.card_eq_two_iff' (1 : F)).mp hF
  let w := inclusion (le_conjugateSpanBy F C) v
  refine ⟨Additive.ofMul w,?_,?_⟩
  · intro a
    apply Additive.toMul.injective
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hFP v.property a.val.val a.property)
  · apply Representation.conjugateSpan_binary_orbit_span F C U (le_conjugateSpanBy F C) rfl
      (MonoidHom.id U) Function.surjective_id actor
    · intro c x hx
      rfl
    · intro a
      by_cases ha : a = 1
      · exact Or.inl (by simp [ha])
      · exact Or.inr (congrArg (inclusion (le_conjugateSpanBy F C)) (huniq a ha))

/-- Each original fixed-line orbit has the corresponding natural quotient,
under a single full component quotient marking. -/
theorem original_pair_alternating_same_marking_heads_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (h1332 : Source1332OneTwo T)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (e : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃* A6)
    (hA : (A.subgroupOf (K.map (A ⊔ B).subtype)).map
      (e.toMonoidHom.comp (QuotientGroup.mk' _)) = a6DuadStabilizer)
    (hB : (B.subgroupOf (K.map (A ⊔ B).subtype)).map
      (e.toMonoidHom.comp (QuotientGroup.mk' _)) = a6SynthemeStabilizer) :
    let C := K.map (A ⊔ B).subtype
    let F₁ := omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)
    let F₂ := omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)
    let U₁ := conjugateSpanBy F₁ C
    let U₂ := conjugateSpanBy F₂ C
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
    ∃ he₁ : IsElementaryAbelian 2 U₁, ∃ he₂ : IsElementaryAbelian 2 U₂,
      let := he₁
      let := he₂
      let ρ₁ := Representation.elementaryRepresentation (p := 2)
        (U₁.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy F₁ C)))
      let ρ₂ := Representation.elementaryRepresentation (p := 2)
        (U₂.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy F₂ C)))
      (∃ q : ρ₁.IntertwiningMap (firstAlternating.comp f), Function.Surjective q) ∧
      (∃ q : ρ₂.IntertwiningMap (secondAlternating.comp f), Function.Surjective q) ∧
      (Module.finrank (ZMod 2) (Additive U₁) = 4 ∨
        Module.finrank (ZMod 2) (Additive U₁) = 5 ∨
        Module.finrank (ZMod 2) (Additive U₁) = 9 ∨
        Module.finrank (ZMod 2) (Additive U₁) = 10 ∨
        Module.finrank (ZMod 2) (Additive U₁) = 14) ∧
      (Module.finrank (ZMod 2) (Additive U₂) = 4 ∨
        Module.finrank (ZMod 2) (Additive U₂) = 5 ∨
        Module.finrank (ZMod 2) (Additive U₂) = 9 ∨
        Module.finrank (ZMod 2) (Additive U₂) = 10 ∨
        Module.finrank (ZMod 2) (Additive U₂) = 14) := by
  let X := A ⊔ B
  let C := K.map X.subtype
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let W := conjugateSpanBy Z X
  have hWX : W ≤ X := conjugateSpanBy_le (fun z hz =>
    (hTA.trans le_sup_left) ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) X.le_normalizer
  have hred := (original_pair_action_kernel h₀ D m hTA hTB eA eB hne hindexA hindexB).1
  let : IsElementaryAbelian 2 (W.subgroupOf X) := hred.elementary
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hWX).symm.toMonoidHom (subgroupOfEquivOfLe hWX).symm.injective
  let F₁ := Z ⊓ centralizer (A : Set G)
  let F₂ := Z ⊓ centralizer (B : Set G)
  let U₁ := conjugateSpanBy F₁ C
  let U₂ := conjugateSpanBy F₂ C
  have hUW (P : Subgroup G) : conjugateSpanBy (Z ⊓ centralizer (P : Set G)) C ≤ W :=
    conjugateSpanBy_mono inf_le_left (map_subtype_le K)
  let he₁ : IsElementaryAbelian 2 U₁ := IsElementaryAbelian.of_injective
    (inclusion (hUW A)) (inclusion_injective _)
  let he₂ : IsElementaryAbelian 2 U₂ := IsElementaryAbelian.of_injective
    (inclusion (hUW B)) (inclusion_injective _)
  let := he₁
  let := he₂
  let ρ₁ := Representation.elementaryRepresentation (p := 2)
    (U₁.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy F₁ C)))
  let ρ₂ := Representation.elementaryRepresentation (p := 2)
    (U₂.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy F₂ C)))
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hfree := original_pair_component_fixed_free_at h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK
  have free (P : Subgroup G) [IsElementaryAbelian 2 (conjugateSpanBy
      (Z ⊓ centralizer (P : Set G)) C)]
      (v : Additive (conjugateSpanBy (Z ⊓ centralizer (P : Set G)) C))
      (hv : ∀ c : C, Representation.elementaryRepresentation (p := 2)
        ((conjugateSpanBy (Z ⊓ centralizer (P : Set G)) C).normalizerMonoidHom.comp
          (inclusion (le_normalizer_conjugateSpanBy _ C))) c v = v) : v = 0 := by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply hfree.le
    refine ⟨hUW P v.toMul.property,?_⟩
    intro c hc
    have hh := congrArg (fun x => x.toMul.val) (hv ⟨c,hc⟩)
    change c * v.toMul.val * c⁻¹ = v.toMul.val at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  obtain ⟨_,hF₁,hF₂,_,_,_⟩ := original_pair_fixed_lines_at h structural D m hout
    hindexL hindexA hindexB (pair_fixed_subgroups_ne hTA hTB eA eB hne hres)
  have nt (P : Subgroup G) (hc : Nat.card (Z ⊓ centralizer (P : Set G) : Subgroup G) = 2) :
      Nontrivial (Additive (conjugateSpanBy (Z ⊓ centralizer (P : Set G)) C)) := by
    obtain ⟨v,hv,_⟩ := (Nat.card_eq_two_iff' (1 : (Z ⊓ centralizer (P : Set G) : Subgroup G))).mp hc
    let i := inclusion (le_conjugateSpanBy (Z ⊓ centralizer (P : Set G)) C)
    refine ⟨⟨Additive.ofMul (i v),0,fun hh => hv ?_⟩⟩
    apply inclusion_injective (le_conjugateSpanBy (Z ⊓ centralizer (P : Set G)) C)
    exact congrArg Additive.toMul hh
  let : Nontrivial (Additive U₁) := nt A hF₁
  let : Nontrivial (Additive U₂) := nt B hF₂
  obtain ⟨S,hS,_,_,_⟩ := original_pair_component_parabolic_restriction h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK
  have hk (P : Subgroup G) (hTP : (T : Subgroup G) ≤ P) : f.ker ≤ P.subgroupOf C := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact (pCore_isPGroup.le_sylow_of_normal S).trans (by rw [hS]; exact fun _ ht => hTP ht)
  obtain ⟨w₁,hw₁,hs₁⟩ := fixed_orbit_generator F₁ C A hF₁ inf_le_right
  obtain ⟨w₂,hw₂,hs₂⟩ := fixed_orbit_generator F₂ C B hF₂ inf_le_right
  obtain ⟨hq₁,hd₁⟩ := ChapterG.Section05.Structure.marked_fixed_line_natural_head
    f hf (A.subgroupOf C) (hk A hTA) hA ρ₁ w₁ hw₁ hs₁ (free A)
  obtain ⟨hq₂,hd₂⟩ := ChapterG.Section05.Structure.marked_syntheme_natural_head
    f hf (B.subgroupOf C) (hk B hTB) hB ρ₂ w₂ hw₂ hs₂ (free B)
  exact ⟨he₁,he₂,hq₁,hq₂,hd₁,hd₂⟩

/-- Construct both graph-conjugate natural quotients of submodules spanning
the whole original omega module, without a supplied parabolic or module marking. -/
theorem original_pair_alternating_heads_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (h1332 : Source1332OneTwo T)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃* A6) :
    let C := K.map (A ⊔ B).subtype
    let F₁ := omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)
    let F₂ := omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)
    let U₁ := conjugateSpanBy F₁ C
    let U₂ := conjugateSpanBy F₂ C
    ∃ e : (C ⧸ pCore 2 C) ≃* A6,
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
    ((A.subgroupOf C).map f = a6DuadStabilizer ∧
      (B.subgroupOf C).map f = a6SynthemeStabilizer ∧
      ((T : Subgroup G).subgroupOf C).map f = a6Borel) ∧
    U₁ ⊔ U₂ = conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B) ∧
    ∃ he₁ : IsElementaryAbelian 2 U₁, ∃ he₂ : IsElementaryAbelian 2 U₂,
      let := he₁
      let := he₂
      let ρ₁ := Representation.elementaryRepresentation (p := 2)
        (U₁.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy F₁ C)))
      let ρ₂ := Representation.elementaryRepresentation (p := 2)
        (U₂.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy F₂ C)))
      (∃ q : ρ₁.IntertwiningMap (firstAlternating.comp f), Function.Surjective q) ∧
      (∃ q : ρ₂.IntertwiningMap (secondAlternating.comp f), Function.Surjective q) ∧
      (Module.finrank (ZMod 2) (Additive U₁) = 4 ∨
        Module.finrank (ZMod 2) (Additive U₁) = 5 ∨
        Module.finrank (ZMod 2) (Additive U₁) = 9 ∨
        Module.finrank (ZMod 2) (Additive U₁) = 10 ∨
        Module.finrank (ZMod 2) (Additive U₁) = 14) ∧
      (Module.finrank (ZMod 2) (Additive U₂) = 4 ∨
        Module.finrank (ZMod 2) (Additive U₂) = 5 ∨
        Module.finrank (ZMod 2) (Additive U₂) = 9 ∨
        Module.finrank (ZMod 2) (Additive U₂) = 10 ∨
        Module.finrank (ZMod 2) (Additive U₂) = 14) := by
  obtain ⟨e,hA,hB,hS⟩ := original_pair_alternating_oriented_parabolics h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK eK
  refine ⟨e,⟨hA,hB,hS⟩,?_,?_⟩
  · exact (original_pair_component_fixed_line_spans_at h₀ h structural D m
      hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK).symm
  · exact original_pair_alternating_same_marking_heads_at h₀ h structural D m
      hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK e hA hB

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam

module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearOrbitPair
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.ComponentFixedFreeAt

/-!
# Guarded opposite linear orbit modules

Under one simultaneous marking of the two actual parabolics, their fixed
lines generate permutation quotients with no component-fixed vectors.
The first is natural or point core; the other is dual natural or line core.
No supplied orbit model is used. LinearWholeModuleAt uses these opposite
orientations to identify the full original omega module.
Source: Aschbacher--Smith 13.4.7(1ii), printed p.901, using H.5.3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}
open BinaryLinearThree.FanoDecomposition Representation.BinaryOffender
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

/-- Both orbit models use one specified quotient marking, so their natural
heads have opposite orientations. -/
theorem original_pair_linear_same_marking_models_at
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
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Matrix.PSL3Two.PSL)
    (e : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      BinaryLinearThree.Group)
    (hA : (A.subgroupOf (K.map (A ⊔ B).subtype)).map
      (e.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.pointParabolicSL)
    (hB : (B.subgroupOf (K.map (A ⊔ B).subtype)).map
      (e.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.lineParabolicSL) :
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
      (Nonempty (Representation.Equiv (BinaryLinearThree.W.comp f) ρ₁) ∨
        Nonempty (Representation.Equiv (BinaryLinearThree.U₂.comp f) ρ₁)) ∧
      (Nonempty (Representation.Equiv (BinaryLinearThree.W.dual.comp f) ρ₂) ∨
        Nonempty (Representation.Equiv (lineCoreRepresentation.comp f) ρ₂)) := by
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
  have move (P : Subgroup G) (hc : Nat.card (Z ⊓ centralizer (P : Set G) : Subgroup G) = 2) :
      ¬ Z ⊓ centralizer (P : Set G) ≤ centralizer (C : Set G) := by
    intro hh
    have hz : Z ⊓ centralizer (P : Set G) = ⊥ := bot_unique (fun x hx =>
      hfree.le ⟨le_conjugateSpanBy Z X hx.1,hh hx⟩)
    rw [hz,Subgroup.card_bot] at hc
    omega
  have hd₁ := Representation.one_lt_finrank_conjugateLine F₁ C hF₁ (move A hF₁)
  have hd₂ := Representation.one_lt_finrank_conjugateLine F₂ C hF₂ (move B hF₂)
  obtain ⟨S,hS,_⟩ := original_pair_linear_parabolic h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK eK
  have hk (P : Subgroup G) (hTP : (T : Subgroup G) ≤ P) : f.ker ≤ P.subgroupOf C := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact (pCore_isPGroup.le_sylow_of_normal S).trans (by rw [hS]; exact fun _ ht => hTP ht)
  obtain ⟨w₁,hw₁,hs₁⟩ := fixed_orbit_generator F₁ C A hF₁ inf_le_right
  obtain ⟨w₂,hw₂,hs₂⟩ := fixed_orbit_generator F₂ C B hF₂ inf_le_right
  obtain ⟨q₁,hq₁⟩ := BinaryLinearThree.FanoPointFixedFree.marked_quotient f hf
    (A.subgroupOf C) (hk A hTA) hA ρ₁ w₁ hw₁ hs₁
  obtain ⟨q₂,hq₂⟩ := BinaryLinearThree.FixedParabolicQuotient.marked_quotient f hf
    (B.subgroupOf C) (hk B hTB) hB ρ₂ w₂ hw₂ hs₂
  exact ⟨he₁,he₂,BinaryLinearThree.FanoPointFixedFree.whole_models f hf ρ₁ q₁ hq₁
    (Nat.zero_lt_of_lt hd₁) (free A),
    (BinaryLinearThree.FanoFixedFreeQuotient.whole_models f hf ρ₂ q₂ hq₂ hd₂ (free B)).2.2.1⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam

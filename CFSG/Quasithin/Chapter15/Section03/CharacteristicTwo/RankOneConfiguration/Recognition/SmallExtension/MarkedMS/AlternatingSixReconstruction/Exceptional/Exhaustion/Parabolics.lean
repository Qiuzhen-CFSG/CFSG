module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.InitialAction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.CoveredSixModels.Full

/-!
# Parabolic preservation in the exceptional MS quotient

The faithful initial triple-cover action extends to the full hexacode group.
Its coordinate permutations preserve the two A₆ parabolic types. Comparing
surjections with the same kernel transports this fact to the original central
quotient marking. The other possible initial kernel gives the binary natural
A₆ action and the same conclusion. Thus the literal quotient M/E embeds in
S₆, contains A₆, and preserves both source parabolic types.

The original radical image is a two-group, so a conjugate of the standard
incident flag contains it. E retains the cubic covering kernel throughout;
R is never assumed Sylow. These results discharge the parabolic-type step of
weak-BN preparation. Construction of the complete weak-BN data and exhaustion
of [O₂(M),K] remain with this reconstruction owner.

Source: Meierfrankenfeld--Stellmacher (1993), Hypothesis (WBN), pp.827--829,
and (3.2), pp.863--864; Aschbacher--Smith K.1.3, p.453. The imported hexacode
normalizer retains the original ATLAS attribution and LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.CoveredSixModels
open Atlas.Codes
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ R)

theorem layer_full_hexacode_model
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (hc : layerKernel L R = pCore 2 M) :
    ∃ (f : LayerActor L R →* HexAutomorphisms)
      (c : layerComponent L R ≃* HexEvenAutomorphisms),
      Function.Injective f ∧ ∀ g : layerComponent L R, f g = (c g).val := by
  let := layerComponent_normal h
  let := layerComponent_quasisimple h e hz
  obtain ⟨a⟩ := layerComponent_equiv_hexEven h e hz hc
  obtain ⟨m⟩ := nonempty_actionData (layerAction L R) (layerComponent L R) a
    (layerComponent_sqtk h e hz) (layerActor_component_quotient_two h)
    (layerActor_twoCore h e hz) layerAction_faithful (layer_source_conclusion h e hz).1
  obtain ⟨f, c, _, hf, _, hfc, _⟩ := m.exists_full_model a
    (layerActor_component_quotient_two h) (layerActor_twoCore h e hz)
  exact ⟨f, c, hf, hfc⟩

private theorem equiv_of_same_kernel {A B D : Type*} [Group A] [Group B] [Group D]
    (p : A →* B) (q : A →* D) (hp : Function.Surjective p)
    (hq : Function.Surjective q) (hk : p.ker = q.ker) :
    ∃ b : B ≃* D, ∀ x, b (p x) = q x := by
  let ep := QuotientGroup.quotientKerEquivOfSurjective p hp
  let eq := QuotientGroup.quotientKerEquivOfSurjective q hq
  let b := ep.symm.trans ((QuotientGroup.quotientMulEquivOfEq hk).trans eq)
  refine ⟨b, ?_⟩
  intro x
  have hx : ep.symm (p x) = QuotientGroup.mk' p.ker x := by
    apply ep.injective
    rw [ep.apply_symm_apply]
    rfl
  change eq (QuotientGroup.quotientMulEquivOfEq hk (ep.symm (p x))) = q x
  rw [hx]
  rfl

private theorem comap_center_of_surjective {A B : Type*} [Group A] [Group B]
    (s : A →* B) (hs : Function.Surjective s) :
    (center B).comap s = centralPreimage s.ker := by
  let a := QuotientGroup.quotientKerEquivOfSurjective s hs
  ext x
  change s x ∈ center B ↔ QuotientGroup.mk' s.ker x ∈ center (A ⧸ s.ker)
  constructor
  · intro hx
    apply mem_center_iff.mpr
    intro y
    apply a.injective
    simpa only [map_mul] using (show a y * a (QuotientGroup.mk' s.ker x) =
      a (QuotientGroup.mk' s.ker x) * a y from mem_center_iff.mp hx (a y))
  · intro hx
    change a (QuotientGroup.mk' s.ker x) ∈ center B
    exact (centerCongr a ⟨_, hx⟩).property

private theorem natural_of_hexacode_quotient {A : Type*} [Group A]
    (p : A →* alternatingGroup (Fin 6)) (s : A →* HexEvenAutomorphisms)
    (hp : Function.Surjective p) (hs : Function.Surjective s)
    (hk : p.ker = centralPreimage s.ker)
    (α : MulAut A) (β : MulAut (alternatingGroup (Fin 6))) (g : HexAutomorphisms)
    (hpα : ∀ x, p (α x) = β (p x))
    (hsα : ∀ x, (s (α x)).val = g * (s x).val * g⁻¹) :
    β ∈ _root_.AlternatingSix.ShadowLocal.natural := by
  let q := hexEvenCoordinate.comp s
  have hker : p.ker = q.ker := by
    change p.ker = (hexEvenCoordinate.comp s).ker
    rw [← MonoidHom.comap_ker, Hexacode.even_kernel_eq_center,
      comap_center_of_surjective s hs]
    exact hk
  obtain ⟨b, hb⟩ := equiv_of_same_kernel p q hp
    (hexEvenCoordinate_surjective.comp hs) hker
  have he : b * β * b⁻¹ =
      _root_.AlternatingSix.ShadowLocal.permutationAction (hexCoordinateSixHom g) := by
    apply MulEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := (b.surjective.comp hp) y
    change b (β (b.symm (b (p x)))) =
      _root_.AlternatingSix.ShadowLocal.permutationAction (hexCoordinateSixHom g) (b (p x))
    rw [b.symm_apply_apply, ← hpα, hb, hb]
    apply Subtype.ext
    change hexCoordinateSixHom (s (α x)).val =
      hexCoordinateSixHom g * hexCoordinateSixHom (s x).val * (hexCoordinateSixHom g)⁻¹
    rw [hsα, map_mul, map_mul, map_inv]
  apply (BinaryAlternatingSixNaturalNormalizer.natural_conjugation_iff b β).mp
  rw [he]
  exact ⟨hexCoordinateSixHom g, rfl⟩


theorem extensionQuotientAction_natural_of_faithful_layer
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (hc : layerKernel L R = pCore 2 M) (x : M ⧸ extensionKernel h) :
    extensionQuotientAction h e x ∈ _root_.AlternatingSix.ShadowLocal.natural := by
  let := h.relative_normal
  let q := QuotientGroup.mk' (layerKernel L R)
  let π := QuotientGroup.mk' (extensionKernel h)
  let D := (K).map π
  let : D.Normal := (inferInstance : (K).Normal).map π (QuotientGroup.mk'_surjective _)
  let a := extensionKernel_component_equiv h e
  obtain ⟨f, c, _, hfc⟩ := layer_full_hexacode_model h e hz hc
  let p := a.toMonoidHom.comp (π.subgroupMap K)
  let s := c.toMonoidHom.comp (q.subgroupMap K)
  have hp : Function.Surjective p := a.surjective.comp (π.subgroupMap_surjective K)
  have hs : Function.Surjective s := c.surjective.comp (q.subgroupMap_surjective K)
  have hsk : s.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ c.injective, ker_subgroupMap,
      QuotientGroup.ker_mk', hc]
    exact (pCore_subnormal_eq_comap 2 h.component.subnormal).symm
  have hpk : p.ker = centralPreimage s.ker := by
    simp only [hsk]
    rw [MonoidHom.ker_comp_of_injective _ _ a.injective, ker_subgroupMap,
      QuotientGroup.ker_mk']
    exact extensionKernel_component_intersection h
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (extensionKernel h) x
  apply natural_of_hexacode_quotient p s hp hs hpk (MulAut.conjNormal m)
    (extensionQuotientAction h e (π m)) (f (q m))
  · intro k
    change a (π.subgroupMap K (MulAut.conjNormal m k)) =
      a (MulAut.conjNormal (π m) (a.symm (a (π.subgroupMap K k))))
    rw [a.symm_apply_apply]
    apply congrArg a
    apply Subtype.ext
    change π (m * (k : M) * m⁻¹) = π m * π (k : M) * (π m)⁻¹
    simp only [map_mul, map_inv]
  · intro k
    change (c (q.subgroupMap K (MulAut.conjNormal m k))).val =
      f (q m) * (c (q.subgroupMap K k)).val * (f (q m))⁻¹
    rw [← hfc, ← hfc]
    change f (q (m * (k : M) * m⁻¹)) = f (q m) * f (q (k : M)) * (f (q m))⁻¹
    simp only [map_mul, map_inv]

private theorem natural_of_compatible_quotients {A : Type*} [Group A]
    (p s : A →* alternatingGroup (Fin 6))
    (hp : Function.Surjective p) (hs : Function.Surjective s) (hk : p.ker = s.ker)
    (α : MulAut A) (β δ : MulAut (alternatingGroup (Fin 6)))
    (hpα : ∀ x, p (α x) = β (p x)) (hsα : ∀ x, s (α x) = δ (s x))
    (hδ : δ ∈ _root_.AlternatingSix.ShadowLocal.natural) :
    β ∈ _root_.AlternatingSix.ShadowLocal.natural := by
  obtain ⟨b, hb⟩ := equiv_of_same_kernel p s hp hs hk
  have he : b * β * b⁻¹ = δ := by
    apply MulEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := (b.surjective.comp hp) y
    change b (β (b.symm (b (p x)))) = δ (b (p x))
    rw [b.symm_apply_apply, ← hpα, hb, hb, hsα]
  apply (BinaryAlternatingSixNaturalNormalizer.natural_conjugation_iff b β).mp
  exact he.symm ▸ hδ

theorem extensionQuotientAction_natural_of_cubic_layer
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (hc : layerKernel L R = extensionKernel h) (x : M ⧸ extensionKernel h) :
    extensionQuotientAction h e x ∈ _root_.AlternatingSix.ShadowLocal.natural := by
  let := h.relative_normal
  let := layerComponent_normal h
  let q := QuotientGroup.mk' (layerKernel L R)
  let π := QuotientGroup.mk' (extensionKernel h)
  let D := (K).map π
  let : D.Normal := (inferInstance : (K).Normal).map π (QuotientGroup.mk'_surjective _)
  let a := extensionKernel_component_equiv h e
  obtain ⟨c⟩ := layerComponent_equiv_alternating h e hc
  let p := a.toMonoidHom.comp (π.subgroupMap K)
  let s := c.toMonoidHom.comp (q.subgroupMap K)
  have hp : Function.Surjective p := a.surjective.comp (π.subgroupMap_surjective K)
  have hs : Function.Surjective s := c.surjective.comp (q.subgroupMap_surjective K)
  have hk : p.ker = s.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ a.injective,
      MonoidHom.ker_comp_of_injective _ _ c.injective, ker_subgroupMap,
      ker_subgroupMap, QuotientGroup.ker_mk', QuotientGroup.ker_mk', hc]
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (extensionKernel h) x
  apply natural_of_compatible_quotients p s hp hs hk (MulAut.conjNormal m)
    (extensionQuotientAction h e (π m)) (MulAut.congr c (MulAut.conjNormal (q m)))
  · intro k
    change a (π.subgroupMap K (MulAut.conjNormal m k)) =
      a (MulAut.conjNormal (π m) (a.symm (a (π.subgroupMap K k))))
    rw [a.symm_apply_apply]
    apply congrArg a
    apply Subtype.ext
    change π (m * (k : M) * m⁻¹) = π m * π (k : M) * (π m)⁻¹
    simp only [map_mul, map_inv]
  · intro k
    change c (q.subgroupMap K (MulAut.conjNormal m k)) =
      c (MulAut.conjNormal (q m) (c.symm (c (q.subgroupMap K k))))
    rw [c.symm_apply_apply]
    apply congrArg c
    apply Subtype.ext
    change q (m * (k : M) * m⁻¹) = q m * q (k : M) * (q m)⁻¹
    simp only [map_mul, map_inv]
  · exact layer_action_natural_of_cubic_kernel h e hz hc c (q m)

theorem extensionQuotientAction_natural
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3) (x : M ⧸ extensionKernel h) :
    extensionQuotientAction h e x ∈ _root_.AlternatingSix.ShadowLocal.natural :=
  (centralOmega_centralizer_cases h e hz).elim
    (fun hc => extensionQuotientAction_natural_of_faithful_layer h e hz hc x)
    (fun hc => extensionQuotientAction_natural_of_cubic_layer h e hz hc x)

open Theory.SpecificGroups.SymmetricSix in
theorem extensionQuotientAction_parabolic_types
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3) (x : M ⧸ extensionKernel h) :
    (∃ c : alternatingGroup (Fin 6),
      a6DuadStabilizer.map (extensionQuotientAction h e x).toMonoidHom =
        a6DuadStabilizer.map (MulAut.conj c).toMonoidHom) ∧
    (∃ c : alternatingGroup (Fin 6),
      a6SynthemeStabilizer.map (extensionQuotientAction h e x).toMonoidHom =
        a6SynthemeStabilizer.map (MulAut.conj c).toMonoidHom) :=
  (_root_.AlternatingSix.ShadowLocal.FourNormalizers.SixParabolics.natural_iff_preserves_source_parabolic_types _).mp
    (extensionQuotientAction_natural h e hz x)

/-- The actual source quotient embeds into S₆ through its given A₆ marking. -/
@[expose] def extensionPermutationAction
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3) :
    (M ⧸ extensionKernel h) →* Equiv.Perm (Fin 6) :=
  (MonoidHom.ofInjective _root_.AlternatingSix.ShadowLocal.permutationAction_injective).symm.toMonoidHom.comp
    ((extensionQuotientAction h e).codRestrict _
      (extensionQuotientAction_natural h e hz))

theorem extensionPermutationAction_conjugation
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3) (x : M ⧸ extensionKernel h) :
    _root_.AlternatingSix.ShadowLocal.permutationAction (extensionPermutationAction h e hz x) =
      extensionQuotientAction h e x :=
  MonoidHom.apply_ofInjective_symm _root_.AlternatingSix.ShadowLocal.permutationAction_injective
    ⟨extensionQuotientAction h e x, extensionQuotientAction_natural h e hz x⟩

theorem extensionPermutationAction_injective
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3) :
    Function.Injective (extensionPermutationAction h e hz) := by
  intro x y hxy
  apply extensionQuotientAction_injective h e
  rw [← extensionPermutationAction_conjugation h e hz,
    ← extensionPermutationAction_conjugation h e hz, hxy]

/-- Component elements use exactly the original central quotient marking. -/
theorem extensionPermutationAction_component
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3) (k : K) :
    extensionPermutationAction h e hz (QuotientGroup.mk' (extensionKernel h) k) =
      (extensionKernel_component_equiv h e
        ((QuotientGroup.mk' (extensionKernel h)).subgroupMap K k)).val := by
  apply _root_.AlternatingSix.ShadowLocal.permutationAction_injective
  rw [extensionPermutationAction_conjugation,
    _root_.AlternatingSix.ShadowLocal.permutationAction_coe, extensionQuotientAction_component]

theorem extensionPermutationAction_contains_alternating
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3) :
    alternatingGroup (Fin 6) ≤ (extensionPermutationAction h e hz).range := by
  intro g hg
  obtain ⟨k, hk⟩ := (extensionKernel_component_equiv h e).surjective ⟨g, hg⟩
  obtain ⟨k', rfl⟩ := (QuotientGroup.mk' (extensionKernel h)).subgroupMap_surjective K k
  refine ⟨QuotientGroup.mk' (extensionKernel h) k', ?_⟩
  rw [extensionPermutationAction_component]
  exact congrArg Subtype.val hk

/-- The source quotient has the actual A₆ or S₆ permutation image. -/
theorem extensionPermutationAction_range
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3) :
    (extensionPermutationAction h e hz).range = alternatingGroup (Fin 6) ∨
      (extensionPermutationAction h e hz).range = ⊤ := by
  have hle := extensionPermutationAction_contains_alternating h e hz
  have hi := index_dvd_of_le hle
  rw [alternatingGroup.index_eq_two] at hi
  rcases (Nat.dvd_prime Nat.prime_two).mp hi with h1 | h2
  · exact Or.inr (index_eq_one.mp h1)
  · left
    apply le_antisymm _ hle
    apply relIndex_eq_one.mp
    have hr := relIndex_mul_index hle
    rw [h2, alternatingGroup.index_eq_two] at hr
    omega

open Theory.SpecificGroups.SymmetricSix in
/-- A single incident source flag contains the original radical image.
Only the two-group property of R is used; R need not be Sylow. -/
theorem extensionPermutationAction_radical_flag
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3) :
    ∃ g : Equiv.Perm (Fin 6),
      ((R.subgroupOf (L ⊔ R)).map (QuotientGroup.mk' (extensionKernel h))).map
          (extensionPermutationAction h e hz) ≤ borel.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨S, hS⟩ := ((h.relative_radical.isPGroup.map
    (QuotientGroup.mk' (extensionKernel h))).map
      (extensionPermutationAction h e hz)).exists_le_sylow
  obtain ⟨g, hg, _⟩ := coatoms_over_sylow S
  exact ⟨g, hS.trans_eq hg.symm⟩

end AlternatingSixReconstruction.Exceptional.Exhaustion
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

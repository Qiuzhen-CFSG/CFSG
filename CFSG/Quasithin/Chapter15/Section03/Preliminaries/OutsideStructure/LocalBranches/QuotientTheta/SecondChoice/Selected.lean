module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches.QuotientTheta.Source
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches.SpanIntersection
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal.OmegaAction.QuotientAction.Conjugation
public import Theory.ElementaryAbelian.PrimePlane
public import Theory.GroupAction.Extraspecial27ElementaryActor
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Geometry

/-!
# The selected elementary-nine subgroup and its genuine four-group action

Project Y₊ into Y/O₂(Y). Its image has index three, using the earlier
residual-centralizer supplement and the cubic coordinate calculation. In
the extraspecial branch this image has order nine, exponent three, and
contains the center of the order-27 quotient. Its full inverse image in Y
is C_Y(V₁). The projection kernel is exactly O₂(Y₊), giving the actual E₉
quotient equivalence.

The earlier O₂(YT)=C_T(V) calculation makes quotient conjugation descend
to the natural image of T. Restricting that proved faithful action gives
the actual elementary-four image of S and its action on the selected
nine-group. This restricted action is faithful: a nonidentity involution
fixing the center of an extraspecial group of order 27 has only central
fixed points, so cannot fix a subgroup of order nine. The central line is
invariant and the full four-group does not fix it pointwise.

All actions below retain their formula on representatives. This supplies
concrete input to the remaining semidirect-product recognition; it does
not assume a quotient of Y₊S or either final local alternative.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.7(2)
and the second-choice proof of 15.3.11(5i), printed pp.1122–1124.
-/

@[expose] public section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.OutsideStructure.LocalBranches.QuotientTheta
open FusionCore.CosetSetup.ExtraspecialLocal
variable {G : Type*} [Group G] [Finite G]

noncomputable def selectedQuotientMap (d : CharacteristicTwo.LocalData G) :
    d.Yplus →* (d.Y ⧸ pCore 2 d.Y) :=
  (QuotientGroup.mk' (pCore 2 d.Y)).comp
    (inclusion (choice_le d.M d.Y d.S d.V₁ d.Yplus d.choice))

noncomputable def selectedThreeSubgroup (d : CharacteristicTwo.LocalData G) :
    Subgroup (d.Y ⧸ pCore 2 d.Y) := (selectedQuotientMap d).range

omit [Finite G] in
private theorem selected_range_map (d : CharacteristicTwo.LocalData G) :
    selectedThreeSubgroup d = (d.Yplus.subgroupOf d.Y).map (QuotientGroup.mk' (pCore 2 d.Y)) := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨⟨y, choice_le d.M d.Y d.S d.V₁ d.Yplus d.choice y.property⟩, y.property, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

omit [Finite G] in
private theorem supplement_subgroupOf (d : CharacteristicTwo.LocalData G) :
    (d.Yplus ⊔ d.Y.pCoreIn 2).subgroupOf d.Y = d.Yplus.subgroupOf d.Y ⊔ pCore 2 d.Y := by
  apply map_injective d.Y.subtype_injective
  rw [map_subgroupOf_eq_of_le (sup_le
    (choice_le d.M d.Y d.S d.V₁ d.Yplus d.choice) (pCoreIn_le 2 d.Y)), Subgroup.map_sup,
    map_subgroupOf_eq_of_le (choice_le d.M d.Y d.S d.V₁ d.Yplus d.choice)]
  rfl

omit [Finite G] in
private theorem selected_range_supplement (d : CharacteristicTwo.LocalData G) :
    selectedThreeSubgroup d = ((d.Yplus ⊔ d.Y.pCoreIn 2).subgroupOf d.Y).map
      (QuotientGroup.mk' (pCore 2 d.Y)) := by
  rw [supplement_subgroupOf, Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]
  exact selected_range_map d

theorem selectedThreeSubgroup_index (d : CharacteristicTwo.LocalData G)
    (hsecond : OutsideStructure.SecondChoice d)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hodd : IsPGroup 3 (d.Y ⧸ pCore 2 d.Y)) :
    (selectedThreeSubgroup d).index = 3 := by
  have hh := relIndex_map_map (QuotientGroup.mk' (pCore 2 d.Y)) (d.Yplus.subgroupOf d.Y) ⊤
  rw [map_top_of_surjective _ (QuotientGroup.mk'_surjective _), top_sup_eq,
    QuotientGroup.ker_mk', relIndex_top_right, relIndex_top_right,
    ← supplement_subgroupOf, ← selected_range_map] at hh
  exact hh.trans (second_choice_supplement_index d hsecond h7image hodd)

theorem selectedThreeSubgroup_card (d : CharacteristicTwo.LocalData G)
    (hsecond : OutsideStructure.SecondChoice d)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h : ExtraspecialCase d.M d.Y d.V) : Nat.card (selectedThreeSubgroup d) = 9 := by
  let _ := h.extraspecial
  have hh := (selectedThreeSubgroup d).card_mul_index
  rw [selectedThreeSubgroup_index d hsecond h7image (IsExtraspecial.isPGroup 3 _),
    h.quotient_card] at hh
  omega

theorem center_le_selectedThreeSubgroup (d : CharacteristicTwo.LocalData G)
    (hsecond : OutsideStructure.SecondChoice d)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h : ExtraspecialCase d.M d.Y d.V) :
    center (d.Y ⧸ pCore 2 d.Y) ≤ selectedThreeSubgroup d := by
  let _ := h.extraspecial
  intro z hz
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 d.Y) z
  have hcy : (y : G) ∈ d.Y ⊓ centralizer (d.V : Set G) :=
    h.centralizer_eq.ge ⟨y, hz, rfl⟩
  have hc : (y : G) ∈ d.Y ⊓ centralizer (d.V₁ : Set G) :=
    ⟨y.property, centralizer_le (d.action.plane_le 1) hcy.2⟩
  have hs : (y : G) ∈ d.Yplus ⊔ d.Y.pCoreIn 2 :=
    (second_choice_core_supplement d hsecond h7image (IsExtraspecial.isPGroup 3 _)).ge hc
  rw [selected_range_supplement]
  exact ⟨y, hs, rfl⟩

omit [Finite G] in
theorem selectedQuotientMap_kernel (d : CharacteristicTwo.LocalData G)
    (hodd : IsPGroup 3 (d.Y ⧸ pCore 2 d.Y)) :
    (selectedQuotientMap d).ker = pCore 2 d.Yplus := by
  let f := selectedQuotientMap d
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 ((QuotientGroup.mk' (pCore 2 d.Y)).ker.comap (inclusion _))
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
  apply le_antisymm (show f.ker ≤ pCore 2 d.Yplus from le_sSup ⟨inferInstance, hk⟩)
  rw [← Subgroup.map_eq_bot_iff]
  have hd := (pCore_isPGroup (p := 2) (G := d.Yplus)).map f |>.disjoint_of_coprime
    (hodd.to_subgroup ⊤) (by decide : Nat.Coprime 2 3)
  exact disjoint_top.mp hd

noncomputable def selectedQuotientEquiv (d : CharacteristicTwo.LocalData G)
    (hodd : IsPGroup 3 (d.Y ⧸ pCore 2 d.Y)) :
    (d.Yplus ⧸ pCore 2 d.Yplus) ≃* selectedThreeSubgroup d :=
  (QuotientGroup.quotientMulEquivOfEq (selectedQuotientMap_kernel d hodd).symm).trans
    (QuotientGroup.quotientKerEquivRange (selectedQuotientMap d))

theorem selectedThreeSubgroup_elementary (d : CharacteristicTwo.LocalData G)
    (hsecond : OutsideStructure.SecondChoice d)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h : ExtraspecialCase d.M d.Y d.V) : IsElementaryAbelian 3 (selectedThreeSubgroup d) := by
  let _ : IsMulCommutative (selectedThreeSubgroup d) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3)
      (selectedThreeSubgroup_card d hsecond h7image h)
  constructor
  rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
  intro x
  apply Subtype.ext
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (by rw [h.quotient_exponent]) x.val

theorem second_choice_extraspecial_selected_quotient (d : CharacteristicTwo.LocalData G)
    (hsecond : OutsideStructure.SecondChoice d)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h : ExtraspecialCase d.M d.Y d.V) :
    Nonempty ((d.Yplus ⧸ pCore 2 d.Yplus) ≃* Multiplicative (Fin 2 → ZMod 3)) := by
  let _ := h.extraspecial
  let _ := selectedThreeSubgroup_elementary d hsecond h7image h
  have hc : Nat.card (selectedThreeSubgroup d) = 3 ^ 2 := selectedThreeSubgroup_card d hsecond h7image h
  have hdim : Module.finrank (ZMod 3) (Additive (selectedThreeSubgroup d)) = 2 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := Additive (selectedThreeSubgroup d))
    have he : Nat.card (Additive (selectedThreeSubgroup d)) = 3 ^ 2 :=
      (Nat.card_congr Additive.toMul).trans hc
    rw [he, Nat.card_zmod] at hh
    exact (Nat.pow_right_injective (by decide : 2 ≤ 3)) hh.symm
  let e : Additive (selectedThreeSubgroup d) ≃ₗ[ZMod 3] (Fin 2 → ZMod 3) :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using hdim)
  exact ⟨(selectedQuotientEquiv d (IsExtraspecial.isPGroup 3 _)).trans
    e.toAddEquiv.toMultiplicativeRight⟩

/-- Projection from the actual plane stabilizer to its natural image. -/
def selectedSylowProjection (d : CharacteristicTwo.LocalData G) :
    d.S →* d.action.image d.S :=
  (d.action.actor.comp (inclusion (inf_le_left.trans d.sylow_le))).codRestrict _
    (fun s => ⟨⟨s, d.sylow_le s.property.1⟩, s.property, rfl⟩)

omit [Finite G] in
theorem selectedSylowProjection_surjective (d : CharacteristicTwo.LocalData G) :
    Function.Surjective (selectedSylowProjection d) := by
  rintro ⟨a, m, hm, rfl⟩
  exact ⟨⟨m, hm⟩, rfl⟩

/-- The genuine S-image action on the full extraspecial quotient. -/
noncomputable def selectedSylowAction (d : CharacteristicTwo.LocalData G)
    (hcore : (d.Y ⊔ (d.T : Subgroup G)).pCoreIn 2 =
      (d.T : Subgroup G) ⊓ centralizer (d.V : Set G)) :
    d.action.image d.S →* MulAut (d.Y ⧸ pCore 2 d.Y) :=
  (extraspecialQuotientAction d.action d.T d.sylow_le (m_normalizes_y d)
    (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc) hcore).comp
    (inclusion (map_mono (comap_mono (show d.S ≤ (d.T : Subgroup G) from inf_le_left))))

theorem selectedSylowAction_projection (d : CharacteristicTwo.LocalData G)
    (hcore : (d.Y ⊔ (d.T : Subgroup G)).pCoreIn 2 =
      (d.T : Subgroup G) ⊓ centralizer (d.V : Set G)) (s : d.S) :
    selectedSylowAction d hcore (selectedSylowProjection d s) =
      sylowQuotientConjugation d.T d.Y (d.sylow_le.trans (m_normalizes_y d))
        ⟨s, s.property.1⟩ :=
  extraspecialQuotientAction_projection d.action d.T d.sylow_le (m_normalizes_y d)
    (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc) hcore ⟨s, s.property.1⟩

theorem selectedSylowAction_injective (d : CharacteristicTwo.LocalData G)
    (hcore : (d.Y ⊔ (d.T : Subgroup G)).pCoreIn 2 =
      (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h : ExtraspecialCase d.M d.Y d.V) : Function.Injective (selectedSylowAction d hcore) :=
  (extraspecialQuotientAction_injective d.action d.T d.sylow_le (m_normalizes_y d)
    (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc) hcore h.centralizer_eq h7image).comp
    (inclusion_injective _)

/-- Restriction to the selected odd subgroup retains conjugation by S. -/
theorem selectedSylowAction_on_selected (d : CharacteristicTwo.LocalData G)
    (hcore : (d.Y ⊔ (d.T : Subgroup G)).pCoreIn 2 =
      (d.T : Subgroup G) ⊓ centralizer (d.V : Set G)) (s : d.S) (y : d.Yplus) :
    selectedSylowAction d hcore (selectedSylowProjection d s) (selectedQuotientMap d y) =
      selectedQuotientMap d (d.Yplus.normalizerMonoidHom
        ⟨s, ys_normalizes_yplus d (mem_sup_right s.property)⟩ y) := by
  rw [selectedSylowAction_projection]
  change sylowQuotientConjugation _ _ _ _ (QuotientGroup.mk' (pCore 2 d.Y) _) = _
  rw [sylowQuotientConjugation_apply]
  rfl

/-- The selected elementary-nine preimage is stable under this actual four-group action. -/
theorem selectedSylowAction_stable (d : CharacteristicTwo.LocalData G)
    (hcore : (d.Y ⊔ (d.T : Subgroup G)).pCoreIn 2 =
      (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (s : d.action.image d.S) (z : d.Y ⧸ pCore 2 d.Y) (hz : z ∈ selectedThreeSubgroup d) :
    selectedSylowAction d hcore s z ∈ selectedThreeSubgroup d := by
  obtain ⟨s, rfl⟩ := selectedSylowProjection_surjective d s
  obtain ⟨y, rfl⟩ := hz
  rw [selectedSylowAction_on_selected]
  exact ⟨_, rfl⟩


/-- The selected subgroup is the full inverse image of the selected cubic line,
inside the genuine quotient Y/O₂(Y). -/
theorem selectedThreeSubgroup_preimage (d : CharacteristicTwo.LocalData G)
    (hsecond : OutsideStructure.SecondChoice d)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hodd : IsPGroup 3 (d.Y ⧸ pCore 2 d.Y)) :
    (selectedThreeSubgroup d).comap (QuotientGroup.mk' (pCore 2 d.Y)) =
      (d.Y ⊓ centralizer (d.V₁ : Set G)).subgroupOf d.Y := by
  have hk : pCore 2 d.Y ≤ (d.Yplus ⊔ d.Y.pCoreIn 2).subgroupOf d.Y := by
    rw [supplement_subgroupOf]
    exact le_sup_right
  rw [selected_range_supplement, comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hk,
    second_choice_core_supplement d hsecond h7image hodd]

/-- The natural image of S is the actual elementary four-group. -/
theorem selectedSylowImage_elementary (d : CharacteristicTwo.LocalData G) :
    IsElementaryAbelian 2 (d.action.image d.S) :=
  d.action.elementary_image_planeStabilizer d.T d.sylow_le 1

theorem selectedSylowImage_card (d : CharacteristicTwo.LocalData G) :
    Nat.card (d.action.image d.S) = 4 :=
  d.action.card_image_planeStabilizer d.T d.sylow_le 1

/-- Restrict the genuine quotient action to its selected invariant nine-group. -/
noncomputable def selectedPlaneAction (d : CharacteristicTwo.LocalData G)
    (hcore : (d.Y ⊔ (d.T : Subgroup G)).pCoreIn 2 =
      (d.T : Subgroup G) ⊓ centralizer (d.V : Set G)) :
    d.action.image d.S →* MulAut (selectedThreeSubgroup d) where
  toFun s :=
    { toFun z := ⟨selectedSylowAction d hcore s z,
        selectedSylowAction_stable d hcore s z z.property⟩
      invFun z := ⟨selectedSylowAction d hcore s⁻¹ z,
        selectedSylowAction_stable d hcore s⁻¹ z z.property⟩
      left_inv z := by apply Subtype.ext; simp
      right_inv z := by apply Subtype.ext; simp
      map_mul' z w := by apply Subtype.ext; exact map_mul _ _ _ }
  map_one' := by ext z; simp
  map_mul' s t := by
    ext z
    exact congrArg (fun a : MulAut (d.Y ⧸ pCore 2 d.Y) => a z)
      (map_mul (selectedSylowAction d hcore) s t)

/-- Every nonidentity element fixing the center is an involution whose fixed
subgroup in the extraspecial group is exactly the center. Hence no such
element can fix the selected subgroup of order nine. -/
theorem selectedPlaneAction_injective (d : CharacteristicTwo.LocalData G)
    (hsecond : OutsideStructure.SecondChoice d)
    (hcore : (d.Y ⊔ (d.T : Subgroup G)).pCoreIn 2 =
      (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h : ExtraspecialCase d.M d.Y d.V) : Function.Injective (selectedPlaneAction d hcore) := by
  let _ := h.extraspecial
  let _ := selectedSylowImage_elementary d
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro s hs
  by_contra hne
  have hne' : selectedSylowAction d hcore s ≠ 1 := by
    intro he
    exact hne ((selectedSylowAction_injective d hcore h7image h)
      (he.trans (map_one _).symm))
  have hinvol : Function.Involutive (selectedSylowAction d hcore s) := by
    have hh : s ^ 2 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 _) s
    have he := congrArg (selectedSylowAction d hcore) hh
    rw [map_pow, map_one, pow_two] at he
    intro z
    exact congrArg (fun a : MulAut (d.Y ⧸ pCore 2 d.Y) => a z) he
  have hfix (z : selectedThreeSubgroup d) : selectedSylowAction d hcore s z = z :=
    congrArg Subtype.val (DFunLike.congr_fun (show selectedPlaneAction d hcore s = 1 from hs) z)
  have hZ : ∀ z ∈ center (d.Y ⧸ pCore 2 d.Y), selectedSylowAction d hcore s z = z := by
    intro z hz
    exact hfix ⟨z, center_le_selectedThreeSubgroup d hsecond h7image h hz⟩
  have he := MulAut.fixed_eq_center_of_extraspecial27_involution h.quotient_card
    (selectedSylowAction d hcore s) hinvol hne' hZ
  have hle : selectedThreeSubgroup d ≤ center (d.Y ⧸ pCore 2 d.Y) := by
    intro z hz
    exact he.le ((MulAut.mem_fixedSubgroup _ _).mpr (hfix ⟨z, hz⟩))
  have hh := card_le_of_le hle
  rw [selectedThreeSubgroup_card d hsecond h7image h, IsExtraspecial.center_order_p 3 _] at hh
  omega

/-- The central line is not fixed pointwise by the full actual S-image. -/
theorem selectedSylowAction_nontrivial_center (d : CharacteristicTwo.LocalData G)
    (hcore : (d.Y ⊔ (d.T : Subgroup G)).pCoreIn 2 =
      (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h : ExtraspecialCase d.M d.Y d.V) :
    ∃ s : d.action.image d.S, ∃ z ∈ center (d.Y ⧸ pCore 2 d.Y),
      selectedSylowAction d hcore s z ≠ z := by
  let _ := h.extraspecial
  let _ := selectedSylowImage_elementary d
  by_contra hn
  push Not at hn
  have hb := MulAut.elementary_two_center_preserving_card_le_two h.quotient_card
    (selectedSylowAction d hcore) (selectedSylowAction_injective d hcore h7image h) hn
  rw [selectedSylowImage_card] at hb
  omega


/-- The marked central line inside the selected elementary-nine subgroup. -/
noncomputable def selectedCentralLine (d : CharacteristicTwo.LocalData G) :
    Subgroup (selectedThreeSubgroup d) :=
  (center (d.Y ⧸ pCore 2 d.Y)).subgroupOf (selectedThreeSubgroup d)

theorem selectedCentralLine_card (d : CharacteristicTwo.LocalData G)
    (hsecond : OutsideStructure.SecondChoice d)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h : ExtraspecialCase d.M d.Y d.V) : Nat.card (selectedCentralLine d) = 3 := by
  let _ := h.extraspecial
  exact (Nat.card_congr (subgroupOfEquivOfLe
    (center_le_selectedThreeSubgroup d hsecond h7image h)).toEquiv).trans
    (IsExtraspecial.center_order_p 3 _)

/-- The restricted action preserves the actual central line. -/
theorem selectedCentralLine_stable (d : CharacteristicTwo.LocalData G)
    (hcore : (d.Y ⊔ (d.T : Subgroup G)).pCoreIn 2 =
      (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (s : d.action.image d.S) (z : selectedThreeSubgroup d) (hz : z ∈ selectedCentralLine d) :
    selectedPlaneAction d hcore s z ∈ selectedCentralLine d := by
  change selectedSylowAction d hcore s z ∈ center (d.Y ⧸ pCore 2 d.Y)
  rw [mem_center_iff]
  intro w
  obtain ⟨v, rfl⟩ := (selectedSylowAction d hcore s).surjective w
  simpa only [map_mul, Subgroup.subtype_apply] using congrArg (selectedSylowAction d hcore s)
    (mem_center_iff.mp hz v)

end CFSG.Quasithin.Chapter15.Section03.OutsideStructure.LocalBranches.QuotientTheta

end

module

public import Theory.SpecificGroups.ReeTwo.ParabolicIndexTwo.Derived
public import Theory.SpecificGroups.ReeTwo.ParabolicQuotientAction
public import Theory.ElementaryAbelian.Quotient

/-!
# Quotient actions of the three index-two Ree local kernels

For each kernel L, this module uses its intrinsic two-core Q = O₂(L) and
F = C_Q(Q'). In the core-character and mixed-character kernels, F = Q' has
order 32; in the parity kernel, F has order 64. All three quotients Q/F are
elementary abelian of order sixteen, and their actual conjugation actions by
L have no nontrivial proper invariant subgroup.

The inclusion of omega into the full coordinate core induces a surjection
onto Core/C_Core(Core'): the intersection calculation gives its kernel and
the generation calculation gives surjectivity. The marked two-core
isomorphisms then identify each intrinsic quotient with this same quotient.
Their inclusion formulas prove compatibility with conjugation. Consequently
the specified five-element still acts with order five, proving irreducibility.
The centralizer comparison also explicitly relates the intrinsic convention
to centralizing the derived subgroup as embedded in L.

These are unconditional statements about the three concrete kernels; the
only selector for the two alternative kernels is their defining character.
Ambient Ree or Tits parabolic identification belongs to the consuming result.
Sources: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma 14.2.21, printed p.989 (PDF p.1006); Aschbacher, *The Tits group as a
standard subgroup* (1982), Section 3, via the verified coordinate calculations
in `CoreOmegaDerived` and the actual action in `ParabolicQuotientAction`.
-/

@[expose] public section

open Subgroup
namespace ReeTwo.Centralizer.IndexTwo

private theorem derived_map_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (commutator A).map e.toMonoidHom = commutator B := by
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
  rfl

private theorem centralizer_derived_map_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) :
    (centralizer (commutator A : Set A)).map e.toMonoidHom =
      centralizer (commutator B : Set B) := by
  rw [← derived_map_equiv e]
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)

/-- The centralizer of the derived subgroup inside the intrinsic two-core. -/
abbrev derivedCentralizer (L : Subgroup Centralizer) : Subgroup (pCore 2 L) :=
  centralizer (commutator (pCore 2 L) : Set (pCore 2 L))

/-- The intrinsic quotient O₂(L)/C_O₂(L)(O₂(L)'). -/
abbrev CoreQuotient (L : Subgroup Centralizer) :=
  pCore 2 L ⧸ derivedCentralizer L

/-- Conjugation by the local group on its intrinsic normal two-core. -/
def intrinsicCoreConjugation (L : Subgroup Centralizer) : L →* MulAut (pCore 2 L) :=
  MulAut.conjNormal

/-- The intrinsic core action is literal conjugation in the local group. -/
theorem intrinsicCoreConjugation_val (L : Subgroup Centralizer) (g : L) (x : pCore 2 L) :
    (intrinsicCoreConjugation L g x : L) = g * (x : L) * g⁻¹ := rfl

/-- The induced conjugation action on the intrinsic derived-centralizer quotient. -/
def intrinsicQuotientAction (L : Subgroup Centralizer) : L →* MulAut (CoreQuotient L) :=
  (quotientAut (derivedCentralizer L)).comp (intrinsicCoreConjugation L)

/-- The intrinsic quotient action is induced by the core action on representatives. -/
theorem intrinsicQuotientAction_mk (L : Subgroup Centralizer) (g : L) (x : pCore 2 L) :
    intrinsicQuotientAction L g (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' _ (intrinsicCoreConjugation L g x) :=
  quotientAut_apply_mk _ _ _

/-- The actual omega inclusion followed by the full core quotient map. -/
def omegaProjection : omega₁ Core (p := 2) →*
    (Core ⧸ centralizer (commutator Core : Set Core)) :=
  (QuotientGroup.mk' _).comp (omega₁ Core (p := 2)).subtype

/-- The inclusion's quotient kernel is the intrinsic derived centralizer of omega. -/
theorem omegaProjection_ker : omegaProjection.ker =
    centralizer (commutator (omega₁ Core (p := 2)) : Set (omega₁ Core (p := 2))) := by
  rw [Core.omega_centralizer_derived, Core.omega_derived_eq]
  ext x
  change QuotientGroup.mk' (centralizer (commutator Core : Set Core)) (x : Core) = 1 ↔
    (x : Core) ∈ commutator Core
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro hx
    exact Core.omega_inf_centralizer_derived ▸ ⟨x.property, hx⟩
  · intro hx
    exact (show (x : Core) ∈ omega₁ Core (p := 2) ⊓
      centralizer (commutator Core : Set Core) from
        Core.omega_inf_centralizer_derived.symm ▸ hx).2

/-- Omega surjects onto the full core quotient because it supplements the centralizer. -/
theorem omegaProjection_surjective : Function.Surjective omegaProjection := by
  apply MonoidHom.range_eq_top.mp
  rw [omegaProjection, MonoidHom.range_comp, range_subtype]
  have h := congrArg
    (fun H : Subgroup Core => H.map (QuotientGroup.mk'
      (centralizer (commutator Core : Set Core)))) Core.omega_sup_centralizer_derived
  simpa only [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq,
    map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using h

/-- The quotient isomorphism induced by the actual inclusion of omega into Core. -/
noncomputable def omegaQuotientEquiv :
    (omega₁ Core (p := 2) ⧸
      centralizer (commutator (omega₁ Core (p := 2)) : Set (omega₁ Core (p := 2)))) ≃*
        (Core ⧸ centralizer (commutator Core : Set Core)) :=
  (QuotientGroup.quotientMulEquivOfEq omegaProjection_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective omegaProjection omegaProjection_surjective)

/-- The omega quotient comparison preserves the actual core representative. -/
theorem omegaQuotientEquiv_mk (x : omega₁ Core (p := 2)) :
    omegaQuotientEquiv (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ (x : Core) := rfl

/-- The intrinsic alternative quotient identified through the marked omega inclusion. -/
noncomputable def alternativeCoreQuotientEquiv (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) :
    CoreQuotient χ.ker ≃* (Core ⧸ centralizer (commutator Core : Set Core)) :=
  (QuotientGroup.congr _ _ (omegaEquiv χ hχ).symm
    (by exact centralizer_derived_map_equiv (omegaEquiv χ hχ).symm)).trans omegaQuotientEquiv

/-- The alternative quotient comparison uses the specified omega coordinates. -/
theorem alternativeCoreQuotientEquiv_mk (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) (x : pCore 2 χ.ker) :
    alternativeCoreQuotientEquiv χ hχ (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' _ ((omegaEquiv χ hχ).symm x : Core) := rfl

/-- The intrinsic parity quotient identified through the marked full-core inclusion. -/
noncomputable def parityCoreQuotientEquiv :
    CoreQuotient parityLocal ≃* (Core ⧸ centralizer (commutator Core : Set Core)) :=
  QuotientGroup.congr _ _ parityCoreEquiv.symm
    (by exact centralizer_derived_map_equiv parityCoreEquiv.symm)

/-- The parity quotient comparison uses the specified core coordinates. -/
theorem parityCoreQuotientEquiv_mk (x : pCore 2 parityLocal) :
    parityCoreQuotientEquiv (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' _ (parityCoreEquiv.symm x) := rfl

/-- Recovering omega coordinates preserves the inclusion into the full local model. -/
theorem omegaEquiv_symm_val (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) (x : pCore 2 χ.ker) :
    (SemidirectProduct.inl ((omegaEquiv χ hχ).symm x : Core) : Centralizer) = x := by
  rw [← omegaEquiv_val χ hχ, (omegaEquiv χ hχ).apply_symm_apply]

/-- Recovering parity-core coordinates preserves the full local inclusion. -/
theorem parityCoreEquiv_symm_val (x : pCore 2 parityLocal) :
    (SemidirectProduct.inl (parityCoreEquiv.symm x) : Centralizer) = x := by
  rw [← parityCoreEquiv_val, parityCoreEquiv.apply_symm_apply]

/-- The marked alternative-core coordinates intertwine intrinsic and model conjugation. -/
theorem alternative_coreConjugation_intertwine (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) (g : χ.ker) (x : pCore 2 χ.ker) :
    ((omegaEquiv χ hχ).symm (intrinsicCoreConjugation χ.ker g x) : Core) =
      coreConjugation g ((omegaEquiv χ hχ).symm x : Core) := by
  apply SemidirectProduct.inl_injective (φ := Core.complement.subtype)
  rw [omegaEquiv_symm_val, inl_coreConjugation, omegaEquiv_symm_val]
  rfl

/-- The marked parity-core coordinates intertwine intrinsic and model conjugation. -/
theorem parity_coreConjugation_intertwine (g : parityLocal) (x : pCore 2 parityLocal) :
    parityCoreEquiv.symm (intrinsicCoreConjugation parityLocal g x) =
      coreConjugation g (parityCoreEquiv.symm x) := by
  apply SemidirectProduct.inl_injective (φ := Core.complement.subtype)
  rw [parityCoreEquiv_symm_val, inl_coreConjugation, parityCoreEquiv_symm_val]
  rfl

/-- The alternative quotient isomorphism intertwines the actual local actions. -/
theorem alternative_quotientAction_intertwine (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) (g : χ.ker) (v : CoreQuotient χ.ker) :
    alternativeCoreQuotientEquiv χ hχ (intrinsicQuotientAction χ.ker g v) =
      quotientAction g (alternativeCoreQuotientEquiv χ hχ v) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (derivedCentralizer χ.ker) v
  rw [intrinsicQuotientAction_mk, alternativeCoreQuotientEquiv_mk,
    alternativeCoreQuotientEquiv_mk, alternative_coreConjugation_intertwine]
  exact (quotientAut_apply_mk _ _ _).symm

/-- The parity quotient isomorphism intertwines the actual local actions. -/
theorem parity_quotientAction_intertwine (g : parityLocal) (v : CoreQuotient parityLocal) :
    parityCoreQuotientEquiv (intrinsicQuotientAction parityLocal g v) =
      quotientAction g (parityCoreQuotientEquiv v) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (derivedCentralizer parityLocal) v
  rw [intrinsicQuotientAction_mk, parityCoreQuotientEquiv_mk,
    parityCoreQuotientEquiv_mk, parity_coreConjugation_intertwine]
  exact (quotientAut_apply_mk _ _ _).symm

/-- Intrinsic centralization agrees with centralizing the derived subgroup embedded in L. -/
theorem derivedCentralizer_eq_subgroupOf (L : Subgroup Centralizer) :
    derivedCentralizer L =
      (centralizer ((⁅pCore 2 L, pCore 2 L⁆ : Subgroup L) : Set L)).subgroupOf
        (pCore 2 L) := by
  rw [← Subgroup.map_subtype_commutator]
  ext x
  constructor
  · intro hx y hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact congrArg Subtype.val (hx z hz)
  · intro hx y hy
    exact Subtype.ext (hx (y : L) (mem_map_of_mem _ hy))

/-- In either alternative two-core the derived subgroup is self-centralizing. -/
theorem alternative_derivedCentralizer (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) :
    derivedCentralizer χ.ker = commutator (pCore 2 χ.ker) := by
  apply Subgroup.map_injective (f := (omegaEquiv χ hχ).symm.toMonoidHom)
    (omegaEquiv χ hχ).symm.injective
  rw [centralizer_derived_map_equiv, derived_map_equiv, Core.omega_centralizer_derived]

/-- The intrinsic derived centralizer of either alternative two-core has order 32. -/
theorem alternative_derivedCentralizer_card (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) :
    Nat.card (derivedCentralizer χ.ker) = 32 := by
  rw [alternative_derivedCentralizer χ hχ]
  calc
    Nat.card (commutator (pCore 2 χ.ker)) =
        Nat.card ((commutator (pCore 2 χ.ker)).map (pCore 2 χ.ker).subtype) :=
      Nat.card_congr ((commutator (pCore 2 χ.ker)).equivMapOfInjective
        (pCore 2 χ.ker).subtype (pCore 2 χ.ker).subtype_injective).toEquiv
    _ = 32 := by
      rw [Subgroup.map_subtype_commutator]
      exact alternative_derived_card χ hχ

/-- The intrinsic derived centralizer of the parity two-core has order 64. -/
theorem parity_derivedCentralizer_card : Nat.card (derivedCentralizer parityLocal) = 64 := by
  calc
    Nat.card (derivedCentralizer parityLocal) =
        Nat.card ((derivedCentralizer parityLocal).map parityCoreEquiv.symm.toMonoidHom) :=
      Nat.card_congr ((derivedCentralizer parityLocal).equivMapOfInjective
        parityCoreEquiv.symm.toMonoidHom parityCoreEquiv.symm.injective).toEquiv
    _ = 64 := by
      rw [centralizer_derived_map_equiv]
      exact Core.centralizer_derived_card

/-- The intrinsic quotient of either alternative two-core has order sixteen. -/
theorem alternative_coreQuotient_card (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) : Nat.card (CoreQuotient χ.ker) = 16 :=
  (Nat.card_congr (alternativeCoreQuotientEquiv χ hχ).toEquiv).trans
    Core.quotient_centralizer_derived_card

/-- The intrinsic quotient of the parity two-core has order sixteen. -/
theorem parity_coreQuotient_card : Nat.card (CoreQuotient parityLocal) = 16 :=
  (Nat.card_congr parityCoreQuotientEquiv.toEquiv).trans Core.quotient_centralizer_derived_card

/-- The intrinsic quotient of either alternative two-core is elementary abelian. -/
theorem alternative_coreQuotient_elementary (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) : IsElementaryAbelian 2 (CoreQuotient χ.ker) := by
  let : IsElementaryAbelian 2 (Core ⧸ centralizer (commutator Core : Set Core)) :=
    Core.quotient_centralizer_derived_elementary
  exact IsElementaryAbelian.of_surjective (alternativeCoreQuotientEquiv χ hχ).symm.toMonoidHom
    (alternativeCoreQuotientEquiv χ hχ).symm.surjective

/-- The intrinsic quotient of the parity two-core is elementary abelian. -/
theorem parity_coreQuotient_elementary : IsElementaryAbelian 2 (CoreQuotient parityLocal) := by
  let : IsElementaryAbelian 2 (Core ⧸ centralizer (commutator Core : Set Core)) :=
    Core.quotient_centralizer_derived_elementary
  exact IsElementaryAbelian.of_surjective parityCoreQuotientEquiv.symm.toMonoidHom
    parityCoreQuotientEquiv.symm.surjective

/-- The alternative action is conjugate, as a homomorphism, to the restricted model action. -/
theorem alternative_quotientAction_congr (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) :
    (MulAut.congr (alternativeCoreQuotientEquiv χ hχ)).toMonoidHom.comp
        (intrinsicQuotientAction χ.ker) = quotientAction.comp χ.ker.subtype := by
  apply MonoidHom.ext
  intro g
  apply MulEquiv.ext
  intro v
  obtain ⟨x, rfl⟩ := (alternativeCoreQuotientEquiv χ hχ).surjective v
  change alternativeCoreQuotientEquiv χ hχ (intrinsicQuotientAction χ.ker g
    ((alternativeCoreQuotientEquiv χ hχ).symm (alternativeCoreQuotientEquiv χ hχ x))) = _
  rw [(alternativeCoreQuotientEquiv χ hχ).symm_apply_apply]
  exact alternative_quotientAction_intertwine χ hχ g x

/-- The parity action is conjugate, as a homomorphism, to the restricted model action. -/
theorem parity_quotientAction_congr :
    (MulAut.congr parityCoreQuotientEquiv).toMonoidHom.comp
        (intrinsicQuotientAction parityLocal) = quotientAction.comp parityLocal.subtype := by
  apply MonoidHom.ext
  intro g
  apply MulEquiv.ext
  intro v
  obtain ⟨x, rfl⟩ := parityCoreQuotientEquiv.surjective v
  change parityCoreQuotientEquiv (intrinsicQuotientAction parityLocal g
    (parityCoreQuotientEquiv.symm (parityCoreQuotientEquiv x))) = _
  rw [parityCoreQuotientEquiv.symm_apply_apply]
  exact parity_quotientAction_intertwine g x

/-- Every alternative actor has the same image order in the intrinsic and model actions. -/
theorem alternative_quotientAction_order (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) (g : χ.ker) :
    orderOf (intrinsicQuotientAction χ.ker g) = orderOf (quotientAction g) := by
  have h := DFunLike.congr_fun (alternative_quotientAction_congr χ hχ) g
  exact (orderOf_injective (MulAut.congr (alternativeCoreQuotientEquiv χ hχ)).toMonoidHom
    (MulAut.congr (alternativeCoreQuotientEquiv χ hχ)).injective _).symm.trans
      (congrArg orderOf h)

/-- Every parity actor has the same image order in the intrinsic and model actions. -/
theorem parity_quotientAction_order (g : parityLocal) :
    orderOf (intrinsicQuotientAction parityLocal g) = orderOf (quotientAction g) := by
  have h := DFunLike.congr_fun parity_quotientAction_congr g
  exact (orderOf_injective (MulAut.congr parityCoreQuotientEquiv).toMonoidHom
    (MulAut.congr parityCoreQuotientEquiv).injective _).symm.trans (congrArg orderOf h)

/-- The specified five-element acts with order five in both alternative kernels. -/
theorem alternative_quotientAction_five_order (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) :
    orderOf (intrinsicQuotientAction χ.ker ⟨fiveGenerator, alternative_five_mem χ hχ⟩) = 5 :=
  (alternative_quotientAction_order χ hχ _).trans quotientAction_five_order

/-- The specified five-element acts with order five in the parity kernel. -/
theorem parity_quotientAction_five_order :
    orderOf (intrinsicQuotientAction parityLocal ⟨fiveGenerator, character_fiveGenerator⟩) = 5 :=
  (parity_quotientAction_order _).trans quotientAction_five_order

/-- The intrinsic alternative action image has order divisible by five. -/
theorem alternative_five_dvd_quotientAction_range (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) :
    5 ∣ Nat.card (intrinsicQuotientAction χ.ker).range := by
  have h := orderOf_dvd_natCard ((intrinsicQuotientAction χ.ker).rangeRestrict
    ⟨fiveGenerator, alternative_five_mem χ hχ⟩)
  rw [← Subgroup.orderOf_coe] at h
  exact alternative_quotientAction_five_order χ hχ ▸ h

/-- The intrinsic parity action image has order divisible by five. -/
theorem parity_five_dvd_quotientAction_range :
    5 ∣ Nat.card (intrinsicQuotientAction parityLocal).range := by
  have h := orderOf_dvd_natCard ((intrinsicQuotientAction parityLocal).rangeRestrict
    ⟨fiveGenerator, character_fiveGenerator⟩)
  rw [← Subgroup.orderOf_coe] at h
  exact parity_quotientAction_five_order ▸ h

/-- The actual intrinsic quotient action of either alternative kernel is irreducible. -/
theorem alternative_quotientAction_invariant_subgroup (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) (D : Subgroup (CoreQuotient χ.ker))
    (hD : ∀ g : χ.ker, ∀ v, v ∈ D ↔ intrinsicQuotientAction χ.ker g v ∈ D) :
    D = ⊥ ∨ D = ⊤ :=
  Theory.GroupAction.invariant_eq_bot_or_top_of_image_five (intrinsicQuotientAction χ.ker)
    (alternative_five_dvd_quotientAction_range χ hχ) (alternative_coreQuotient_card χ hχ) D hD

/-- The actual intrinsic quotient action of the parity kernel is irreducible. -/
theorem parity_quotientAction_invariant_subgroup (D : Subgroup (CoreQuotient parityLocal))
    (hD : ∀ g : parityLocal, ∀ v, v ∈ D ↔ intrinsicQuotientAction parityLocal g v ∈ D) :
    D = ⊥ ∨ D = ⊤ :=
  Theory.GroupAction.invariant_eq_bot_or_top_of_image_five (intrinsicQuotientAction parityLocal)
    parity_five_dvd_quotientAction_range parity_coreQuotient_card D hD

end ReeTwo.Centralizer.IndexTwo

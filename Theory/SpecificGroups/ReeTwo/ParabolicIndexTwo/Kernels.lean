module

public import Theory.SpecificGroups.ReeTwo.ParabolicCoreStructure
public import Theory.SpecificGroups.ReeTwo.CoreOmegaDerived

/-!
# The three concrete index-two Ree local kernels

The parity, core-character and mixed-character kernels are treated as literal
subgroups of `ReeTwo.Centralizer`. Normality identifies their intrinsic two-cores
with their intersections with the full core. The latter two intersections are
the embedded omega subgroup of order 512; the parity kernel retains all 1024
core elements. Compatible complement projections identify the alternative
quotients with the specified faithful C5:C4 group, and the parity quotient with
its actual even-coordinate subgroup of order ten. A core root power supplies
the character correction needed for surjectivity in both alternative cases.

These are local-model calculations, not ambient Tits-parabolic identifications.
In particular the order-512/order-20 pair must be kept distinct from the
order-1024/order-10 pair. The latter quotient is not recognized here by order.
Sources: Aschbacher--Smith, quasithin Lemma 14.2.21, printed p.989;
Aschbacher (1982), Section 3; Parrott (1972), printed p.672. The proofs use the
verified Shinoda root coordinates and the intrinsic omega calculation.
-/

@[expose] public section
open Subgroup
namespace ReeTwo.Centralizer.IndexTwo

/-- The kernel of complement parity in the concrete local group. -/
noncomputable abbrev parityLocal := character.ker
/-- The kernel of the binary core character in the concrete local group. -/
abbrev coreLocal := coreCharacter.ker
/-- The kernel of the product of core character and complement parity. -/
noncomputable abbrev mixedLocal := mixedCharacter.ker

/-- The actual embedded first omega subgroup of the ten-root core. -/
def omega : Subgroup Centralizer :=
  (omega₁ Core (p := 2)).map (SemidirectProduct.inl : Core →* Centralizer)

/-- In a normal local subgroup, the intrinsic two-core is its intersection with the full core. -/
theorem core_subgroupOf_eq_pCore (L : Subgroup Centralizer) [L.Normal] :
    core.subgroupOf L = pCore 2 L := by
  rw [core_eq_pCore]
  apply le_antisymm
  · exact le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩
  · have hn : ((pCore 2 L).map L.subtype).Normal := inferInstance
    have hm : (pCore 2 L).map L.subtype ≤ pCore 2 Centralizer :=
      le_sSup ⟨hn, pCore_isPGroup.map L.subtype⟩
    exact Subgroup.map_le_iff_le_comap.mp hm

/-- Complement parity is trivial on the core inclusion. -/
@[simp] theorem character_inl (x : Core) :
    character (SemidirectProduct.inl x : Centralizer) = 1 := by
  simp [character]

/-- The extended core character restricts to the binary core character. -/
@[simp] theorem coreCharacter_inl (x : Core) :
    coreCharacter (SemidirectProduct.inl x : Centralizer) = Core.binaryCharacter x := rfl

/-- The mixed character also restricts to the binary core character. -/
@[simp] theorem mixedCharacter_inl (x : Core) :
    mixedCharacter (SemidirectProduct.inl x : Centralizer) = Core.binaryCharacter x := by
  simp [mixedCharacter]

/-- The two alternative characters have the same restriction to the core. -/
theorem alternative_inl (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) (x : Core) :
    χ (SemidirectProduct.inl x) = Core.binaryCharacter x := by
  rcases hχ with rfl | rfl <;> simp

/-- The parity kernel retains the entire ten-root core. -/
theorem core_le_parityLocal : core ≤ parityLocal := by
  rintro x ⟨y,rfl⟩
  exact character_inl y

/-- Both alternative kernels contain the actual embedded omega subgroup. -/
theorem omega_le_kernel (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) : omega ≤ χ.ker := by
  rintro x ⟨y,hy,rfl⟩
  change χ (SemidirectProduct.inl y) = 1
  rw [alternative_inl χ hχ, ← MonoidHom.mem_ker, Core.binaryCharacter_ker_eq_omega]
  exact hy

/-- Intersecting either alternative kernel with the full core gives exactly omega. -/
theorem core_inf_kernel (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) : core ⊓ χ.ker = omega := by
  apply le_antisymm
  · rintro x ⟨⟨y,rfl⟩,hy⟩
    refine ⟨y,?_,rfl⟩
    rw [← Core.binaryCharacter_ker_eq_omega]
    exact (alternative_inl χ hχ y).symm.trans hy
  · exact le_inf (Subgroup.map_le_range _ _) (omega_le_kernel χ hχ)

/-- The intrinsic two-core of either alternative kernel is the embedded omega subgroup. -/
theorem alternative_pCore (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) :
    pCore 2 χ.ker = omega.subgroupOf χ.ker := by
  rw [← core_subgroupOf_eq_pCore, ← core_inf_kernel χ hχ]
  ext x
  exact ⟨fun h => ⟨h,x.property⟩, fun h => h.1⟩

/-- The marked inclusion of the order-512 omega group into either alternative kernel. -/
def omegaInclusion (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) :
    omega₁ Core (p := 2) →* χ.ker :=
  ((SemidirectProduct.inl : Core →* Centralizer).comp
    (omega₁ Core (p := 2)).subtype).codRestrict χ.ker
      (fun x => omega_le_kernel χ hχ (Subgroup.mem_map_of_mem _ x.property))

/-- The marked omega inclusion is injective. -/
theorem omegaInclusion_injective (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) :
    Function.Injective (omegaInclusion χ hχ) := by
  intro x y h
  exact Subtype.ext (SemidirectProduct.inl_injective (congrArg Subtype.val h))

/-- The marked omega inclusion has exactly the intrinsic two-core as its range. -/
theorem omegaInclusion_range (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) :
    (omegaInclusion χ hχ).range = pCore 2 χ.ker := by
  rw [alternative_pCore χ hχ]
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact Subgroup.mem_map_of_mem _ y.property
  · rintro ⟨y,hy,he⟩
    exact ⟨⟨y,hy⟩,Subtype.ext he⟩

/-- The intrinsic alternative two-core identified by its actual inclusion of core coordinates. -/
noncomputable def omegaEquiv (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) :
    omega₁ Core (p := 2) ≃* pCore 2 χ.ker :=
  (MonoidHom.ofInjective (omegaInclusion_injective χ hχ)).trans
    (MulEquiv.subgroupCongr (omegaInclusion_range χ hχ))

/-- Each alternative kernel has two-core of order 512. -/
theorem alternative_pCore_card (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) : Nat.card (pCore 2 χ.ker) = 512 :=
  (Nat.card_congr (omegaEquiv χ hχ).symm.toEquiv).trans Core.omega_card

/-- Projection to the specified five-by-four complement, with its existing model equivalence. -/
noncomputable def projection : Centralizer →* FiveFour.Group :=
  Core.complementEquiv.symm.toMonoidHom.comp SemidirectProduct.rightHom

/-- The complement projection kills the core inclusion. -/
@[simp] theorem projection_inl (x : Core) : projection (SemidirectProduct.inl x) = 1 := by
  simp [projection]

/-- On the complement inclusion the projection is the specified complement equivalence. -/
@[simp] theorem projection_inr (t : Core.complement) :
    projection (SemidirectProduct.inr t) = Core.complementEquiv.symm t := rfl

/-- The complement projection has precisely the full core as its kernel. -/
theorem projection_ker : projection.ker = core := by
  ext x
  change Core.complementEquiv.symm x.right = 1 ↔ x ∈ core
  rw [Core.complementEquiv.symm.map_eq_one_iff]
  change x ∈ (SemidirectProduct.rightHom (φ := Core.complement.subtype)).ker ↔ x ∈ core
  rw [← SemidirectProduct.range_inl_eq_ker_rightHom]
  rfl

/-- Restriction of the compatible complement projection to a local subgroup. -/
noncomputable def localProjection (L : Subgroup Centralizer) : L →* FiveFour.Group :=
  projection.comp L.subtype

/-- For a normal local subgroup the restricted projection has its intrinsic two-core as kernel. -/
theorem localProjection_ker (L : Subgroup Centralizer) [L.Normal] :
    (localProjection L).ker = pCore 2 L := by
  rw [localProjection, ← MonoidHom.comap_ker, projection_ker]
  exact core_subgroupOf_eq_pCore L

/-- A root-5 power corrects the character without changing the complement coordinate. -/
theorem alternative_projection_surjective (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) :
    Function.Surjective (localProjection χ.ker) := by
  intro t
  let g : Centralizer := SemidirectProduct.inr (Core.complementEquiv t)
  let x : Core := Core.root 2 ^ (χ g).toAdd.val
  have hx : Core.binaryCharacter x = χ g :=
    (by decide +kernel : ∀ v : FiveFour.Cyclic 2,
      Core.binaryCharacter (Core.root 2 ^ v.toAdd.val) = v) _
  have hg : SemidirectProduct.inl x * g ∈ χ.ker := by
    change χ (SemidirectProduct.inl x * g) = 1
    rw [map_mul, alternative_inl χ hχ, hx]
    exact (by decide : ∀ v : FiveFour.Cyclic 2, v*v=1) _
  refine ⟨⟨SemidirectProduct.inl x * g,hg⟩,?_⟩
  change projection (SemidirectProduct.inl x * g) = t
  rw [map_mul, projection_inl, one_mul, projection_inr, Core.complementEquiv.symm_apply_apply]

/-- The actual quotient by the alternative two-core is the specified faithful five-by-four group. -/
noncomputable def alternativeQuotientEquiv (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) :
    (χ.ker ⧸ pCore 2 χ.ker) ≃* FiveFour.Group :=
  (QuotientGroup.quotientMulEquivOfEq (localProjection_ker χ.ker).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (alternative_projection_surjective χ hχ))

/-- Each alternative two-core quotient has order twenty, by the compatible isomorphism. -/
theorem alternative_quotient_card (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) :
    Nat.card (χ.ker ⧸ pCore 2 χ.ker) = 20 :=
  (Nat.card_congr (alternativeQuotientEquiv χ hχ).toEquiv).trans FiveFour.card


/-- The marked inclusion of the full ten-root core into the parity kernel. -/
noncomputable def parityCoreInclusion : Core →* parityLocal :=
  (SemidirectProduct.inl : Core →* Centralizer).codRestrict parityLocal
    (fun x => character_inl x)

/-- The marked full-core inclusion into the parity kernel is injective. -/
theorem parityCoreInclusion_injective : Function.Injective parityCoreInclusion := by
  intro x y h
  exact SemidirectProduct.inl_injective (congrArg Subtype.val h)

/-- The full-core inclusion has the intrinsic parity two-core as its range. -/
theorem parityCoreInclusion_range : parityCoreInclusion.range = pCore 2 parityLocal := by
  rw [← core_subgroupOf_eq_pCore]
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact ⟨y,rfl⟩
  · rintro ⟨y,hy⟩
    exact ⟨y,Subtype.ext hy⟩

/-- The parity two-core identified with the full coordinate core by its actual inclusion. -/
noncomputable def parityCoreEquiv : Core ≃* pCore 2 parityLocal :=
  (MonoidHom.ofInjective parityCoreInclusion_injective).trans
    (MulEquiv.subgroupCongr parityCoreInclusion_range)

/-- The parity kernel has two-core of order 1024. -/
theorem parity_pCore_card : Nat.card (pCore 2 parityLocal) = 1024 :=
  (Nat.card_congr parityCoreEquiv.symm.toEquiv).trans Core.card

/-- Parity of the cyclic-four coordinate in the specified five-by-four group. -/
def parityComplementCharacter : FiveFour.Group →* FiveFour.Cyclic 2 :=
  SylowModel.parity.comp SemidirectProduct.rightHom

/-- The actual even-coordinate subgroup of the specified five-by-four group. -/
abbrev parityComplement := parityComplementCharacter.ker

/-- The compatible projection of the parity kernel onto the even-coordinate complement. -/
noncomputable def parityProjection : parityLocal →* parityComplement :=
  (localProjection parityLocal).codRestrict parityComplement (fun x => x.property)

/-- Every even complement element lifts to the parity kernel by the complement inclusion. -/
theorem parityProjection_surjective : Function.Surjective parityProjection := by
  intro t
  have ht : (SemidirectProduct.inr (Core.complementEquiv t) : Centralizer) ∈ parityLocal := by
    change SylowModel.parity (Core.complementEquiv.symm (Core.complementEquiv t)).right = 1
    rw [Core.complementEquiv.symm_apply_apply]
    exact t.property
  refine ⟨⟨SemidirectProduct.inr (Core.complementEquiv t),ht⟩,?_⟩
  apply Subtype.ext
  exact Core.complementEquiv.symm_apply_apply t

/-- The parity projection has the intrinsic parity two-core as kernel. -/
theorem parityProjection_ker : parityProjection.ker = pCore 2 parityLocal := by
  rw [← localProjection_ker]
  ext x
  exact Subtype.ext_iff

/-- The parity two-core quotient identified with the actual even-coordinate complement subgroup. -/
noncomputable def parityQuotientEquiv :
    (parityLocal ⧸ pCore 2 parityLocal) ≃* parityComplement :=
  (QuotientGroup.quotientMulEquivOfEq parityProjection_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ parityProjection_surjective)

/-- The even-coordinate complement has order ten. -/
theorem parityComplement_card : Nat.card parityComplement = 10 := by
  have hs : Function.Surjective parityComplementCharacter := by
    intro y
    refine ⟨SemidirectProduct.inr (FiveFour.generator 4 ^ y.toAdd.val),?_⟩
    exact (by decide +kernel : ∀ y : FiveFour.Cyclic 2,
      SylowModel.parity (FiveFour.generator 4 ^ y.toAdd.val) = y) y
  have hi : parityComplement.index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hs,
      Nat.card_congr Subgroup.topEquiv.toEquiv]
    change Nat.card (ZMod 2) = 2
    simp
  have h := parityComplement.index_mul_card
  rw [hi, FiveFour.card] at h
  omega

/-- The parity quotient has order ten, by the compatible subgroup isomorphism. -/
theorem parity_quotient_card : Nat.card (parityLocal ⧸ pCore 2 parityLocal) = 10 :=
  (Nat.card_congr parityQuotientEquiv.toEquiv).trans parityComplement_card

/-- Each alternative local group has order 10240. -/
theorem alternative_card (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) : Nat.card χ.ker = 10240 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 χ.ker),
    alternative_pCore_card χ hχ, alternative_quotient_card χ hχ]

/-- The parity local group has order 10240. -/
theorem parity_card : Nat.card parityLocal = 10240 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 parityLocal),
    parity_pCore_card, parity_quotient_card]

/-- Both alternative character kernels have index two in the full local group. -/
theorem alternative_index (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) : χ.ker.index = 2 := by
  have h := χ.ker.index_mul_card
  rw [alternative_card χ hχ, Centralizer.card] at h
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 10240) h

/-- The parity character kernel has index two in the full local group. -/
theorem parity_index : parityLocal.index = 2 := by
  have h := parityLocal.index_mul_card
  rw [parity_card, Centralizer.card] at h
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 10240) h

/-- The alternative quotient equivalence retains the original complement projection. -/
@[simp] theorem alternativeQuotientEquiv_mk (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) (x : χ.ker) :
    alternativeQuotientEquiv χ hχ (QuotientGroup.mk' _ x) = projection x := rfl

/-- The parity quotient equivalence retains the original restricted projection. -/
@[simp] theorem parityQuotientEquiv_mk (x : parityLocal) :
    parityQuotientEquiv (QuotientGroup.mk' _ x) = parityProjection x := rfl


/-- The specified five-element projects to the standard five-generator. -/
@[simp] theorem projection_fiveGenerator : projection fiveGenerator = FiveFour.c := by
  rw [fiveGenerator, projection_inr, ← Core.complementEquiv_a,
    ← Core.complementEquiv_r, ← map_pow, ← map_mul,
    Core.complementEquiv.symm_apply_apply]
  exact FiveFour.c_eq.symm

/-- The specified five-element belongs to the parity kernel. -/
@[simp] theorem character_fiveGenerator : character fiveGenerator = 1 := by
  change parityComplementCharacter (projection fiveGenerator) = 1
  rw [projection_fiveGenerator]
  exact map_one SylowModel.parity

/-- The specified five-element belongs to the core-character kernel. -/
@[simp] theorem coreCharacter_fiveGenerator : coreCharacter fiveGenerator = 1 :=
  Core.binaryCharacter.map_one

/-- The specified five-element belongs to the mixed-character kernel. -/
@[simp] theorem mixedCharacter_fiveGenerator : mixedCharacter fiveGenerator = 1 := by
  simp [mixedCharacter]

/-- Both alternative local groups contain the same specified five-element. -/
theorem alternative_five_mem (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) : fiveGenerator ∈ χ.ker := by
  rcases hχ with rfl | rfl
  · exact coreCharacter_fiveGenerator
  · exact mixedCharacter_fiveGenerator

/-- The intrinsic omega equivalence preserves the actual core inclusion. -/
@[simp] theorem omegaEquiv_val (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) (x : omega₁ Core (p := 2)) :
    (((omegaEquiv χ hχ x : pCore 2 χ.ker) : χ.ker) : Centralizer) =
      SemidirectProduct.inl (x : Core) := rfl

/-- The intrinsic parity-core equivalence preserves the actual core inclusion. -/
@[simp] theorem parityCoreEquiv_val (x : Core) :
    (((parityCoreEquiv x : pCore 2 parityLocal) : parityLocal) : Centralizer) =
      SemidirectProduct.inl x := rfl

end ReeTwo.Centralizer.IndexTwo

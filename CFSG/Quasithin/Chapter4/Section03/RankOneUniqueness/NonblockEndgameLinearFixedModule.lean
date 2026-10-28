module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameLinearSource
public import Theory.SpecificGroups.PSL3.LinearThreeRadicalCoordinates

/-!
# The natural module on the original cubic-fixed radical

The marked natural action sends the entire secondary radical R₂ onto the
point radical of SL₃, with kernel exactly Q. Affine coordinates therefore
identify R₂/Q with the additive plane and retain the original K₂ action.

For the source cubic X, the fixed complement C_R₂(X) maps injectively to
this plane. Its proved order sixteen makes this map an isomorphism.
Coprime lifting through O₂(K₂) shows that C_K₂(X) induces the full SL₂(4)
on it, with kernel the actual intersection with O₂(K₂). Two elementary
transvections then give C_R₂(K₂X)=1. Thus the natural fixed-module input
of the terminal linear-four argument is proved on the original groups.

The final application uses the same constructed X and the same PGL₃(4)
extension projection as `NonblockEndgameLinearSource`. Its exact kernel,
component marking and normalQuotientAction are retained. This does not
identify a PGL₃ module from its SL₃ restriction or discard the determinant
twist. Construction of MSData and the remaining secondary source geometry,
and exclusion of the actual extension representations, remain with
`qt-d-1222-rankone-uniqueness-nonblock`.

Source: Aschbacher--Smith, conclusion of original 4.3.2, pp.618--619;
F.1.12(I), pp.262--264, for the affine point-local coordinates.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups commutatorElement
open Matrix.PSL3.LinearThree
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ} {d : MSData c n}
namespace RootCoordinates
variable (m : RootCoordinates d) (hn : 1 < n)
  (D : Chapter12.Section02.ChosenModule T L V) (s : SecondarySourceData c n)

omit [Finite G] in
private theorem naturalAction_on_original (k : K c) :
    m.naturalAction ⟨k,mem_sup_left k.property⟩ = naturalAut (linearThreeActor d.model k) := by
  apply MulEquiv.ext
  intro v
  apply Multiplicative.toAdd.injective
  let u := m.coordinates.symm v
  have hnU : K c ⊔ S c ≤ normalizer (U c : Set G) :=
    ((sup_le (map_subtype_le _) inf_le_right).trans (core_normalized c)).trans
      (normalizer_le_normalizer_characteristic_image (Q c) (center (Q c)))
  let u' := (U c).normalizerMonoidHom ⟨k,hnU (mem_sup_left k.property)⟩ u
  have hh := m.compatible k u u' (normalizerMonoidHom_apply_apply_coe _ _ _)
  rw [show m.coordinates u = v from m.coordinates.apply_symm_apply v] at hh
  exact hh

/-- The original SL₃ marking restricted to the whole radical. -/
noncomputable def radicalOriginalActor : R₂ c →* SL(3,d.field.Carrier) :=
  (linearThreeActor d.model).comp (inclusion (m.radical_le_original hn D s.core_eq))

private theorem radicalOriginalActor_mem (r : R₂ c) :
    m.radicalOriginalActor hn D s r ∈
      (pointRadicalSL d.field.Carrier).map (pointLocalSL d.field.Carrier).subtype := by
  have hh := m.naturalAction_radical_le_rootPlane hn D
    (mem_map_of_mem (x := (⟨r,(radical_le_sylow c r.property |> mem_sup_right)⟩ :
      (K c ⊔ S c : Subgroup G))) m.naturalAction (show (⟨r,(radical_le_sylow c r.property |> mem_sup_right)⟩ :
      (K c ⊔ S c : Subgroup G)) ∈ (R₂ c).subgroupOf (K c ⊔ S c) from r.property))
  obtain ⟨g,hg,he⟩ := hh
  have ha := m.naturalAction_on_original
    ⟨r,m.radical_le_original hn D s.core_eq r.property⟩
  have hg' : g = m.radicalOriginalActor hn D s r :=
    naturalAut_injective (he.trans ha)
  exact hg' ▸ hg

/-- Coverage places the literal radical image in the point root plane. -/
noncomputable def radicalPoint : R₂ c →* pointRadicalSL d.field.Carrier := {
  toFun := fun r => ⟨⟨m.radicalOriginalActor hn D s r, by
    obtain ⟨v,hv,he⟩ := m.radicalOriginalActor_mem hn D s r
    exact he ▸ v.property⟩, by
    obtain ⟨v,hv,he⟩ := m.radicalOriginalActor_mem hn D s r
    exact (show v = ⟨m.radicalOriginalActor hn D s r,_⟩ from Subtype.ext he) ▸ hv⟩
  map_one' := by apply Subtype.ext; apply Subtype.ext; exact map_one _
  map_mul' _ _ := by apply Subtype.ext; apply Subtype.ext; exact map_mul _ _ _ }

/-- The additive plane coordinates of the whole secondary radical. -/
noncomputable def radicalCoordinates : R₂ c →* Multiplicative (Fin 2 → d.field.Carrier) :=
  (pointRadicalCoordinates d.field.Carrier).toMonoidHom.comp (m.radicalPoint hn D s)

/-- The coordinates kill exactly the original core Q. -/
theorem radicalCoordinates_ker : (m.radicalCoordinates hn D s).ker = (Q c).subgroupOf (R₂ c) := by
  rw [radicalCoordinates,MonoidHom.ker_comp_of_injective _ _
    (pointRadicalCoordinates d.field.Carrier).injective]
  ext r
  change m.radicalPoint hn D s r = 1 ↔ (r : G) ∈ Q c
  rw [s.core_eq_original]
  constructor
  · intro hr
    have ha : linearThreeActor d.model
        ⟨r,m.radical_le_original hn D s.core_eq r.property⟩ = 1 :=
      congrArg (fun z : pointRadicalSL d.field.Carrier => z.val.val) hr
    have hk : (⟨r,m.radical_le_original hn D s.core_eq r.property⟩ : K c) ∈ pCore 2 (K c) := by
      apply (QuotientGroup.eq_one_iff _).mp
      exact d.model.injective (ha.trans d.model.map_one.symm)
    exact mem_map_of_mem (K c).subtype hk
  · intro hr
    apply Subtype.ext
    apply Subtype.ext
    change linearThreeActor d.model ⟨r,m.radical_le_original hn D s.core_eq r.property⟩ = 1
    have hk : (⟨r,m.radical_le_original hn D s.core_eq r.property⟩ : K c) ∈ pCore 2 (K c) := by
      exact (mem_map_iff_mem (K c).subtype_injective).mp hr
    exact (congrArg d.model ((QuotientGroup.eq_one_iff _).mpr hk)).trans d.model.map_one

/-- The secondary two-core already supplies every point-radical element. -/
theorem radicalPoint_surjective : Function.Surjective (m.radicalPoint hn D s) := by
  intro v
  have hv : (v : pointLocalSL d.field.Carrier) ∈ pCore 2 (pointLocalSL d.field.Carrier) := by
    rw [pointLocalSL_twoCore_eq]
    exact v.property
  rw [←m.secondary_core_image hn] at hv
  obtain ⟨k,hk,hkv⟩ := hv
  let r : R₂ c := ⟨k,secondary_core_le_radical D (mem_map_of_mem _ hk)⟩
  refine ⟨r,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg Subtype.val hkv

/-- All vectors occur in the literal radical quotient. -/
theorem radicalCoordinates_surjective : Function.Surjective (m.radicalCoordinates hn D s) :=
  (pointRadicalCoordinates d.field.Carrier).surjective.comp (m.radicalPoint_surjective hn D s)

/-- The original point-local projection followed by its affine linear part. -/
noncomputable def secondaryLinear : secondary c →* SL(2,d.field.Carrier) :=
  (SemidirectProduct.rightHom : Matrix.SL2.Affine d.field.Carrier →* SL(2,d.field.Carrier)).comp
    ((pointLocalAffineEquiv d.field.Carrier).toMonoidHom.comp m.secondaryProjection)

include hn in
/-- The secondary action induces the full natural SL₂. -/
theorem secondaryLinear_surjective : Function.Surjective m.secondaryLinear :=
  SemidirectProduct.rightHom_surjective.comp
    ((pointLocalAffineEquiv d.field.Carrier).surjective.comp (m.secondaryProjection_surjective hn))

include hn in
/-- Its kernel is the intrinsic secondary two-core. -/
theorem secondaryLinear_ker : m.secondaryLinear.ker = pCore 2 (secondary c) := by
  change (((SemidirectProduct.rightHom : Matrix.SL2.Affine d.field.Carrier →*
    SL(2,d.field.Carrier)).comp (pointLocalAffineEquiv d.field.Carrier).toMonoidHom).comp
      m.secondaryProjection).ker = _
  rw [←MonoidHom.comap_ker]
  change (pointRadicalSL d.field.Carrier).comap m.secondaryProjection = _
  rw [←pointLocalSL_twoCore_eq]
  exact m.secondaryProjection.comap_pCore_of_ker_isPGroup
    (m.secondaryProjection_surjective hn) m.secondaryProjection_kernel

/-- Radical coordinates intertwine actual conjugation by the secondary group. -/
theorem radicalCoordinates_conjugate (k : secondary c) (r t : R₂ c)
    (ht : (t : G) = k * r * (k : G)⁻¹) :
    m.radicalCoordinates hn D s t = Matrix.SL2.naturalAction d.field.Carrier
      (m.secondaryLinear k) (m.radicalCoordinates hn D s r) := by
  apply pointRadicalCoordinates_conjugate
  apply Subtype.ext
  change linearThreeActor d.model ⟨t,_⟩ =
    linearThreeActor d.model ⟨k,_⟩ * linearThreeActor d.model ⟨r,_⟩ *
      (linearThreeActor d.model ⟨k,_⟩)⁻¹
  rw [←map_inv,←map_mul,←map_mul]
  exact congrArg (linearThreeActor d.model) (Subtype.ext ht)

section Cubic
variable {d₂ : MSData c 2} (m₂ : RootCoordinates d₂) (s₂ : SecondarySourceData c 2)
  (X : Subgroup G) (hX3 : Nat.card X = 3) (hX : X ≤ (K c).coreCenterIn 2)
  (hfix : Q c ⊓ centralizer (X : Set G) = ⊥)

/-- The same coordinate map restricted to the cubic-fixed radical. -/
noncomputable def fixedRadicalMap : (R₂ c ⊓ centralizer (X : Set G) : Subgroup G) →*
    Multiplicative (Fin 2 → d₂.field.Carrier) :=
  (m₂.radicalCoordinates (by decide) D s₂).comp (inclusion inf_le_left)

include hfix in
/-- Fixed-point-freeness on Q makes this restriction injective. -/
theorem fixedRadicalMap_injective : Function.Injective (m₂.fixedRadicalMap D s₂ X) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro r hr
  have hq : (r : G) ∈ Q c := by
    have hh : (⟨r,r.property.1⟩ : R₂ c) ∈ (m₂.radicalCoordinates (by decide) D s₂).ker := hr
    rw [m₂.radicalCoordinates_ker] at hh
    exact hh
  have he : (r : G) = 1 := mem_bot.mp (hfix ▸ (show (r : G) ∈ Q c ⊓ centralizer (X : Set G) from
    ⟨hq,r.property.2⟩))
  exact mem_bot.mpr (Subtype.ext he)

/-- The exact order-sixteen complement is the full natural plane. -/
noncomputable def fixedRadicalCoordinates :
    (R₂ c ⊓ centralizer (X : Set G) : Subgroup G) ≃*
      Multiplicative (Fin 2 → d₂.field.Carrier) :=
  MulEquiv.ofBijective (m₂.fixedRadicalMap D s₂ X) ((Nat.bijective_iff_injective_and_card _).mpr
    ⟨m₂.fixedRadicalMap_injective D s₂ X hfix, by
      rw [m₂.radical_cubic_fixed_card D s₂ X hX3 hX hfix]
      change 16 = Nat.card (Fin 2 → d₂.field.Carrier)
      rw [Nat.card_fun,Nat.card_fin,d₂.field.card_eq,d₂.degree_eq]
      decide⟩)

/-- The fixed-plane coordinates retain the original conjugation formula. -/
theorem fixedRadicalCoordinates_conjugate (k : secondary c)
    (r t : (R₂ c ⊓ centralizer (X : Set G) : Subgroup G))
    (ht : (t : G) = k * r * (k : G)⁻¹) :
    m₂.fixedRadicalCoordinates D s₂ X hX3 hX hfix t =
      Matrix.SL2.naturalAction d₂.field.Carrier (m₂.secondaryLinear k)
        (m₂.fixedRadicalCoordinates D s₂ X hX3 hX hfix r) :=
  m₂.radicalCoordinates_conjugate (by decide) D s₂ k
    ⟨r,r.property.1⟩ ⟨t,t.property.1⟩ ht

include m₂ D s₂ hX3 hX hfix in
/-- The original fixed subgroup is elementary abelian, not merely of order sixteen. -/
theorem fixedRadical_elementary :
    IsElementaryAbelian 2 (R₂ c ⊓ centralizer (X : Set G) : Subgroup G) :=
  IsElementaryAbelian.of_injective
    (m₂.fixedRadicalCoordinates D s₂ X hX3 hX hfix).toMonoidHom
    (m₂.fixedRadicalCoordinates D s₂ X hX3 hX hfix).injective

/-- The literal centralizer in K₂ acts through the same linear-part map. -/
noncomputable def fixedSecondaryLinear :
    (secondary c ⊓ centralizer (X : Set G) : Subgroup G) →* SL(2,d₂.field.Carrier) :=
  m₂.secondaryLinear.comp (inclusion inf_le_left)

/-- The restricted kernel retains the actual O₂(K₂) embedding. -/
theorem fixedSecondaryLinear_ker : (m₂.fixedSecondaryLinear X).ker =
    ((secondary c).pCoreIn 2).subgroupOf
      (secondary c ⊓ centralizer (X : Set G)) := by
  rw [fixedSecondaryLinear,←MonoidHom.comap_ker,m₂.secondaryLinear_ker (by decide)]
  ext k
  change (⟨k,k.property.1⟩ : secondary c) ∈ pCore 2 (secondary c) ↔
    (secondary c).subtype ⟨k,k.property.1⟩ ∈ (pCore 2 (secondary c)).map (secondary c).subtype
  exact (mem_map_iff_mem (secondary c).subtype_injective).symm

include hX3 in
/-- Coprime lifting gives every SL₂ element in the cubic centralizer. -/
theorem fixedSecondaryLinear_surjective
    (hcomm : ⁅secondary c,X⁆ ≤ (secondary c).pCoreIn 2) :
    Function.Surjective (m₂.fixedSecondaryLinear X) := by
  have hXN : X ≤ normalizer (secondary c : Set G) :=
    le_normalizer_iff_commutator_le_right.mpr
      ((commutator_comm X (secondary c)).le.trans (hcomm.trans (pCoreIn_le 2 _)))
  let : Normalizes X (secondary c) := ⟨hXN⟩
  let : MulDistribMulAction X SL(2,d₂.field.Carrier) :=
    MulDistribMulAction.compHom _ (1 : X →* MulAut SL(2,d₂.field.Carrier))
  have he (x : X) (k : secondary c) : m₂.secondaryLinear (x • k) = x • m₂.secondaryLinear k := by
    change m₂.secondaryLinear (x • k) = m₂.secondaryLinear k
    apply (m₂.secondaryLinear.div_mem_ker_iff).mp
    rw [m₂.secondaryLinear_ker (by decide)]
    have hh := hcomm ((commutator_comm X (secondary c)).le
      (commutator_mem_commutator x.property k.property))
    apply (mem_map_iff_mem (secondary c).subtype_injective).mp
    simp only [div_eq_mul_inv]
    change (x : G) * (k : G) * (x : G)⁻¹ * (k : G)⁻¹ ∈ (secondary c).pCoreIn 2
    exact hh
  have hp : IsPGroup 3 X := IsPGroup.of_card (n := 1) (by simpa using hX3)
  have hk : ¬ 3 ∣ Nat.card m₂.secondaryLinear.ker := by
    rw [m₂.secondaryLinear_ker (by decide)]
    obtain ⟨j,hj⟩ := (pCore_isPGroup (p := 2) (G := secondary c)).exists_card_eq
    rw [hj]
    exact Nat.prime_three.coprime_iff_not_dvd.mp ((by decide : Nat.Coprime 3 2).pow_right j)
  have hs := FixedPoints.mapHom_surjective_of_coprime_kernel hp m₂.secondaryLinear
    (m₂.secondaryLinear_surjective (by decide)) he hk
  intro a
  obtain ⟨k,hk⟩ := hs ⟨a,fun _ => rfl⟩
  refine ⟨⟨k.val, k.val.property, ?_⟩, congrArg Subtype.val hk⟩
  intro x hx
  have hh := congrArg Subtype.val (k.property (⟨x,hx⟩ : X))
  change x * (k.val : G) * x⁻¹ = k.val at hh
  exact mul_inv_eq_iff_eq_mul.mp hh

omit [Finite G] in
/-- The centralizer in the secondary group preserves the cubic-fixed radical. -/
theorem fixedSecondary_normalizes_fixedRadical :
    secondary c ⊓ centralizer (X : Set G) ≤
      normalizer ((R₂ c ⊓ centralizer (X : Set G) : Subgroup G) : Set G) := by
  have hR : secondary c ≤ normalizer (R₂ c : Set G) :=
    (le_sup_left : secondary c ≤ secondary c ⊔ S c).trans
      ((secondary c ⊔ S c).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (secondary c ⊔ S c)
          (pCore 2 (secondary c ⊔ S c : Subgroup G))))
  exact (inf_le_inf hR (centralizer (X : Set G)).le_normalizer).trans
    inf_normalizer_le_normalizer_inf

/-- Actual conjugation on the fixed radical, through its normalizer inclusion. -/
noncomputable def fixedRadicalAction :
    (secondary c ⊓ centralizer (X : Set G) : Subgroup G) →*
      MulAut (R₂ c ⊓ centralizer (X : Set G) : Subgroup G) :=
  (R₂ c ⊓ centralizer (X : Set G) : Subgroup G).normalizerMonoidHom.comp
    (inclusion (fixedSecondary_normalizes_fixedRadical X))

/-- This entire conjugation action is the natural plane action. -/
theorem fixedRadical_action_natural
    (k : (secondary c ⊓ centralizer (X : Set G) : Subgroup G))
    (r : (R₂ c ⊓ centralizer (X : Set G) : Subgroup G)) :
    m₂.fixedRadicalCoordinates D s₂ X hX3 hX hfix (fixedRadicalAction X k r) =
      Matrix.SL2.naturalAction d₂.field.Carrier (m₂.fixedSecondaryLinear X k)
        (m₂.fixedRadicalCoordinates D s₂ X hX3 hX hfix r) :=
  m₂.fixedRadicalCoordinates_conjugate D s₂ X hX3 hX hfix
    ⟨k,k.property.1⟩ r _ rfl

private theorem natural_fixed_eq_one {F : Type*} [Field F]
    (v : Multiplicative (Fin 2 → F))
    (hv : ∀ a : SL(2,F), Matrix.SL2.naturalAction F a v = v) : v = 1 := by
  let a : SL(2,F) := ⟨!![1,1;0,1],by simp [Matrix.det_fin_two]⟩
  let b : SL(2,F) := ⟨!![1,0;1,1],by simp [Matrix.det_fin_two]⟩
  have h₀ := congrArg (fun w : Multiplicative (Fin 2 → F) => w.toAdd 0) (hv a)
  have h₁ := congrArg (fun w : Multiplicative (Fin 2 → F) => w.toAdd 1) (hv b)
  change (a.val.mulVec v.toAdd) 0 = v.toAdd 0 at h₀
  change (b.val.mulVec v.toAdd) 1 = v.toAdd 1 at h₁
  have hz₁ : v.toAdd 1 = 0 := by
    simpa [a,Matrix.SL2.naturalAction_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_two] using h₀
  have hz₀ : v.toAdd 0 = 0 := by
    simpa [b,Matrix.SL2.naturalAction_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_two] using h₁
  apply Multiplicative.toAdd.injective
  ext i
  fin_cases i <;> assumption

include m₂ D s₂ hfix in
/-- No nonidentity radical element centralizes both K₂ and the source cubic. -/
theorem radical_centralizer_secondary_cubic :
    R₂ c ⊓ centralizer ((secondary c ⊔ X : Subgroup G) : Set G) = ⊥ := by
  apply bot_unique
  intro r hr
  have hcK : r ∈ centralizer (secondary c : Set G) := centralizer_le (show (secondary c : Set G) ⊆ (secondary c ⊔ X : Subgroup G) from fun _ hx => mem_sup_left hx) hr.2
  have hcX : r ∈ centralizer (X : Set G) := centralizer_le (show (X : Set G) ⊆ (secondary c ⊔ X : Subgroup G) from fun _ hx => mem_sup_right hx) hr.2
  let rR : R₂ c := ⟨r,hr.1⟩
  have hz : m₂.radicalCoordinates (by decide) D s₂ rR = 1 := by
    apply natural_fixed_eq_one
    intro a
    obtain ⟨k,rfl⟩ := m₂.secondaryLinear_surjective (by decide) a
    symm
    apply m₂.radicalCoordinates_conjugate (by decide) D s₂ k rR rR
    symm
    change (k : G) * r * (k : G)⁻¹ = r
    rw [mem_centralizer_iff.mp hcK k k.property,mul_inv_cancel_right]
  have hq : r ∈ Q c := by
    have hh : rR ∈ (m₂.radicalCoordinates (by decide) D s₂).ker := hz
    rwa [m₂.radicalCoordinates_ker] at hh
  exact hfix ▸ (show r ∈ Q c ⊓ centralizer (X : Set G) from ⟨hq,hcX⟩)

end Cubic

end RootCoordinates
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock

namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceEndgame
open RootCoordinates
open Matrix.PSL3.OuterSolvable Matrix.PSL3.ExtensionBorel
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]
  {T : Sylow 2 G} {L V : Subgroup G} {c : SourceConfiguration T L}

/-- The constructed source cubic supplies the natural fixed module and the
original marked PGL₃ extension simultaneously. No representation-extension
choice is inferred from an SL₃ restriction. -/
theorem exists_source_cubic_extension_with_natural_fixed_radical (d : MSData c 2)
    (m : RootCoordinates d) (s : SecondarySourceData c 2)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hF : Nat.card F = 4) (e : (s.component ⧸ pCore 2 s.component) ≃* PSL(3,F)) :
    ∃ X : Subgroup G, Nat.card X = 3 ∧ X ≤ (K c).coreCenterIn 2 ∧
      X ≤ rootNormalizer c ∧ X ⊓ s.component.map (rootNormalizer c).subtype = ⊥ ∧
      Q c ⊓ centralizer (X : Set G) = ⊥ ∧
      ⁅R₂ c,X⁆ = Q c ∧
      R₂ c ⊓ centralizer ((secondary c ⊔ X : Subgroup G) : Set G) = ⊥ ∧
      Function.Surjective (m.fixedSecondaryLinear X) ∧
      (∃ E : (R₂ c ⊓ centralizer (X : Set G) : Subgroup G) ≃*
          Multiplicative (Fin 2 → d.field.Carrier),
        ∀ k v, E (fixedRadicalAction X k v) =
          Matrix.SL2.naturalAction d.field.Carrier (m.fixedSecondaryLinear X k) (E v)) ∧
      ∃ φ : cubicExtension s X →* Matrix.ProjGenLinGroup (Fin 3) F,
        Function.Surjective φ ∧
        φ.ker = (pCore 2 s.component).map (cubicComponentInclusion s X) ∧
        pCore 2 (cubicExtension s X) =
          (pCore 2 s.component).map (cubicComponentInclusion s X) ∧
        (∀ b : s.component, φ (cubicComponentInclusion s X b) =
          Matrix.ProjectiveSpecialLinearGroup.toPGL
            (e (QuotientGroup.mk' (pCore 2 s.component) b))) ∧
        ∀ (g : cubicExtension s X) (z : s.component ⧸ pCore 2 s.component),
          e (s.action g z) = (pglEquivInnerDiagonal F (φ g)).val (e z) := by
  obtain ⟨X,hX,hXK,hr,hdisj,hfix,hcomm,_,hRX,_,_,φ,hφ,hker,hcore,hmark,haction⟩ :=
    exists_source_cubic_extension_with_fixed_radical d m s D h hF e
  exact ⟨X,hX,hXK,hr,hdisj,hfix,hRX,
    m.radical_centralizer_secondary_cubic D s X hfix,
    m.fixedSecondaryLinear_surjective X hX hcomm,
    ⟨m.fixedRadicalCoordinates D s X hX hXK hfix,
      m.fixedRadical_action_natural D s X hX hXK hfix⟩,
    φ,hφ,hker,hcore,hmark,haction⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceEndgame

module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.SeparateActions
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.Complements

/-!
# The compatible field construction on the original chosen seed

Vanishing of C_V(L) identifies V with the original chosen central quotient.
Its original natural coordinates therefore give a field structure on V,
and the source flag V₂ is an actual subspace for that structure. Independent
natural-plane and P-action markings feed the restriction construction,
which supplies a compatible field on P and preserves the whole Y-action.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 11.3.8
and the following complement construction, printed p.775. The Cartan
weights and nontrivial commutator calculation are not asserted here.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan
open CFSG.Quasithin.Chapter12.Section02 LocalGeometry
section Original
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) {F : CFSG.Quasithin.ChapterB.QuasisimpleSource.BinaryField}
    (c : Coordinates D F)

omit [Finite G] in
/-- Vanishing of the fixed part makes the original chosen quotient map injective. -/
theorem original_quotient_injective (hfixed : V ⊓ centralizer (L : Set G) = ⊥) :
    Function.Injective D.toCentralQuotient := by
  apply D.toCentralQuotient.ker_eq_bot_iff.mp
  apply bot_unique
  intro v hv
  have hc := (LocalGeometry.quotient_eq_one_iff D v).mp hv
  have hz : (v : G) ∈ (⊥ : Subgroup G) := hfixed ▸ (show (v : G) ∈ V ⊓ centralizer (L : Set G) from
    ⟨v.property, hc⟩)
  exact Subtype.ext hz

variable [IsMulCommutative V]

/-- The original quotient coordinates now identify the whole actual seed V. -/
def originalCoordinates (hfixed : V ⊓ centralizer (L : Set G) = ⊥) :
    Additive V ≃+ c.Space :=
  (AddEquiv.ofBijective (M := Additive V) (N := D.chosenCentralQuotient) D.toCentralQuotient.toAdditiveLeft
    ⟨fun a b h => Additive.toMul.injective (original_quotient_injective D hfixed (congrArg Multiplicative.ofAdd h)), by
      intro q
      obtain ⟨v, hv⟩ := D.toCentralQuotient_surjective (Multiplicative.ofAdd q)
      exact ⟨Additive.ofMul v, congrArg Multiplicative.toAdd hv⟩⟩).trans
      c.linearEquiv.toAddEquiv

/-- The field structure on V is transported from its original natural marking. -/
@[instance_reducible] def originalModule (hfixed : V ⊓ centralizer (L : Set G) = ⊥) :
    Module F.Carrier (Additive V) := (originalCoordinates D c hfixed).module F.Carrier

theorem originalCoordinates_smul (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (a : F.Carrier) (v : Additive V) :
    letI := originalModule D c hfixed
    originalCoordinates D c hfixed (a • v) = a • originalCoordinates D c hfixed v := by
  exact (originalCoordinates D c hfixed).apply_symm_apply _

/-- The actual flag subgroup V₂ is a field subspace of the original V. -/
def originalPlane (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (f : InvariantFlag c) :
    letI := originalModule D c hfixed
    Submodule F.Carrier (Additive V) := by
  letI := originalModule D c hfixed
  exact (f.space 1).comap ((originalCoordinates D c hfixed).linearEquiv F.Carrier).toLinearMap

theorem mem_originalPlane (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (f : InvariantFlag c) (v : Additive V) :
    v ∈ originalPlane D c hfixed f ↔ (v.toMul : G) ∈ f.Vi 1 :=
  (c.mem_preimage (f.space 1) v.toMul).symm

/-- The transported original flag plane has exactly the source ambient image. -/
theorem ambient_originalPlane (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (f : InvariantFlag c) :
    letI := originalModule D c hfixed
    ambientSubgroup (originalPlane D c hfixed f) = f.Vi 1 := by
  let := originalModule D c hfixed
  apply le_antisymm
  · rintro g ⟨v, hv, rfl⟩
    exact (mem_originalPlane D c hfixed f (Additive.ofMul v)).mp hv
  · intro g hg
    have hV : g ∈ V := D.centralQuotientPreimage_le _ hg
    exact (mem_ambientSubgroup (originalPlane D c hfixed f) ⟨g, hV⟩).mpr
      ((mem_originalPlane D c hfixed f (Additive.ofMul ⟨g, hV⟩)).mpr hg)

end Original

section Chosen
open CFSG.Quasithin.Chapter12.Section02 LocalGeometry
variable {G E : Type*} [Group G] [Field E] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (P Y : Subgroup G) [IsMulCommutative P] [IsMulCommutative V]
    [Module E (Additive P)] [Module S.field.Carrier (Additive V)]

/-- Source 11.3.8's field alignment on the literal V₂, from separate natural
section markings. The preserved Y-action is the same pointwise action. -/
theorem exists_compatible_source_fields
    (hc : Nat.card E = 2 ^ S.field.degree) (hPV : P ⊓ V = f.Vi 1)
    (d : SeparatePlaneActions (E := E) (F := S.field.Carrier) P V (f.Li 1))
    (ρ : Representation E Y (Additive P)) :
    ∃ m : Module S.field.Carrier (Additive P),
      letI := m
      (∀ (a : S.field.Carrier) (b : f.Vi 1),
        ((a • Additive.ofMul (⟨b, (show (b : G) ∈ P ⊓ V from hPV.symm ▸ b.property).1⟩ : P)).toMul : G) =
        ((a • Additive.ofMul (⟨b, (show (b : G) ∈ P ⊓ V from hPV.symm ▸ b.property).2⟩ : V)).toMul : G)) ∧
      ∃ σ : Representation S.field.Carrier Y (Additive P),
        ∀ y p, σ y p = ρ y p := by
  have hcard : Nat.card E = Nat.card S.field.Carrier := hc.trans S.field.card_eq.symm
  refine ⟨d.compatibleModule hcard, ?_⟩
  constructor
  · intro a b
    exact d.common_smul hcard a (Additive.ofMul ⟨b, hPV.symm ▸ b.property⟩)
  · exact ⟨d.restrictionDatum.compatibleRepresentation hcard ρ, fun _ _ => rfl⟩


/-- The source field construction directly from the fixed-plane identity and
separate natural action markings. Stability under the P-scalars, restriction
ring equality, and agreement of the two scalar structures are all proved. -/
theorem exists_compatible_source_fields_of_fixed_plane
    (hc : Nat.card E = 2 ^ S.field.degree) (hPV : P ⊓ V = f.Vi 1)
    (ρ : Representation E Y (Additive P))
    (hρ : ∀ (y : Y) (p : Additive P),
      ((ρ y p).toMul : G) = (MulAut.conj (y : G)) (p.toMul : G))
    (hVY : V ≤ Y) (hL₂Y : f.Li 1 ≤ Y)
    (hfixed : P ⊓ centralizer (V : Set G) = P ⊓ V)
    (e : Additive (P ⊓ V : Subgroup G) ≃+ (Fin 2 → S.field.Carrier))
    (he : ∀ (a : S.field.Carrier) v,
      (Subgroup.inclusion (inf_le_right : P ⊓ V ≤ V)).toAdditive (e.symm (a • v)) =
        a • (Subgroup.inclusion (inf_le_right : P ⊓ V ≤ V)).toAdditive (e.symm v))
    (α : f.Li 1 →* Matrix.SpecialLinearGroup (Fin 2) S.field.Carrier)
    (hα : Function.Surjective α)
    (ha : ∀ (g : f.Li 1) (v : Fin 2 → S.field.Carrier),
      ((e.symm ((α g).val.mulVec v)).toMul : G) =
        (MulAut.conj (g : G)) ((e.symm v).toMul : G)) :
    ∃ m : Module S.field.Carrier (Additive P),
      letI := m
      (∀ (a : S.field.Carrier) (b : f.Vi 1),
        ((a • Additive.ofMul (⟨b, (show (b : G) ∈ P ⊓ V from hPV.symm ▸ b.property).1⟩ : P)).toMul : G) =
        ((a • Additive.ofMul (⟨b, (show (b : G) ∈ P ⊓ V from hPV.symm ▸ b.property).2⟩ : V)).toMul : G)) ∧
      ∃ σ : Representation S.field.Carrier Y (Additive P),
        ∀ y p, σ y p = ρ y p :=
  exists_compatible_source_fields D S f P Y hc hPV
    (SeparatePlaneActions.ofFixedPlane ρ hρ hVY hL₂Y hfixed e he α hα ha) ρ

omit [Module S.field.Carrier (Additive V)] in
/-- The literal two-core identification supplies P ≤ L, hence its normalization
of V. The Y-normalization supplies the reverse normalization. Therefore the
actual commutator is central, with no extra centrality premise. -/
theorem source_commutator_central
    (hP : P = (f.Li 1).pCoreIn 2) (hVY : V ≤ Y)
    (hYP : Y ≤ normalizer (P : Set G))
    {W₁ W₂ : Subgroup G} (h₁ : W₁ ≤ V) (h₂ : W₂ ≤ P) :
    ⁅W₁, W₂⁆ ≤ V ⊓ P ∧
      ⁅W₁, W₂⁆ ≤ centralizer ((W₁ ⊔ W₂ : Subgroup G) : Set G) := by
  have hPL : P ≤ L := hP ▸ (pCoreIn_le 2 (f.Li 1)).trans
    ((LocalGeometry.localResidual_le _).trans inf_le_left)
  exact commutator_central (hVY.trans hYP) (hPL.trans D.normalizes) h₁ h₂

variable [CharP E 2]

/-- The actual Cartan supplies both invariant field complements used after
11.3.8. The subspaces U and B are the literal V₂ and P intersect R₁. -/
theorem exists_source_complements
    (X : Subgroup G) (hX : IsCartan T L X)
    (ρV : Representation S.field.Carrier X (Additive V))
    (ρP : Representation E X (Additive P))
    (hρV : ∀ (x : X) (v : Additive V),
      ((ρV x v).toMul : G) = (MulAut.conj (x : G)) (v.toMul : G))
    (hρP : ∀ (x : X) (p : Additive P),
      ((ρP x p).toMul : G) = (MulAut.conj (x : G)) (p.toMul : G))
    (U : Submodule S.field.Carrier (Additive V))
    (B : Submodule E (Additive P))
    (hU : ambientSubgroup U = f.Vi 1) (hB : ambientSubgroup B = P ⊓ f.Ri 0)
    (hUi : ∀ x : X, ∀ u ∈ U, ρV x u ∈ U)
    (hBi : ∀ x : X, ∀ b ∈ B, ρP x b ∈ B) :
    ∃ W₁ : Submodule S.field.Carrier (Additive V),
      ∃ W₂ : Submodule E (Additive P),
        IsCompl U W₁ ∧ IsCompl B W₂ ∧
        Disjoint (f.Vi 1) (ambientSubgroup W₁) ∧
        f.Vi 1 ⊔ ambientSubgroup W₁ = V ∧
        Disjoint (P ⊓ f.Ri 0) (ambientSubgroup W₂) ∧
        (P ⊓ f.Ri 0) ⊔ ambientSubgroup W₂ = P ∧
        X ≤ normalizer (ambientSubgroup W₁ : Set G) ∧
        X ≤ normalizer (ambientSubgroup W₂ : Set G) ∧
        X ≤ normalizer ((⁅ambientSubgroup W₁, ambientSubgroup W₂⁆ : Subgroup G) : Set G) := by
  obtain ⟨W₁, hc₁, hd₁, hs₁, hn₁⟩ :=
    exists_ambient_field_complement hX.odd ρV hρV U hUi
  obtain ⟨W₂, hc₂, hd₂, hs₂, hn₂⟩ :=
    exists_ambient_field_complement hX.odd ρP hρP B hBi
  exact ⟨W₁, W₂, hc₁, hc₂, hU ▸ hd₁, hU ▸ hs₁, hB ▸ hd₂, hB ▸ hs₂,
    hn₁, hn₂, normalizes_commutator hn₁ hn₂⟩

end Chosen

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan

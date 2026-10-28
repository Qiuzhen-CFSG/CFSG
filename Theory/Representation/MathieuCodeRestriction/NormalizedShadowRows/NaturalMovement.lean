module
public import Theory.Representation.SL2NaturalOffenders.NaturalPair
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CubicMovement

/-!
# Component movement on single and paired natural modules

A nontrivial subgroup of SL₂(F) fixes at most one field line in its natural
module. Hence the movement of any element on that fixed space has binary
rank at most the field degree. In a pair of natural modules, an element in
one component has zero displacement on the passive coordinate; factor its
displacement through the fixed line in the active coordinate. This bounds
movement by two when |F| = 4, without bounding the entire paired fixed space
by two.

Injective coordinates and restriction to an original subgroup preserve these
bounds. The coordinate contract retains the full actor map and its kernel,
the fixed actor, and the particular component element. The actual original
chief-section application is Chapter8/MathieuShadowRows/NaturalChiefMovement.
Source: Aschbacher--Smith, proof of 3.1.9(6), printed p.578,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace MathieuCode.NormalizedShadowRows.NaturalMovement
open Representation.SL2NaturalOffenders
variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
local notation "D" => NoStrong.Actor F
local notation "N" => NoStrong.natural (F := F)
local notation "P" => naturalPair (F := F)

section Transport
variable {G K W Z : Type*} [Group G] [Group K]
  [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup Z] [Module (ZMod 2) Z] [FiniteDimensional (ZMod 2) Z]

/-- Injective coordinates compare displacement on the specified fixed spaces. -/
theorem movement_le_of_injective
    (ρ : Representation (ZMod 2) G W) (σ : Representation (ZMod 2) K Z)
    (g : G) (b : K) (f : W →ₗ[ZMod 2] Z) (hf : Function.Injective f)
    (he : ∀ w, f (ρ g w) = σ b (f w))
    (C : Submodule (ZMod 2) W) (U : Submodule (ZMod 2) Z)
    (hU : ∀ w ∈ C, f w ∈ U) :
    Module.finrank (ZMod 2) (LinearMap.range ((ρ g - LinearMap.id).domRestrict C)) ≤
      Module.finrank (ZMod 2) (LinearMap.range ((σ b - LinearMap.id).domRestrict U)) := by
  let δ := (ρ g - LinearMap.id).domRestrict C
  let ε := (σ b - LinearMap.id).domRestrict U
  let j : LinearMap.range δ →ₗ[ZMod 2] LinearMap.range ε :=
    (f.comp (LinearMap.range δ).subtype).codRestrict _ (by
      rintro ⟨x,w,rfl⟩
      refine ⟨⟨f w,hU w w.property⟩,?_⟩
      change σ b (f w) - f w = f (ρ g w - w)
      rw [map_sub,he])
  have hj : Function.Injective j := by
    intro x y hxy
    exact Subtype.ext (hf (congrArg Subtype.val hxy))
  exact LinearMap.finrank_le_finrank_of_injective hj
end Transport

theorem natural_fixed_finrank_le (A : Subgroup D) (hA : A ≠ ⊥) :
    Module.finrank (ZMod 2) (fixedSpace N A) ≤ Module.finrank (ZMod 2) F := by
  have hc := fixedSpace_card_le_of_le (⊤ : Subgroup D) topEquiv N
    (fun _ _ => rfl) hA le_top
  have hpow : 2 ^ Module.finrank (ZMod 2) (fixedSpace N A) ≤
      2 ^ Module.finrank (ZMod 2) F := by
    have hC : Nat.card (fixedSpace N A) =
        2 ^ Module.finrank (ZMod 2) (fixedSpace N A) := by
      simpa using (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace N A))
    have hF : Nat.card F = 2 ^ Module.finrank (ZMod 2) F := by
      simpa using (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F))
    rwa [←hC,←hF]
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpow

theorem single_movement_le (A : Subgroup D) (hA : A ≠ ⊥) (b : D) :
    Module.finrank (ZMod 2) (LinearMap.range
      ((N b - LinearMap.id).domRestrict (fixedSpace N A))) ≤
      Module.finrank (ZMod 2) F :=
  (LinearMap.finrank_range_le _).trans (natural_fixed_finrank_le A hA)

theorem pair_first_movement_le (A : Subgroup (D × D))
    (hA : A.map (MonoidHom.fst D D) ≠ ⊥) (b : D) :
    Module.finrank (ZMod 2) (LinearMap.range
      ((P (b,1) - LinearMap.id).domRestrict (fixedSpace P A))) ≤
      Module.finrank (ZMod 2) F := by
  let B := A.map (MonoidHom.fst D D)
  let f : fixedSpace P A →ₗ[ZMod 2] fixedSpace N B :=
    ((LinearMap.fst (ZMod 2) (Fin 2 → F) (Fin 2 → F)).comp
      (fixedSpace P A).subtype).codRestrict _ (by
        intro v
        rintro ⟨_,a,ha,rfl⟩
        exact congrArg Prod.fst (v.property ⟨a,ha⟩))
  let d : fixedSpace N B →ₗ[ZMod 2] ((Fin 2 → F) × (Fin 2 → F)) :=
    (LinearMap.inl (ZMod 2) (Fin 2 → F) (Fin 2 → F)).comp
      ((N b - LinearMap.id).domRestrict (fixedSpace N B))
  have he : (P (b,1) - LinearMap.id).domRestrict (fixedSpace P A) = d.comp f := by
    apply LinearMap.ext
    intro v
    apply Prod.ext
    · rfl
    · change N 1 v.val.2 - v.val.2 = 0
      rw [map_one]
      exact sub_self _
  rw [he]
  have h₁ : Module.finrank (ZMod 2) (LinearMap.range (d.comp f)) ≤
      Module.finrank (ZMod 2) (LinearMap.range d) :=
    Submodule.finrank_mono (LinearMap.range_comp_le_range f d)
  have h₂ : Module.finrank (ZMod 2) (LinearMap.range d) ≤
      Module.finrank (ZMod 2) (fixedSpace N B) := d.finrank_range_le
  exact h₁.trans (h₂.trans (natural_fixed_finrank_le B hA))

theorem pair_second_movement_le (A : Subgroup (D × D))
    (hA : A.map (MonoidHom.snd D D) ≠ ⊥) (b : D) :
    Module.finrank (ZMod 2) (LinearMap.range
      ((P (1,b) - LinearMap.id).domRestrict (fixedSpace P A))) ≤
      Module.finrank (ZMod 2) F := by
  let B := A.map (MonoidHom.snd D D)
  let f : fixedSpace P A →ₗ[ZMod 2] fixedSpace N B :=
    ((LinearMap.snd (ZMod 2) (Fin 2 → F) (Fin 2 → F)).comp
      (fixedSpace P A).subtype).codRestrict _ (by
        intro v
        rintro ⟨_,a,ha,rfl⟩
        exact congrArg Prod.snd (v.property ⟨a,ha⟩))
  let d : fixedSpace N B →ₗ[ZMod 2] ((Fin 2 → F) × (Fin 2 → F)) :=
    (LinearMap.inr (ZMod 2) (Fin 2 → F) (Fin 2 → F)).comp
      ((N b - LinearMap.id).domRestrict (fixedSpace N B))
  have he : (P (1,b) - LinearMap.id).domRestrict (fixedSpace P A) = d.comp f := by
    apply LinearMap.ext
    intro v
    apply Prod.ext
    · change N 1 v.val.1 - v.val.1 = 0
      rw [map_one]
      exact sub_self _
    · rfl
  rw [he]
  have h₁ : Module.finrank (ZMod 2) (LinearMap.range (d.comp f)) ≤
      Module.finrank (ZMod 2) (LinearMap.range d) :=
    Submodule.finrank_mono (LinearMap.range_comp_le_range f d)
  have h₂ : Module.finrank (ZMod 2) (LinearMap.range d) ≤
      Module.finrank (ZMod 2) (fixedSpace N B) := d.finrank_range_le
  exact h₁.trans (h₂.trans (natural_fixed_finrank_le B hA))

section Coordinates
variable {G W : Type*} [Group G]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- Single natural coordinates retain the complete original actor map. -/
theorem single_coordinates_movement_le
    (ρ : Representation (ZMod 2) G W) (q : G →* D)
    (f : W →ₗ[ZMod 2] (Fin 2 → F)) (hf : Function.Injective f)
    (he : ∀ g w, f (ρ g w) = N (q g) (f w))
    (A : Subgroup G) (hA : A.map q ≠ ⊥) (b : G) :
    Module.finrank (ZMod 2) (LinearMap.range
      ((ρ b - LinearMap.id).domRestrict (fixedSpace ρ A))) ≤
      Module.finrank (ZMod 2) F := by
  have hfix (w : W) (hw : w ∈ fixedSpace ρ A) : f w ∈ fixedSpace N (A.map q) := by
    rintro ⟨_,a,ha,rfl⟩
    exact (he a w).symm.trans (congrArg f (hw ⟨a,ha⟩))
  exact (movement_le_of_injective ρ N b (q b) f hf (he b)
    (fixedSpace ρ A) (fixedSpace N (A.map q)) hfix).trans
      (single_movement_le (A.map q) hA (q b))

/-- A component element only moves its active natural coordinate, even if
both Sylow fixed lines occur in the source fixed space. -/
theorem pair_coordinates_movement_le
    (ρ : Representation (ZMod 2) G W) (q : G →* D × D)
    (f : W →ₗ[ZMod 2] ((Fin 2 → F) × (Fin 2 → F))) (hf : Function.Injective f)
    (he : ∀ g w, f (ρ g w) = P (q g) (f w))
    (A : Subgroup G)
    (hA₁ : (A.map q).map (MonoidHom.fst D D) ≠ ⊥)
    (hA₂ : (A.map q).map (MonoidHom.snd D D) ≠ ⊥)
    (b : G) (hb : (q b).1 = 1 ∨ (q b).2 = 1) :
    Module.finrank (ZMod 2) (LinearMap.range
      ((ρ b - LinearMap.id).domRestrict (fixedSpace ρ A))) ≤
      Module.finrank (ZMod 2) F := by
  have hfix (w : W) (hw : w ∈ fixedSpace ρ A) : f w ∈ fixedSpace P (A.map q) := by
    rintro ⟨_,a,ha,rfl⟩
    exact (he a w).symm.trans (congrArg f (hw ⟨a,ha⟩))
  apply (movement_le_of_injective ρ P b (q b) f hf (he b)
    (fixedSpace ρ A) (fixedSpace P (A.map q)) hfix).trans
  rcases hb with hb | hb
  · have hqb : q b = (1,(q b).2) := Prod.ext hb rfl
    rw [hqb]
    exact pair_second_movement_le (A.map q) hA₂ _
  · have hqb : q b = ((q b).1,1) := Prod.ext rfl hb
    rw [hqb]
    exact pair_first_movement_le (A.map q) hA₁ _

/-- Literal single or paired natural coordinates on an original subgroup
containing the fixed actor and the element whose movement is measured.
The actor map may have its full covering kernel. In the paired case the
element belongs to one component and the fixed actor meets both coordinates. -/
@[expose] def HasComponentCoordinates (ρ : Representation (ZMod 2) G W)
    (A : Subgroup G) (b : G) : Prop :=
  ∃ K : Subgroup G, A ≤ K ∧ ∃ hb : b ∈ K,
    (∃ q : K →* D, ∃ f : W →ₗ[ZMod 2] (Fin 2 → F),
      Function.Injective f ∧
      (∀ (g : K) w, f (ρ (g : G) w) = N (q g) (f w)) ∧
      (A.subgroupOf K).map q ≠ ⊥) ∨
    (∃ q : K →* D × D, ∃ f : W →ₗ[ZMod 2] ((Fin 2 → F) × (Fin 2 → F)),
      Function.Injective f ∧
      (∀ (g : K) w, f (ρ (g : G) w) = P (q g) (f w)) ∧
      (((A.subgroupOf K).map q).map (MonoidHom.fst D D) ≠ ⊥) ∧
      (((A.subgroupOf K).map q).map (MonoidHom.snd D D) ≠ ⊥) ∧
      ((q ⟨b,hb⟩).1 = 1 ∨ (q ⟨b,hb⟩).2 = 1))

/-- Restriction to the original subgroup preserves the original fixed space. -/
theorem component_coordinates_movement_le
    (ρ : Representation (ZMod 2) G W) (A : Subgroup G) (b : G)
    (h : HasComponentCoordinates (F := F) ρ A b) :
    Module.finrank (ZMod 2) (LinearMap.range
      ((ρ b - LinearMap.id).domRestrict (fixedSpace ρ A))) ≤
      Module.finrank (ZMod 2) F := by
  obtain ⟨K,hAK,hb,h⟩ := h
  have hfix : fixedSpace (ρ.comp K.subtype) (A.subgroupOf K) = fixedSpace ρ A := by
    rw [fixedSpace_comp_map,map_subgroupOf_eq_of_le hAK]
  rcases h with ⟨q,f,hf,he,ha⟩ | ⟨q,f,hf,he,ha₁,ha₂,hqb⟩
  · have hm := single_coordinates_movement_le (ρ.comp K.subtype) q f hf he
      (A.subgroupOf K) ha ⟨b,hb⟩
    rw [hfix] at hm
    exact hm
  · have hm := pair_coordinates_movement_le (ρ.comp K.subtype) q f hf he
      (A.subgroupOf K) ha₁ ha₂ ⟨b,hb⟩ hqb
    rw [hfix] at hm
    exact hm
end Coordinates

/-- Field order four gives the required binary plane bound. -/
theorem field_four_finrank (hF : Nat.card F = 4) : Module.finrank (ZMod 2) F = 2 := by
  have hpow : 2 ^ Module.finrank (ZMod 2) F = 2 ^ 2 := by
    have hcard := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
    calc
      _ = Nat.card F := by simpa only [Nat.card_zmod] using hcard.symm
      _ = 2 ^ 2 := by norm_num [hF]
  exact (Nat.pow_right_injective (by decide : 2 ≤ 2)) hpow

end MathieuCode.NormalizedShadowRows.NaturalMovement

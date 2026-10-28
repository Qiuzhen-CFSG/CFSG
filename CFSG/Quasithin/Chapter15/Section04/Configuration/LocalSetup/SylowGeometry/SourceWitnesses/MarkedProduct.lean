module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.MarkedProduct.FullAction
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.MarkedProduct.Concrete.Axes
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.FactorActors

/-!
# The actual marked symmetric-three product for the retained source pair

Each original factor has cubic image and fixes the nontrivial sibling module.
Its image in the natural rotation group is therefore exactly one coordinate
axis. Generation forces the two axes to differ; a coordinate swap gives the
literal false/true marking without rechoosing the source pair. The resulting
surjection has kernel O₂(XS) and feeds the actual independent-inverter consumer.

All input is the earlier source ModuleStructure.Input and the already-produced
Pair. No whole-module decomposition or later Sylow conclusion is assumed.
Source: Aschbacher–Smith, 15.4.12(6) and 15.4.20, pp.1160–1164.
-/

@[expose] public section
open Subgroup Stellmacher
open OrthogonalFourBinary OrthogonalFourBinary.TerminalLines OrthogonalFourBinary.SylowGeometry
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.MarkedProduct
open FamilySource FamilySource.ModuleStructure
open FamilySource.ModuleStructure.BinaryNormalizer FamilySource.ModuleStructure.BaumannPair
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M X : Subgroup G}

omit [Finite G] in
theorem map_subgroupOf_inclusion {L H M : Subgroup G} (hLH : L ≤ H) (hHM : H ≤ M) :
    (L.subgroupOf H).map (inclusion hHM) = L.subgroupOf M := by
  ext m
  constructor
  · rintro ⟨x,hx,rfl⟩; exact hx
  · intro hm
    exact ⟨⟨m,hLH hm⟩,hm,rfl⟩

theorem SourceAction.factor_image_card (d : SourceAction T M X) (h : Input K T M X 2)
    (p : Pair T M X) (i : Bool) :
    Nat.card (((p.quotient.factor i).subgroupOf M).map d.actor) = 3 := by
  let S := ChapterB.baumann (T : Subgroup G)
  let H := X ⊔ S
  let L := p.quotient.factor i
  have hLX : L ≤ X := by
    cases i
    · exact le_sup_left.trans_eq (p.quotient.factor_generate h)
    · exact le_sup_right.trans_eq (p.quotient.factor_generate h)
  have hLH : L ≤ H := hLX.trans le_sup_left
  have hn : H ≤ normalizer (L : Set G) := sup_le (p.quotient.factor_normalized h i) (p.baumann i)
  have hk := restricted_kernel_eq_core L H hLH hn (d.productMap h) (d.productMap_kernel h)
  have hc := image_card_of_restricted_kernel L H hLH (d.productMap h) hk
  rw [p.quotient.factor_quotient_card i] at hc
  rw [← card_map_of_injective Concrete.productIsometry_injective,
    map_map, d.productMap_action, ←map_map,
    map_subgroupOf_inclusion hLH (d.join_le h)] at hc
  exact hc

theorem SourceAction.factor_image_axis (d : SourceAction T M X) (h : Input K T M X 2)
    (p : Pair T M X) (i : Bool) :
    ∃ b : Bool, ((p.quotient.factor i).subgroupOf M).map d.actor = Concrete.rotationAxis b := by
  let L := p.quotient.factor
  let V := p.quotient.moduleFactor
  let W := movedModule (T : Subgroup G) M X
  have hLX (j : Bool) : L j ≤ X := by
    cases j
    · exact le_sup_left.trans_eq (p.quotient.factor_generate h)
    · exact le_sup_right.trans_eq (p.quotient.factor_generate h)
  have hVW (j : Bool) : V j ≤ W := by
    have hj : V j ≤ V false ⊔ V true := by cases j; exact le_sup_left; exact le_sup_right
    exact hj.trans_eq p.module_join
  have hnormV : M ≤ normalizer (localV (T : Subgroup G) M : Set G) :=
    localV_normalized (T : Subgroup G) M
  have hVL : X ≤ normalizer (localV (T : Subgroup G) M : Set G) := le_trans h.member_le hnormV
  have hcen : V (!i) ≤ centralizer (L i : Set G) := by
    cases i
    · apply TwoFactors.SourceFactors.factor_centralizes_sibling_module (Y₁ := L true)
      · rw [sup_comm, p.quotient.factor_generate h]; exact hVL
      · rw [sup_comm, p.quotient.factor_generate h]; exact p.quotient.factor_normalized h true
      · exact p.module_disjoint.symm
    · apply TwoFactors.SourceFactors.factor_centralizes_sibling_module (Y₁ := L false)
      · rw [p.quotient.factor_generate h]; exact hVL
      · rw [p.quotient.factor_generate h]; exact p.quotient.factor_normalized h false
      · exact p.module_disjoint
  have hvne : V (!i) ≠ ⊥ := by
    intro hh
    have hc : Nat.card (V (!i)) = 4 := p.module_card (!i)
    rw [hh,card_bot] at hc
    omega
  obtain ⟨v,hv⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hvne
  let w : W := ⟨v,hVW (!i) v.property⟩
  apply Concrete.cubic_fixed_subgroup_eq_axis _
    ((map_mono (subgroupOf_mono M (hLX i))).trans_eq d.cubic_image)
    (d.factor_image_card h p i) (d.coordinates w).toAdd
  · intro he
    apply hv
    apply Subtype.ext
    have hw : w = 1 := d.coordinates.injective (he.trans (map_one d.coordinates).symm)
    exact congrArg (fun x : W => (x : G)) hw
  · rintro g ⟨m,hm,rfl⟩
    have he := d.intertwines m w
    have hc : (m : G) * (w : G) * (m : G)⁻¹ = w :=
      mul_inv_eq_iff_eq_mul.mpr ((hcen v.property) m hm)
    have hh : d.coordinates.symm (vectorAction (d.actor m) (d.coordinates w)) = w :=
      Subtype.ext (he.trans hc)
    exact (d.coordinates.apply_symm_apply _).symm.trans (congrArg d.coordinates hh)

theorem SourceAction.product_factor_axis (d : SourceAction T M X) (h : Input K T M X 2)
    (p : Pair T M X) (i : Bool) :
    ∃ b : Bool, ((p.quotient.factor i).subgroupOf
      (X ⊔ ChapterB.baumann (T : Subgroup G))).map (d.productMap h) = Concrete.standardAxis b := by
  obtain ⟨b,hb⟩ := d.factor_image_axis h p i
  refine ⟨b, ?_⟩
  have hLX : p.quotient.factor i ≤ X := by
    cases i
    · exact le_sup_left.trans_eq (p.quotient.factor_generate h)
    · exact le_sup_right.trans_eq (p.quotient.factor_generate h)
  apply Subgroup.map_injective Concrete.productIsometry_injective
  rw [map_map, d.productMap_action, ←map_map,
    map_subgroupOf_inclusion (hLX.trans le_sup_left)
      (d.join_le h), hb]
  rfl

theorem standardAxis_swap (b : Bool) :
    (Concrete.standardAxis b).map ((MulEquiv.prodComm : Concrete.S3 × Concrete.S3 ≃* Concrete.S3 × Concrete.S3)).toMonoidHom =
      Concrete.standardAxis (!b) := by
  cases b <;>
    ext x <;>
    simp only [Concrete.standardAxis, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      Bool.not_true, mem_map, mem_prod, mem_bot]
  · constructor
    · rintro ⟨⟨a,b⟩,⟨ha,hb⟩,rfl⟩; exact ⟨hb,ha⟩
    · rintro ⟨h₁,h₂⟩; exact ⟨(x.2,x.1),⟨h₂,h₁⟩,rfl⟩
  · constructor
    · rintro ⟨⟨a,b⟩,⟨ha,hb⟩,rfl⟩; exact ⟨hb,ha⟩
    · rintro ⟨h₁,h₂⟩; exact ⟨(x.2,x.1),⟨h₂,h₁⟩,rfl⟩

theorem SourceAction.product_axes_distinct (d : SourceAction T M X) (h : Input K T M X 2)
    (p : Pair T M X) (b₀ b₁ : Bool)
    (h₀ : ((p.quotient.factor false).subgroupOf M).map d.actor = Concrete.rotationAxis b₀)
    (h₁ : ((p.quotient.factor true).subgroupOf M).map d.actor = Concrete.rotationAxis b₁) : b₀ ≠ b₁ := by
  intro he
  have hL (i : Bool) : p.quotient.factor i ≤ M := by
    have hi : p.quotient.factor i ≤ X := by
      cases i
      · exact le_sup_left.trans_eq (p.quotient.factor_generate h)
      · exact le_sup_right.trans_eq (p.quotient.factor_generate h)
    exact hi.trans h.member_le
  have hj := congrArg (fun A : Subgroup G => (A.subgroupOf M).map d.actor)
    (p.quotient.factor_generate h)
  rw [subgroupOf_sup (hL false) (hL true), Subgroup.map_sup, h₀, h₁, he, sup_idem, d.cubic_image] at hj
  have hc : Nat.card rotations = 9 := by
    rw [rotations, ←Nat.card_congr (MonoidHom.ofInjective rotationHom_injective).toEquiv,
      Nat.card_eq_fintype_card]
    decide
  rw [←hj, Concrete.rotationAxis_card] at hc
  omega

/-- The full quotient with both original factors marked, for any retained
source pair. Its kernel is the actual two-core, and its whole action comes
from the original moved module. -/
theorem source_marked_product (h : Input K T M X 2) (p : Pair T M X) :
    ∃ f : (X ⊔ ChapterB.baumann (T : Subgroup G) : Subgroup G) →*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)),
      Function.Surjective f ∧
      f.ker = pCore 2 (X ⊔ ChapterB.baumann (T : Subgroup G) : Subgroup G) ∧
      ((p.quotient.factor false).subgroupOf (X ⊔ ChapterB.baumann (T : Subgroup G))).map f =
        (alternatingGroup (Fin 3)).prod ⊥ ∧
      ((p.quotient.factor true).subgroupOf (X ⊔ ChapterB.baumann (T : Subgroup G))).map f =
        (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod (alternatingGroup (Fin 3)) := by
  obtain ⟨d⟩ := exists_sourceAction h
  obtain ⟨b₀,h₀⟩ := d.product_factor_axis h p false
  obtain ⟨b₁,h₁⟩ := d.product_factor_axis h p true
  have hne : b₀ ≠ b₁ := by
    apply d.product_axes_distinct h p
    · have hh := congrArg (Subgroup.map Concrete.productIsometry) h₀
      rw [map_map, d.productMap_action, ←map_map,
        map_subgroupOf_inclusion ((le_sup_left.trans_eq (p.quotient.factor_generate h)).trans le_sup_left)
          (d.join_le h)] at hh
      exact hh
    · have hh := congrArg (Subgroup.map Concrete.productIsometry) h₁
      rw [map_map, d.productMap_action, ←map_map,
        map_subgroupOf_inclusion ((le_sup_right.trans_eq (p.quotient.factor_generate h)).trans le_sup_left)
          (d.join_le h)] at hh
      exact hh
  cases b₀ <;> cases b₁
  · exact (hne rfl).elim
  · exact ⟨d.productMap h,d.productMap_surjective h,d.productMap_kernel h,h₀,h₁⟩
  · let e := (MulEquiv.prodComm : Concrete.S3 × Concrete.S3 ≃* Concrete.S3 × Concrete.S3)
    refine ⟨e.toMonoidHom.comp (d.productMap h),
      e.surjective.comp (d.productMap_surjective h),?_,?_,?_⟩
    · rw [MonoidHom.ker_comp_of_injective _ _ e.injective, d.productMap_kernel]
    · rw [←map_map,h₀,standardAxis_swap]; rfl
    · rw [←map_map,h₁,standardAxis_swap]; rfl
  · exact (hne rfl).elim

/-- Literal FactorActors consumer: independent inversion in every source
overgroup U containing the same Baumann subgroup. -/
theorem source_independent_inverter (h : Input K T M X 2) (p : Pair T M X)
    (U : Subgroup G) (hSU : ChapterB.baumann (T : Subgroup G) ≤ U)
    (hn : U ≤ normalizer (X : Set G)) :
    let A₁ := ((p.quotient.factor false).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
    let A₂ := ((p.quotient.factor true).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
    A₁ ⊔ A₂ = ⊤ ∧ Nat.card A₁ = 3 ∧ Nat.card A₂ = 3 ∧
      ∃ a : U,
        (∀ x ∈ A₁, quotientAut (pCore 2 X) (X.normalizerMonoidHom (inclusion hn a)) x = x⁻¹) ∧
        (∀ x ∈ A₂, quotientAut (pCore 2 X) (X.normalizerMonoidHom (inclusion hn a)) x = x) := by
  obtain ⟨f,hf,hker,h₁,h₂⟩ := source_marked_product h p
  exact independent_inverter_from_product X (ChapterB.baumann (T : Subgroup G)) U hSU hn
    p.quotient.factor (p.quotient.factor_generate h) f hf hker h₁ h₂

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.MarkedProduct

module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentSevenFour
public import Theory.Representation.Mathieu.M22James.InnerChief
/-!
# The original cubic Mathieu action and its twelve-dimensional chief section

The marked V-action supplies a nontrivial involution in the literal H/O₂(H).
Its action on K-star is inner and K-star is normal. Restrict the original
faithful U_H/V₁ action to the actual join of K-star with that involution.
The three-conjugate calculation bounds the whole moved space by twelve.
Detection of the cubic center on a chief factor, inner-involution restriction,
and James's degree theorem identify a faithful irreducible twelve-dimensional
component section; the same involution has displacement exactly four there.
The final application constructs the quotient action and retains its original
coordinate map and full V-star marking.

The whole component commutator still needs to be identified with this section
before applying the nonsingular point-stabilizer exclusion. This module does
not exclude M₂₂ or assert 12.6.26 or the universal natural reduction.
Source: Aschbacher–Smith, proof of 12.6.26, printed p.832, and H.12.1,
printed pp.393–394.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- Keep the actual component, marked involution, and binary section in the
Mathieu chief-module calculation. -/
theorem SourceHypothesis.original_mathieuCover_chief_of_binary_section
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
    (hm : Chapter1.Section02.LocalModels.IsM22Cover (Nonabelian.Setup.star H c.K))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (σ : Representation (ZMod 2) (Nonabelian.Setup.Hstar H) W)
    (hσ : Function.Injective σ)
    (κ : BinaryConjugationSection H ((D.fullSetup hZ T z).UH H)
      ((D.fullSetup hZ T z).V₁) (σ.comp (QuotientGroup.mk' (pCore 2 H)))) :
    ∃ t : Nonabelian.Setup.Hstar H,
      t ∈ Nonabelian.Setup.star H V ∧ orderOf t = 2 ∧
      let B := Nonabelian.Setup.star H c.K
      let X := B ⊔ zpowers t
      let ρ := σ.comp X.subtype
      Module.finrank (ZMod 2) (Coinvariants.ker ρ) ≤ 12 ∧
      ∃ U N : Subrepresentation ρ,
        let τ := sectionRepresentation ρ U N
        τ.IsIrreducible ∧ IsIrreducible (τ.comp (B.subgroupOf X).subtype) ∧
        Function.Injective (τ.comp (B.subgroupOf X).subtype) ∧
        Module.finrank (ZMod 2) (N.toSubmodule ⧸ (sectionLower ρ U N).toSubmodule) = 12 ∧
        fixedCodim τ (zpowers (⟨t,(le_sup_right : zpowers t ≤ B ⊔ zpowers t) (mem_zpowers t)⟩ : X)) = 4 ∧
        ∃ ec : B.subgroupOf X ≃* Sporadic.Mathieu.M22TripleCover,
          Nonempty (Representation.Equiv (τ.comp (B.subgroupOf X).subtype)
            (Sporadic.Mathieu.M22TripleCover.representationOfEquiv ec)) := by
  let E := D.fullSetup hZ T z
  let B := Nonabelian.Setup.star H c.K
  let := c.component.2
  let : B.Normal := (S.original_cubicCover_component_normal D hZ z hz hH c (Or.inr hm)).1
  let A := (V.subgroupOf c.localActor).map a.action
  have hAc : Nat.card A = 2 := a.module_card
  obtain ⟨α,hα⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 (by rw [hAc])
  have hαo : orderOf (α : MulAut B) = 2 := (Subgroup.orderOf_coe α).trans hα
  have hα1 : (α : MulAut B) ≠ 1 := by intro he; simp [he] at hαo
  obtain ⟨v,hv,hvα⟩ := α.property
  let t := QuotientGroup.mk' (pCore 2 H) (inclusion a.local_le v)
  have htV : t ∈ Nonabelian.Setup.star H V := mem_map_of_mem _ hv
  have ht2 : t ^ 2 = 1 := by
    have hv2 : v ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian v.val hv)
    rw [←map_pow,←map_pow,hv2,map_one,map_one]
  have hact : MulAut.conjNormal (H := B) t = (α : MulAut B) := by
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    change t*b.val*t⁻¹ = ((α : MulAut B) b).val
    rw [←a.conjugation v b,hvα]
  have ht1 : t ≠ 1 := by
    intro he
    apply hα1
    rw [←hact,he,map_one]
  let X := B ⊔ zpowers t
  let K := B.subgroupOf X
  let tx : X := ⟨t,(le_sup_right : zpowers t ≤ B ⊔ zpowers t) (mem_zpowers t)⟩
  let ek : K ≃* B := subgroupOfEquivOfLe le_sup_left
  let : IsQuasisimple K := IsQuasisimple.of_mulEquiv ek.symm
  let ρ := σ.comp X.subtype
  have hgen : K ⊔ zpowers tx = ⊤ := by
    apply (map_injective (f := X.subtype) X.subtype_injective)
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show B ≤ X from le_sup_left),MonoidHom.map_zpowers,
      ←MonoidHom.range_eq_map,range_subtype]
    rfl
  have htransport (k : K) :
      ek (MulAut.conjNormal (H := K) tx k) = (α : MulAut B) (ek k) := by
    apply Subtype.ext
    exact congrArg (fun f : MulAut B => (f (ek k)).val) hact
  have hinner : ∃ b : K, MulAut.conjNormal (H := K) tx = MulAut.conj b := by
    obtain ⟨b,hb⟩ := S.original_cubicCover_module_inner D hZ z hz hTV hTz hbound hH hn c a
      (Or.inr hm) α.property
    refine ⟨ek.symm b,?_⟩
    apply MulEquiv.ext
    intro k
    apply ek.injective
    rw [htransport,←hb]
    simp only [MulAut.conj_apply,map_mul,map_inv,ek.apply_symm_apply]
  have hnon : MulAut.conjNormal (H := K) tx ≠ 1 := by
    intro hh
    apply hα1
    apply MulEquiv.ext
    intro b
    obtain ⟨k,rfl⟩ := ek.surjective b
    simpa only [hh,MulAut.one_apply] using (htransport k).symm
  obtain ⟨_,⟨ez⟩,⟨eq⟩⟩ := hm
  have hcB : Nat.card (center B) = 3 := by rw [Nat.card_congr ez.toEquiv]; simp
  have hc : Nat.card (center K) = 3 := (Nat.card_congr (centerCongr ek).toEquiv).trans hcB
  let eqc : (K ⧸ center K) ≃* (B ⧸ center B) := QuotientGroup.congr _ _ ek (by
    apply le_antisymm
    · rintro _ ⟨k,hk,rfl⟩
      exact (centerCongr ek ⟨k,hk⟩).property
    · intro b hb
      exact ⟨ek.symm b,(centerCongr ek.symm ⟨b,hb⟩).property,ek.apply_symm_apply b⟩)
  have hr : fixedCodim ρ (zpowers tx) ≤ 4 := by
    rw [fixedCodim_zpowers_eq_displacement_rank]
    exact S.original_binary_displacement_bound D hZ z hz hTV hTz hbound hH hn σ κ t htV
  refine ⟨t,htV,orderOf_eq_prime ht2 ht1,?_⟩
  refine ⟨Sporadic.Mathieu.M22TripleCover.inner_moved_finrank_le_twelve
    ρ K hc (eqc.trans eq) tx (Subtype.ext ht2) hgen hinner hnon hr,?_⟩
  exact Sporadic.Mathieu.M22TripleCover.inner_chief_twelve ρ (hσ.comp X.subtype_injective)
    K hc (eqc.trans eq) tx (Subtype.ext ht2) hgen hinner hnon hr

/-- The faithful chief section is constructed on the literal U_H/V₁ action,
with the original quotient-coordinate identity retained. -/
theorem SourceHypothesis.original_mathieuCover_chief
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
    (hm : Chapter1.Section02.LocalModels.IsM22Cover (Nonabelian.Setup.star H c.K))
    : let h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
      let _ : ((D.fullSetup hZ T z).V₁.subgroupOf ((D.fullSetup hZ T z).UH H)).Normal :=
        h.point_normal_in_UH
      let _ : IsElementaryAbelian 2 ((D.fullSetup hZ T z).UH H ⧸
          (D.fullSetup hZ T z).V₁.subgroupOf ((D.fullSetup hZ T z).UH H)) :=
        h.point_quotient_elementary
      ∃ (σ : Representation (ZMod 2) (Nonabelian.Setup.Hstar H)
          (Additive ((D.fullSetup hZ T z).UH H ⧸
            (D.fullSetup hZ T z).V₁.subgroupOf ((D.fullSetup hZ T z).UH H))))
        (κ : BinaryConjugationSection H ((D.fullSetup hZ T z).UH H)
          ((D.fullSetup hZ T z).V₁) (σ.comp (QuotientGroup.mk' (pCore 2 H)))),
        Function.Injective σ ∧
        (∀ u : (D.fullSetup hZ T z).UH H, (κ.coordinates u).toAdd =
          Additive.ofMul (QuotientGroup.mk' ((D.fullSetup hZ T z).V₁.subgroupOf
            ((D.fullSetup hZ T z).UH H)) u)) ∧
    ∃ t : Nonabelian.Setup.Hstar H,
      t ∈ Nonabelian.Setup.star H V ∧ orderOf t = 2 ∧
      let B := Nonabelian.Setup.star H c.K
      let X := B ⊔ zpowers t
      let ρ := σ.comp X.subtype
      Module.finrank (ZMod 2) (Coinvariants.ker ρ) ≤ 12 ∧
      ∃ U N : Subrepresentation ρ,
        let τ := sectionRepresentation ρ U N
        τ.IsIrreducible ∧ IsIrreducible (τ.comp (B.subgroupOf X).subtype) ∧
        Function.Injective (τ.comp (B.subgroupOf X).subtype) ∧
        Module.finrank (ZMod 2) (N.toSubmodule ⧸ (sectionLower ρ U N).toSubmodule) = 12 ∧
        fixedCodim τ (zpowers (⟨t,(le_sup_right : zpowers t ≤ B ⊔ zpowers t) (mem_zpowers t)⟩ : X)) = 4 ∧
        ∃ ec : B.subgroupOf X ≃* Sporadic.Mathieu.M22TripleCover,
          Nonempty (Representation.Equiv (τ.comp (B.subgroupOf X).subtype)
            (Sporadic.Mathieu.M22TripleCover.representationOfEquiv ec)) := by
  let h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  let := h.point_normal_in_UH
  let := h.point_quotient_elementary
  obtain ⟨σ,κ,hσ,hcoordinates⟩ := h.faithful_point_quotient
  exact ⟨σ,κ,hσ,hcoordinates,
    S.original_mathieuCover_chief_of_binary_section D hZ z hz hTV hTz hbound hH hn c a hm σ hσ κ⟩

end CFSG.Quasithin.Chapter12.Section06

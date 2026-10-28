module
public import Theory.SpecificGroups.SymplecticFour.ReciprocalSmallActors
public import Theory.Representation.SemilinearFixedIndex
public import Theory.SpecificGroups.SymplecticFour.RootHyperplaneComparison
public import Theory.Representation.SymplecticNaturalNormalizer.FixedLineInner
public import Theory.Representation.BinaryOffender.EmbeddedFixedIndex
/-!
# Small commutators in a semilinear symplectic natural module

For an elementary actor on the field-four natural module, a commutator of
order at most four excludes every nontrivial field twist: such a twist has
fixed quotient of order at least sixteen. Each remaining involution fixes
a field line, so the centric symplectic component contains the actor.
Symplectic orthogonality then identifies its fixed quotient order with its
displacement order, giving centralizer index at most four.

The embedding and ambient conjugation action are literal. The source
consumer is OriginalSmallCommutator in the Sp4Four comparison layer.
Source: MS93 (3.3)(ii) as used in (5.7), printed pp.867 and919.
-/

public noncomputable section
open Subgroup Representation
open Theory.SpecificGroups.SymplecticFour
open scoped commutatorElement
namespace Theory.SpecificGroups.SymplecticFour
variable {F G J : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [Group G] [Group J]

/-- An elementary actor with a four-element commutator on the original
natural module has centralizer index at most four, even when the ambient
marked action is initially only semilinear. -/
theorem centralizer_index_le_four_of_small_natural_commutator
    (hF : Nat.card F = 4) (B : Subgroup J) [B.Normal]
    (hcent : centralizer (B : Set J) ≤ B) (e : B ≃* Sp F)
    (ρ : Representation (ZMod 2) J (Vector F)) (hfaith : Function.Injective ρ)
    (hB : ∀ b : B, ∀ v, ρ (b:J) v = symplecticNatural 2 (e b) v)
    (N A : Subgroup G) [IsElementaryAbelian 2 A]
    (j : Multiplicative (Vector F) →* G) (hj : Function.Injective j)
    (hjr : j.range = N) (α : A →* J)
    (hact : ∀ (a : A) v,
      j (Multiplicative.ofAdd (ρ (α a) v)) = a.val*j (Multiplicative.ofAdd v)*a.val⁻¹)
    (hsmall : Nat.card (⁅A,N⁆ : Subgroup G) ≤ 4)
    [Finite (⁅A,N⁆ : Subgroup G)] :
    (centralizer (A : Set G)).relIndex N ≤ 4 := by
  have hinner (a : A) : α a ∈ B := by
    obtain ⟨σ,hσ⟩ := SymplecticNaturalNormalizer.exists_field_twist
      ⟨SymplecticConjugatePair.Ambient.linearAction ρ (α a),
        SymplecticNaturalNormalizer.operator_mem_naturalNormalizer B (by omega) e ρ hB (α a)⟩
    change ∀ c v, ρ (α a) (c • v) = σ c • ρ (α a) v at hσ
    let δ := ρ (α a) - LinearMap.id
    have hk : δ.ker = Representation.BinaryOffender.fixedSpace ρ (zpowers (α a)) := by
      ext v
      change ρ (α a) v-v=0 ↔ _
      rw [sub_eq_zero,Representation.BinaryOffender.mem_fixedSpace_zpowers_iff]
    have hr : Nat.card δ.range ≤ 4 := by
      let f : δ.range → (⁅A,N⁆ : Subgroup G) := fun v => ⟨j (Multiplicative.ofAdd v.val),by
        obtain ⟨w,hw⟩ := v.property
        rw [←hw]
        change j (Multiplicative.ofAdd (ρ (α a) w-w)) ∈ _
        rw [ofAdd_sub,map_div,div_eq_mul_inv,hact]
        exact commutator_mem_commutator a.property
          (hjr ▸ (show j (Multiplicative.ofAdd w) ∈ j.range from ⟨_,rfl⟩))⟩
      exact (Nat.card_le_card_of_injective f (fun v w h =>
        Subtype.ext (Multiplicative.ofAdd.injective (hj (congrArg Subtype.val h))))).trans hsmall
    have hfixcard : Nat.card (Vector F ⧸ Representation.BinaryOffender.fixedSpace ρ
        (zpowers (α a))) ≤ 4 := by
      rw [←hk]
      exact (Nat.card_congr δ.quotKerEquivRange.toEquiv).le.trans hr
    have hs : σ = RingEquiv.refl F := by
      by_contra hs
      have h := Representation.sixteen_le_fixed_quotient_card_of_twist hF ρ
        (zpowers (α a)) (mem_zpowers _) hs hσ
      omega
    by_cases hone : α a = 1
    · rw [hone]; exact B.one_mem
    obtain ⟨w,hw⟩ : ∃ w, ρ (α a) w ≠ w := by
      by_contra! h
      apply hone
      apply hfaith
      rw [map_one]
      exact LinearMap.ext h
    let v := ρ (α a) w-w
    have hv : v ≠ 0 := sub_ne_zero.mpr hw
    have haa : α a * α a = 1 := by
      rw [←map_mul,←pow_two,Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 A) a,map_one]
    have hfix : ρ (α a) v = v := by
      change ρ (α a) (ρ (α a) w-w)=ρ (α a) w-w
      rw [map_sub,←Module.End.mul_apply,←map_mul,haa,map_one]
      change w-ρ (α a) w=ρ (α a) w-w
      have hneg (u : Vector F) : -u = u := by
        simpa only [CharTwo.neg_eq,one_smul] using (neg_smul (1 : ZMod 2) u).symm
      simp only [sub_eq_add_neg,hneg,add_comm]
    apply SymplecticNaturalNormalizer.mem_component_of_fixes_field_line
      B hcent (by omega) e ρ hB (α a) v hv
    intro c
    rw [hσ,hs,hfix]
    rfl
  let f : A →* Sp F := e.toMonoidHom.comp (α.codRestrict B hinner)
  have hact' (a : A) v : j (Multiplicative.ofAdd (f a • v)) =
      a.val*j (Multiplicative.ofAdd v)*a.val⁻¹ := by
    rw [←hact]
    congr 2
    exact (hB ⟨α a,hinner a⟩ v).symm
  have he := RootHyperplaneComparison.commutator_eq_displacement_image A N j hjr f hact'
  have hc : Nat.card (displacementSpace f.range) ≤ 4 := by
    rw [he,card_map_of_injective hj] at hsmall
    exact hsmall
  let σ := Representation.restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)
  have hi := Representation.BinaryOffender.embedded_centralizer_index σ N A j hj hjr f hact'
  have hquot : 2 ^ Representation.BinaryOffender.fixedCodim σ f.range =
      Nat.card (Vector F ⧸ TwoLocalCover.fixedSpace f.range) := by
    let C := TwoLocalCover.fixedSpace f.range
    have hfixed : Representation.BinaryOffender.fixedSpace σ f.range = C.restrictScalars (ZMod 2) := by
      ext v
      exact ⟨fun h g hg => h ⟨g,hg⟩,fun h g => h g.val g.property⟩
    change 2 ^ Module.finrank (ZMod 2) (Vector F ⧸ Representation.BinaryOffender.fixedSpace σ f.range) = _
    rw [hfixed]
    have hc := Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv (ZMod 2) C).toEquiv
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hc
    exact hc
  rw [hi,hquot,fixed_quotient_card]
  rwa [Module.natCard_eq_pow_finrank (K := F)] at hc
end Theory.SpecificGroups.SymplecticFour

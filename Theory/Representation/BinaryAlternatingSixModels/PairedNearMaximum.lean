module
public import Theory.Representation.BinaryAlternatingSixModels.PairedNormalizer
public import Theory.Representation.AlternatingSixPairedCovers.MovementCubic
public import Theory.Representation.AlternatingSixPairedCovers.QuadraticComponent
public import Theory.Representation.BinaryOffender.SmallFixedCodimension
public import Theory.Representation.BinaryOddDisplacement.PrimeDivisibility
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.OuterCommutator

/-!
# Near-maximum movement on two natural A₆ heads

The two graph-related natural heads cost at least five on an elementary
four-group: if both costs were two, both actions would be quadratic, contrary
to the simultaneous quadratic calculation. Cubics cost at least six and
quintics at least eight. Every outer involution has a component commutator
of order three or five; the commutator rank inequality therefore makes its
own movement at least three.

For an elementary actor in a group with self-centralizing normal A₆, its
index over the component intersection is at most two. Splitting by the
intersection's order (one, two, or four) gives movement strictly greater
than actor rank plus one. Only the actual component heads are used: no
extension of either head to the full group is assumed. The Chapter 13
application supplies their additive bound through its full two-core quotient.

Source: Aschbacher--Smith 13.4.7(1iv), printed p.901, with B.3.4 and the
odd-commutator calculation also used in 14.6.24(2), printed p.1041.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymmetricSix BinaryDuadModule BinaryPermutation
namespace BinaryAlternatingSix

private theorem first_movement (a : A6) (ha : a ≠ 1) :
    2 ≤ fixedCodim firstAlternating (zpowers a) := by
  have hf : Function.Injective firstAlternating := by
    intro x y he
    apply Subtype.ext
    apply polarRepresentation_injective
    apply Subtype.ext
    exact congrArg LinearMap.toMatrix' he
  by_contra hn
  exact ha (Representation.SixLetterTransvections.alternating_eq_one_of_displacement_le_one
    firstAlternating hf a (by rw [←fixedCodim_zpowers_eq_displacement_rank]; omega))

private theorem first_codim (R : Subgroup A6) :
    fixedCodim firstAlternating R =
      fixedCodim (naturalRepresentation (Fin 6)) (R.map A6.subtype) :=
  fixedCodim_map_equivariant firstAlternating (naturalRepresentation (Fin 6))
    A6.subtype PolarNatural.equiv (fun g v => PolarNatural.equiv_action g v) R

private theorem second_codim (R : Subgroup A6) :
    fixedCodim secondAlternating R =
      fixedCodim (naturalRepresentation (Fin 6))
        (R.map (diagramAut.toMonoidHom.comp A6.subtype)) :=
  fixedCodim_map_equivariant secondAlternating (naturalRepresentation (Fin 6))
    (diagramAut.toMonoidHom.comp A6.subtype) PolarNatural.equiv
    (fun g v => PolarNatural.equiv_action (diagramAut g) v) R

private theorem second_movement (a : A6) (ha : a ≠ 1) :
    2 ≤ fixedCodim secondAlternating (zpowers a) := by
  have hh := first_movement (alternatingDiagramAut a)
    (fun he => ha (alternatingDiagramAut.injective (he.trans (map_one _).symm)))
  have he := fixedCodim_map_equivariant secondAlternating firstAlternating
    alternatingDiagramAut.toMonoidHom (LinearEquiv.refl (ZMod 2) NaturalModule)
    (fun _ _ => rfl) (zpowers a)
  rw [MonoidHom.map_zpowers] at he
  rw [he]
  exact hh

/-- A four-group costs at least five dimensions on the two natural heads. -/
theorem paired_four_group_movement (R : Subgroup A6) [IsElementaryAbelian 2 R]
    (hR : 2 < Nat.card R) :
    5 ≤ fixedCodim firstAlternating R + fixedCodim secondAlternating R := by
  have hn : R ≠ ⊥ := by intro h; simp [h] at hR
  obtain ⟨a,ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hn
  have ha' : (a : A6) ≠ 1 := fun h => ha (Subtype.ext h)
  have h₁ := first_movement a ha'
  have h₂ := second_movement a ha'
  have hmono (σ : Representation (ZMod 2) A6 NaturalModule) :
      fixedCodim σ (zpowers (a : A6)) ≤ fixedCodim σ R := by
    have hh := Submodule.finrank_mono (fixedSpace_antitone σ (zpowers_le.mpr a.property))
    have hx := fixedCodim_add_finrank σ (zpowers (a : A6))
    have hy := fixedCodim_add_finrank σ R
    omega
  have hm₁ := hmono firstAlternating
  have hm₂ := hmono secondAlternating
  by_contra h
  have hd₁ : fixedCodim ((naturalRepresentation (Fin 6)).comp A6.subtype) R ≤ 2 := by
    change Module.finrank (ZMod 2) (_ ⧸ fixedSpace _ _) ≤ _
    rw [fixedSpace_comp_map]
    change fixedCodim (naturalRepresentation (Fin 6)) (R.map A6.subtype) ≤ 2
    rw [←first_codim]
    omega
  have hd₂ : fixedCodim ((naturalRepresentation (Fin 6)).comp
      (diagramAut.toMonoidHom.comp A6.subtype)) R ≤ 2 := by
    change Module.finrank (ZMod 2) (_ ⧸ fixedSpace _ _) ≤ _
    rw [fixedSpace_comp_map]
    change fixedCodim (naturalRepresentation (Fin 6))
      (R.map (diagramAut.toMonoidHom.comp A6.subtype)) ≤ 2
    rw [←second_codim]
    omega
  have hb := AlternatingSixPairedCovers.simultaneous_quadratic_card_le_two R
    (isQuadratic_of_fixedCodim_le_two _ hd₁) (isQuadratic_of_fixedCodim_le_two _ hd₂)
  exact (not_le_of_gt hR) hb

private theorem codim_conj {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (σ : Representation (ZMod 2) D W)
    {a b : D} (h : IsConj a b) : fixedCodim σ (zpowers a) = fixedCodim σ (zpowers b) := by
  obtain ⟨c,rfl⟩ := isConj_iff.mp h
  rw [fixedCodim_zpowers_conj]

/-- Component cubics cost at least six dimensions on the paired natural heads. -/
theorem paired_cubic_movement (a : A6) (ha : orderOf a = 3) :
    6 ≤ fixedCodim firstAlternating (zpowers a) +
      fixedCodim secondAlternating (zpowers a) := by
  have hn : a ≠ 1 := by intro h; simp [h] at ha
  have h₁ := first_movement a hn
  have h₂ := second_movement a hn
  rcases GLS3.Chapter5.alternatingSix_cycleType_of_order_three a ha with hs | hd
  · have hc : IsConj GLS3.Chapter5.threeCyclePerm a.val :=
      Equiv.Perm.isConj_iff_cycleType_eq.mpr
        (GLS3.Chapter5.baseThreeCycle_isThreeCycle.trans hs.symm)
    have he := codim_conj (naturalRepresentation (Fin 6))
      (diagramAut.toMonoidHom.map_isConj hc)
    change fixedCodim (naturalRepresentation (Fin 6))
      (zpowers (diagramAut GLS3.Chapter5.threeCyclePerm)) = _ at he
    rw [AlternatingSixPairedCovers.natural_diagram_threeCycle_fixedCodim] at he
    have hh := second_codim (zpowers a)
    rw [MonoidHom.map_zpowers] at hh
    have hv : fixedCodim secondAlternating (zpowers a) = 4 := hh.trans he.symm
    omega
  · have hc : IsConj GLS3.Chapter5.doubleThreeCyclePerm a.val :=
      Equiv.Perm.isConj_iff_cycleType_eq.mpr
        (GLS3.Chapter5.doubleThreeCyclePerm_cycleType.trans hd.symm)
    have he := codim_conj (naturalRepresentation (Fin 6)) hc
    rw [AlternatingSixPairedCovers.natural_doubleThree_fixedCodim] at he
    have hh := first_codim (zpowers a)
    rw [MonoidHom.map_zpowers] at hh
    have hv : fixedCodim firstAlternating (zpowers a) = 4 := hh.trans he.symm
    omega

/-- Component quintics cost at least eight dimensions on the paired heads. -/
theorem paired_quintic_movement (a : A6) (ha : orderOf a = 5) :
    8 ≤ fixedCodim firstAlternating (zpowers a) +
      fixedCodim secondAlternating (zpowers a) := by
  have hn : a ≠ 1 := by intro h; simp [h] at ha
  have h₁ := first_movement a hn
  have h₂ := second_movement a hn
  have hd₁ := four_dvd_fixedCodim_of_order_five firstAlternating a ha
  have hd₂ := four_dvd_fixedCodim_of_order_five secondAlternating a ha
  have h₁' := Nat.le_of_dvd (by omega : 0 < fixedCodim firstAlternating (zpowers a)) hd₁
  have h₂' := Nat.le_of_dvd (by omega : 0 < fixedCodim secondAlternating (zpowers a)) hd₂
  omega

variable {H M : Type*} [Group H]
  [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]

private theorem elementary_card_le_twice_component
    (K : Subgroup H) [K.Normal] (e : K ≃* A6)
    (hc : centralizer (K : Set H) = ⊥)
    (B : Subgroup H) [IsElementaryAbelian 2 B] :
    Nat.card B ≤ 2 * Nat.card (B.subgroupOf K) := by
  let f := AlternatingSix.ShadowLocal.conjugationAction K e
  let : IsElementaryAbelian 2 (B.map f) := IsElementaryAbelian.map f
  have hpre : AlternatingSix.ShadowLocal.inner.comap f = K := by
    rw [AlternatingSix.ShadowLocal.conjugationAction_preimage_inner,hc,sup_bot_eq]
  have hi : K.relIndex B ≤ 2 := by
    rw [←hpre,relIndex_comap]
    exact AlternatingSix.ShadowLocal.elementary_inner_relIndex (B.map f)
  have hk : Nat.card (K.subgroupOf B) = Nat.card (B.subgroupOf K) := by
    calc
      _ = Nat.card ((K.subgroupOf B).map B.subtype) :=
        (card_map_of_injective B.subtype_injective).symm
      _ = Nat.card ((B.subgroupOf K).map K.subtype) := by
        rw [subgroupOf_map_subtype,subgroupOf_map_subtype,inf_comm]
      _ = _ := card_map_of_injective K.subtype_injective
  have hm := (K.subgroupOf B).card_mul_index
  change Nat.card (K.subgroupOf B) * K.relIndex B = Nat.card B at hm
  rw [hk] at hm
  nlinarith

/-- The paired heads force every ambient involution to move at least three,
without an extension of either head to the whole actor. -/
theorem involution_movement_of_paired_heads
    (ρ : Representation (ZMod 2) H M)
    (K : Subgroup H) [K.Normal] (e : K ≃* A6)
    (hc : centralizer (K : Set H) = ⊥)
    (hm : ∀ R : Subgroup K,
      fixedCodim firstAlternating (R.map e.toMonoidHom) +
        fixedCodim secondAlternating (R.map e.toMonoidHom) ≤
          fixedCodim ρ (R.map K.subtype))
    (a : H) (ha : orderOf a = 2) : 3 ≤ fixedCodim ρ (zpowers a) := by
  by_cases hin : a ∈ K
  · let k : K := ⟨a,hin⟩
    have hn : e k ≠ 1 := by
      intro he
      have hh := congrArg (fun k : K => k.val) (e.injective (he.trans (map_one _).symm))
      have : a = 1 := hh
      simp [this] at ha
    have hl := paired_natural_movement (e k) hn
    have hu := hm (zpowers k)
    rw [MonoidHom.map_zpowers,MonoidHom.map_zpowers] at hu
    have hu' : fixedCodim firstAlternating (zpowers (e k)) +
        fixedCodim secondAlternating (zpowers (e k)) ≤ fixedCodim ρ (zpowers a) := hu
    omega
  let f := AlternatingSix.ShadowLocal.conjugationAction K e
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    exact (AlternatingSix.ShadowLocal.conjugationAction_ker K e).trans hc
  have hout : f a ∉ AlternatingSix.ShadowLocal.inner := by
    intro hh
    have hm : a ∈ AlternatingSix.ShadowLocal.inner.comap f := hh
    rw [AlternatingSix.ShadowLocal.conjugationAction_preimage_inner,hc,sup_bot_eq] at hm
    exact hin hm
  obtain ⟨g,hg⟩ := AlternatingSix.ShadowLocal.outer_involution_odd_commutator
    (f a) ((orderOf_injective f hf a).trans ha) hout
  let k : K := e.symm g
  let b : K := e.symm (f a g*g⁻¹)
  have he : b.val = a*k.val*a⁻¹*k.val⁻¹ := by
    have hh := AlternatingSix.ShadowLocal.conjugationAction_apply K e a k
    have hh' : e.symm (f a g) = ⟨a*k.val*a⁻¹,(inferInstance : K.Normal).conj_mem _ k.property a⟩ := by
      apply e.injective
      change f a (e (e.symm g)) = e ⟨a*k.val*a⁻¹,_⟩ at hh
      simpa only [e.apply_symm_apply] using hh
    change (e.symm (f a g*g⁻¹)).val = _
    rw [map_mul,map_inv,hh']
    rfl
  have hu := fixedCodim_commutator_le_twice ρ a k.val
  have hb := hm (zpowers b)
  rw [MonoidHom.map_zpowers,MonoidHom.map_zpowers] at hb
  have hb' : fixedCodim firstAlternating (zpowers (f a g*g⁻¹)) +
      fixedCodim secondAlternating (zpowers (f a g*g⁻¹)) ≤
        fixedCodim ρ (zpowers b.val) := by
      change fixedCodim firstAlternating (zpowers (e b)) +
        fixedCodim secondAlternating (zpowers (e b)) ≤ fixedCodim ρ (zpowers b.val) at hb
      simpa only [b,e.apply_symm_apply] using hb
  rw [he] at hb'
  rcases hg with h3 | h5
  · have hl := paired_cubic_movement (f a g*g⁻¹) h3
    omega
  · have hl := paired_quintic_movement (f a g*g⁻¹) h5
    omega

/-- Every nontrivial elementary actor exceeds the near-maximum rank-plus-one
budget, retaining the full actor and both actual component heads. -/
theorem paired_heads_exceed_full_near_maximum_budget
    (ρ : Representation (ZMod 2) H M)
    (K : Subgroup H) [K.Normal] (e : K ≃* A6)
    (hc : centralizer (K : Set H) = ⊥)
    (hm : ∀ R : Subgroup K,
      fixedCodim firstAlternating (R.map e.toMonoidHom) +
        fixedCodim secondAlternating (R.map e.toMonoidHom) ≤
          fixedCodim ρ (R.map K.subtype))
    (B : Subgroup H) (hB : IsElementaryTwo B) :
    rank B + 1 < fixedCodim ρ B := by
  let := hB.2
  let I := B.subgroupOf K
  let : IsElementaryAbelian 2 I := IsElementaryAbelian.comap_of_injective K.subtype
    K.subtype_injective B
  let J := I.map e.toMonoidHom
  let : IsElementaryAbelian 2 J := IsElementaryAbelian.map e.toMonoidHom
  have hcard : Nat.card B ≤ 2 * Nat.card I := elementary_card_le_twice_component K e hc B
  have hJcard : Nat.card J = Nat.card I := card_map_of_injective e.injective
  have hi : Nat.card I ≤ 4 := by
    by_cases hz : J = ⊥
    · rw [hz,card_bot] at hJcard
      omega
    · have hr := elementary_rank_le_two J
      have he := (show IsElementaryTwo J from ⟨hz,inferInstance⟩).card_eq_two_pow_rank
      rw [hJcard] at he
      exact he.trans_le (by simpa using Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hr)
  have hr : rank B ≤ 3 := (Nat.log_monotone (b := 2) (show Nat.card B ≤ 8 by omega)).trans (by decide)
  have hmono (R : Subgroup H) (hR : R ≤ B) : fixedCodim ρ R ≤ fixedCodim ρ B := by
    have hh := Submodule.finrank_mono (fixedSpace_antitone ρ hR)
    have h1 := fixedCodim_add_finrank ρ R
    have h2 := fixedCodim_add_finrank ρ B
    omega
  by_cases hz : I = ⊥
  · rw [hz,card_bot] at hcard
    have hr1 : rank B ≤ 1 := (Nat.log_monotone (b := 2) (show Nat.card B ≤ 2 by omega)).trans (by decide)
    obtain ⟨b,hb⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB.1
    have ho : orderOf (b : H) = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian b.val b.property)
      (fun hh => hb (Subtype.ext hh))
    have hl := involution_movement_of_paired_heads ρ K e hc hm b ho
    have hu := hmono (zpowers b.val) (zpowers_le.mpr b.property)
    omega
  · have hmap : I.map K.subtype ≤ B := by
      rw [subgroupOf_map_subtype]
      exact inf_le_left
    have hu := hmono (I.map K.subtype) hmap
    have hb := hm I
    by_cases hsmall : Nat.card I ≤ 2
    · have hr2 : rank B ≤ 2 := (Nat.log_monotone (b := 2) (show Nat.card B ≤ 4 by omega)).trans (by decide)
      obtain ⟨k,hk⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hz
      have hn : e k.val ≠ 1 := fun hh => hk (Subtype.ext (e.injective (hh.trans (map_one _).symm)))
      have hl := paired_natural_movement (e k.val) hn
      have hp := hm (zpowers k.val)
      rw [MonoidHom.map_zpowers,MonoidHom.map_zpowers] at hp
      have hp' : fixedCodim firstAlternating (zpowers (e k.val)) +
          fixedCodim secondAlternating (zpowers (e k.val)) ≤
            fixedCodim ρ (zpowers (k.val : H)) := hp
      have hmB := hmono (zpowers (k.val : H)) (zpowers_le.mpr k.property)
      omega
    · have hl := paired_four_group_movement J (by omega : 2 < Nat.card J)
      change fixedCodim firstAlternating J + fixedCodim secondAlternating J ≤ _ at hb
      omega
end BinaryAlternatingSix

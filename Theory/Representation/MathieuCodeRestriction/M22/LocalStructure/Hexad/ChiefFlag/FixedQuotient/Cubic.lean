module

public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.Spectrum.Averaging
public import Mathlib.GroupTheory.PGroup
public import Mathlib.RepresentationTheory.Coinvariants

/-!
# The order-three fixed-space calculation for a 1,5,6,10 flag

Odd-order averaging makes displacement additive. A cubic action on a binary
line is trivial, and an invariant plane in a module with a one-dimensional
fixed space has no fixed vectors. Applying these observations to the images
of the six-space and an involution's six-dimensional fixed space modulo the
five-space proves the intersection asserted in H.16.4(5).

Source: Aschbacher--Smith, H.16.4, printed p.403, manuscript of 1 March 2004.
The group is the actual order-three actor when this calculation is applied.
-/

public section
noncomputable section
namespace MathieuCode.Hexad.ChiefFlag.FixedQuotientCubic
open Representation Representation.BinaryOffender

variable {G V : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]


/-- Restriction retains the same literal invariant subspace. -/
@[expose] def restrict (ρ : Representation (ZMod 2) G V) (A : Subrepresentation ρ)
    (H : Subgroup G) : Subrepresentation (ρ.comp H.subtype) where
  toSubmodule := A.toSubmodule
  apply_mem_toSubmodule g := A.apply_mem_toSubmodule g.val

omit [FiniteDimensional (ZMod 2) V] in
theorem fixedSpace_restrict_top (ρ : Representation (ZMod 2) G V) (H : Subgroup G) :
    fixedSpace (ρ.comp H.subtype) ⊤ = fixedSpace ρ H := by
  ext v
  exact ⟨fun hv g => hv ⟨g, Subgroup.mem_top _⟩, fun hv g => hv g.val⟩

omit [FiniteDimensional (ZMod 2) V] in
theorem fixedCodim_restrict_top (ρ : Representation (ZMod 2) G V) (H : Subgroup G) :
    fixedCodim (ρ.comp H.subtype) ⊤ = fixedCodim ρ H := by
  unfold fixedCodim
  rw [fixedSpace_restrict_top]

/-- Orbit counting for the actual cubic action, including the zero vector. -/
theorem fixed_card_mod_three (ρ : Representation (ZMod 2) G V)
    (hG : Nat.card G = 3) :
    2 ^ Module.finrank (ZMod 2) V % 3 =
      2 ^ Module.finrank (ZMod 2) (fixedSpace ρ ⊤) % 3 := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : MulAction G V := {
    smul g v := ρ g v
    one_smul v := by change ρ 1 v = v; simp
    mul_smul g h v := by change ρ (g * h) v = ρ g (ρ h v); simp }
  have hp : IsPGroup 3 G := IsPGroup.of_card (n := 1) (by simpa using hG)
  let e : MulAction.fixedPoints G V ≃ fixedSpace ρ ⊤ := {
    toFun v := ⟨v, fun g => v.property g.val⟩
    invFun v := ⟨v, fun g => v.property ⟨g, Subgroup.mem_top _⟩⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hc := hp.card_modEq_card_fixedPoints V
  have hcV : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hcF : Nat.card (fixedSpace ρ ⊤) =
      2 ^ Module.finrank (ZMod 2) (fixedSpace ρ ⊤) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [Nat.card_congr e, hcV, hcF] at hc
  exact hc

/-- Displacement is additive across an invariant quotient for a cubic actor. -/
theorem displacement_add [Finite G] (ρ : Representation (ZMod 2) G V)
    (hG : Nat.card G = 3) (A : Subrepresentation ρ) :
    fixedCodim A.quotientRepresentation ⊤ + fixedCodim A.toRepresentation ⊤ =
      fixedCodim ρ ⊤ := by
  have ho : Odd (Nat.card (⊤ : Subgroup G)) := by rw [Subgroup.card_top, hG]; decide
  have hf := finrank_fixedSpace_quotient_of_odd ρ A ⊤ ho
  have ha := fixedCodim_add_finrank A.toRepresentation ⊤
  have hq := fixedCodim_add_finrank A.quotientRepresentation ⊤
  have hv := fixedCodim_add_finrank ρ ⊤
  have hd := A.toSubmodule.finrank_quotient_add_finrank
  omega

/-- The same additivity for an explicitly specified odd-order subgroup. -/
theorem displacement_add_subgroup (ρ : Representation (ZMod 2) G V)
    (A : Subrepresentation ρ) (Y : Subgroup G) [Finite Y] (hY : Odd (Nat.card Y)) :
    fixedCodim A.quotientRepresentation Y + fixedCodim A.toRepresentation Y =
      fixedCodim ρ Y := by
  have hf := finrank_fixedSpace_quotient_of_odd ρ A Y hY
  have ha := fixedCodim_add_finrank A.toRepresentation Y
  have hq := fixedCodim_add_finrank A.quotientRepresentation Y
  have hv := fixedCodim_add_finrank ρ Y
  have hd := A.toSubmodule.finrank_quotient_add_finrank
  omega

/-- Dimension of an arbitrary subspace image in a quotient. -/
theorem image_finrank (A C : Submodule (ZMod 2) V) :
    Module.finrank (ZMod 2) (C.map A.mkQ) +
      Module.finrank (ZMod 2) (A ⊓ C : Submodule (ZMod 2) V) =
      Module.finrank (ZMod 2) C := by
  let f := A.mkQ.domRestrict C
  let e : f.ker ≃ₗ[ZMod 2] (A ⊓ C : Submodule (ZMod 2) V) := {
    toFun v := ⟨v.val, (Submodule.Quotient.mk_eq_zero A).mp v.property, v.val.property⟩
    invFun v := ⟨⟨v, v.property.2⟩, (Submodule.Quotient.mk_eq_zero A).mpr v.property.1⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have h := f.finrank_range_add_finrank_ker
  rw [e.finrank_eq] at h
  have hr : f.range = C.map A.mkQ := by
    change (A.mkQ.comp C.subtype).range = _
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rwa [hr] at h

/-- A cubic action on a binary line fixes the whole line. -/
theorem fixed_eq_top_of_dim_one (ρ : Representation (ZMod 2) G V)
    (hG : Nat.card G = 3) (hd : Module.finrank (ZMod 2) V = 1) :
    fixedSpace ρ ⊤ = ⊤ := by
  have hm := fixed_card_mod_three ρ hG
  have hl := (fixedSpace ρ ⊤).finrank_le
  rw [hd] at hm hl
  have he : Module.finrank (ZMod 2) (fixedSpace ρ ⊤) = 1 := by
    rcases Nat.eq_zero_or_pos (Module.finrank (ZMod 2) (fixedSpace ρ ⊤)) with hz | hp
    · simp [hz] at hm
    · omega
  apply Submodule.eq_top_of_finrank_eq
  exact he.trans hd.symm

/-- An invariant plane has zero cubic fixed space when the ambient fixed space
has dimension at most one. -/
theorem plane_fixed_eq_bot (ρ : Representation (ZMod 2) G V)
    (hG : Nat.card G = 3) (C : Subrepresentation ρ)
    (hd : Module.finrank (ZMod 2) C.toSubmodule = 2)
    (hf : Module.finrank (ZMod 2) (fixedSpace ρ ⊤) ≤ 1) :
    fixedSpace C.toRepresentation ⊤ = ⊥ := by
  have he := (subrepresentationFixedEquiv ρ C ⊤).finrank_eq
  have hl := Submodule.finrank_mono
    (show C.toSubmodule ⊓ fixedSpace ρ ⊤ ≤ fixedSpace ρ ⊤ from inf_le_right)
  have hm := fixed_card_mod_three C.toRepresentation hG
  rw [hd] at hm
  apply Submodule.finrank_eq_zero.mp
  by_contra hn
  have h1 : Module.finrank (ZMod 2) (fixedSpace C.toRepresentation ⊤) = 1 := by omega
  simp [h1] at hm

omit [FiniteDimensional (ZMod 2) V] in
/-- The source sum identity: if the image of C modulo A has no cubic fixed
vectors, averaging expresses every element of C modulo A as a commutator. -/
theorem sup_eq_sup_commutator [Finite G]
    (ρ : Representation (ZMod 2) G V) (hG : Nat.card G = 3)
    (A C : Subrepresentation ρ)
    (hf : fixedSpace (A.quotientImage C).toRepresentation ⊤ = ⊥) :
    A.toSubmodule ⊔ C.toSubmodule = A.toSubmodule ⊔
      (Coinvariants.ker C.toRepresentation).map C.toSubmodule.subtype := by
  classical
  let : Fintype G := Fintype.ofFinite G
  have hc : (Fintype.card G : ZMod 2) = 1 := by
    rw [← Nat.card_eq_fintype_card, hG]
    decide
  apply le_antisymm
  · apply sup_le le_sup_left
    intro v hv
    let c : C.toSubmodule := ⟨v, hv⟩
    let n := Representation.norm C.toRepresentation c
    have hn : n.val ∈ A.toSubmodule := by
      have hm : A.toSubmodule.mkQ n.val ∈ (A.quotientImage C).toSubmodule :=
        ⟨n.val, n.property, rfl⟩
      have hfix : (⟨A.toSubmodule.mkQ n.val, hm⟩ : (A.quotientImage C).toSubmodule) ∈
          fixedSpace (A.quotientImage C).toRepresentation ⊤ := by
        intro g
        apply Subtype.ext
        change A.toSubmodule.mkQ (ρ g.val n.val) = A.toSubmodule.mkQ n.val
        exact congrArg (fun w : C.toSubmodule => A.toSubmodule.mkQ w.val)
          (Representation.self_norm_apply C.toRepresentation g.val c)
      rw [hf] at hfix
      exact (Submodule.Quotient.mk_eq_zero A.toSubmodule).mp (congrArg Subtype.val hfix)
    have hd : c - n ∈ Coinvariants.ker C.toRepresentation := by
      have hs : (∑ g : G, (c - C.toRepresentation g c)) ∈
          Coinvariants.ker C.toRepresentation := by
        apply Submodule.sum_mem
        intro g _
        simpa only [neg_sub] using
          (Coinvariants.ker C.toRepresentation).neg_mem (Coinvariants.sub_mem_ker g c)
      simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        ← Nat.cast_smul_eq_nsmul (ZMod 2), hc, one_smul,
        n, Representation.norm, LinearMap.sum_apply] using hs
    apply Submodule.mem_sup.mpr
    refine ⟨n.val, hn, (c - n).val, ⟨c - n, hd, rfl⟩, ?_⟩
    change n.val + (v - n.val) = v
    abel
  · apply sup_le le_sup_left
    rintro _ ⟨c, _, rfl⟩
    exact (show C.toSubmodule ≤ A.toSubmodule ⊔ C.toSubmodule from le_sup_right) c.property

/-- The cubic has displacement exactly two on the five-space and six on
V, and moves the entire four-dimensional quotient by the six-space. -/
theorem full_quotient_displacement [Finite G]
    (ρ : Representation (ZMod 2) G V) (hG : Nat.card G = 3)
    (A B : Subrepresentation ρ) (hAB : A ≤ B)
    (hV : Module.finrank (ZMod 2) V = 10)
    (hA : Module.finrank (ZMod 2) A.toSubmodule = 5)
    (hB : Module.finrank (ZMod 2) B.toSubmodule = 6)
    (hmove : 6 ≤ fixedCodim ρ ⊤)
    (hmoveA : fixedCodim A.toRepresentation ⊤ ≤ 2) :
    fixedCodim A.toRepresentation ⊤ = 2 ∧ fixedCodim ρ ⊤ = 6 ∧
      fixedCodim B.quotientRepresentation ⊤ = 4 ∧
      fixedSpace B.quotientRepresentation ⊤ = ⊥ := by
  have ha := fixedCodim_add_finrank A.toRepresentation ⊤
  have hb := fixedCodim_add_finrank B.toRepresentation ⊤
  have hv := fixedCodim_add_finrank ρ ⊤
  have hABf : Module.finrank (ZMod 2) (fixedSpace A.toRepresentation ⊤) ≤
      Module.finrank (ZMod 2) (fixedSpace B.toRepresentation ⊤) := by
    rw [(subrepresentationFixedEquiv ρ A ⊤).finrank_eq,
      (subrepresentationFixedEquiv ρ B ⊤).finrank_eq]
    exact Submodule.finrank_mono (inf_le_inf hAB le_rfl)
  have hBf : Module.finrank (ZMod 2) (fixedSpace B.toRepresentation ⊤) ≤
      Module.finrank (ZMod 2) (fixedSpace ρ ⊤) := by
    rw [(subrepresentationFixedEquiv ρ B ⊤).finrank_eq]
    exact Submodule.finrank_mono inf_le_right
  have hmB := fixed_card_mod_three B.toRepresentation hG
  rw [hB] at hmB
  have hfB : Module.finrank (ZMod 2) (fixedSpace B.toRepresentation ⊤) = 4 := by
    have hd : Module.finrank (ZMod 2) (fixedSpace B.toRepresentation ⊤) = 3 ∨
        Module.finrank (ZMod 2) (fixedSpace B.toRepresentation ⊤) = 4 := by omega
    rcases hd with hd | hd
    · simp [hd] at hmB
    · exact hd
  have hmA := fixed_card_mod_three A.toRepresentation hG
  rw [hA] at hmA
  have hfA : Module.finrank (ZMod 2) (fixedSpace A.toRepresentation ⊤) = 3 := by
    have hd : Module.finrank (ZMod 2) (fixedSpace A.toRepresentation ⊤) = 3 ∨
        Module.finrank (ZMod 2) (fixedSpace A.toRepresentation ⊤) = 4 := by omega
    rcases hd with hd | hd
    · exact hd
    · simp [hd] at hmA
  have hadd := displacement_add ρ hG B
  have hq := fixedCodim_add_finrank B.quotientRepresentation ⊤
  have hdq := B.toSubmodule.finrank_quotient_add_finrank
  refine ⟨by omega, by omega, by omega, ?_⟩
  apply Submodule.finrank_eq_zero.mp
  omega

/-- The two image calculations in the source: the six-space has a fixed line
modulo the five-space, while the involution-fixed six-space has a moved plane.
Their images therefore have zero intersection. -/
theorem fixed_six_intersection [Finite G]
    (ρ : Representation (ZMod 2) G V) (hG : Nat.card G = 3)
    (A B C : Subrepresentation ρ) (hAB : A ≤ B)
    (hV : Module.finrank (ZMod 2) V = 10)
    (hA : Module.finrank (ZMod 2) A.toSubmodule = 5)
    (hB : Module.finrank (ZMod 2) B.toSubmodule = 6)
    (hC : Module.finrank (ZMod 2) C.toSubmodule = 6)
    (hAC : Module.finrank (ZMod 2) (A.toSubmodule ⊓ C.toSubmodule :
      Submodule (ZMod 2) V) = 4)
    (hmove : 6 ≤ fixedCodim ρ ⊤)
    (hmoveA : fixedCodim A.toRepresentation ⊤ ≤ 2) :
    B.toSubmodule ⊓ C.toSubmodule = A.toSubmodule ⊓ C.toSubmodule := by
  let Bq := A.quotientImage B
  let Cq := A.quotientImage C
  have hQ : Module.finrank (ZMod 2) (V ⧸ A.toSubmodule) = 5 := by
    have := A.toSubmodule.finrank_quotient_add_finrank
    omega
  have hBq : Module.finrank (ZMod 2) Bq.toSubmodule = 1 := by
    have hi := image_finrank A.toSubmodule B.toSubmodule
    rw [inf_eq_left.mpr (show A.toSubmodule ≤ B.toSubmodule from hAB)] at hi
    change Module.finrank (ZMod 2) Bq.toSubmodule + _ = _ at hi
    omega
  have hCq : Module.finrank (ZMod 2) Cq.toSubmodule = 2 := by
    have hi := image_finrank A.toSubmodule C.toSubmodule
    change Module.finrank (ZMod 2) Cq.toSubmodule + _ = _ at hi
    omega
  have hfQ : Module.finrank (ZMod 2) (fixedSpace A.quotientRepresentation ⊤) ≤ 1 := by
    have hadd := displacement_add ρ hG A
    have hq := fixedCodim_add_finrank A.quotientRepresentation ⊤
    omega
  have hBfix : Bq.toSubmodule ≤ fixedSpace A.quotientRepresentation ⊤ := by
    intro v hv g
    have hf := fixed_eq_top_of_dim_one Bq.toRepresentation hG hBq
    have hvf : (⟨v, hv⟩ : Bq.toSubmodule) ∈ fixedSpace Bq.toRepresentation ⊤ := by
      rw [hf]; trivial
    exact congrArg Subtype.val (hvf g)
  have hCfix := plane_fixed_eq_bot A.quotientRepresentation hG Cq hCq hfQ
  apply le_antisymm
  · intro v hv
    refine ⟨?_, hv.2⟩
    have hqb : A.toSubmodule.mkQ v ∈ Bq.toSubmodule := ⟨v, hv.1, rfl⟩
    have hqc : A.toSubmodule.mkQ v ∈ Cq.toSubmodule := ⟨v, hv.2, rfl⟩
    have hx : (⟨A.toSubmodule.mkQ v, hqc⟩ : Cq.toSubmodule) ∈
        fixedSpace Cq.toRepresentation ⊤ := fun g => Subtype.ext (hBfix hqb g)
    rw [hCfix] at hx
    exact (Submodule.Quotient.mk_eq_zero A.toSubmodule).mp (congrArg Subtype.val hx)
  · exact inf_le_inf hAB le_rfl

/-- All cubic conclusions used in the source's terminal fixed-space argument. -/
theorem source_calculation [Finite G]
    (ρ : Representation (ZMod 2) G V) (hG : Nat.card G = 3)
    (A B C : Subrepresentation ρ) (hAB : A ≤ B)
    (hV : Module.finrank (ZMod 2) V = 10)
    (hA : Module.finrank (ZMod 2) A.toSubmodule = 5)
    (hB : Module.finrank (ZMod 2) B.toSubmodule = 6)
    (hC : Module.finrank (ZMod 2) C.toSubmodule = 6)
    (hAC : Module.finrank (ZMod 2) (A.toSubmodule ⊓ C.toSubmodule :
      Submodule (ZMod 2) V) = 4)
    (hmove : 6 ≤ fixedCodim ρ ⊤)
    (hmoveA : fixedCodim A.toRepresentation ⊤ ≤ 2) :
    fixedCodim A.toRepresentation ⊤ = 2 ∧
      fixedCodim ρ ⊤ = 6 ∧
      fixedCodim B.quotientRepresentation ⊤ = 4 ∧
      fixedSpace B.quotientRepresentation ⊤ = ⊥ ∧
      A.toSubmodule ⊔ C.toSubmodule = A.toSubmodule ⊔
        (Coinvariants.ker C.toRepresentation).map C.toSubmodule.subtype ∧
      B.toSubmodule ⊓ C.toSubmodule = A.toSubmodule ⊓ C.toSubmodule := by
  obtain ⟨h2, h6, h4, hzero⟩ := full_quotient_displacement ρ hG A B hAB hV hA hB hmove hmoveA
  refine ⟨h2, h6, h4, hzero, ?_,
    fixed_six_intersection ρ hG A B C hAB hV hA hB hC hAC hmove hmoveA⟩
  apply sup_eq_sup_commutator ρ hG A C
  apply plane_fixed_eq_bot A.quotientRepresentation hG (A.quotientImage C)
  · have hi := image_finrank A.toSubmodule C.toSubmodule
    change Module.finrank (ZMod 2) (A.quotientImage C).toSubmodule + _ = _ at hi
    omega
  · have hd := A.toSubmodule.finrank_quotient_add_finrank
    have hadd := displacement_add ρ hG A
    have hq := fixedCodim_add_finrank A.quotientRepresentation ⊤
    omega

end MathieuCode.Hexad.ChiefFlag.FixedQuotientCubic

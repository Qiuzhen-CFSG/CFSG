module
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Involutions
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Coverage
public import Theory.Representation.ElementaryPerfectSplit
public import Theory.GroupTheory.Recognition.JankoFour.LocalGeometry.Intrinsic
public import Theory.GroupTheory.ElementaryThompsonFusion

/-!
# Small three-spaces in a marked cocode normalizer

An involution acting nontrivially on the native M24 cocode has fixed
codimension at least four. If a smaller elementary subgroup A normalizes
the cocode subgroup W and is normalized by W, each displacement embeds
in A. Hence |A| < 16 forces A to centralize W. With C_G(W)=W this places
the source three-space inside W, using the literal conjugation action.

A point centralizing a Sylow Thompson subgroup also has its original
extraspecial core in the Thompson normalizer: their product is a two-group,
and every two-group containing a Sylow Thompson subgroup normalizes it.
These results supply the containment and core-normalization steps of the
original marked Mathieu application, without assuming a Todd splitting.

Source: Aschbacher--Segev, *The uniqueness of groups of type J4*, Invent.
Math. 105 (1991), (4.6)--(4.7), p.598, DOI 10.1007/BF01232280;
Aschbacher--Smith H.14.4(3), H.15.2(5) for the cocode involution ranks.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative commutatorElement
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
variable {G : Type*} [Group G] [Finite G]


/-- Small elementary subgroups normalized by a marked cocode centralize it. -/
theorem cocode_small_normalized_centralizes
    (W A : Subgroup G) [IsElementaryAbelian 2 W] [IsElementaryAbelian 2 A]
    (f : normalizer (W : Set G) →* M24)
    (E : Additive W ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (elementaryRepresentation (p := 2) W.normalizerMonoidHom b v) =
      cocodeRepresentation (f b) (E v))
    (hAW : A ≤ normalizer (W : Set G)) (hWA : W ≤ normalizer (A : Set G))
    (hA : Nat.card A < 16) : A ≤ Subgroup.centralizer (W : Set G) := by
  intro x hx
  let b : normalizer (W : Set G) := ⟨x,hAW hx⟩
  let ρ := elementaryRepresentation (p := 2) W.normalizerMonoidHom
  have htr : f b = 1 := by
    by_contra hne
    have hb : b ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian x hx)
    have hf : orderOf (f b) = 2 := orderOf_eq_prime (by rw [←map_pow,hb,map_one]) hne
    have hlo : 4 ≤ fixedCodim cocodeRepresentation (zpowers (f b)) := by
      rcases M24InvolutionCentralizers.involution_classes (f b) hf with hz | ht
      · rw [CocodeOctad.Involutions.fixedCodim_of_isConj_z _ hz]
      · rw [CocodeOctad.Involutions.fixedCodim_of_isConj_t _ ht]
        decide
    have hcod := fixedCodim_map_equivariant ρ cocodeRepresentation f E hE (zpowers b)
    rw [MonoidHom.map_zpowers] at hcod
    rw [←hcod,fixedCodim_zpowers_eq_displacement_rank] at hlo
    let P := LinearMap.range (ρ b - LinearMap.id)
    have hrange (v : P) : v.val.toMul.val ∈ A := by
      obtain ⟨w,hw⟩ := v.property
      rw [←hw]
      change (x * w.toMul.val * x⁻¹) / w.toMul.val ∈ A
      have hc := (le_normalizer_iff_commutator_le_left.mp hWA)
        (commutator_mem_commutator hx w.toMul.property)
      simpa only [commutatorElement_def,div_eq_mul_inv] using hc
    let j : P → A := fun v => ⟨v.val.toMul.val,hrange v⟩
    have hj : Function.Injective j := by
      intro v w he
      have he' : v.val.toMul.val = w.val.toMul.val := congrArg (fun y : A => (y : G)) he
      exact Subtype.ext (congrArg Additive.ofMul (Subtype.ext he' : v.val.toMul = w.val.toMul))
    have hc := Nat.card_le_card_of_injective j hj
    have hp : Nat.card P = 2 ^ Module.finrank (ZMod 2) P := by
      simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := P)
    have hh : 16 ≤ Nat.card P := by
      rw [hp]
      have hh : 2^4 ≤ 2 ^ Module.finrank (ZMod 2) P :=
        Nat.pow_le_pow_right (by decide) hlo
      exact hh
    omega
  intro w hw
  have he := hE b (Additive.ofMul (⟨w,hw⟩ : W))
  rw [htr,map_one] at he
  have hfix : ρ b (Additive.ofMul (⟨w,hw⟩ : W)) = Additive.ofMul ⟨w,hw⟩ := E.injective he
  have hh := congrArg (fun v : Additive W => v.toMul.val) hfix
  change x*w*x⁻¹=w at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm
/-- A point centralizing the Thompson subgroup has its two-core in the same normalizer. -/
theorem ambientCore_le_normalizer_thompson {t : G} (ht : IsTypeJ4 t)
    (U : Sylow 2 G)
    (htJ : t ∈ Subgroup.centralizer (Stellmacher.elementaryAbelianMaxJ (U : Subgroup G) : Set G)) :
    ambientCore t ≤ normalizer (Stellmacher.elementaryAbelianMaxJ (U : Subgroup G) : Set G) := by
  let J := Stellmacher.elementaryAbelianMaxJ (U : Subgroup G)
  have hJQ : J ≤ normalizer (ambientCore t : Set G) := by
    rw [LocalGeometry.normalizer_ambientCore ht]
    intro j hj
    exact mem_centralizer_singleton_iff.mpr (htJ j hj)
  let := ht.extraspecial
  have hpQ : IsPGroup 2 (ambientCore t) :=
    (IsExtraspecial.isPGroup 2 (core t)).map (centralizer t).subtype
  have hpJ : IsPGroup 2 J := U.isPGroup'.to_le (sSup_le fun _ hA => hA.1)
  exact le_sup_right.trans (Stellmacher.pgroup_le_normalizer_maxJ U (J ⊔ ambientCore t)
    (hpJ.to_sup_of_normal_right' hpQ hJQ) le_sup_left)

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition

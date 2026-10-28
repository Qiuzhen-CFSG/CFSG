module

public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.Quotient
public import Theory.Representation.HexacodeAction.CentralCharacter
public import Theory.GroupTheory.NoncentralChiefRefinement.BinarySections
public import Theory.GroupTheory.ConjugateSpanOrder
public import Mathlib.Order.Atoms.Finite

/-!
# Constructing the maximal quotient used in 13.8.30

Choose a maximal L-normal subgroup W below U_L and above V. The literal chief
quotient U_L/W is elementary abelian even if U_L is not. The seed commutator
relation and generation by L-conjugates force the central cubic to act
nontrivially. The two-core acts trivially, and the actual triple-cover marking
then makes the descended representation faithful. Its binary degree is six
or eighteen by the checked central coset filtration.

The same generation relation makes U_L contained in W L₀. Restriction to
U_L intersect L₀ is therefore still onto U_L/W, with kernel W intersect L₀.
The scalar character is constructed from the original quotient marking. The
final application uses these literal coordinates to turn the corrected
tensor-span dimension calculation into nine actual noncentral chief factors.

The earlier seed action and covered-A₆ marking remain explicit. The original
tensor spans, their dimensions, and the element moving the three-space still
require the 13.8.29 geometry; this does not complete 13.8.30 or 13.8.28.
Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), printed p.964.
-/

public section

open Subgroup Representation NoncentralChiefRefinement
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section08.LinearFour

/-- Restriction retains the literal quotient, its exact kernel and its conjugation action. -/
noncomputable def source_intersection_coordinates
    {L : Type*} [Group L] (W U : NormalNode L)
    [IsElementaryAbelian 2 (Section W U)]
    (X : Subgroup L) [X.Normal] (hWU : W ≤ U)
    (hcover : U.val ≤ W.val ⊔ X) :
    BinaryConjugationSection X (U.val ⊓ X) (W.val ⊓ X)
      ((binarySectionRepresentation W U).comp X.subtype) where
  section_le := inf_le_right
  kernel_le := inf_le_inf_right X hWU
  normalized := by rw [normalizer_eq_top]; exact le_top
  coordinates := {
    toFun := fun u => Multiplicative.ofAdd (Additive.ofMul
      (QuotientGroup.mk' (W.val.subgroupOf U.val) (inclusion (inf_le_left : U.val ⊓ X ≤ U.val) u)))
    map_one' := map_one (QuotientGroup.mk' (W.val.subgroupOf U.val))
    map_mul' := fun u v => map_mul (QuotientGroup.mk' (W.val.subgroupOf U.val))
      (inclusion (inf_le_left : U.val ⊓ X ≤ U.val) u)
      (inclusion (inf_le_left : U.val ⊓ X ≤ U.val) v) }
  onto := by
    intro y
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (W.val.subgroupOf U.val) y.toAdd.toMul
    obtain ⟨w, hw, x, hx, hwx⟩ := mem_sup_of_normal_right.mp (hcover u.property)
    have hxu : x ∈ U.val := by
      have ht := U.val.mul_mem (U.val.inv_mem (hWU hw)) u.property
      rw [← hwx, inv_mul_cancel_left] at ht
      exact ht
    refine ⟨⟨x, hxu, hx⟩, ?_⟩
    change QuotientGroup.mk' (W.val.subgroupOf U.val) ⟨x, hxu⟩ =
      QuotientGroup.mk' (W.val.subgroupOf U.val) u
    apply QuotientGroup.eq_iff_div_mem.mpr
    change x / (u : L) ∈ W.val
    rw [← hwx]
    simpa only [div_eq_mul_inv, mul_inv_rev, mul_inv_cancel_left] using W.val.inv_mem hw
  kernel_eq := by
    ext u
    change QuotientGroup.mk' (W.val.subgroupOf U.val) (inclusion (inf_le_left : U.val ⊓ X ≤ U.val) u) = 1 ↔
      (u : L) ∈ W.val ⊓ X
    exact (QuotientGroup.eq_one_iff (N := W.val.subgroupOf U.val)
      (inclusion (inf_le_left : U.val ⊓ X ≤ U.val) u)).trans
        ⟨fun hw => ⟨hw, u.property.2⟩, fun hw => hw.1⟩
  equivariant _ _ := rfl

/-- The local seed commutator relation propagates through its actual conjugate span. -/
theorem source_generated_commutator
    {L : Type*} [Group L]
    (V U : NormalNode L) (X : Subgroup L) [X.Normal]
    (S : Subgroup L) (hSU : S ≤ U.val) (hVU : V ≤ U)
    (hU : U.val = conjugateSpanBy S ⊤)
    (hseed : S ≤ V.val ⊔ ⁅S, X⁆) : V.val ⊔ ⁅U.val, X⁆ = U.val := by
  apply le_antisymm (sup_le (show V.val ≤ U.val from hVU) (commutator_le_left _ _))
  calc U.val = conjugateSpanBy S ⊤ := hU
       _ ≤ V.val ⊔ ⁅U.val, X⁆ := ?_
  apply conjugateSpanBy_le
  · exact hseed.trans (sup_le_sup_left (commutator_mono hSU le_rfl) V.val)
  · rw [normalizer_eq_top]

end CFSG.Quasithin.Chapter13.Section08.LinearFour

open Theory.GroupTheory Atlas.Codes
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter13.Section08.LinearFour

/-- Construct a maximal quotient, its faithful triple-cover action and its degree alternatives. -/
theorem exists_source_maximal_quotient
    {L : Type*} [Group L] [Finite L]
    (V U : NormalNode L) (hVU : V < U) (hp : IsPGroup 2 U.val)
    (X : Subgroup L) [X.Normal]
    (S : Subgroup L) (hSU : S ≤ U.val)
    (hU : U.val = conjugateSpanBy S ⊤)
    (hseed : S ≤ V.val ⊔ ⁅S, X⁆)
    (e : (L ⧸ pCore 2 L) ≃* HexEvenAutomorphisms)
    (hX : X.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) =
      center HexEvenAutomorphisms) :
    ∃ W : NormalNode L, V ≤ W ∧ W ⋖ U ∧ U.val ≤ W.val ⊔ X ∧
      ∃ hbin : IsElementaryAbelian 2 (Section W U),
        let _ := hbin
        ∃ σ : Representation (ZMod 2) HexEvenAutomorphisms (Additive (Section W U)),
          IsIrreducible σ ∧ Function.Injective σ ∧
          σ.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) =
            binarySectionRepresentation W U ∧
          (Module.finrank (ZMod 2) (Additive (Section W U)) = 6 ∨
            Module.finrank (ZMod 2) (Additive (Section W U)) = 18) := by
  have hgen := source_generated_commutator V U X S hSU hVU.le hU hseed
  obtain ⟨W, hVW, hWU⟩ := exists_le_covBy_of_lt hVU
  have hcover : U.val ≤ W.val ⊔ X := by
    rw [← hgen]
    exact sup_le (le_trans hVW le_sup_left)
      ((commutator_le_right U.val X).trans le_sup_right)
  let hbin := chief_elementary W U hWU hp
  let _ := hbin
  let ρ := binarySectionRepresentation W U
  let _ := binarySection_irreducible W U hWU
  have hk : pCore 2 L ≤ ρ.ker := normal_p_subgroup_le_ker ρ _ pCore_isPGroup
  let σ := (quotientOfLEKer ρ (pCore 2 L) hk).comp e.symm.toMonoidHom
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have he : σ.comp π = ρ := by
    ext g v
    change quotientOfLEKer ρ (pCore 2 L) hk
      (e.symm (e (QuotientGroup.mk' (pCore 2 L) g))) v = ρ g v
    rw [e.symm_apply_apply]
    rfl
  let hirr : IsIrreducible σ := (irreducible_comp_surjective_iff π
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) σ).mp
      (he ▸ (inferInstance : IsIrreducible ρ))
  have hnX : ¬ X ≤ ρ.ker := by
    intro hXker
    have hc : ⁅U.val, X⁆ ≤ W.val := by
      rw [commutator_comm, commutator_le]
      intro x hx u hu
      have heq : sectionAction W U x (QuotientGroup.mk' (W.val.subgroupOf U.val) ⟨u,hu⟩) =
          QuotientGroup.mk' (W.val.subgroupOf U.val) ⟨u,hu⟩ :=
        congrArg (fun f : Module.End (ZMod 2) (Additive (Section W U)) =>
          f (Additive.ofMul (QuotientGroup.mk' (W.val.subgroupOf U.val) ⟨u,hu⟩)))
            (hXker hx)
      have hm := QuotientGroup.eq_iff_div_mem.mp heq
      change x * u * x⁻¹ / u ∈ W.val at hm
      simpa only [commutatorElement_def, div_eq_mul_inv] using hm
    have hUW : U.val ≤ W.val := by rw [← hgen]; exact sup_le hVW hc
    exact hWU.lt.not_ge hUW
  have hf : Function.Injective σ := by
    apply Representation.Hexacode.faithful_of_center_not_le_ker
    intro hc
    apply hnX
    intro x hx
    have hm : π x ∈ center HexEvenAutomorphisms := hX ▸ mem_map_of_mem π hx
    have hh := hc hm
    change σ (π x) = 1 at hh
    change ρ x = 1
    rw [← he]
    exact hh
  exact ⟨W, hVW, hWU, hcover, hbin, σ, hirr, hf, he,
    Representation.Hexacode.TwelveDimensional.faithful_finrank_six_or_eighteen σ hf⟩

end CFSG.Quasithin.Chapter13.Section08.LinearFour

open Subgroup Representation NoncentralChiefRefinement Atlas.Codes
open Representation.Hexacode
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour

/-- The actual marked chief quotient supplies the scalar character and intersected section
needed for the nine-factor argument; only the tensor-span geometry is retained. -/
theorem source_nine_factors_of_chief_quotient
    {L : Type*} [Group L] [Finite L]
    (W U : NormalNode L) [IsElementaryAbelian 2 (Section W U)]
    (X : Subgroup L) [X.Normal] (hWU : W ≤ U)
    (hcover : U.val ≤ W.val ⊔ X)
    (e : (L ⧸ pCore 2 L) ≃* HexEvenAutomorphisms)
    (hX : X.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) =
      center HexEvenAutomorphisms)
    [Module F (Additive (Section W U))]
    [IsScalarTower Bit F (Additive (Section W U))]
    [FiniteDimensional F (Additive (Section W U))]
    (σ : Representation F HexEvenAutomorphisms (Additive (Section W U)))
    [IsIrreducible σ]
    (hs : ∀ w, σ hexEvenZ w = omega • w)
    (haction : ∀ l v, binarySectionRepresentation W U l v =
      σ (e (QuotientGroup.mk' (pCore 2 L) l)) v)
    (S3 : Submodule F (Additive (Section W U))) (UHimage : Submodule F S3)
    (hline : Module.finrank F UHimage = 1)
    (hquotient : Module.finrank F (S3 ⧸ UHimage) = 2)
    (hmoved : ∃ g w, w ∈ S3 ∧ σ g w ∉ S3)
    (t : ChiefSeries X) (ht0 : t.head = ⊥) (ht1 : t.last = ⊤) :
    9 ≤ t.noncentralTwoCount := by
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hc (x : X) : π x.val ∈ center HexEvenAutomorphisms :=
    hX ▸ mem_map_of_mem π x.property
  let c : X →* center HexEvenAutomorphisms :=
    (π.comp X.subtype).codRestrict _ hc
  let χ : X →* Fˣ := centerCharacter.toMonoidHom.comp c
  have hχ : Function.Surjective χ := by
    intro a
    have ha : (centerCharacter.symm a).val ∈ X.map π := by
      rw [hX]
      exact (centerCharacter.symm a).property
    obtain ⟨x, hx, he⟩ := ha
    refine ⟨⟨x, hx⟩, ?_⟩
    change centerCharacter (c ⟨x, hx⟩) = a
    have he' : c ⟨x, hx⟩ = centerCharacter.symm a := Subtype.ext he
    rw [he', centerCharacter.apply_symm_apply]
  have hn : ∃ x, χ x ≠ 1 := by
    let : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp (by
      rw [Nat.card_units, Nat.card_eq_fintype_card, field_card]
      decide)
    obtain ⟨a, ha⟩ := exists_ne (1 : Fˣ)
    obtain ⟨x, rfl⟩ := hχ a
    exact ⟨x, ha⟩
  let τ := (binarySectionRepresentation W U).comp X.subtype
  have hscalar (x : X) (w : Additive (Section W U)) :
      τ x w = (χ x : F) • w := by
    change binarySectionRepresentation W U x.val w = _
    rw [haction]
    exact centerCharacter_action σ hs (c x) w
  exact source_nine_factors_of_marked_quotient X U.val W.val σ hs τ
    (source_intersection_coordinates W U X hWU hcover) χ hχ hn hscalar
    S3 UHimage hline hquotient hmoved t ht0 ht1

end CFSG.Quasithin.Chapter13.Section08.LinearFour

module
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.CentralQuotientSource
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.NaturalSetup
public import CFSG.Quasithin.Chapter6.SourceDefs.ReducedImage

/-!
# Constructing the natural-six source setup from the original quotient

Once the earlier fixed-line alternative has been excluded, the central
quotient map of the chosen Irr⁺ module is injective. Its natural marking
therefore lifts to the same original V, equivariantly for the literal
L/O₂,Z(L) projection. The Sylow two-group supplies the actual nested flag
of orders two, four and eight. No NaturalSetup or flag is an input.

T-invariance, the natural central-quotient classification and triviality of
C_V(L) remain earlier source obligations. In particular this construction
does not eliminate the five-dimensional permutation core in 13.4.1.
Source: Aschbacher–Smith 13.3.2(3), 13.5.2(3), Notation 13.2.1, pp.877,885,915.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.Preparation
open Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
/-- Lift the natural central quotient to the original chosen subgroup.
The acting quotient and its projection are preserved. -/
theorem six_coordinates_of_fixed_quotient
    (D : Chapter12.Section02.ChosenModule T L V)
    (e : (L ⧸ centralCore L) ≃* alternatingGroup (Fin 6))
    (a : D.chosenCentralQuotient ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
    (ha : ∀ (l : L) v, a (D.chosenCentralAction l v) =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 6)
        (e (QuotientGroup.mk' (centralCore L) l)) (a v))
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) :
    ∃ f : V ≃* Multiplicative (BinaryPermutation.natural (Fin 6)),
      ∀ (l : L) (v : V),
        (f (V.normalizerMonoidHom ⟨l.val,D.normalizes l.property⟩ v)).toAdd =
          BinaryPermutation.alternatingNaturalRepresentation (Fin 6)
            (e (QuotientGroup.mk' (centralCore L) l)) (f v).toAdd := by
  let C := (fixedSpace (Chapter12.Section02.reducedRepresentation (L ⊔ (T : Subgroup G)))
    (L.subgroupOf (L ⊔ (T : Subgroup G)))).comap D.space.subtype
  have hC : C = ⊥ := by
    apply bot_unique
    intro v hv
    let x : V := D.spaceEquiv (Multiplicative.ofAdd v)
    have hx : x.val ∈ V ⊓ centralizer (L : Set G) := by
      refine ⟨x.property,?_⟩
      apply mem_centralizer_iff.mpr
      intro l hl
      let l' : L.subgroupOf (L ⊔ (T : Subgroup G)) := ⟨⟨l,mem_sup_left hl⟩,hl⟩
      have hh := hv l'
      have he := congrArg (fun w : Additive (Chapter12.Section02.ReducedModule
        (L ⊔ (T : Subgroup G))) => w.toMul.val.val) hh
      change l * v.val.toMul.val.val * l⁻¹ = v.val.toMul.val.val at he
      rw [show x.val = v.val.toMul.val.val from D.spaceEquiv_apply v]
      exact mul_inv_eq_iff_eq_mul.mp he
    have hx1 : x = 1 := Subtype.ext (mem_bot.mp (hfixed ▸ hx))
    have hv1 : Multiplicative.ofAdd v = 1 :=
      D.spaceEquiv.injective (hx1.trans D.spaceEquiv.map_one.symm)
    exact congrArg Multiplicative.toAdd hv1
  let b : D.space ≃ₗ[ZMod 2] D.chosenCentralQuotient :=
    (Submodule.quotEquivOfEqBot C hC).symm
  let f : V ≃* Multiplicative (BinaryPermutation.natural (Fin 6)) :=
    D.spaceEquiv.symm.trans ((b.trans a).toAddEquiv.toMultiplicative)
  refine ⟨f,?_⟩
  intro l v
  let w : D.space := (D.spaceEquiv.symm v).toAdd
  have hv : (D.spaceEquiv (Multiplicative.ofAdd w) : G) = v.val :=
    congrArg Subtype.val (D.spaceEquiv.apply_symm_apply v)
  have he : V.normalizerMonoidHom ⟨l.val,D.normalizes l.property⟩ v =
      D.spaceEquiv (Multiplicative.ofAdd (D.chosenAction l w)) := by
    apply Subtype.ext
    rw [D.spaceEquiv_apply]
    change l.val * v.val * l.val⁻¹ = l.val * w.val.toMul.val.val * l.val⁻¹
    rw [←D.spaceEquiv_apply w,hv]
  rw [he]
  change a (b (D.spaceEquiv.symm (D.spaceEquiv
    (Multiplicative.ofAdd (D.chosenAction l w)))).toAdd) = _
  rw [D.spaceEquiv.symm_apply_apply]
  exact ha l (C.mkQ w)

/-- Construct the precise ordinary/covered natural-six setup consumed by
13.5, with no assumed flag or prescribed coordinate position. -/
theorem exists_six_setup_of_fixed_quotient
    (h : Counterexample T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (e : (L ⧸ centralCore L) ≃* alternatingGroup (Fin 6))
    (a : D.chosenCentralQuotient ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
    (ha : ∀ (l : L) v, a (D.chosenCentralAction l v) =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 6)
        (e (QuotientGroup.mk' (centralCore L) l)) (a v))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) :
    ∃ V₁ V₂ V₃ : Subgroup G,
      Nonempty (NaturalSetup T L V V₁ V₂ V₃
        (normalizer (L : Set G)) (normalizer (V₁ : Set G))) := by
  obtain ⟨f,hf⟩ := six_coordinates_of_fixed_quotient D e a ha hfixed
  have hcard : Nat.card V = 16 := by
    rw [Nat.card_congr f.toEquiv]
    change Nat.card (BinaryPermutation.natural (Fin 6)) = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      BinaryPermutation.finrank_natural_even (Fin 6) (by decide)]
    rfl
  obtain ⟨V₁,V₂,V₃,h12,h23,h3,hc1,hc2,hc3,hn1,hn2,hn3⟩ :=
    Section03.A5Setup.exists_invariant_flag D.le_sylow hTV hcard
  refine ⟨V₁,V₂,V₃,⟨{
    counterexample := h
    normalizes_L := D.sylow_normalizes_component
    normalizes_V := sup_le D.normalizes hTV
    local_quotient := e
    module_in_reduced := ?_
    coordinate := f
    conjugation := hf
    line_le_plane := h12
    plane_le_seed := h23
    seed_le := h3
    line_card := hc1
    plane_card := hc2
    seed_card := hc3
    line_stable := hn1
    plane_stable := hn2
    seed_stable := hn3
    first_normalizer := rfl
    local_normalizer := rfl
    chosen := D }⟩⟩
  rw [Chapter6.Source.reducedSubgroup_eq_map]
  exact D.le_reduced
end CFSG.Quasithin.Chapter13.Section05.Preparation

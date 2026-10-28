module
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.SourceFF.JankoTwoDegree
public import Theory.Representation.JankoTwo.BinaryTwelveRecognition
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.SourceFF.JankoTwoRootFacts
public import Mathlib.FieldTheory.Finite.Basic

/-!
# The Janko-two source FF exclusion

The source hypotheses first force the binary degree to be twelve. Recognition
then identifies the full original action with the natural G2(4) action, including
the outer field automorphism. The concrete long-root calculation excludes FF.
This supplies the J2 branch of Theorem K.4 and hence Theorem B.4.2.
-/

public noncomputable section

open Representation Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue.SourceFF
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.G2FourModule
open Sporadic.LeechRelated.J2.ExceptionalParabolics
open Atlas.G2.Natural.BinarySemilinear

private theorem inner_index_two : intoExtension.range.index = 2 := by
  have hc : Nat.card intoExtension.range = 604800 :=
    (Nat.card_congr (MonoidHom.ofInjective SecondParabolic.intoExtension_injective).toEquiv).symm.trans
      (SecondParabolic.card_carrier FirstParabolic.card_l₁)
  have h := intoExtension.range.card_mul_index
  rw [hc, SecondParabolic.card_extension FirstParabolic.card_l₁] at h
  omega

private theorem involution_outside : extensionInvolution ∉ intoExtension.range := by
  rintro ⟨j,hj⟩
  exact involution_not_mem_generated (by
    change (extensionInvolution : Equiv.Perm (Fin 100)) ∈ generated
    rw [← hj]
    exact j.property)

private theorem extension_involution_square : extensionInvolution ^ 2 = 1 := by
  apply Subtype.ext
  change involution ^ 2 = 1
  simpa only [pow_two] using involution_mul_self

private theorem outer_coset {x : Extension} (hx : x ∉ intoExtension.range) :
    ∃ j : Carrier, x = intoExtension j * extensionInvolution := by
  have hm : x * extensionInvolution ∈ intoExtension.range :=
    (intoExtension.range.mul_mem_iff_of_index_two inner_index_two).mpr
      (iff_of_false hx involution_outside)
  obtain ⟨j,hj⟩ := hm
  refine ⟨j, ?_⟩
  rw [hj, mul_assoc, ← pow_two, extension_involution_square, mul_one]

private theorem field_smul (c : F) (v : V) :
    fieldEquivalence F fourFrobenius (c • v) = c ^ 2 • fieldEquivalence F fourFrobenius v := by
  have hcoord (x : V) : coordinatesEquiv F (fieldEquivalence F fourFrobenius x) =
      fieldLinear F fourFrobenius (coordinatesEquiv F x) :=
    (coordinatesEquiv F).apply_symm_apply _
  have hsmul (r : F) (x : V) : coordinatesEquiv F (r • x) = r • coordinatesEquiv F x :=
    (Atlas.G2.Restricted.NaturalCoordinates.equiv F).map_smul r x
  apply (coordinatesEquiv F).injective
  rw [hcoord,hsmul,hsmul,hcoord]
  ext i
  change fourFrobenius (c * coordinatesEquiv F v i) = c ^ 2 * fourFrobenius (coordinatesEquiv F v i)
  rw [map_mul,fourFrobenius_apply]

private theorem outer_semilinear (d : MarkedEmbedding) {x : Extension}
    (hx : x ∉ intoExtension.range) (c : F) (v : V) :
    d.outerRepresentation x (c • v) = c ^ 2 • d.outerRepresentation x v := by
  obtain ⟨j,rfl⟩ := outer_coset hx
  rw [map_mul, Module.End.mul_apply, d.outer_on_involution, d.outer_on_inner,
    field_smul, map_smul, Module.End.mul_apply, d.outer_on_involution, d.outer_on_inner]

private theorem four_generator : ∃ a : F, a ^ 2 - a = 1 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hc : Nat.card F = 4 := GaloisField.card 2 2 (by decide)
  have hcu : Nat.card Fˣ = 3 := by
    rw [Nat.card_units, hc]
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 (by rw [hcu])
  have hne : (a : F) ≠ 1 := by
    intro h
    have ha1 : a = 1 := Units.ext h
    simp only [ha1,orderOf_one] at ha
    omega
  have hp : (a : F) ^ 3 = 1 := by
    have hh : a ^ 3 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
    exact congrArg (fun a : Fˣ => (a : F)) hh
  have hz : ((a : F)-1)*((a : F)^2+a+1) = 0 := by
    calc
      _ = (a : F)^3-1 := by ring
      _ = 0 := by rw [hp,sub_self]
  have hs := (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)
  refine ⟨a, ?_⟩
  have hh : (a : F)^2+a = -1 := eq_neg_of_add_eq_zero_left hs
  simpa only [sub_eq_add_neg,CharTwo.neg_eq] using hh

universe u v
variable {G : Type u} [Group G] [Finite G]
  {W : Type v} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

private theorem range_cases (eL : generalizedFitting G ≃* Carrier) :
    (SimpleFittingExtensions.ambientAction eL).range = intoExtension.range ∨
    (SimpleFittingExtensions.ambientAction eL).range = ⊤ := by
  have hle := SimpleFittingExtensions.inner_le_ambientAction_range eL
  have hd : (SimpleFittingExtensions.ambientAction eL).range.index ∣ 2 :=
    inner_index_two ▸ Subgroup.index_dvd_of_le hle
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · exact Or.inr (Subgroup.index_eq_one.mp h)
  · have hh := Subgroup.relIndex_mul_index hle
    rw [h,inner_index_two] at hh
    have hr : intoExtension.range.relIndex (SimpleFittingExtensions.ambientAction eL).range = 1 := by omega
    exact Or.inl (le_antisymm (Subgroup.relIndex_eq_one.mp hr) hle)

set_option backward.isDefEq.respectTransparency false in
private theorem whole_equivalence [IsSimpleGroup Carrier] [IsSimpleGroup (generalizedFitting G)]
    (ρ : Representation (ZMod 2) G W)
    (hf : Function.Injective ρ) (hi : IsIrreducible (ρ.comp (generalizedFitting G).subtype))
    (hd : Module.finrank (ZMod 2) W = 12) (eL : generalizedFitting G ≃* Carrier) :
    Nonempty (RepEquiv ρ
      (Embedding.markedEmbedding.outerRepresentation.comp (SimpleFittingExtensions.ambientAction eL))) := by
  let f := SimpleFittingExtensions.ambientAction eL
  have hf' : Function.Injective f := SimpleFittingExtensions.ambientAction_injective eL
  rcases range_cases eL with hrange | hrange
  · have htop : generalizedFitting G = ⊤ := by
      apply top_unique
      intro x _
      have hx : f x ∈ intoExtension.range := hrange ▸ (show f x ∈ f.range from ⟨x,rfl⟩)
      obtain ⟨j,hj⟩ := hx
      have he : f (eL.symm j) = f x := by
        rw [SimpleFittingExtensions.ambientAction_on_fitting,eL.apply_symm_apply]
        exact hj
      exact hf' he ▸ (eL.symm j).property
    let d : generalizedFitting G ≃* G := (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
    let a : G ≃* Carrier := d.symm.trans eL
    have hfa (x : G) : f x = intoExtension (a x) := by
      have hx : ((d.symm x : generalizedFitting G) : G) = x := d.apply_symm_apply x
      change f x = intoExtension (eL (d.symm x))
      rw [← SimpleFittingExtensions.ambientAction_on_fitting, hx]
    have his : IsIrreducible ρ :=
      (irreducible_comp_surjective_iff (generalizedFitting G).subtype
        (fun x => ⟨d.symm x,d.apply_symm_apply x⟩) ρ).mp hi
    let σ := ρ.comp a.symm.toMonoidHom
    let : IsIrreducible σ :=
      (irreducible_comp_surjective_iff a.symm.toMonoidHom a.symm.surjective ρ).mpr his
    obtain ⟨e⟩ := Embedding.binary_equiv_marked_of_finrank_twelve σ (hf.comp a.symm.injective) hd
    refine ⟨{toLinearEquiv := e.toLinearEquiv, isIntertwining' := fun g => ?_}⟩
    apply LinearMap.ext
    intro w
    have he := LinearMap.congr_fun (e.isIntertwining' (a g)) w
    change e (ρ (a.symm (a g)) w) = Embedding.markedEmbedding.innerRepresentation (a g) (e w) at he
    rw [a.symm_apply_apply,Embedding.markedEmbedding.innerRepresentation_apply] at he
    change e (ρ g w) = Embedding.markedEmbedding.outerRepresentation (f g) (e w)
    rw [hfa,Embedding.markedEmbedding.outer_on_inner]
    exact he
  · have hsur : Function.Surjective f := MonoidHom.range_eq_top.mp hrange
    let a : G ≃* Extension := MulEquiv.ofBijective f ⟨hf',hsur⟩
    have hin (j : Carrier) : a.symm (intoExtension j) = (eL.symm j : G) := by
      apply a.injective
      rw [a.apply_symm_apply]
      change intoExtension j = f (eL.symm j)
      rw [SimpleFittingExtensions.ambientAction_on_fitting,eL.apply_symm_apply]
    let σ := ρ.comp a.symm.toMonoidHom
    have heq : σ.comp intoExtension = (ρ.comp (generalizedFitting G).subtype).comp eL.symm.toMonoidHom := by
      ext j w
      change ρ (a.symm (intoExtension j)) w = ρ (eL.symm j) w
      rw [hin]
    let : IsIrreducible (σ.comp intoExtension) := by
      rw [heq]
      exact (irreducible_comp_surjective_iff eL.symm.toMonoidHom eL.symm.surjective _).mpr hi
    obtain ⟨e⟩ := Embedding.outer_equiv_marked_of_finrank_twelve σ (hf.comp a.symm.injective) hd
    refine ⟨{toLinearEquiv := e.toLinearEquiv, isIntertwining' := fun g => ?_}⟩
    apply LinearMap.ext
    intro w
    have he := LinearMap.congr_fun (e.isIntertwining' (a g)) w
    change e (ρ (a.symm (a g)) w) = Embedding.markedEmbedding.outerRepresentation (a g) (e w) at he
    change e (ρ g w) = Embedding.markedEmbedding.outerRepresentation (a g) (e w)
    simpa only [a.symm_apply_apply] using he

/-- Degree twelve and a center-free component supply the genuine marking of
 the original whole action, including its outer field action. The degree
 reduction can be supplied by either the FF or the cubic source argument. -/
theorem j2_marked_of_center_and_degree (ρ : Representation (ZMod 2) G W) (L : Subgroup G)
    (h : RankOne.SourceHypotheses ρ L)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.j2.Carrier))
    (hZ : center L = ⊥) (hd : Module.finrank (ZMod 2) W = 12) :
    Nonempty (JankoTwo.MarkedModule (K := F) ρ) := by
  rcases h.fitting with rfl
  obtain ⟨e⟩ := he
  let : IsSimpleGroup (generalizedFitting G ⧸ center (generalizedFitting G)) := h.quasisimple.simple
  let : IsSimpleGroup Carrier := e.symm.isSimpleGroup
  let eL : generalizedFitting G ≃* Carrier :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e
  let : IsSimpleGroup (generalizedFitting G) := eL.isSimpleGroup
  let d := Embedding.markedEmbedding
  let f := SimpleFittingExtensions.ambientAction eL
  have hf : Function.Injective f := SimpleFittingExtensions.ambientAction_injective eL
  obtain ⟨E⟩ := whole_equivalence ρ h.faithful h.irreducible hd eL
  obtain ⟨a,ha⟩ := four_generator
  refine ⟨{
    fieldDegree := GaloisField.finrank 2 (by decide : 2 ≠ 0)
    fieldGenerator := a
    generator_relation := ha
    inner := generalizedFitting G
    normal := inferInstance
    carrierEquiv := eL
    ambientEmbedding := extensionEquivAut.toMonoidHom.comp f
    ambient_injective := extensionEquivAut.injective.comp hf
    ambient_inner := ?_
    embedding := d.inner.comp eL.toMonoidHom
    embedding_injective := d.inner_injective.comp eL.injective
    action := d.outerRepresentation.comp f
    equiv := E.toRepresentationEquiv
    inner_action := ?_
    outer_semilinear := ?_ }⟩
  · intro l
    change extensionEquivAut (f l) = MulAut.conj (eL l)
    rw [SimpleFittingExtensions.ambientAction_on_fitting,extensionEquivAut_intoExtension]
  · intro l v
    change d.outerRepresentation (f l) v = JankoTwo.naturalAction F (d.inner (eL l)) v
    rw [SimpleFittingExtensions.ambientAction_on_fitting,d.outer_on_inner]
    rfl
  · intro i hi _ c v
    have hout : f i ∉ intoExtension.range := by
      rintro ⟨j,hj⟩
      have hh : f (eL.symm j) = f i := by
        rw [SimpleFittingExtensions.ambientAction_on_fitting,eL.apply_symm_apply]
        exact hj
      exact hi (hf hh ▸ (eL.symm j).property)
    exact outer_semilinear d hout c v

/-- The original source FF action has the genuine natural-module marking,
including its outer action. -/
theorem j2_marked (ρ : Representation (ZMod 2) G W) (L : Subgroup G)
    (h : RankOne.SourceHypotheses ρ L) (hff : Representation.BinaryOffender.IsFFModule ρ)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.j2.Carrier)) :
    Nonempty (JankoTwo.MarkedModule (K := F) ρ) := by
  obtain ⟨hZ, hd⟩ := j2_center_and_degree h hff he
  exact j2_marked_of_center_and_degree ρ L h he hZ hd

/-- The J2 central quotient is impossible for the original source FF action. -/
theorem not_ff_j2 {ρ : Representation (ZMod 2) G W} {L : Subgroup G} (h : RankOne.SourceHypotheses ρ L)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.j2.Carrier)) :
    ¬ Representation.BinaryOffender.IsFFModule ρ := by
  intro hff
  obtain ⟨D⟩ := j2_marked ρ L h hff he
  exact D.not_isFFModule_four hff

end CFSG.Quasithin.ChapterK.SporadicCatalogue.SourceFF

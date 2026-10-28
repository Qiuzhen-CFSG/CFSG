module

public import CFSG.Quasithin.Chapter13.Section05.A5Source.LocalNormality
public import CFSG.Quasithin.ChapterB.Section02.OffenderFactorization
public import CFSG.Quasithin.ChapterB.Section03.Offenders.OddParity
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Stellmacher.ElementaryAbelianMaxJMap

/-!
# The full original symmetric-five action when J(T) moves V

The chosen module provides literal coordinates on V≤LT. B.2.7 gives an
actual offender in the faithful local action image whenever J(T) moves V.
Transporting through the original marked coordinates gives an offender on
the five-point augmentation core. Such an offender contains an odd
permutation, so the action image, already containing A₅, is all of S₅.

All maps are the original Context maps. No surjectivity, Thompson image,
Baumann identity or outside-subgroup conclusion is assumed.
Source: Aschbacher–Smith 13.2.4(2b), printed p.879, using B.2.7 and B.3.2.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

/-- The original marked core identifies the actual module inside LT. -/
noncomputable def localModuleCoordinates :
    letI := d.reduced.elementary
    BinaryPermutation.core (Fin 5) ≃ₗ[ZMod 2]
      Additive (V.subgroupOf (L ⊔ (T : Subgroup G))) := by
  let := d.reduced.elementary
  let η : Multiplicative (BinaryPermutation.core (Fin 5)) →*
      V.subgroupOf (L ⊔ (T : Subgroup G)) := {
    toFun := fun x => ⟨⟨d.flag.module.map x,
      (le_sup_right : (T : Subgroup G) ≤ L ⊔ (T : Subgroup G))
        (d.chosen.le_sylow (d.flag.module.range_eq.le ⟨x,rfl⟩))⟩,
      d.flag.module.range_eq.le ⟨x,rfl⟩⟩
    map_one' := Subtype.ext (Subtype.ext (map_one _))
    map_mul' := fun x y => Subtype.ext (Subtype.ext (map_mul _ x y)) }
  have hi : Function.Injective η := fun x y h => d.flag.module.injective
    (congrArg (fun v : V.subgroupOf (L ⊔ (T : Subgroup G)) => ((v : (L ⊔ (T : Subgroup G) : Subgroup G)) : G)) h)
  have hs : Function.Surjective η := by
    intro v
    obtain ⟨x,hx⟩ := d.flag.module.range_eq.ge v.property
    exact ⟨x,Subtype.ext (Subtype.ext hx)⟩
  let e := MulEquiv.ofBijective η ⟨hi,hs⟩
  let a := (AddEquiv.additiveMultiplicative (BinaryPermutation.core (Fin 5))).symm.trans e.toAdditive
  exact { a with map_smul' := ZMod.map_smul a }

/-- Pointwise compatibility with the literal local action-image representation. -/
theorem localModuleCoordinates_equivariant :
    letI := d.reduced.normal
    letI := d.reduced.elementary
    let q := d.localActor.rangeRestrict
    let hk := d.localActor.ker_rangeRestrict.trans d.localActor_kernel
    let ρ := NormalElementaryQuotient.representation
      (V.subgroupOf (L ⊔ (T : Subgroup G))) q d.localActor.rangeRestrict_surjective hk
    ∀ (g : (L ⊔ (T : Subgroup G) : Subgroup G)) (v : BinaryPermutation.core (Fin 5)),
      ρ (q g) (d.localModuleCoordinates v) =
        d.localModuleCoordinates (BinaryPermutation.coreRepresentation (Fin 5) (d.localActor g) v) := by
  let := d.reduced.normal
  let := d.reduced.elementary
  dsimp only
  intro g v
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Subtype.ext
  rw [NormalElementaryQuotient.representation_apply]
  exact d.flag.normalizer_equivariant
    ⟨g,(sup_le d.chosen.normalizes d.flag.T_normalizes) g.property⟩ v

/-- The original LT action is onto S₅ as soon as J(T) moves its chosen module. -/
theorem localActor_surjective_of_thompson_moves
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G)) :
    Function.Surjective d.localActor := by
  let K := L ⊔ (T : Subgroup G)
  let U := V.subgroupOf K
  let := d.reduced.normal
  let := d.reduced.elementary
  let q := d.localActor.rangeRestrict
  have hk : q.ker = centralizer (U : Set K) :=
    d.localActor.ker_rangeRestrict.trans d.localActor_kernel
  let ρ := NormalElementaryQuotient.representation U q d.localActor.rangeRestrict_surjective hk
  let S := T.subtype (show (T : Subgroup G) ≤ K from le_sup_right)
  have hm : (elementaryAbelianMaxJ (S : Subgroup K)).map K.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective K.subtype K.subtype_injective]
    congr 1
    exact map_subgroupOf_eq_of_le le_sup_right
  have hj : ¬ elementaryAbelianMaxJ (S : Subgroup K) ≤ q.ker := by
    intro hc
    apply hJ
    rw [← hm]
    rintro x ⟨x,hx,rfl⟩ v hv
    have hc' := hk ▸ hc hx
    exact congrArg K.subtype (hc' ⟨v,(le_sup_right : (T : Subgroup G) ≤ K) (d.chosen.le_sylow hv)⟩ hv)
  have hUS : U ≤ (S : Subgroup K) := fun _ hv => d.chosen.le_sylow hv
  obtain ⟨A,hA⟩ := (ChapterB.lemma_B_2_7_local U q d.localActor.rangeRestrict_surjective hk
    (S : Subgroup K) hUS hj).1
  have he : ∀ g v, d.localModuleCoordinates.symm (ρ g v) =
      BinaryPermutation.coreRepresentation (Fin 5) g.val (d.localModuleCoordinates.symm v) := by
    intro g v
    obtain ⟨g,rfl⟩ := d.localActor.rangeRestrict_surjective g
    apply d.localModuleCoordinates.injective
    rw [LinearEquiv.apply_symm_apply]
    have hh := d.localModuleCoordinates_equivariant g (d.localModuleCoordinates.symm v)
    rw [LinearEquiv.apply_symm_apply] at hh
    exact hh
  have ha := hA.map_equivariant ρ (BinaryPermutation.coreRepresentation (Fin 5))
    d.localActor.range.subtype d.localActor.range.subtype_injective d.localModuleCoordinates.symm he
  have hnot := ChapterB.Offenders.core_offender_not_le_alternating (Or.inl rfl) ha
  apply MonoidHom.range_eq_top.mp
  have hi : d.localActor.range.index ∣ 2 := by
    simpa only [alternatingGroup.index_eq_two] using
      index_dvd_of_le d.alternating_le_localActor
  rcases (Nat.dvd_prime Nat.prime_two).mp hi with hi | hi
  · exact index_eq_one.mp hi
  · have hr := Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi
    exact (hnot ((map_subtype_le A).trans_eq hr)).elim

end CFSG.Quasithin.Chapter13.Section05.A5Source.Context

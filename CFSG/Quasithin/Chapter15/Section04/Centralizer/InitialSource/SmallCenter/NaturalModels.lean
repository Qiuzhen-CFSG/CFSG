module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.SmallCenter.PairFailure
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.CentralLineAction
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.NaturalModels

/-!
# Actual natural actions in the small-center source branch

The local module is the original normal closure of Ω₁(Z(T)), and its
centralizer is the actual two-core. The constructed solvable Thompson
action, with no supplied factors or coordinates, is either the full natural
binary SL₂ action or the full split four-dimensional orthogonal action.
The actor equivalence uses M/O₂(M) and intertwines the original conjugation
on V(M), pointwise on the original quotient map.

The final consumer applies these coordinates to the very maximal local
where the specified characteristic Baumann subgroup fails pair control.
The uniform C.1.18 pair and fixed-pair C.1.28 block remain source obligations.
Source: Aschbacher--Smith 15.4.7, printed p.1158.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource.SmallCenter
open FamilySource FamilySource.ModuleStructure ChapterA.Section05To06
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Full compatible coordinates on the original core quotient and module;
neither a local model nor a decomposition is an input. -/
theorem local_natural_coordinates {T : Sylow 2 G} {M X : Subgroup G} {s : ℕ}
    (h : Input KnownSimple.IsKnownSimple T M X s)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2) :
    let U := internalModule T M
    letI := internalModule_elementary T M h.sylow_le
      (h.ambient.evenCharacteristic T M h.maximal h.sylow_le)
    (∃ (c : Additive U ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
      (e : CoreQuotient M ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)),
      ∀ (m : M) (v : U), c (Additive.ofMul (MulAut.conjNormal m v)) =
        Representation.specialLinearNatural 2 (e (quotientMap M m)) (c (Additive.ofMul v))) ∨
    (∃ (c : Additive U ≃ₗ[ZMod 2] OrthogonalFourBinary.Space)
      (e : CoreQuotient M ≃* OrthogonalFourBinary.TerminalLines.IsometryGroup),
      ∀ (m : M) (v : U), c (Additive.ofMul (MulAut.conjNormal m v)) =
        (e (quotientMap M m)).val (c (Additive.ofMul v))) := by
  let U := internalModule T M
  let := internalModule_elementary T M h.sylow_le
    (h.ambient.evenCharacteristic T M h.maximal h.sylow_le)
  have hU : IsPReduced 2 U := ⟨inferInstance,inferInstance,
    internalModule_reduced T M h.sylow_le h.center_centralizer⟩
  have hJ : ¬ elementaryAbelianMaxJ
      ((T.subtype h.sylow_le : Sylow 2 M) : Subgroup M) ≤ centralizer (U : Set M) := by
    intro hh
    apply h.thompson_moved
    have hm := map_mono (f := M.subtype) hh
    rw [←elementaryAbelianMaxJ_map_injective M.subtype M.subtype_injective,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le h.sylow_le,map_centralizer_subtype] at hm
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp (hm.trans inf_le_right))
  obtain ⟨d,hn,hW,hcent,honto,_,_⟩ :=
    Section03.InitialSource.solvable_small_action_of_central_order_two h.ambient T
      ⟨h.maximal,h.sylow_le⟩ hZ h.solvable U hU hJ
  let q := QuotientGroup.mk' (centralizer (U : Set M))
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  let a : CoreQuotient M ≃* (M ⧸ centralizer (U : Set M)) :=
    QuotientGroup.quotientMulEquivOfEq (internal_centralizer T M h.sylow_le h.center_centralizer).symm
  have hact (m : M) (v : U) :
      ρ (q m) (Additive.ofMul v) = Additive.ofMul (MulAut.conjNormal m v) := by
    apply Additive.toMul.injective
    exact Subtype.ext (NormalElementaryQuotient.representation_apply U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) m (Additive.ofMul v))
  rcases hn with hn | hn
  · obtain ⟨c,e,he⟩ := d.toSolvableFFFactors.one_factor_natural_coordinates hn hW hcent
    refine Or.inl ⟨c,a.trans e,?_⟩
    intro m v
    have hh := he (q m) (Additive.ofMul v)
    change c (ρ (q m) (Additive.ofMul v)) = _ at hh
    rw [hact] at hh
    exact hh
  · obtain ⟨c,e,he⟩ := d.toSolvableFFFactors.two_factor_orthogonal_coordinates hn
      (NormalElementaryQuotient.representation_injective U q
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) hW hcent honto
    refine Or.inr ⟨c,a.trans e,?_⟩
    intro m v
    have hh := he (q m) (Additive.ofMul v)
    change c (ρ (q m) (Additive.ofMul v)) = _ at hh
    rw [hact] at hh
    exact hh

/-- The actual fixed-pair obstruction local has one of the two original
small natural core quotients; all local hypotheses and the member are built. -/
theorem source_fixed_pair_failure_models
    (hA : ∀ (H : Type u) [Group H] [Finite H],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple H)
    (hC : ∀ (H : Type u) [Group H] [Finite H],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple H)
    (h311 : RatioSource.Earlier311 (G := G))
    (h29 : RatioSource.OutsideWitness.EarlierE29Solvable.{u})
    (hB : Chapter1.RadicalNormalizers.ThompsonSource.TheoremB216.{u})
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (D : Subgroup (ChapterB.baumann (T : Subgroup G))) [D.Characteristic] (hne : D ≠ ⊥) :
    ∃ (M X : Subgroup G) (s : ℕ),
      Input KnownSimple.IsKnownSimple T M X s ∧ Group.rank (localV T M) = 2*s ∧
      (centralizer (((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf M) : Set M) ⊔
        normalizer (((D.map (ChapterB.baumann (T : Subgroup G)).subtype).subgroupOf M) : Set M)) < ⊤ ∧
      (Nonempty (CoreQuotient M ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) ∨
        Nonempty (CoreQuotient M ≃* OrthogonalFourBinary.TerminalLines.IsometryGroup)) := by
  obtain ⟨M,X,s,hs,hr,hp⟩ := source_fixed_pair_failure hA hC h311 h29 hB
    hG T hempty hmany hZ D hne
  refine ⟨M,X,s,hs,hr,hp,?_⟩
  rcases local_natural_coordinates hs hZ with ⟨_,e,_⟩ | ⟨_,e,_⟩
  · exact Or.inl ⟨e⟩
  · exact Or.inr ⟨e⟩

end CFSG.Quasithin.Chapter15.Section04.InitialSource.SmallCenter

module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.G2.LowerObstruction.ComponentRank.Radical
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.G2.LowerObstruction.ComponentRank.FixedGeometry
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing

/-!
# The G₂ component rank obstruction

The E₂ rank is computed in the intrinsic quotient H/O∞(H). Linear two-core
saturation makes the intersection of a full highest-root group with O₂(H)
trivial or total. Both source component alternatives exclude the total case.
The two-closed radical then gives a trivial kernel in the literal radical
quotient, so its image has rank exactly f. The rank obstruction and confinement
below have no remaining geometry premises. The earlier conditional reduction
is retained as a separate public interface.

This proves the component E-member obstruction used in Aschbacher--Smith
E.1.14(1), printed p.214, citing Asc82a Lemma 4.7, with the definitions of
E.1.1--6 on pp.209--210. The local tau orbit, two-closed radical, O^2(H)=H∞,
and both component alternatives are retained in `ECaseComponent`. Normality
of the model copy suffices, including all ambient outer two-extensions.
The parent owns the remaining E₁ and weak-closure assembly for n(G) ≥ f.
-/

public section

namespace CFSG.Quasithin.ChapterE.ExceptionalValues.G2.LowerObstruction.ComponentRank
open Subgroup Theory.GroupTheory Atlas.G2
variable {G F : Type*} [Group G] [Finite G] [Field F] [CharP F 2]

/-- Conditional assembly, retaining the exact local component witnesses.
The two geometric premises are not supplied by this theorem. -/
theorem rank_lower_bound_of_component_geometry
    (L T : Subgroup G) (e : L ≃* Model F)
    {A H : Subgroup G} (hA : A ∈ family L e)
    (hm : IsEMember T A H) (hc : ECaseComponent T A H)
    {f : ℕ} (hF : Nat.card F = 2 ^ f)
    (hfixed : ∀ D : Subgroup (H ⧸ solvableRadical H),
      IsComponent (H ⧸ solvableRadical H) D →
      componentLayer (H ⧸ solvableRadical H) = conjugateJoin
        ((tau (T.subgroupOf H) (A.subgroupOf H)).map
          (QuotientGroup.mk' (solvableRadical H))) D →
      D = ⁅D, (A.subgroupOf H).map (QuotientGroup.mk' (solvableRadical H))⁆ →
      A.subgroupOf H ⊓ pCore 2 H ≠ ⊥ → H ≤ shortOvergroup L T e)
    (hpermuted : ∀ D : Subgroup (H ⧸ solvableRadical H),
      IsComponent (H ⧸ solvableRadical H) D →
      componentLayer (H ⧸ solvableRadical H) = conjugateJoin
        ((tau (T.subgroupOf H) (A.subgroupOf H)).map
          (QuotientGroup.mk' (solvableRadical H))) D →
      ¬ (A.subgroupOf H).map (QuotientGroup.mk' (solvableRadical H)) ≤
        normalizer (D : Set (H ⧸ solvableRadical H)) →
      Group.rank ((A.subgroupOf H).map
        (QuotientGroup.mk' (solvableRadical H))) = 1 → H ≤ shortOvergroup L T e)
    (hescape : ¬ H ≤ shortOvergroup L T e) :
    f ≤ Group.rank ((A.subgroupOf H).map
      (QuotientGroup.mk' (solvableRadical H))) := by
  by_contra hlt
  have hkernel := (proper_core_kernel_of_rank_lt L e hA hm hc hF
    (Nat.lt_of_not_ge hlt)).1
  obtain ⟨_, _, _, D, hD, horbit, haction | hperm⟩ := hc
  · exact hescape (hfixed D hD horbit haction hkernel)
  · exact hescape (hpermuted D hD horbit hperm.1 hperm.2)

omit [CharP F 2] in
/-- The literal quotient-rank bound gives the confinement form used in the
parent lower-bound assembly. The geometric rank theorem remains an input. -/
theorem confinement_of_rank_obstruction
    (L T : Subgroup G) (e : L ≃* Model F) {A H : Subgroup G}
    {f : ℕ} (hf : 0 < f)
    (hobstruction : ¬ H ≤ shortOvergroup L T e →
      f ≤ Group.rank ((A.subgroupOf H).map
        (QuotientGroup.mk' (solvableRadical H))))
    (hr : Group.rank ((A.subgroupOf H).map
      (QuotientGroup.mk' (solvableRadical H))) ≤ f - 1) :
    H ≤ shortOvergroup L T e := by
  by_contra h
  have := hobstruction h
  omega

/-- The source E₂ quotient-rank obstruction. In fact the literal image has
rank exactly f, whether its component is fixed or permuted. Normality suffices;
the stronger source hypotheses on the socle and its Sylow alignment are not
needed for this branch. -/
theorem rank_lower_bound
    (L T : Subgroup G) [L.Normal] (e : L ≃* Model F)
    {A H : Subgroup G} (hA : A ∈ family L e)
    (hm : IsEMember T A H) (hc : ECaseComponent T A H)
    {f : ℕ} (hF : Nat.card F = 2 ^ f) :
    f ≤ Group.rank ((A.subgroupOf H).map
      (QuotientGroup.mk' (solvableRadical H))) :=
  (component_rank_eq_field_degree L e hA hm hc hF).ge

/-- An E₂ member of the full ambient root family at quotient rank at most
f-1 lies in the specified short overgroup. This discharges the E₂ branch in
E.1.5 for the parent lower-obstruction assembly, without an E₁ or weak-closure
assumption. -/
theorem confinement
    (L T : Subgroup G) [L.Normal] (e : L ≃* Model F)
    {A H : Subgroup G} (hA : A ∈ family L e)
    (hm : IsEMember T A H) (hc : ECaseComponent T A H)
    {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2 ^ f)
    (hr : Group.rank ((A.subgroupOf H).map
      (QuotientGroup.mk' (solvableRadical H))) ≤ f - 1) :
    H ≤ shortOvergroup L T e :=
  confinement_of_rank_obstruction L T e hf
    (fun _ => rank_lower_bound L T e hA hm hc hF) hr

/-- Apply the completed obstruction to the literal generalized Fitting
subgroup and Sylow subgroup of E.1.14. The parent supplies the actual full-model
equivalence; no quotient identification or geometric witness is assumed. -/
theorem source_confinement
    (T : Sylow 2 G) (e : generalizedFitting G ≃* Model F)
    {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    {A H : Subgroup G} (hA : A ∈ family (generalizedFitting G) e)
    (hm : IsEMember (T : Subgroup G) A H)
    (hc : ECaseComponent (T : Subgroup G) A H)
    (hr : Group.rank ((A.subgroupOf H).map
      (QuotientGroup.mk' (solvableRadical H))) ≤ f - 1) :
    H ≤ shortOvergroup (generalizedFitting G) (T : Subgroup G) e :=
  confinement (generalizedFitting G) (T : Subgroup G) e hA hm hc
    (lt_trans Nat.zero_lt_one hf) hF hr

end CFSG.Quasithin.ChapterE.ExceptionalValues.G2.LowerObstruction.ComponentRank

module
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Order
public import Mathlib.Order.Cover

/-!
# Covers through subgroup correspondence

A surjective group homomorphism identifies subgroups of its target with
subgroups containing its kernel. This correspondence preserves covers and
maximal proper subgroups. Inclusion of a subgroup identifies its subgroup
lattice with the lower interval and also preserves covers.

These facts retain the literal maps used to lift binary parabolics.
-/

public noncomputable section
namespace Subgroup
private def surjectiveCorrespondence {H K : Type*} [Group H] [Group K]
    (f : H →* K) (hf : Function.Surjective f) :
    Subgroup K ≃o Set.Ici f.ker where
  toFun P := ⟨P.comap f,P.ker_le_comap f⟩
  invFun P := P.val.map f
  left_inv P := map_comap_eq_self_of_surjective hf P
  right_inv P := Subtype.ext (comap_map_eq_self P.property)
  map_rel_iff' := comap_le_comap_of_surjective hf

theorem comap_covBy_iff_of_surjective {H K : Type*} [Group H] [Group K]
    (f : H →* K) (hf : Function.Surjective f) (A B : Subgroup K) :
    A.comap f ⋖ B.comap f ↔ A ⋖ B := by
  have hconv : (Set.range (OrderEmbedding.subtype (fun P : Subgroup H => f.ker ≤ P))).OrdConnected := by
    simpa only [OrderEmbedding.coe_subtype,Subtype.range_coe_subtype] using! Set.ordConnected_Ici
  exact (Set.OrdConnected.apply_covBy_apply_iff
    (OrderEmbedding.subtype (fun P : Subgroup H => f.ker ≤ P)) hconv).trans
      (apply_covBy_apply_iff (surjectiveCorrespondence f hf))

theorem isCoatom_map_of_surjective_of_ker_le {H K : Type*} [Group H] [Group K]
    (f : H →* K) (hf : Function.Surjective f) (C : Subgroup H)
    (hk : f.ker ≤ C) (hC : IsCoatom C) : IsCoatom (C.map f) := by
  have hr : f.range = ⊤ := MonoidHom.range_eq_top.mpr hf
  constructor
  · intro he
    have hh := congrArg (Subgroup.comap f) he
    rw [comap_map_eq_self hk,comap_top] at hh
    exact hC.1 hh
  · intro P hP
    have hle : C ≤ P.comap f := map_le_iff_le_comap.mp hP.le
    have hne : C ≠ P.comap f := by
      intro he
      have hh := congrArg (Subgroup.map f) he
      rw [map_comap_eq_self_of_surjective hf] at hh
      exact hP.ne hh
    have hh := congrArg (Subgroup.map f) (hC.2 _ (lt_of_le_of_ne hle hne))
    rwa [map_comap_eq_self_of_surjective hf,←MonoidHom.range_eq_map,hr] at hh

/-- The literal subgroup inclusion preserves covers, since its image is
the interval of subgroups contained in H. -/
theorem covBy_map_subtype_iff {K : Type*} [Group K] (H : Subgroup K)
    (A B : Subgroup H) : A.map H.subtype ⋖ B.map H.subtype ↔ A ⋖ B := by
  have hconv : (Set.range (OrderEmbedding.subtype (fun P : Subgroup K => P ≤ H))).OrdConnected := by
    simpa only [OrderEmbedding.coe_subtype,Subtype.range_coe_subtype] using! Set.ordConnected_Iic
  exact (Set.OrdConnected.apply_covBy_apply_iff
    (OrderEmbedding.subtype (fun P : Subgroup K => P ≤ H)) hconv).trans
      (apply_covBy_apply_iff (MapSubtype.orderIso H))


end Subgroup

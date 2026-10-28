module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysisData

/-!
# The two elementary subgroups in Janko's Case II

The binary factor is `E`, and the centralizer of the actor `d` inside the
local model is `F`. Finite coordinate calculations prove their orders,
exponents and centralizers. Both contain `z 0`, so their ambient centralizers
lie in the given involution centralizer; this makes the local calculations
valid in the arbitrary ambient group.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), 1–19, Section 2, pp.3–4.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy
namespace CaseII
universe u

local instance : DecidableEq TwistedModel := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) SemidirectProduct.ext_iff.symm
local instance : Fintype TwistedModel := Fintype.ofEquiv
  (BinaryFour × SymmetricFour) SemidirectProduct.equivProd.symm

/-- The first elementary subgroup in the coordinate model. -/
@[expose] public def modelE : Subgroup TwistedModel :=
  (SemidirectProduct.rightHom : TwistedModel →* SymmetricFour).ker

/-- The second elementary subgroup in the coordinate model. -/
@[expose] public def modelF : Subgroup TwistedModel := centralizer {d}

local instance : DecidablePred (· ∈ modelE) := fun x =>
  inferInstanceAs (Decidable (x.right = 1))
local instance : DecidablePred (· ∈ modelF) := fun x =>
  decidable_of_iff (x * d = d * x) mem_centralizer_singleton_iff.symm

private theorem elementary_of_square {A : Type*} [Group A]
    (h : ∀ x : A, x ^ 2 = 1) : IsElementaryAbelian 2 A where
  is_comm.comm x y := (Commute.of_orderOf_dvd_two
    (fun x => orderOf_dvd_of_pow_eq_one (h x)) x y).eq
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr h

/-- The binary factor is elementary abelian. -/
public theorem modelE_elementary : IsElementaryAbelian 2 modelE := by
  apply elementary_of_square
  have h : ∀ x : modelE, (x : TwistedModel) ^ 2 = 1 := by decide +kernel
  exact fun x => Subtype.ext (h x)

/-- Its order is sixteen. -/
public theorem modelE_card : Nat.card modelE = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- All four source vectors lie in the binary factor. -/
public theorem z_mem_modelE : ∀ i, z i ∈ modelE := by decide +kernel

/-- Commuting with the four source vectors forces trivial actor component. -/
public theorem centralizes_basis_iff : ∀ x : TwistedModel,
    (∀ i, x * z i = z i * x) ↔ x ∈ modelE := by decide +kernel

/-- The binary factor is self-centralizing in the local model. -/
public theorem modelE_centralizer : centralizer (modelE : Set TwistedModel) = modelE := by
  apply le_antisymm
  · intro x hx
    exact (centralizes_basis_iff x).mp (fun i => (hx _ (z_mem_modelE i)).symm)
  · let := modelE_elementary
    exact le_centralizer modelE

/-- The second subgroup has exponent two. -/
public theorem modelF_elementary : IsElementaryAbelian 2 modelF := by
  apply elementary_of_square
  have h : ∀ x : modelF, (x : TwistedModel) ^ 2 = 1 := by decide +kernel
  exact fun x => Subtype.ext (h x)

/-- Its order is sixteen. -/
public theorem modelF_card : Nat.card modelF = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- The source generators of the second subgroup commute with `d`. -/
public theorem modelF_generators : z 0 ∈ modelF ∧ z 2 ∈ modelF ∧
    a ∈ modelF ∧ d ∈ modelF := by decide +kernel

/-- Every element of the second subgroup has the stated source coordinates. -/
public theorem modelF_expansion : ∀ x : modelF, ∃ r : Fin 4 → Fin 2,
    (x : TwistedModel) = z 0 ^ (r 0).val * z 2 ^ (r 1).val *
      a ^ (r 2).val * d ^ (r 3).val := by decide +kernel

/-- The second subgroup is self-centralizing in the local model. -/
public theorem modelF_centralizer : centralizer (modelF : Set TwistedModel) = modelF := by
  apply le_antisymm
  · intro x hx
    exact mem_centralizer_singleton_iff.mpr (hx d modelF_generators.2.2.2).symm
  · let := modelF_elementary
    exact le_centralizer modelF

variable {G : Type u} [Group G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

/-- The image of the coordinate binary factor is precisely the published `E`. -/
public theorem modelE_map : modelE.map (into D k) = E D k := by
  rw [modelE, ← SemidirectProduct.range_inl_eq_ker_rightHom]
  exact (MonoidHom.range_comp _ _).symm

/-- The image of the coordinate centralizer is precisely the published `F`. -/
public theorem modelF_map : modelF.map (into D k) = F D k := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨r, hr⟩ := modelF_expansion ⟨y, hy⟩
    change y = _ at hr
    rw [hr, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow]
    have h0 : into D k (z 0) ∈ F D k := subset_closure (by simp)
    have h2 : into D k (z 2) ∈ F D k := subset_closure (by simp)
    have ha : into D k a ∈ F D k := subset_closure (by simp)
    have hd : into D k d ∈ F D k := subset_closure (by simp)
    exact mul_mem (mul_mem (mul_mem (pow_mem h0 _) (pow_mem h2 _))
      (pow_mem ha _)) (pow_mem hd _)
  · apply (closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact mem_map_of_mem _ modelF_generators.1
    · exact mem_map_of_mem _ modelF_generators.2.1
    · exact mem_map_of_mem _ modelF_generators.2.2.1
    · exact mem_map_of_mem _ modelF_generators.2.2.2

/-- A subgroup containing the marked involution has its entire ambient
centralizer inside the image of the Case II coordinates. -/
public theorem centralizer_map [Finite G] (S : Subgroup TwistedModel) (hz : z 0 ∈ S) :
    centralizer (S.map (into D k) : Set G) =
      (centralizer (S : Set TwistedModel)).map (into D k) := by
  apply le_antisymm
  · intro x hx
    have hxC : x ∈ D.centralizer := by
      apply mem_centralizer_singleton_iff.mpr
      rw [← into_z_zero D k]
      exact (hx _ (mem_map_of_mem _ hz)).symm
    obtain ⟨y, hy⟩ := k.surjective ⟨x, hxC⟩
    have hyx : into D k y = x := congrArg Subtype.val hy
    refine ⟨y, ?_, hyx⟩
    intro t ht
    apply into_injective D k
    simp only [map_mul, hyx]
    exact hx _ (mem_map_of_mem _ ht)
  · rintro x ⟨y, hy, rfl⟩ t ⟨s, hs, rfl⟩
    simpa only [← map_mul] using congrArg (into D k) (hy s hs)

/-- Janko's first actual ambient subgroup is elementary abelian. -/
public theorem E_elementary : IsElementaryAbelian 2 (E D k) := by
  rw [← modelE_map D k]
  let := modelE_elementary
  exact IsElementaryAbelian.map _

/-- Janko's first actual ambient subgroup has order sixteen. -/
public theorem E_card : Nat.card (E D k) = 16 := by
  rw [← modelE_map D k, ← Nat.card_congr
    (modelE.equivMapOfInjective (into D k) (into_injective D k)).toEquiv]
  exact modelE_card

/-- Its ambient centralizer is itself. -/
public theorem E_centralizer [Finite G] : centralizer (E D k : Set G) = E D k := by
  rw [← modelE_map D k, centralizer_map D k modelE (z_mem_modelE 0), modelE_centralizer]

/-- Janko's second actual ambient subgroup is elementary abelian. -/
public theorem F_elementary : IsElementaryAbelian 2 (F D k) := by
  rw [← modelF_map D k]
  let := modelF_elementary
  exact IsElementaryAbelian.map _

/-- Janko's second actual ambient subgroup has order sixteen. -/
public theorem F_card : Nat.card (F D k) = 16 := by
  rw [← modelF_map D k, ← Nat.card_congr
    (modelF.equivMapOfInjective (into D k) (into_injective D k)).toEquiv]
  exact modelF_card

/-- Its ambient centralizer is itself. -/
public theorem F_centralizer [Finite G] : centralizer (F D k : Set G) = F D k := by
  rw [← modelF_map D k, centralizer_map D k modelF modelF_generators.1, modelF_centralizer]

end CaseII
end Theory.GroupTheory.HeldM22A10.M22Identification

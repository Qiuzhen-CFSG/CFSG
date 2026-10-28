module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ThompsonFactors.Basic
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Permutation and Sylow geometry of the actual Thompson factors

The marked direct product makes the symmetric-three factors disjoint,
commuting, and normal in the Thompson image. Conjugation permutes them.
The source Sylow assertion then gives independent involutions in each
factor, a projected image of order two, and total image order 2^r.
These are the literal group inputs for 15.4.12 and the Baumann application.
-/

@[expose] public noncomputable section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section04.FamilySource.ThompsonFactors
open Chapter1.RadicalNormalizers.ThompsonSource
variable {H : Type*} [Group H] {S : Sylow 2 H}
  [IsElementaryAbelian 2 (closure S)]

theorem factor_card (d : Exceptional S) (i : Fin d.count) :
    Nat.card (d.factor i) = 6 := by
  rw [Nat.card_congr (factorModel d i).toEquiv, Nat.card_eq_fintype_card,
    Fintype.card_perm, Fintype.card_fin]
  decide

theorem factors_commute (d : Exceptional S) {i j : Fin d.count} (hij : i ≠ j)
    {x y : Star (S := S)} (hx : x ∈ d.factor i) (hy : y ∈ d.factor j) : Commute x y := by
  simpa only [productMap_single] using
    (Pi.mulSingle_commute hij (⟨x,hx⟩ : d.factor i) (⟨y,hy⟩ : d.factor j)).map (productMap d)

theorem factors_disjoint (d : Exceptional S) {i j : Fin d.count} (hij : i ≠ j) :
    Disjoint (d.factor i) (d.factor j) := by
  classical
  apply disjoint_iff_inf_le.mpr
  intro x ⟨hx,hy⟩
  change x = 1
  have he : productMap d (Pi.mulSingle i (⟨x,hx⟩ : d.factor i)) =
      productMap d (Pi.mulSingle j (⟨x,hy⟩ : d.factor j)) := by
    simp only [productMap_single]
  have hh := congrFun (productMap_injective d he) i
  simpa only [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij, Subgroup.coe_one] using
    congrArg Subtype.val hh

theorem factor_injective (d : Exceptional S) : Function.Injective d.factor := by
  intro i j he
  by_contra hij
  have hi := factors_disjoint d hij
  rw [he, disjoint_self] at hi
  have hc := factor_card d j
  rw [hi] at hc
  simp only [Nat.card_unique] at hc
  omega

def factorPerm (d : Exceptional S) (g : Star (S := S)) : Equiv.Perm (Fin d.count) :=
  Classical.choose (d.permutes g)

theorem factorPerm_apply (d : Exceptional S) (g : Star (S := S)) (i : Fin d.count) :
    (d.factor i).map (MulAut.conj g).toMonoidHom = d.factor (factorPerm d g i) :=
  (Classical.choose_spec (d.permutes g)).1 i

omit [IsElementaryAbelian 2 (closure S)] in
private theorem map_conj_mul (K : Subgroup (Star (S := S))) (g h : Star (S := S)) :
    K.map (MulAut.conj (g*h)).toMonoidHom =
      (K.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  change (g*h)*x*(g*h)⁻¹ = g*(h*x*h⁻¹)*g⁻¹
  simp only [mul_inv_rev, mul_assoc]

def factorAction (d : Exceptional S) : Star (S := S) →* Equiv.Perm (Fin d.count) where
  toFun := factorPerm d
  map_one' := by
    apply Equiv.ext
    intro i
    apply factor_injective d
    rw [← factorPerm_apply]
    have hc : (MulAut.conj (1 : Star (S := S))).toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro x
      change 1 * x * 1⁻¹ = x
      simp only [inv_one, one_mul, mul_one]
    rw [hc, map_id]
    rfl
  map_mul' := by
    intro g h
    apply Equiv.ext
    intro i
    apply factor_injective d
    change d.factor (factorPerm d (g*h) i) = d.factor (factorPerm d g (factorPerm d h i))
    rw [← factorPerm_apply, map_conj_mul, factorPerm_apply, factorPerm_apply]

theorem factorAction_apply (d : Exceptional S) (g : Star (S := S)) (i : Fin d.count) :
    (d.factor i).map (MulAut.conj g).toMonoidHom = d.factor (factorAction d g i) :=
  factorPerm_apply d g i

theorem cubicFactor_action (d : Exceptional S) (g : Star (S := S)) (i : Fin d.count) :
    (cubicFactor d i).map (MulAut.conj g).toMonoidHom =
      cubicFactor d (factorAction d g i) :=
  cubicFactor_conj d g i _ (factorAction_apply d g i)

theorem thompsonImage_card (d : Exceptional S) :
    Nat.card (thompsonImage (S := S)) = 6 ^ d.count := by
  calc
    Nat.card (thompsonImage (S := S)) = Nat.card ((i : Fin d.count) → d.factor i) :=
      (Nat.card_congr d.groupProduct.toEquiv).symm
    _ = 6 ^ d.count := by
      rw [Nat.card_pi]
      simp only [factor_card, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

def sylowImage : Subgroup (Star (S := S)) :=
  (elementaryAbelianMaxJ (S : Subgroup H)).map (starMap (closure S))

def factorProjection (d : Exceptional S) (i : Fin d.count) :
    thompsonImage (S := S) →* d.factor i :=
  (Pi.evalMonoidHom _ i).comp d.groupProduct.symm.toMonoidHom

theorem factorProjection_surjective (d : Exceptional S) (i : Fin d.count) :
    Function.Surjective (factorProjection d i) := by
  classical
  intro x
  refine ⟨d.groupProduct (Pi.mulSingle i x), ?_⟩
  change (d.groupProduct.symm (d.groupProduct (Pi.mulSingle i x))) i = x
  rw [d.groupProduct.symm_apply_apply, Pi.mulSingle_eq_same]

theorem productMap_conj_single (d : Exceptional S) (f : (i : Fin d.count) → d.factor i)
    (i : Fin d.count) (x : d.factor i) :
    productMap d f * (x : Star (S := S)) * (productMap d f)⁻¹ =
      ((f i * x * (f i)⁻¹ : d.factor i) : Star (S := S)) := by
  classical
  have he : f * Pi.mulSingle i x * f⁻¹ = Pi.mulSingle i (f i * x * (f i)⁻¹) := by
    funext j
    by_cases h : j = i
    · subst j
      simp only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_same]
    · simp only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_of_ne h, mul_one, mul_inv_cancel]
  rw [← productMap_single d i x, ← map_inv, ← map_mul, ← map_mul, he, productMap_single]

theorem factor_normal (d : Exceptional S) (i : Fin d.count) :
    ((d.factor i).subgroupOf (thompsonImage (S := S))).Normal := by
  constructor
  intro x hx g
  obtain ⟨f,hf⟩ := d.groupProduct.surjective g
  have he : productMap d f = (g : Star (S := S)) := congrArg Subtype.val hf
  change (g : Star (S := S)) * (x : Star (S := S)) * (g : Star (S := S))⁻¹ ∈ d.factor i
  rw [← he, productMap_conj_single d f i ⟨x,hx⟩]
  exact (f i * (⟨x,hx⟩ : d.factor i) * (f i)⁻¹).property

variable [Finite H]

theorem sylowImage_card (d : Exceptional S) :
    Nat.card (sylowImage (S := S)) = 2 ^ d.count := by
  obtain ⟨P,hP⟩ := d.sylow
  change Sylow 2 (thompsonImage (S := S)) at P
  change (P : Subgroup (thompsonImage (S := S))).map thompsonImage.subtype = sylowImage at hP
  rw [← hP, card_map_of_injective thompsonImage.subtype_injective, P.card_eq_multiplicity,
    thompsonImage_card d, Nat.factorization_pow]
  have h6 : (6 : ℕ).factorization 2 = 1 := by decide +kernel
  simp only [Finsupp.smul_apply, smul_eq_mul, h6, mul_one]

theorem sylowProjection_card (d : Exceptional S) (i : Fin d.count) :
    Nat.card ((sylowImage (S := S)).subgroupOf thompsonImage |>.map (factorProjection d i)) = 2 := by
  obtain ⟨P,hP⟩ := d.sylow
  change Sylow 2 (thompsonImage (S := S)) at P
  change (P : Subgroup (thompsonImage (S := S))).map thompsonImage.subtype = sylowImage at hP
  have he : (sylowImage (S := S)).subgroupOf thompsonImage = (P : Subgroup thompsonImage) := by
    rw [← hP]
    ext x
    exact mem_map_iff_mem thompsonImage.subtype_injective
  rw [he]
  have hc := (P.mapSurjective (factorProjection_surjective d i)).card_eq_multiplicity
  rw [factor_card d i] at hc
  have h6 : (6 : ℕ).factorization 2 = 1 := by decide +kernel
  simpa only [h6, pow_one, Sylow.coe_mapSurjective] using hc

theorem exists_factor_involution (d : Exceptional S) (i : Fin d.count) :
    ∃ t : Star (S := S), t ∈ d.factor i ∧ t ∈ sylowImage (S := S) ∧ t ≠ 1 ∧ t^2 = 1 := by
  obtain ⟨P,hP⟩ := d.sylow
  change Sylow 2 (thompsonImage (S := S)) at P
  change (P : Subgroup (thompsonImage (S := S))).map thompsonImage.subtype = sylowImage at hP
  let E := (d.factor i).subgroupOf (thompsonImage (S := S))
  let : E.Normal := factor_normal d i
  have hE : Nat.card E = 6 :=
    (Nat.card_congr (subgroupOfEquivOfLe (factor_le_thompsonImage d i)).toEquiv).trans
      (factor_card d i)
  obtain ⟨Q,hQ⟩ := P.exists_subgroupOf_eq_of_normal E
  let R : Subgroup E := Q
  have hcard : Nat.card R = 2 := by
    change Nat.card (Q : Subgroup E) = 2
    rw [Q.card_eq_multiplicity, hE]
    decide +kernel
  let : Nontrivial R := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨t,ht⟩ := exists_ne (1 : R)
  refine ⟨t.val.val.val, t.val.property, ?_, ?_, ?_⟩
  · rw [← hP]
    apply mem_map.mpr
    refine ⟨t.val.val, ?_, rfl⟩
    have hm : t.val ∈ (Q : Subgroup E) := t.property
    rw [hQ] at hm
    exact hm
  · intro he
    apply ht
    exact Subtype.ext (Subtype.ext (Subtype.ext he))
  · have hp := pow_card_eq_one' (x := t)
    rw [hcard] at hp
    exact congrArg (fun x : R => x.val.val.val) hp

end CFSG.Quasithin.Chapter15.Section04.FamilySource.ThompsonFactors

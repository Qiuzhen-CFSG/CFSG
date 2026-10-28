module

public import CFSG.Quasithin.Chapter2.Section05.A6Shadow
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.ElementaryAbelian.Join
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# Algebra in the terminal A₆ construction

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, printed pp.569–570, following Lemma 2.5.27.

Disjoint centers force two normal subgroups of a finite two-group to be
disjoint, hence to commute. A Klein four-group in one factor then gives an
actual elementary group of order sixteen together with its conjugate. The
normalizing-element lemma records the additional square-stability condition
needed for the conjugating element to normalize this product.

These are algebraic steps, not the Aut(A₆) geometry or the source normalizer
calculation. The final construction must supply their hypotheses.
-/

namespace CFSG.Quasithin.Chapter2.A6ShadowConstruction

open Subgroup

variable {G : Type*} [Group G]

/-- Right conjugation, as in the source: `Dˣ = x⁻¹ D x`. -/
@[expose] public def conjugate (x : G) (D : Subgroup G) : Subgroup G :=
  D.map (MulAut.conj x⁻¹).toMonoidHom

/-- Disjoint centers make normal subgroups of a finite two-group disjoint.
Apply inside `S`, not in the whole ambient group. -/
public theorem disjoint_of_disjoint_centers [Finite G] (hG : IsPGroup 2 G)
    (D F : Subgroup G) [D.Normal] [F.Normal]
    (hcenters : Disjoint ((center D).map D.subtype) ((center F).map F.subtype)) :
    Disjoint D F := by
  by_contra hdisj
  have hne : D ⊓ F ≠ ⊥ := fun h => hdisj (disjoint_iff.mpr h)
  apply center_inf_ne_bot_of_normal hG (D ⊓ F) hne
  apply bot_unique
  rintro g ⟨hgZ, hgD, hgF⟩
  have hD : g ∈ (center D).map D.subtype := by
    refine ⟨⟨g, hgD⟩, mem_center_iff.mpr ?_, rfl⟩
    intro d
    exact Subtype.ext (mem_center_iff.mp hgZ d)
  have hF : g ∈ (center F).map F.subtype := by
    refine ⟨⟨g, hgF⟩, mem_center_iff.mpr ?_, rfl⟩
    intro f
    exact Subtype.ext (mem_center_iff.mp hgZ f)
  exact disjoint_def.mp hcenters hD hF

/-- The commuting conclusion used after proving `S_K ∩ S_Kˣ = 1`. -/
public theorem centralizes_of_disjoint_normal
    (D F : Subgroup G) [D.Normal] [F.Normal] (hdisj : Disjoint D F) :
    D ≤ centralizer (F : Set G) := by
  apply commutator_eq_bot_iff_le_centralizer.mp
  exact bot_unique ((commutator_le_inf D F).trans (disjoint_iff.mp hdisj).le)

/-- Restrict a homomorphism to a subgroup disjoint from its kernel and then
identify the containing image subgroup with an actual group model. -/
public theorem exists_embedding_of_image_le
    {Q R : Type*} [Group Q] [Group R]
    (f : G →* Q) (C : Subgroup G) (B : Subgroup Q)
    (hker : Disjoint C f.ker) (himage : C.map f ≤ B) (model : B ≃* R) :
    ∃ j : C →* R, Function.Injective j := by
  let j₀ : C →* B := (f.comp C.subtype).codRestrict B
    (fun c => himage (mem_map_of_mem f c.property))
  have hj₀ : Function.Injective j₀ := by
    apply (MonoidHom.ker_eq_bot_iff j₀).mp
    apply bot_unique
    intro c hc
    have hcKer : (c : G) ∈ f.ker := by
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp hc)
    exact Subtype.ext (disjoint_def.mp hker c.property hcKer)
  exact ⟨model.toMonoidHom.comp j₀, model.injective.comp hj₀⟩

/-- Inversion in a faithful image of a normalized subgroup lifts to that
subgroup. This is the step from `ē` inverting `V̄ˣ` to `e` inverting `Vˣ`. -/
public theorem inversion_of_faithful_image
    {Q : Type*} [Group Q] (f : G →* Q) (V : Subgroup G)
    (hker : Disjoint V f.ker) {e : G}
    (he : e ∈ normalizer (V : Set G))
    (hinverts : ∀ v ∈ V, f (e⁻¹ * v * e) = f v⁻¹) :
    ∀ v ∈ V, e⁻¹ * v * e = v⁻¹ := by
  intro v hv
  have hc : e⁻¹ * v * e ∈ V := by
    simpa using (mem_normalizer_iff.mp ((normalizer (V : Set G)).inv_mem he) v).mp hv
  have hprod : (e⁻¹ * v * e) * v ∈ V := V.mul_mem hc hv
  have hprodKer : (e⁻¹ * v * e) * v ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, hinverts v hv, map_inv, inv_mul_cancel]
  exact mul_eq_one_iff_eq_inv.mp (disjoint_def.mp hker hprod hprodKer)

/-- Build the actual internal direct product `E × Eˣ`, and prove its elementary
abelian structure and order. The displayed equivalence retains the two copies
of `E`; it is not a group-family label. -/
public theorem elementarySixteen_of_disjoint_conjugates
    (E : Subgroup G) [IsKleinFour E] (x : G)
    (hdisj : Disjoint E (conjugate x E))
    (hcomm : E ≤ centralizer (conjugate x E : Set G)) :
    Nonempty ((E ⊔ conjugate x E : Subgroup G) ≃* E × E) ∧
      IsElementaryAbelian 2 (E ⊔ conjugate x E : Subgroup G) ∧
      Nat.card (E ⊔ conjugate x E : Subgroup G) = 16 := by
  let a : E ≃* conjugate x E := (MulAut.conj x⁻¹).subgroupMap E
  obtain ⟨m, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    E (conjugate x E) hdisj hcomm
  let e : (E ⊔ conjugate x E : Subgroup G) ≃* E × E :=
    m.symm.trans ((MulEquiv.refl E).prodCongr a.symm)
  let : IsElementaryAbelian 2 E :=
    { toIsMulCommutative := IsKleinFour.isMulCommutative
      exponent_dvd_p := by rw [IsKleinFour.exponent_two] }
  let : IsElementaryAbelian 2 (conjugate x E) :=
    IsElementaryAbelian.map (MulAut.conj x⁻¹).toMonoidHom
  have hcomm' : conjugate x E ≤ centralizer (E : Set G) := by
    intro v hv u hu
    exact (hcomm hu v hv).symm
  refine ⟨⟨e⟩, IsElementaryAbelian.sup_of_le_centralizer hcomm', ?_⟩
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, IsKleinFour.card_four]

/-- The normalizer of the product contains `x` once the selected four-group is
stable under `x²`. Membership of `x²` in `S` alone is not this premise. -/
public theorem normalizes_join_conjugate_of_square_normalizes
    (E : Subgroup G) {x : G} (hx2 : x ^ 2 ∈ normalizer (E : Set G)) :
    x ∈ normalizer ((E ⊔ conjugate x E : Subgroup G) : Set G) := by
  have hdouble : conjugate x (conjugate x E) = E := by
    unfold conjugate
    rw [map_map]
    have hmaps : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x⁻¹).toMonoidHom =
        (MulAut.conj (x ^ 2)⁻¹).toMonoidHom := by
      ext g
      simp [pow_two, mul_assoc]
    rw [hmaps]
    exact mem_normalizer_iff_map_conj_eq.mp ((normalizer (E : Set G)).inv_mem hx2)
  have hinv : x⁻¹ ∈ normalizer ((E ⊔ conjugate x E : Subgroup G) : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change conjugate x (E ⊔ conjugate x E) = _
    unfold conjugate at *
    rw [Subgroup.map_sup, hdouble, sup_comm]
  simpa using (normalizer ((E ⊔ conjugate x E : Subgroup G) : Set G)).inv_mem hinv

/-- Locate the source involution `z = t zK` in the constructed product. -/
public theorem product_involution_mem_join
    (E : Subgroup G) {x t zK z : G} (hzK : zK ∈ E)
    (hzKx : x⁻¹ * zK * x = t) (hz : z = t * zK) :
    z ∈ E ⊔ conjugate x E := by
  have ht : t ∈ conjugate x E := ⟨zK, hzK, by simpa using hzKx⟩
  rw [hz]
  exact (E ⊔ conjugate x E).mul_mem (mem_sup_right ht) (mem_sup_left hzK)

end CFSG.Quasithin.Chapter2.A6ShadowConstruction

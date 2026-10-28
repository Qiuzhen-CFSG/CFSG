module
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.CharacteristicCentralizerFusion
/-!
# A central factor and a disjoint conjugate

If D centralizes P and is abelian, the center of PD is Z(P)D. A conjugator
normalizing PD preserves that center. When D meets its conjugate trivially,
the relative-index formula therefore bounds |D| by |Z(P)|.

This is the central-factor estimate used in Aschbacher–Smith 2.4.29,
printed p.545. No invariance of either individual factor is assumed.
-/
public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
open scoped Pointwise

omit [Finite G] in
theorem center_sup_of_central_factor (P D : Subgroup G)
    (hDP : D ≤ centralizer (P : Set G)) (hDD : D ≤ centralizer (D : Set G)) :
    (center (P ⊔ D : Subgroup G)).map (P ⊔ D).subtype = (center P).map P.subtype ⊔ D := by
  let E := P ⊔ D
  let Z := (center P).map P.subtype
  have hDn : P ≤ normalizer (D : Set G) :=
    (le_centralizer_iff.mp hDP).trans (centralizer_le_normalizer _)
  have hDc : D ≤ centralizer (E : Set G) := by
    exact le_centralizer_iff.mpr
      (sup_le (le_centralizer_iff.mp hDP) (le_centralizer_iff.mp hDD))
  apply le_antisymm
  · rintro z ⟨z,hz,rfl⟩
    have hm : (z : G) ∈ (P : Set G) * (D : Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right P D hDn]
      exact z.property
    obtain ⟨p,hp,d,hd,hpd⟩ := hm
    have hpc : (⟨p,hp⟩ : P) ∈ center P := by
      apply mem_center_iff.mpr
      intro a
      apply Subtype.ext
      apply mul_right_cancel (b:=d)
      have hz' := congrArg Subtype.val
        (mem_center_iff.mp hz (⟨a,mem_sup_left a.property⟩ : E))
      change (a:G)*(z:G) = (z:G)*a at hz'
      rw [←hpd] at hz'
      calc
        (a:G)*p*d = (a:G)*(p*d) := mul_assoc _ _ _
        _ = (p*d)*a := hz'
        _ = p*a*d := by rw [mul_assoc,←hDP hd a a.property,←mul_assoc]
    change (z : G) ∈ (center P).map P.subtype ⊔ D
    rw [←hpd]
    exact mul_mem_sup (mem_map.mpr ⟨⟨p,hp⟩,hpc,rfl⟩) hd
  · have hZc : Z ≤ centralizer (E : Set G) := by
      have hZP : Z ≤ centralizer (P : Set G) := by
        rintro z ⟨z,hz,rfl⟩ p hp
        exact congrArg Subtype.val (mem_center_iff.mp hz ⟨p,hp⟩)
      exact le_centralizer_iff.mpr (sup_le (le_centralizer_iff.mp hZP)
        (hDP.trans (centralizer_le (map_subtype_le _))))
    have hc : Z ⊔ D ≤ centralizer (E : Set G) := sup_le hZc hDc
    have hi : Z ⊔ D ≤ E := sup_le ((map_subtype_le _).trans le_sup_left) le_sup_right
    intro z hz
    refine mem_map.mpr ⟨⟨z,hi hz⟩,mem_center_iff.mpr ?_,rfl⟩
    intro a
    exact Subtype.ext (hc hz a a.property)

/-- A central factor disjoint from a conjugate is bounded by the center of
the other factor whenever the conjugator normalizes their product. -/
theorem card_central_factor_le_center_of_disjoint_conjugate
    (P D : Subgroup G) (hDP : D ≤ centralizer (P : Set G))
    (hDD : D ≤ centralizer (D : Set G)) (x : G)
    (hx : x ∈ normalizer ((P ⊔ D : Subgroup G) : Set G))
    (hd : D ⊓ D.map (MulAut.conj x⁻¹).toMonoidHom = ⊥) :
    Nat.card D ≤ Nat.card (center P) := by
  let E := (center (P ⊔ D : Subgroup G)).map (P ⊔ D).subtype
  let Z := (center P).map P.subtype
  let f := (MulAut.conj x⁻¹).toMonoidHom
  have hE : E = Z ⊔ D := center_sup_of_central_factor P D hDP hDD
  have hDE : D ≤ E := hE ▸ le_sup_right
  have hEx : E.map f = E := mem_normalizer_iff_map_conj_eq.mp
    ((normalizer (E : Set G)).inv_mem
      (normalizer_le_normalizer_characteristic_image (P ⊔ D) (center (P ⊔ D : Subgroup G)) hx))
  have hDx : D.map f ≤ E := (map_mono hDE).trans hEx.le
  have hix : D.relIndex (D.map f) = Nat.card D := by
    rw [←inf_relIndex_right,hd,relIndex_bot_left,card_map_of_injective (MulAut.conj x⁻¹).injective]
  have hi : Nat.card D ≤ D.relIndex E := by
    rw [←hix]
    exact relIndex_le_of_le_right hDx index_ne_zero_of_finite
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes Z D
    ((hDP.trans (centralizer_le (map_subtype_le _))).trans (centralizer_le_normalizer _))
  have hp : 1 ≤ Nat.card (Z ⊓ D : Subgroup G) := Nat.card_pos
  have hcE : Nat.card E ≤ Nat.card (center P) * Nat.card D := by
    rw [←hE,card_map_of_injective P.subtype_injective] at hc
    nlinarith
  have hcount := relIndex_mul_relIndex (⊥ : Subgroup G) D E bot_le hDE
  rw [relIndex_bot_left,relIndex_bot_left] at hcount
  have hpos : 0 < Nat.card D := Nat.card_pos
  have hindex : D.relIndex E ≤ Nat.card (center P) := by nlinarith
  exact hi.trans hindex
end Subgroup

module
public import Theory.SpecificGroups.SymplecticFour.PrescribedRootPairPlaneGeneration
public import Theory.SpecificGroups.SymplecticFour.ReciprocalSmallActors
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.DegreeRootProduct

/-!
# The same full actors in opposite plane coordinates

This transport retains the actual two full root actors and the actual large
actor. It is consumed by the positioned selector; no new root actors are
chosen in the ambient group.
-/

public noncomputable section
open Subgroup Representation
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.PrescribedActorPlaneGeneration
open CentralRootGeometry CentralRootGeometry.SmallMovers
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem full_root_in_upper (E : Subgroup (Sp F))
    (hEP : E ≤ (wing true).map (unipotent (F := F)).subtype)
    (hc : Nat.card E = Nat.card F)
    (hd : Module.finrank F (displacementSpace E) = 1) :
    ∃ s : Option F, E = rootImage s := by
  let A := E.subgroupOf unipotent
  have hEU : E ≤ unipotent := hEP.trans (map_subtype_le _)
  have hmap : A.map unipotent.subtype = E := map_subgroupOf_eq_of_le hEU
  have hfixed : fixed A = TwoLocalCover.fixedSpace E := by
    ext v
    simp only [fixed,mem_invariants,TwoLocalCover.mem_fixedSpace]
    constructor
    · intro hh q hq
      exact hh ⟨⟨q,hEU hq⟩,hq⟩
    · intro hh q
      exact hh q.val.val q.property
  have hAc : Nat.card A = Nat.card F := by
    rw [←card_map_of_injective unipotent.subtype_injective,hmap,hc]
  have hAm : movingIndex A = Nat.card F := by
    rw [movingIndex,hfixed,←Module.natCard_eq_pow_finrank (K := F),
      fixed_quotient_card,hd,pow_one]
  obtain ⟨s,hs⟩ := Degree.eq_rootFamily_of_field_indices A hAc hAm
  exact ⟨s,by rw [←hmap,hs]⟩

omit [Finite F] [CharP F 2] in
private theorem map_conj_mul (A : Subgroup (Sp F)) (g h : Sp F) :
    (A.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj (g*h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply,mul_assoc]

/-- Opposite-plane positioning generates with the two unchanged full roots. -/
theorem positioned_large_actor_and_prescribed_full_roots_generate
    (hq : 2 < Nat.card F) (P A E₁ E₂ : Subgroup (Sp F)) (c : Sp F)
    (hP : P.map (MulAut.conj c).toMonoidHom =
      ((wing true).map (unipotent (F := F)).subtype).map
        (MulAut.conj (TwoConjugate.opposition (F := F))).toMonoidHom)
    (hA : A.map (MulAut.conj c).toMonoidHom ≤
      (wing true).map (unipotent (F := F)).subtype)
    (hcard : Nat.card F ^ 2 < Nat.card A)
    (hE₁ : E₁ ≤ P) (hE₂ : E₂ ≤ P)
    (hc₁ : Nat.card E₁ = Nat.card F) (hc₂ : Nat.card E₂ = Nat.card F)
    (hd₁ : Module.finrank F (displacementSpace E₁) = 1)
    (hd₂ : Module.finrank F (displacementSpace E₂) = 1)
    (hne : E₁ ≠ E₂) : (A ⊔ E₁) ⊔ E₂ = ⊤ := by
  let o := TwoConjugate.opposition (F := F)
  let z := o*c
  have hoo : o*o=1 := by
    calc o*o = o⁻¹*o := by rw [TwoConjugate.opposition_inv]
         _ = 1 := inv_mul_cancel _
  have hPo : (P.map (MulAut.conj c).toMonoidHom).map
      (MulAut.conj o).toMonoidHom = (wing true).map unipotent.subtype := by
    rw [hP,map_conj_mul,hoo]
    rw [show (MulAut.conj (1 : Sp F)).toMonoidHom = MonoidHom.id _ by ext x; simp,
      Subgroup.map_id]
  have root (E : Subgroup (Sp F)) (hEP : E ≤ P)
      (hc : Nat.card E = Nat.card F)
      (hd : Module.finrank F (displacementSpace E) = 1) :
      ∃ s : Option F, E.map (MulAut.conj z).toMonoidHom = rootImage s := by
    apply full_root_in_upper
    · rw [←map_conj_mul]
      exact hPo ▸ map_mono (map_mono hEP)
    · rwa [card_map_of_injective (MulAut.conj z).injective]
    · rw [displacementSpace_conjugate,(toLinear z).finrank_map_eq,hd]
  obtain ⟨s,hs⟩ := root E₁ hE₁ hc₁ hd₁
  obtain ⟨t,ht⟩ := root E₂ hE₂ hc₂ hd₂
  have hst : s ≠ t := by
    intro he
    exact hne (Subgroup.map_injective (MulAut.conj z).injective
      (hs.trans ((congrArg rootImage he).trans ht.symm)))
  have hAz : A.map (MulAut.conj z).toMonoidHom ≤
      ((wing true).map (unipotent (F := F)).subtype).map
        (MulAut.conj o).toMonoidHom := by
    rw [←map_conj_mul]
    exact map_mono hA
  have hgen := PrescribedRootPairPlaneGeneration.large_opposite_plane_and_prescribed_root_pair_generate
    hq (A.map (MulAut.conj z).toMonoidHom) hAz
    (by rwa [card_map_of_injective (MulAut.conj z).injective]) s t hst
  apply Subgroup.map_injective (f := (MulAut.conj z).toMonoidHom) (MulAut.conj z).injective
  rw [Subgroup.map_sup,Subgroup.map_sup,hs,ht,
    map_top_of_surjective _ (MulAut.conj z).surjective]
  exact hgen

end Theory.SpecificGroups.SymplecticFour.PrescribedActorPlaneGeneration

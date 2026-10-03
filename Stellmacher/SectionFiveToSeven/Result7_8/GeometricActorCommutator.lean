module
public import Stellmacher.SectionFiveToSeven.Result7_8.GeometricExtraction

/-!
# The prescribed actor has a commutator which is not a two-group

Retain an actual geometric extraction with actor module V a two-group.
If a subgroup Z of V contains the prescribed actor, then [Z,E] cannot be
a two-group. This conclusion uses the actual residual conjugator and
outside-actor generation; no dihedral quotient model is required.

Suppose K=[Z,E] were a two-group. The group E normalizes N=Z∨K because
conjugating an element of Z changes it by a commutator in K, and E
normalizes K. Thus N is a two-group. The prescribed generation identity
E=⟨actor⟩∨V^x gives E=N∨V^x, another normalized join of two-groups.
Consequently E is a two-group, its two-residual is trivial, and x=1.
The conjugate-module core containment then puts the actor in the new
stabilizer, contradicting its recorded exclusion.

This supplies both non-two-group commutator contradictions in Stellmacher
(9.3), Journal of Algebra 190 (1997), pp.49–50,
`refs/files/stellmacher-n-group.pdf`. It is placed with the generic (7.8)
geometry so both actual extractions use the same proved argument.
-/
namespace Stellmacher.SectionsFiveToSeven
open Stellmacher.SectionNine CosetGraphContext SevenSix
open scoped commutatorElement
universe u

private theorem normalizes_sup_full_commutator
    {G : Type u} [Group G] [Finite G] (Z E : Subgroup G) :
    E ≤ Subgroup.normalizer ((Z ⊔ ⁅Z,E⁆ : Subgroup G) : Set G) := by
  let K := ⁅Z,E⁆
  let N := Z ⊔ K
  intro e he
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  have hmap : N.map (MulAut.conj e).toMonoidHom ≤ N := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro g ⟨z,hz,rfl⟩
      have hc : ⁅e,z⁆ ∈ K := by
        rw [show K = ⁅E,Z⁆ from Subgroup.commutator_comm _ _]
        exact Subgroup.commutator_mem_commutator he hz
      have hm := N.mul_mem ((show K ≤ N from le_sup_right) hc) ((show Z ≤ N from le_sup_left) hz)
      simpa [commutatorElement_def, MulAut.conj_apply, mul_assoc] using hm
    · have heK := Subgroup.normalizer_commutator_ge_right Z E he
      have hKeq := Subgroup.mem_normalizer_iff_map_conj_eq.mp heK
      exact hKeq.le.trans le_sup_right
  exact Subgroup.eq_of_le_of_card_ge hmap
    (Subgroup.card_map_of_injective (MulAut.conj e).injective).ge

public theorem geometric_actor_commutator_not_two
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Γ : CosetGraphContext G T A B) (d l : Γ.Vertex)
    (V E A0 : Subgroup G) (actor : G)
    (data : NineThreeGeometricData Γ d l V E A0 actor)
    (hV : IsPGroup 2 V) (Z : Subgroup G) (hZV : Z ≤ V) (haZ : actor ∈ Z) :
    ¬ IsPGroup 2 (⁅Z,E⁆ : Subgroup G) := by
  let K := ⁅Z,E⁆
  let N := Z ⊔ K
  have hVE : V ≤ E := by rw [data.generated]; exact le_sup_left
  have hZE : Z ≤ E := hZV.trans hVE
  have hKE : K ≤ E := (Subgroup.commutator_le_sup Z E).trans (sup_le hZE le_rfl)
  have hNE : N ≤ E := sup_le hZE hKE
  have hEN := normalizes_sup_full_commutator Z E
  intro hK
  have hN : IsPGroup 2 N := (hV.to_le hZV).to_sup_of_normal_right' hK
    (Subgroup.normalizer_commutator_ge_left Z E)
  have hconj : IsPGroup 2 (V.conjBy data.x) := hV.map (MulAut.conj data.x).toMonoidHom
  have hconjE : V.conjBy data.x ≤ E := le_sup_right.trans data.generated.ge
  have hgen : E = N ⊔ V.conjBy data.x := by
    apply le_antisymm ?_ (sup_le hNE hconjE)
    apply (data.actor_generated actor (hZV haZ) data.actor_outside).le.trans
    refine sup_le ?_ le_sup_right
    apply (Subgroup.closure_le _).mpr
    exact Set.singleton_subset_iff.mpr ((show N ≤ N ⊔ V.conjBy data.x from le_sup_left)
      ((show Z ≤ N from le_sup_left) haZ))
  have hE : IsPGroup 2 E := by
    rw [hgen]
    exact hN.to_sup_of_normal_left' hconj (hconjE.trans hEN)
  have hres : twoResidualSubgroup E = ⊥ := by
    apply bot_unique
    apply sInf_le
    refine ⟨inferInstance,?_⟩
    obtain ⟨n,hn⟩ := (IsPGroup.iff_card (p := 2)).mp hE
    exact ⟨n,by simpa using hn⟩
  have hx : data.x = 1 := by
    have hh := data.residual_mem
    change data.x ∈ (twoResidualSubgroup E).map E.subtype at hh
    rw [hres,Subgroup.map_bot] at hh
    exact hh
  apply data.actor_outside
  have hQG : q Γ (Γ.act data.x⁻¹ l) ≤ stabilizer Γ (Γ.act data.x⁻¹ l) := by
    rw [q,Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  apply hQG
  apply data.conjugate_core_le
  simpa [hx,Subgroup.conjBy] using hZV haZ
end Stellmacher.SectionsFiveToSeven

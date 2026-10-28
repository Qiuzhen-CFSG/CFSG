module

public import Stellmacher.SectionThree.GeneratedDihedralAction.ActorCore
public import Theory.GroupTheory.NormalNilpotentConjugateGenerator

/-!
# Generation by every actor outside the coatom

The extracted actor coatom has index two, so any actor outside it generates
its quotient. The coatom is the actor's intersection with the generated
group's two-core. Its conjugate lies in the conjugate actor subgroup, and
the chosen conjugator belongs to the generated group. The normal-nilpotent
conjugate-generator lemma therefore removes the coatom from the generating
set. This proves the every-outside-actor assertion in Stellmacher (7.8)(d),
Journal of Algebra 190 (1997), p. 36.
-/

namespace Stellmacher.SectionThree

private theorem index_two_sup_zpowers_outside
    {G : Type*} [Group G] [Finite G]
    (A A₀ : Subgroup G) (hA₀A : A₀ ≤ A)
    (hindex : Nat.card A = 2 * Nat.card A₀)
    (b : G) (hb : b ∈ A) (hb₀ : b ∉ A₀) :
    A₀ ⊔ Subgroup.zpowers b = A := by
  let H := A₀ ⊔ Subgroup.zpowers b
  have hHA : H ≤ A := sup_le hA₀A (Subgroup.zpowers_le.mpr hb)
  have hA₀H : A₀ ≤ H := le_sup_left
  have hHne : H ≠ A₀ := by
    intro heq
    have hbH : b ∈ H := (show Subgroup.zpowers b ≤ H from le_sup_right)
      (Subgroup.mem_zpowers b)
    exact hb₀ (heq ▸ hbH)
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hA₀H
  have hk0 : k ≠ 0 := by
    intro heq
    have hzero : Nat.card H = 0 := by simpa [heq] using hk
    exact (Nat.card_pos (α := H)).ne' hzero
  have hk1 : k ≠ 1 := by
    intro heq
    have hcard : Nat.card H = Nat.card A₀ := by simpa [heq] using hk
    exact hHne (Subgroup.eq_of_le_of_card_ge hA₀H hcard.le).symm
  have hk2 : 2 ≤ k := by omega
  have hcard : Nat.card A ≤ Nat.card H := by nlinarith
  exact Subgroup.eq_of_le_of_card_ge hHA hcard

public theorem extracted_generated_by_outside_actor
    {G : Type*} [Group G] [Finite G]
    (P T A : Subgroup G) (hAP : A ≤ P) (a : G) (haA : a ∈ A)
    (d : PrimitiveDihedralExtractionData P T A hAP a haA)
    (hAelem : IsElementaryAbelian 2
      ((A.subgroupOf P).map (QuotientGroup.mk' (pCore 2 P))))
    (b : G) (hb : b ∈ A) (hb₀ : b ∉ d.A₀) :
    A ⊔ A.conjBy (d.x : G) = Subgroup.zpowers b ⊔ A.conjBy (d.x : G) := by
  let L := A ⊔ A.conjBy (d.x : G)
  let H := Subgroup.zpowers b ⊔ A.conjBy (d.x : G)
  have hAL : A ≤ L := le_sup_left
  have hA₀L : d.A₀ ≤ L := d.A₀_le.trans hAL
  have hHL : H ≤ L := sup_le ((Subgroup.zpowers_le.mpr hb).trans hAL) le_sup_right
  have hAgen : d.A₀ ⊔ Subgroup.zpowers b = A :=
    index_two_sup_zpowers_outside A d.A₀ d.A₀_le d.A₀_index_two b hb hb₀
  have hLgen : L = d.A₀ ⊔ H := by
    dsimp only [L, H]
    rw [← sup_assoc, hAgen]
  let N := pCore 2 L
  let B := d.A₀.subgroupOf L
  let HL := H.subgroupOf L
  have hBcore : B ≤ N := by
    have hcore := extracted_actor_eq_core_intersection P T A hAP a haA d hAelem
    have hA₀core : d.A₀ ≤ twoCoreAmbient L := by rw [hcore]; exact inf_le_right
    have hsub := Subgroup.subgroupOf_mono L hA₀core
    change B ≤ ((pCore 2 L).map L.subtype).subgroupOf L at hsub
    rw [subgroupOf_map_subtype_eq] at hsub
    exact hsub
  have htopmap : (⊤ : Subgroup L).map L.subtype = L :=
    L.subtype.range_eq_map.symm.trans L.range_subtype
  have hgen : B ⊔ HL = ⊤ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hA₀L,
      Subgroup.map_subgroupOf_eq_of_le hHL, htopmap]
    exact hLgen.symm
  let xL : L := ⟨d.x, d.x_mem_generated⟩
  have hconj : B.conjBy xL ≤ HL := by
    rintro y ⟨c, hc, rfl⟩
    apply (show A.conjBy (d.x : G) ≤ H from le_sup_right)
    exact Subgroup.mem_map_of_mem (MulAut.conj (d.x : G)).toMonoidHom (d.A₀_le hc)
  have hHLtop : HL = ⊤ := Subgroup.eq_top_of_conjugate_normal_nilpotent_generator_le N B HL pCore_normal
    (pCore_isPGroup (p := 2) (G := L)).isNilpotent hBcore hgen xL hconj
  have hHeq : H = L := by
    calc
      H = HL.map L.subtype := (Subgroup.map_subgroupOf_eq_of_le hHL).symm
      _ = (⊤ : Subgroup L).map L.subtype := by rw [hHLtop]
      _ = L := htopmap
  exact hHeq.symm

end Stellmacher.SectionThree

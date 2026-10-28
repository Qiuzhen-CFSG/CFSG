module

public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Sextet.Quotient

/-! The stabilizer of one of the six exceptional four-groups has index six
in the actual rectangle normalizer. This retains the original six-point
conjugation action and determines the intersection order. -/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
open UniquenessLinear
variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z)

theorem plane_four_normalizer_card
    (hc : (F.fusion F.plane).ncard = 45) (i : Fin 6) :
    Nat.card ((normalizer (planeFour F i : Set G)).subgroupOf (planeNormalizer F)) = 23040 := by
  classical
  let q := QuotientGroup.mk' (F.plane.subgroupOf (planeNormalizer F))
  let f := (planeSextetAction F hc).comp q
  have hf : Function.Surjective f :=
    (planeSextetAction_structure F hc).2.comp (QuotientGroup.mk'_surjective _)
  let : MulAction (planeNormalizer F) (Fin 6) := MulAction.compHom (Fin 6) f
  have ho : MulAction.orbit (planeNormalizer F) i = Set.univ := by
    apply Set.eq_univ_of_forall
    intro j
    obtain ⟨n,hn⟩ := hf (Equiv.swap i j)
    exact MulAction.mem_orbit_iff.mpr ⟨n,by
      change f n i=j
      rw [hn,Equiv.swap_apply_left]⟩
  have hs : MulAction.stabilizer (planeNormalizer F) i =
      (normalizer (planeFour F i : Set G)).subgroupOf (planeNormalizer F) := by
    ext n
    change f n i = i ↔ (n:G) ∈ normalizer (planeFour F i : Set G)
    rw [mem_normalizer_iff_map_conj_eq]
    change f n i = i ↔ (planeFour F i).map (MulAut.conj (n:G)).toMonoidHom = planeFour F i
    rw [planeSextetAction_conjugation F hc n i]
    exact (planeFour_injective F).eq_iff.symm
  have hNc : Nat.card (planeNormalizer F) = 138240 := by
    rw [card_eq_card_quotient_mul_card_subgroup
      (F.plane.subgroupOf (planeNormalizer F)),
      planeSextet_quotient_card F hc,
      Nat.card_congr (subgroupOfEquivOfLe F.plane.le_normalizer).toEquiv,plane_card]
  have hm := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (planeNormalizer F) i)
  rw [Nat.card_prod,ho,Nat.card_congr (Equiv.Set.univ (Fin 6)),Nat.card_fin,hs,hNc] at hm
  omega

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer

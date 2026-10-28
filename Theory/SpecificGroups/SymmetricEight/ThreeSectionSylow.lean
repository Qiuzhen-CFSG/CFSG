module
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.PerfectImage
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.MaximalLevi
public import Theory.SpecificGroups.SymmetricEight.PerfectSylow
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8

/-!
# Eight-letter Sylow overgroups with a normal binary-three section

A subgroup containing a full Sylow of A8 and acting on a normal perfect
seven-divisible, five-free subgroup must be even. An odd element would
supply a full Sylow of S8; its transpositions and the seven-element would
force the normal perfect subgroup to be all of A8, contradicting the
missing factor five.

Every quotient with trivial solvable radical of the resulting A8 Sylow
overgroup is perfect. We lift the corresponding binary-four overgroup to
an endpoint parabolic in SL5(2), where the flag theorem proves the claim.
The actual quotient and Sylow maps are preserved.

Source application: Aschbacher--Smith 12.1.1, printed pp.788--789,
excluding the L4(2) star component. The original point action supplies
Aut(L3(2)), a radical-free nonperfect quotient, in `Parabolic.FourLinearStar`.
Imported matrix and alternating-group comparisons retain their attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.SpecificGroups.SymmetricEight.ThreeSectionSylow
open BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
open BinaryLinear.FiveFlagGeometry.MaximalOvergroups
private instance (n : ℕ) : Finite (LinearGroup n) :=
  Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective

/-- Lift a binary-four Sylow overgroup into an endpoint parabolic in binary degree five. -/
theorem four_sylow_radical_free_image_perfect
    (S : Sylow 2 (LinearGroup 4)) (P : Subgroup (LinearGroup 4))
    (hSP : (S : Subgroup _) ≤ P) {J : Type*} [Group J]
    (f : P →* J) (hf : Function.Surjective f) (hr : solvableRadical J = ⊥) :
    Group.IsPerfect J := by
  let b : FiveBasis := Pi.basisFun (ZMod 2) (Fin 5)
  let E := flagStabilizer b {0}
  let e := (lineQuotientEquiv b).trans (projectiveEquivLinear (by decide : 0 < 4))
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 E))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨U,hU⟩ := Sylow.mapSurjective_surjective hq 2 S
  have hSE : (flagSylow b : Subgroup (LinearGroup 5)) ≤ E := by
    rw [flagSylow_coe]
    exact flagStabilizer_antitone b (Set.subset_univ _)
  have hEi : ¬ 2 ∣ E.index := fun hh => (flagSylow b).not_dvd_index
    (hh.trans (index_dvd_of_le hSE))
  let U' : Sylow 2 (LinearGroup 5) := (U.isPGroup'.map E.subtype).toSylow (by
    rw [index_map_subtype]
    exact Nat.prime_two.not_dvd_mul U.not_dvd_index hEi)
  let D := P.comap q
  let C := D.map E.subtype
  have hUC : (U' : Subgroup (LinearGroup 5)) ≤ C := by
    apply map_mono
    intro u hu
    apply hSP
    have hh := mem_map_of_mem q hu
    change q u ∈ ((U.mapSurjective hq : Sylow 2 (LinearGroup 4)) : Subgroup _) at hh
    rwa [hU] at hh
  let d : D →* P := (q.comp D.subtype).codRestrict P (fun x => x.property)
  have hd : Function.Surjective d := by
    intro p
    obtain ⟨x,hx⟩ := hq p
    exact ⟨⟨x,show q x ∈ P from hx ▸ p.property⟩,Subtype.ext hx⟩
  let c := D.equivMapOfInjective E.subtype E.subtype_injective
  let g := f.comp (d.comp c.symm.toMonoidHom)
  exact BinaryLinear.sylow_overgroup_radical_free_image_perfect U' C hUC g
    (hf.comp (hd.comp c.symm.surjective)) hr


/-- A full even Sylow and a normal perfect seven-divisible, five-free subgroup
force an eight-letter overgroup to be even. -/
theorem eight_overgroup_even_of_normal_three_section
    (S : Sylow 2 (alternatingGroup (Fin 8))) (N A : Subgroup (Equiv.Perm (Fin 8)))
    (hSN : (S : Subgroup _).map (alternatingGroup (Fin 8)).subtype ≤ N)
    [Group.IsPerfect A] (hNA : N ≤ normalizer (A : Set _))
    (h7 : 7 ∣ Nat.card A) (h5 : ¬ 5 ∣ Nat.card A) : N ≤ alternatingGroup (Fin 8) := by
  by_contra hn
  let E := alternatingGroup (Fin 8)
  have hEi : E.relIndex N = 2 := by
    have hd : E.relIndex N ∣ 2 := (alternatingGroup.index_eq_two (α := Fin 8)) ▸
      relIndex_dvd_index_of_normal E N
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with he | he
    · exact (hn ((relIndex_eq_one).mp he)).elim
    · exact he
  have hS : Nat.card S = 64 := by
    rw [S.card_eq_multiplicity,nat_card_alternatingGroup,Nat.card_fin]
    decide +kernel
  let j : S →* E.subgroupOf N :=
    { toFun := fun x => ⟨⟨x.val,hSN (mem_map_of_mem E.subtype x.property)⟩,x.val.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun a : E.subgroupOf N => (a : Equiv.Perm (Fin 8))) he))
  have h64 : 64 ∣ Nat.card (E.subgroupOf N) := hS ▸ card_dvd_of_injective j hj
  have h128 : 128 ∣ Nat.card N := by
    have hc := (E.subgroupOf N).card_mul_index
    change Nat.card (E.subgroupOf N) * E.relIndex N = Nat.card N at hc
    rw [hEi] at hc
    rw [←hc]
    exact Nat.mul_dvd_mul h64 (dvd_refl 2)
  have hNi : ¬ 2 ∣ N.index := by
    intro hh
    have hd : 256 ∣ Nat.card N * N.index := Nat.mul_dvd_mul h128 hh
    rw [N.card_mul_index,Nat.card_perm,Nat.card_fin] at hd
    norm_num [Nat.factorial] at hd
  let P : Sylow 2 N := Classical.choice inferInstance
  let P' : Sylow 2 (Equiv.Perm (Fin 8)) := (P.isPGroup'.map N.subtype).toSylow (by
    rw [index_map_subtype]
    exact Nat.prime_two.not_dvd_mul P.not_dvd_index hNi)
  have he := Theory.SpecificGroups.SymmetricEight.PerfectSylow.eq_alternating_of_seven_dvd
    A P' ((map_subtype_le _).trans hNA) h7
  rw [he,nat_card_alternatingGroup,Nat.card_fin] at h5
  norm_num [Nat.factorial] at h5


/-- The full even Sylow and the original normal three-space section make
every radical-free quotient of the eight-letter normalizer perfect. -/
theorem eight_sylow_three_section_image_perfect
    (S : Sylow 2 (alternatingGroup (Fin 8))) (N A : Subgroup (Equiv.Perm (Fin 8)))
    (hSN : (S : Subgroup _).map (alternatingGroup (Fin 8)).subtype ≤ N)
    [Group.IsPerfect A] (hNA : N ≤ normalizer (A : Set _))
    (h7 : 7 ∣ Nat.card A) (h5 : ¬ 5 ∣ Nat.card A)
    {J : Type*} [Group J] (f : N →* J) (hf : Function.Surjective f)
    (hr : solvableRadical J = ⊥) : Group.IsPerfect J := by
  have hN := eight_overgroup_even_of_normal_three_section S N A hSN hNA h7 h5
  let e := Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.trans
    (projectiveEquivLinear (by decide : 0 < 4))
  let P := (N.subgroupOf (alternatingGroup (Fin 8))).map e.toMonoidHom
  let t := (subgroupOfEquivOfLe hN).symm.trans (e.subgroupMap _)
  apply four_sylow_radical_free_image_perfect (S.mapSurjective (f := e.toMonoidHom) e.surjective) P _
    (f.comp t.symm.toMonoidHom) (hf.comp t.symm.surjective) hr
  apply map_mono
  intro x hx
  exact hSN (mem_map_of_mem (alternatingGroup (Fin 8)).subtype hx)

end Theory.SpecificGroups.SymmetricEight.ThreeSectionSylow

module
public import Theory.Alternating.FivePairTorusAxes
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.Torus
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.TorusAxes

/-!
# Literal coordinates of the containing A₅ Hall torus

The original A₅-pair quotient is injective on the actual order-nine torus.
After marking its two factors as SL₂, the opposite projection kernels give
its two disjoint axes of order three. Their join is the whole torus. These
are the literal kernel images required by the natural-generation Cartan-axis
argument. The source natural marking and fixed vector remain inputs from
E.2.3; this module discharges torus size, exponent, and axis order.

Source: Aschbacher–Smith 10.2.3(4), printed p.746.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
local notation "A" => alternatingGroup (Fin 5)
variable {G F : Type*} [Group G] [Finite G] [Field F] [CharP F 2]

omit [CharP F 2] in
theorem source_a5_torus_coordinate_axes
    (C : Subgroup G) (q : C →* A × A) (hq : Function.Injective q)
    (hc : Nat.card C = 9) (a₁ a₂ : A ≃* SL(2,F)) :
    let q₁ := a₁.toMonoidHom.comp ((MonoidHom.fst A A).comp q)
    let q₂ := a₂.toMonoidHom.comp ((MonoidHom.snd A A).comp q)
    Nat.card (q₂.ker.map C.subtype) = 3 ∧ Nat.card (q₁.ker.map C.subtype) = 3 ∧
      Disjoint (q₂.ker.map C.subtype) (q₁.ker.map C.subtype) ∧
      q₂.ker.map C.subtype ⊔ q₁.ker.map C.subtype = C := by
  dsimp only
  let r₁ := (MonoidHom.fst A A).comp q
  let r₂ := (MonoidHom.snd A A).comp q
  have hC : IsPGroup 3 C := IsPGroup.of_card (n := 2) hc
  obtain ⟨h₁,h₂,hd,hs⟩ := Theory.AlternatingFive.nine_torus_coordinate_kernels q hq hC hc
  have hk₁ : (a₁.toMonoidHom.comp r₁).ker = r₁.ker := by
    ext x
    change a₁ (r₁ x) = 1 ↔ r₁ x = 1
    exact a₁.map_eq_one_iff
  have hk₂ : (a₂.toMonoidHom.comp r₂).ker = r₂.ker := by
    ext x
    change a₂ (r₂ x) = 1 ↔ r₂ x = 1
    exact a₂.map_eq_one_iff
  change Nat.card ((a₂.toMonoidHom.comp r₂).ker.map C.subtype) = 3 ∧
    Nat.card ((a₁.toMonoidHom.comp r₁).ker.map C.subtype) = 3 ∧ _
  rw [hk₁,hk₂]
  refine ⟨?_,?_,Subgroup.disjoint_map C.subtype_injective hd.symm,?_⟩
  · rw [card_map_of_injective C.subtype_injective]
    exact h₂
  · rw [card_map_of_injective C.subtype_injective]
    exact h₁
  · rw [← Subgroup.map_sup,sup_comm,hs,← MonoidHom.range_eq_map,range_subtype]

theorem source_a5_cartan_eq_coordinate_axis
    (C P : Subgroup G) (q : C →* A × A) (hq : Function.Injective q)
    (hc : Nat.card C = 9) (hC : IsElementaryAbelian 3 C)
    (a₁ a₂ : A ≃* SL(2,F)) (hPC : P ≤ C) (hP : Nat.card P = 3)
    (v : (Fin 2 → F) × (Fin 2 → F)) (hv : v ≠ 0)
    (hfix : ∀ p : C, (p : G) ∈ P →
      ((a₁ (q p).1).val *ᵥ v.1,(a₂ (q p).2).val *ᵥ v.2) = v) :
    P = (a₂.toMonoidHom.comp ((MonoidHom.snd A A).comp q)).ker.map C.subtype ∨
    P = (a₁.toMonoidHom.comp ((MonoidHom.fst A A).comp q)).ker.map C.subtype := by
  let q₁ := a₁.toMonoidHom.comp ((MonoidHom.fst A A).comp q)
  let q₂ := a₂.toMonoidHom.comp ((MonoidHom.snd A A).comp q)
  have ha := source_a5_torus_coordinate_axes C q hq hc a₁ a₂
  exact source_natural_cartan_eq_axis C (q₂.ker.map C.subtype) (q₁.ker.map C.subtype)
    P q₁ q₂ hPC
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hC.exponent_dvd_p)
    rfl rfl hP ha.1 ha.2.1 v hv hfix


variable {T : Sylow 2 G} {L : Subgroup G}

omit [Finite G] in
theorem source_a5_borel_torus_quotient_injective
    (C : Subgroup G) (hCB : C ≤ sourceOrbitBorel T L) (hC : IsPGroup 3 C)
    (q : localOrbit T L →* A × A) (hk : IsPGroup 2 q.ker) :
    let hCR : C ≤ localOrbit T L := hCB.trans ((map_subtype_le _).trans inf_le_left)
    Function.Injective (q.comp (Subgroup.inclusion hCR)) := by
  dsimp only
  let R := localOrbit T L
  have hCR : C ≤ R := hCB.trans ((map_subtype_le _).trans inf_le_left)
  let a : C ≃* C.subgroupOf R := (subgroupOfEquivOfLe hCR).symm
  have hi := Theory.AlternatingFive.injective_on_three_subgroup q hk
    (C.subgroupOf R) hC.comap_subtype
  exact hi.comp a.injective


omit [CharP F 2] in
theorem source_a5_borel_torus_original_coordinate_axes
    (C : Subgroup G) (hCB : C ≤ sourceOrbitBorel T L) (hc : Nat.card C = 9)
    (q : localOrbit T L →* A × A) (hk : IsPGroup 2 q.ker)
    (a₁ a₂ : A ≃* SL(2,F)) :
    let hCR : C ≤ localOrbit T L := hCB.trans ((map_subtype_le _).trans inf_le_left)
    let r := q.comp (Subgroup.inclusion hCR)
    let q₁ := a₁.toMonoidHom.comp ((MonoidHom.fst A A).comp r)
    let q₂ := a₂.toMonoidHom.comp ((MonoidHom.snd A A).comp r)
    Nat.card (q₂.ker.map C.subtype) = 3 ∧ Nat.card (q₁.ker.map C.subtype) = 3 ∧
      Disjoint (q₂.ker.map C.subtype) (q₁.ker.map C.subtype) ∧
      q₂.ker.map C.subtype ⊔ q₁.ker.map C.subtype = C := by
  dsimp only
  have hC : IsPGroup 3 C := IsPGroup.of_card (n := 2) hc
  exact source_a5_torus_coordinate_axes C _
    (source_a5_borel_torus_quotient_injective C hCB hC q hk) hc a₁ a₂

theorem source_a5_borel_cartan_eq_original_coordinate_axis
    (C P : Subgroup G) (hCB : C ≤ sourceOrbitBorel T L)
    (hc : Nat.card C = 9) (hC : IsElementaryAbelian 3 C)
    (q : localOrbit T L →* A × A) (hk : IsPGroup 2 q.ker)
    (a₁ a₂ : A ≃* SL(2,F)) (hPC : P ≤ C) (hP : Nat.card P = 3)
    (v : (Fin 2 → F) × (Fin 2 → F)) (hv : v ≠ 0) :
    let hCR : C ≤ localOrbit T L := hCB.trans ((map_subtype_le _).trans inf_le_left)
    let r := q.comp (Subgroup.inclusion hCR)
    (∀ p : C, (p : G) ∈ P →
      ((a₁ (r p).1).val *ᵥ v.1,(a₂ (r p).2).val *ᵥ v.2) = v) →
    P = (a₂.toMonoidHom.comp ((MonoidHom.snd A A).comp r)).ker.map C.subtype ∨
    P = (a₁.toMonoidHom.comp ((MonoidHom.fst A A).comp r)).ker.map C.subtype := by
  dsimp only
  intro hfix
  exact source_a5_cartan_eq_coordinate_axis C P _
    (source_a5_borel_torus_quotient_injective C hCB (IsPGroup.of_card (n := 2) hc) q hk)
    hc hC a₁ a₂ hPC hP v hv hfix

end CFSG.Quasithin.Chapter10

module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Inputs
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Sylow
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import Theory.GroupTheory.GeneralizedFitting.ComponentCenterPrimeCore

/-!
# Odd-core and local-family facts for block enlargement

O₂,₃ is a solvable normal subgroup. Trivial odd core descends to it, so its
layer vanishes and its Fitting subgroup is its two-core. This supplies C.1.9's
extra local hypothesis even when the full centralizer has components.
Trivial odd core also excludes the actual alternating triple covers.

The A₃ diagnostic follows already from the defining quotient of order three:
an A₃ block is not perfect and therefore cannot belong to the C-component
family in Definition 1.2.3. Thus the invocation of 1.2.4 in the proof of E.6.23
needs a separate argument in this branch. This does not refute E.6.23.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.9 and
C.1.12, pp.123–124; 1.2.3–4, p.505; E.6.23, p.254 (PDF p.265).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection
open ComponentBalance

/-- Odd-core vanishing proves the full extra hypothesis in C.1.9. -/
theorem c19Condition_of_oddCore_eq_bot {D : Type*} [Group D] [Finite D]
    (ho : pPrimeCore 2 D = ⊥) :
    C19Condition D := by
  unfold C19Condition
  let N := (pCore 3 (D ⧸ pCore 2 D)).comap (QuotientGroup.mk' (pCore 2 D))
  let f : N →* pCore 3 (D ⧸ pCore 2 D) :=
    (QuotientGroup.mk' (pCore 2 D)).subgroupComap (pCore 3 (D ⧸ pCore 2 D))
  let : Group.IsNilpotent (pCore 3 (D ⧸ pCore 2 D)) := pCore_isNilpotent
  have hker : IsPGroup 2 f.ker := by
    apply (pCore_isPGroup (p := 2) (G := D)).of_injective
      (show f.ker →* pCore 2 D from
        { toFun := fun x => ⟨x.val.val, (QuotientGroup.eq_one_iff _).mp
            (congrArg Subtype.val x.property)⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl })
    intro x y hxy
    exact Subtype.ext (Subtype.ext (congrArg (fun z : pCore 2 D => (z : D)) hxy))
  let : Group.IsNilpotent f.ker := hker.isNilpotent
  let : Group.IsSolvable N := Group.isSolvable_of_ker_le_range f.ker.subtype f
    (by rw [range_subtype])
  have hNo : pPrimeCore 2 N = ⊥ := by
    apply (map_eq_bot_iff_of_injective _ N.subtype_injective).mp
    exact eq_bot_mono (pPrimeCore_map_subtype_le_pPrimeCore_of_normal 2 N) ho
  have hE : componentLayer N = ⊥ := by
    apply sSup_eq_bot.mpr
    intro J hJ
    let := hJ.2
    let : IsSimpleGroup (J ⧸ center J) := IsQuasisimple.simple
    let : Nontrivial J := (QuotientGroup.mk'_surjective (center J)).nontrivial
    exact (Group.IsPerfect.not_isSolvable J inferInstance).elim
  change generalizedFitting N = pCore 2 N
  rw [generalizedFitting, hE, sup_bot_eq, Fitting_eq_pcore N 2 hNo]

/-- An A₃ block has a nontrivial abelian quotient, so it is not perfect. -/
theorem alternatingBlock_three_not_perfect {D : Type*} [Group D]
    (h : ChapterC.IsAlternatingBlock D 3) :
    ¬ Group.IsPerfect D := by
  intro hp
  let := hp
  obtain ⟨e⟩ := h.2.2.quotient_iso
  let : Group.IsPerfect (alternatingGroup (Fin 3)) := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 D)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hc : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  have hp3 : IsPGroup 3 (alternatingGroup (Fin 3)) :=
    IsPGroup.of_card (n := 1) (by simpa only [pow_one] using hc)
  let : Group.IsNilpotent (alternatingGroup (Fin 3)) := hp3.isNilpotent
  let : Nontrivial (alternatingGroup (Fin 3)) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 3)) inferInstance

variable {G : Type*} [Group G]

/-- The literal 1.2.4 route is unavailable for the solvable block alternative. -/
theorem alternatingBlock_three_not_mem_localFamily {L Q : Subgroup G}
    (hL : ChapterC.IsAlternatingBlock L 3) : L ∉ Chapter1.L G Q :=
  fun hmem => alternatingBlock_three_not_perfect hL (Chapter1.mem_L_isPerfect hmem)

variable [Finite G] {M V : Subgroup G}

/-- C.1.9 applies in every nonidentity subspace centralizer after E.6.21. -/
theorem c19Condition_centralizer (h21 : OddCoreFree V) {A : Subgroup G}
    (hAV : A ≤ V) (hne : A ≠ ⊥) : C19Condition (centralizer (A : Set G)) :=
  c19Condition_of_oddCore_eq_bot (h21 A hAV hne)

/-- Distinct genuine blocks in the same subspace centralizer commute in G.
The extra A₃ hypothesis of the earlier C.1.9 input is discharged locally. -/
theorem centralizerBlocks_equal_or_commute (h19 : BlockCommutationInput G)
    (h21 : OddCoreFree V) {A L J : Subgroup G} (hAV : A ≤ V) (hne : A ≠ ⊥)
    (hL : CentralizerBlock A L) (hJ : CentralizerBlock A J) :
    L = J ∨ ⁅L, J⁆ = ⊥ := by
  by_cases he : L = J
  · exact Or.inl he
  · right
    have hne' : L.subgroupOf (centralizer (A : Set G)) ≠
        J.subgroupOf (centralizer (A : Set G)) := by
      intro hh
      have hm := congrArg (Subgroup.map (centralizer (A : Set G)).subtype) hh
      rw [map_subgroupOf_eq_of_le hL.1, map_subgroupOf_eq_of_le hJ.1] at hm
      exact he hm
    have hc := congrArg (Subgroup.map (centralizer (A : Set G)).subtype)
      (h19 (centralizer (A : Set G)) (fun _ => c19Condition_centralizer h21 hAV hne)
        _ _ hL.2 hJ.2 hne')
    simpa only [map_commutator, map_subgroupOf_eq_of_le hL.1,
      map_subgroupOf_eq_of_le hJ.1, Subgroup.map_bot] using hc

/-- Odd-core vanishing excludes the triple cover through relative subnormality. -/
theorem centralizerComponent_not_threeCover (h21 : OddCoreFree V)
    {A X : Subgroup G} (hAV : A ≤ V) (hne : A ≠ ⊥)
    (hX : CentralizerComponent A X) (n : ℕ) :
    ¬ Chapter1.Section02.LocalModels.IsAlternatingCover X n := by
  intro hm
  have ho := hX.2.1.pPrimeCore_eq_bot (h21 A hAV hne)
  have hXo : pPrimeCore 2 X = ⊥ := by
    have he := pPrimeCore_map_iso 2 (subgroupOfEquivOfLe hX.1)
    rw [ho, Subgroup.map_bot] at he
    exact he.symm
  obtain ⟨e⟩ := hm.2.1
  have hc : Nat.card (center X) = 3 := by
    rw [Nat.card_congr e.toEquiv]
    exact Nat.card_zmod 3
  have hz : center X ≤ pPrimeCore 2 X := le_sSup ⟨inferInstance, by rw [hc]; decide⟩
  have hb : center X = ⊥ := eq_bot_mono hz hXo
  rw [hb, Nat.card_eq_fintype_card] at hc
  norm_num at hc

/-- Both actual centralizers have the same ambient Sylow subgroup Q. -/
theorem common_sylow {K : GroupClass} {T : Sylow 2 G}
    (h : HypothesisE61 K T M V) {U A : Subgroup G}
    (hU : U ∈ obstructionFamily M V) (hA : A ∈ obstructionFamily M V) :
    Chapter1.IsSylowIn 2 (sylowCentralizer (T : Subgroup G) V) (centralizer (U : Set G)) ∧
    Chapter1.IsSylowIn 2 (sylowCentralizer (T : Subgroup G) V) (centralizer (A : Set G)) ∧
    V ≤ sylowCentralizer (T : Subgroup G) V ∧
    V ≤ centralizer (sylowCentralizer (T : Subgroup G) V : Set G) :=
  ⟨h.sylow_obstruction hU, h.sylow_obstruction hA, h.le_sylowCentralizer,
    le_centralizer_iff.mp inf_le_right⟩

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection

module
public import Theory.SpecificGroups.BinaryLinear.ParabolicRadicalControl
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.MiddleRecognition

/-!
# Normal seeds control the middle parabolic in binary five-space

The middle parabolic's radical is minimal normal and self-centralizing.
Every normal subgroup which is not a two-group therefore contains the
whole radical. Combining this with the geometric radical control shows
that an actor whose conjugate closure of that seed stays in the same
parabolic must itself lie in the parabolic. Both middle dimensions and
arbitrary basis markings are retained.

Source: Aschbacher--Smith, the linear row of 12.5.4, printed p.819.
The literal quotient application is in the Chapter 12 normalizer source.
-/

public noncomputable section
open Subgroup

namespace BinaryLinear.FiveParabolicRadical

/-- A normal subgroup of the middle parabolic which is not a two-group
contains the entire radical. -/
theorem twoCore_le_of_normal_not_two (N : Subgroup (BinaryLinear.parabolic plane))
    [N.Normal] (hn : ¬ IsPGroup 2 N) : pCore 2 (BinaryLinear.parabolic plane) ≤ N := by
  let P := BinaryLinear.parabolic plane
  let Q := pCore 2 P
  let B := N.map P.subtype
  have hBP : B ≤ P := map_subtype_le _
  have hBN : P ≤ normalizer (B : Set Lin) := by
    apply (normal_subgroupOf_iff_le_normalizer hBP).mp
    change ((N.map P.subtype).comap P.subtype).Normal
    rw [comap_map_eq_self_of_injective P.subtype_injective]
    infer_instance
  have hi : BinaryLinear.parabolic plane ≤ normalizer
      (BinaryLinear.radical plane ⊓ B : Set Lin) :=
    (le_inf (BinaryLinear.parabolic_le_normalizer plane) hBN).trans
      inf_normalizer_le_normalizer_inf
  rcases radical_irreducible _ inf_le_left hi with hz | he
  · exfalso
    have hc : ⁅B,BinaryLinear.radical plane⁆ ≤ BinaryLinear.radical plane ⊓ B :=
      le_inf
        ((le_normalizer_iff_commutator_le_right).mp
          (hBP.trans (BinaryLinear.parabolic_le_normalizer plane)))
        ((le_normalizer_iff_commutator_le_left).mp
          ((BinaryLinear.radical_le_parabolic plane).trans hBN))
    have hcent : B ≤ centralizer (BinaryLinear.radical plane : Set Lin) :=
      commutator_eq_bot_iff_le_centralizer.mp (bot_unique (hz ▸ hc))
    have h0 : plane ≠ ⊥ := by
      intro hzero
      have hx : ((Pi.single 0 1,0) : Space) ∈ plane := by simp [plane]
      rw [hzero,Submodule.mem_bot] at hx
      have := congrArg (fun v : Space => v.1 0) hx
      simp at this
    have ht : plane ≠ ⊤ := by
      intro htop
      have hx : ((0,Pi.single 0 1) : Space) ∈ plane := htop ▸ Submodule.mem_top
      have hz : (Pi.single 0 1 : Tail) = 0 := hx
      have := congrFun hz 0
      simp at this
    have hb := (BinaryLinear.radical_two plane).to_le
      (hcent.trans (BinaryLinear.centralizer_radical_le h0 ht))
    exact hn (hb.of_equiv (N.equivMapOfInjective P.subtype P.subtype_injective).symm)
  · intro n hnq
    have hr : (n : Lin) ∈ BinaryLinear.radical plane := by
      rw [←SmallParabolicLevi.map_twoCore_eq_radical plane]
      exact mem_map_of_mem P.subtype hnq
    have hb : (n : Lin) ∈ B := (he.symm ▸ hr).2
    exact (mem_map_iff_mem P.subtype_injective).mp hb

end BinaryLinear.FiveParabolicRadical

namespace BinaryLinear.FiveFlagGeometry
open OuterCyclic

/-- The minimal radical property is independent of the middle flag's coordinates or orientation. -/
theorem middle_twoCore_le_normal_not_two (b : FiveBasis) (i : Fin 4) (hi : i = 1 ∨ i = 2)
    (N : Subgroup (flagStabilizer b {i})) [N.Normal] (hn : ¬ IsPGroup 2 N) :
    pCore 2 (flagStabilizer b {i}) ≤ N := by
  let e := (middle_flag_equiv b i hi).some.trans FiveParabolicRadical.matrixParabolicEquiv
  let B := N.map e.toMonoidHom
  let : B.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  have hb : ¬ IsPGroup 2 B := fun h => hn (h.of_equiv (e.subgroupMap N).symm)
  have he := FiveParabolicRadical.twoCore_le_of_normal_not_two B hb
  intro n hnq
  have heq : e n ∈ pCore 2 (BinaryLinear.parabolic FiveParabolicRadical.plane) := by
    rw [←pCore_map_iso 2 e]
    exact mem_map_of_mem e.toMonoidHom hnq
  have hh := he heq
  exact (mem_map_iff_mem e.injective).mp hh

/-- A non-two normal seed in a middle parabolic controls every actor whose
conjugate closure remains in that same parabolic. -/
theorem middle_actor_le_of_seed_closure (b : FiveBasis) (i : Fin 4) (hi : i = 1 ∨ i = 2)
    (Y A : Subgroup (LinearGroup 5)) (hY : Y ≤ flagStabilizer b {i})
    (hn : (Y.subgroupOf (flagStabilizer b {i})).Normal) (hp : ¬ IsPGroup 2 Y)
    (hc : conjugateSpanBy Y A ≤ flagStabilizer b {i}) : A ≤ flagStabilizer b {i} := by
  let P := flagStabilizer b {i}
  let := hn
  have hnot : ¬ IsPGroup 2 (Y.subgroupOf P) := fun ht => hp
    (ht.of_equiv (subgroupOfEquivOfLe hY))
  have hcore := middle_twoCore_le_normal_not_two b i hi (Y.subgroupOf P) hnot
  have hr : BinaryLinear.radical (flagSpace b i) ≤ Y := by
    have hh := map_mono (f := P.subtype) hcore
    rw [map_subgroupOf_eq_of_le hY] at hh
    have he := congrArg (fun Q : Subgroup (LinearGroup 5) =>
      (pCore 2 Q).map Q.subtype) (flagStabilizer_singleton b i)
    rw [SmallParabolicLevi.map_twoCore_eq_radical] at he
    exact he ▸ hh
  rw [flagStabilizer_singleton] at hc ⊢
  exact BinaryLinear.le_parabolic_of_conjugateSpan_le _ Y A hr hc

end BinaryLinear.FiveFlagGeometry

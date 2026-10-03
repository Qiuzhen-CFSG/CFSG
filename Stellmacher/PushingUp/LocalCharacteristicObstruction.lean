module

public import Stellmacher.PushingUp.CriticalDistanceBasic

/-!
# Characteristic-subgroup obstruction in local stabilizers

Standing condition (P) of Stellmacher, *Pushing up*, Arch. Math. 46 (1986),
p. 8, excludes a nontrivial characteristic subgroup of a Sylow subgroup
whose image is normal in the ambient finite group. This module transports
that exact condition to every Sylow 2-subgroup of an M-side vertex stabilizer.
It provides the local obstruction needed in the distance-four analysis,
including the central Frattini-subgroup argument on p. 15.

An M-side stabilizer is isomorphic to `M`; Sylow conjugacy adjusts that
isomorphism to match the chosen Sylows. Pulling a subgroup back through its
restriction preserves characteristicity, by conjugating automorphisms, and
preserves nontriviality. The ambient image of the pullback is the comap of
the original ambient image, so normality also transfers. Condition (P) then
gives the contradiction. No finiteness of the free amalgam or its graph, and
no hypothesis (A), is required.
-/

namespace Stellmacher.PushingUp
open AmalgamGraph
open scoped Pointwise

private theorem obstruction_transport
    {G H : Type*} [Group G] [Group H]
    (P : Subgroup G) (Q : Subgroup H) (e : G ≃* H)
    (he : P.map e.toMonoidHom = Q)
    (hP : ∀ K : Subgroup P, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map P.subtype).Normal) :
    ∀ K : Subgroup Q, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map Q.subtype).Normal := by
  let f : P ≃* Q := (e.subgroupMap P).trans (MulEquiv.subgroupCongr he)
  have hf (x : P) : (f x : H) = e x := rfl
  intro K hK hKne hKn
  let Kpre : Subgroup P := K.comap f.toMonoidHom
  have hprechar : Kpre.Characteristic := by
    apply Subgroup.characteristic_iff_le_comap.mpr
    intro α x hx
    have hh := Subgroup.characteristic_iff_le_comap.mp hK
      ((f.symm.trans α).trans f) hx
    simpa [Kpre] using hh
  have hprene : Kpre ≠ ⊥ := by
    intro hb
    apply hKne
    apply le_antisymm _ bot_le
    intro x hx
    have hy : f.symm x ∈ Kpre := by simpa [Kpre] using hx
    rw [hb] at hy
    have : f.symm x = 1 := hy
    have hx1 : x = 1 := f.symm.injective (by simpa using this)
    exact hx1
  apply hP Kpre hprechar hprene
  have himage : Kpre.map P.subtype = (K.map Q.subtype).comap e.toMonoidHom := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨f y, hy, hf y⟩
    · rintro ⟨y, hy, hyx⟩
      refine ⟨f.symm y, ?_, ?_⟩
      · simpa [Kpre] using hy
      · apply e.injective
        change e (f.symm y : G) = e x
        rw [← hf, f.apply_symm_apply]
        exact hyx
  rw [himage]
  exact hKn.comap e.toMonoidHom

private theorem sylow_obstruction_transport
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (T : Sylow 2 G) (U : Sylow 2 H) (e : G ≃* H)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup G).subtype).Normal) :
    ∀ K : Subgroup U, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (U : Subgroup H).subtype).Normal := by
  let T' : Sylow 2 H := T.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H T' U
  let e' : G ≃* H := e.trans (MulAut.conj g)
  have he' : (T : Subgroup G).map e'.toMonoidHom = (U : Subgroup H) := by
    have hh : ((T : Subgroup G).map e.toMonoidHom).map
        (MulAut.conj g).toMonoidHom = (U : Subgroup H) :=
      congrArg Sylow.toSubgroup hg
    simpa [e', Subgroup.map_map] using hh
  exact obstruction_transport (T : Subgroup G) (U : Subgroup H) e' he' hP

/-- Standing condition (P) holds for every Sylow subgroup of an M-side
vertex stabilizer. -/
public theorem local_sylow_characteristic_obstruction
    {M : Type*} [Group M] [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (_hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (a : Vertex S) (ha : InMVertexOrbit S a)
    (Ta : Sylow 2 (stabilizer S a)) :
    ∀ K : Subgroup Ta, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (Ta : Subgroup (stabilizer S a)).subtype).Normal := by
  obtain ⟨e⟩ := mOrbit_stabilizer_nonempty_mulEquiv S a ha
  exact sylow_obstruction_transport T Ta e hP

end Stellmacher.PushingUp

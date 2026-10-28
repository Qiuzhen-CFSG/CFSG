module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Transfers
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Terminal
public import Theory.GroupTheory.NormalFourCentralizerSeparation

/-!
# Nonsingular point Sylow promotion and controlled fusion

The source chooses a nonsingular point whose T-centralizer is Sylow in its
M-centralizer. This choice is retained as an element l of the original L:
the canonical coordinate point z′ need not have that Sylow property for
the fixed flag. The index-four local calculation and the actual W₀ bounds
promote C_T(z′ˡ) to Sylow in C_G(z′ˡ). Comparison with T ≤ C_G(z) separates
the two ambient classes. The intrinsic two L-orbits then give the literal
fusion required by PointControl. Correcting a conjugator inside C_G(z)
and using the elementary point span proves 12.5.9(4).

The final application feeds this constructed PointControl to the existing
terminal contradiction. Existence of PointSylowGeometry and the zeroth
weak-closure bounds remains a source obligation; it is not asserted here.

Source: Aschbacher--Smith, 12.5.9 and the final argument of 12.5.1,
printed pp.821--822.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}

/-- The literal T₁ = C_T(z′ˡ) after the source choice in 12.5.9. -/
def pointSylow (s : SylowExteriorMarking D) (l : L) : Subgroup G :=
  (T : Subgroup G) ⊓ centralizer ({MulAut.conj (l : G) s.marking.zPrime} : Set G)

/-- The two local computations preceding the ambient argument in 12.5.9(1).
Their construction, including the choice of Sylow coordinates, is separate. -/
structure PointSylowGeometry (s : SylowExteriorMarking D) where
  conjugator : L
  index_four : (pointSylow s conjugator).relIndex (T : Subgroup G) = 4
  local_sylow : ¬ 2 ∣ (pointSylow s conjugator).relIndex
    (s.marking.M ⊓ centralizer ({MulAut.conj (conjugator : G) s.marking.zPrime} : Set G))

omit [Finite G] in
theorem point_weakClosure_eq (s : SylowExteriorMarking D) (l : L)
    (hW : ChapterE.indexedWeakClosure V (T : Subgroup G) 0 ≤ centralizer (V : Set G)) :
    ChapterE.indexedWeakClosure V (pointSylow s l) 0 =
      ChapterE.indexedWeakClosure V (T : Subgroup G) 0 := by
  apply ChapterE.weakClosure_eq_of_le_of_closure_le V (pointSylow s l) (T : Subgroup G) 0
    inf_le_left
  exact le_inf (ChapterE.indexedWeakClosure_le _ _ _) (hW.trans
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr
      ((mem_normalizer_iff.mp (D.normalizes l.property) _).mp s.marking.zPrime_mem))))

/-- Normalizer control promotes the local Sylow calculation to C_G(z′). -/
theorem point_centralizer_sylow_index (s : SylowExteriorMarking D)
    (geometry : PointSylowGeometry s)
    (hW : ChapterE.indexedWeakClosure V (T : Subgroup G) 0 ≤ centralizer (V : Set G))
    (hN : normalizer (ChapterE.indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤
      s.marking.M) :
    ¬ 2 ∣ (pointSylow s geometry.conjugator).relIndex (centralizer ({MulAut.conj (geometry.conjugator : G) s.marking.zPrime} : Set G)) := by
  apply not_dvd_relIndex_of_normalizer_inf_le (pointSylow s geometry.conjugator)
    (s.marking.M ⊓ centralizer ({MulAut.conj (geometry.conjugator : G) s.marking.zPrime} : Set G)) _
    (T.isPGroup'.to_le inf_le_left) inf_le_right geometry.local_sylow
  have hn : normalizer (pointSylow s geometry.conjugator : Set G) ≤ s.marking.M := by
    apply le_trans (ChapterE.normalizer_le_weakClosure_normalizer V (pointSylow s geometry.conjugator) 0)
    rw [point_weakClosure_eq s geometry.conjugator hW]
    exact hN
  exact inf_le_inf_right _ hn

theorem point_centralizer_sylow (s : SylowExteriorMarking D)
    (geometry : PointSylowGeometry s)
    (hW : ChapterE.indexedWeakClosure V (T : Subgroup G) 0 ≤ centralizer (V : Set G))
    (hN : normalizer (ChapterE.indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤
      s.marking.M) :
    ∃ P : Sylow 2 (centralizer ({MulAut.conj (geometry.conjugator : G) s.marking.zPrime} : Set G)),
      (P : Subgroup (centralizer ({MulAut.conj (geometry.conjugator : G) s.marking.zPrime} : Set G))).map
        (centralizer ({MulAut.conj (geometry.conjugator : G) s.marking.zPrime} : Set G)).subtype = pointSylow s geometry.conjugator := by
  have hi := point_centralizer_sylow_index s geometry hW hN
  let P := ((T.isPGroup'.to_le (show pointSylow s geometry.conjugator ≤ (T : Subgroup G) from inf_le_left)).comap_subtype
    (K := centralizer ({MulAut.conj (geometry.conjugator : G) s.marking.zPrime} : Set G))).toSylow hi
  exact ⟨P, map_subgroupOf_eq_of_le inf_le_right⟩

/-- The two point types cannot fuse: their Sylow centralizers have different orders. -/
theorem point_orbit_separation (s : SylowExteriorMarking D)
    (geometry : PointSylowGeometry s)
    (hW : ChapterE.indexedWeakClosure V (T : Subgroup G) 0 ≤ centralizer (V : Set G))
    (hN : normalizer (ChapterE.indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤
      s.marking.M) : ¬ IsConj s.marking.z s.marking.zPrime := by
  have hp : pointSylow s geometry.conjugator ≠ (T : Subgroup G) := by
    intro he
    have hi := geometry.index_four
    rw [he, relIndex_self] at hi
    omega
  have hc : Nat.card (pointSylow s geometry.conjugator) < Nat.card (T : Subgroup G) :=
    lt_of_le_of_ne (card_le_of_le inf_le_left)
      (fun he => hp (eq_of_le_of_card_ge inf_le_left he.ge))
  have hn := not_isConj_of_sylow_centralizer_card_lt
    (MulAut.conj (geometry.conjugator : G) s.marking.zPrime) s.marking.z
    (pointSylow s geometry.conjugator) (T : Subgroup G) (T.isPGroup'.to_le inf_le_left) T.isPGroup'
    inf_le_right s.sylow_centralizes_z (point_centralizer_sylow_index s geometry hW hN) hc
  intro h
  exact hn ((isConj_iff.mpr ⟨(geometry.conjugator : G), rfl⟩).symm.trans h.symm)

omit [Finite G] in
/-- Source 12.5.9(3), with literal L-conjugation on the original module. -/
theorem point_fusion_of_separation (a : ExteriorMarking D)
    (hsep : ¬ IsConj a.z a.zPrime) (x : G) (hx : MulAut.conj x a.z ∈ V) :
    ∃ l ∈ L, MulAut.conj x a.z = MulAut.conj l a.z := by
  have hne : MulAut.conj x a.z ≠ 1 := fun he => a.z_ne_one
    ((MulAut.conj x).injective (he.trans (map_one (MulAut.conj x)).symm))
  rcases a.point_orbits _ hx hne with h | h
  · obtain ⟨l, hl, he⟩ := h
    exact ⟨l, hl, he.symm⟩
  · obtain ⟨l, _, he⟩ := h
    exact (hsep ((isConj_iff.mpr ⟨x, rfl⟩).trans
      (isConj_iff.mpr ⟨l, he⟩).symm)).elim

omit [Finite G] in
/-- Construct the exact PointControl consumed by the terminal argument. -/
theorem pointControl_of_separation (a : ExteriorMarking D)
    (hcore : V ≤ (a.Gi 1).pCoreIn 2) (hsep : ¬ IsConj a.z a.zPrime) :
    PointControl a :=
  ⟨a.card_V₁, a.z_mem_V₁, a.Gi_one_eq_centralizer, hcore,
    point_fusion_of_separation a hsep⟩

theorem pointControl_of_weakClosure (s : SylowExteriorMarking D)
    (geometry : PointSylowGeometry s) (hcore : V ≤ (s.marking.Gi 1).pCoreIn 2)
    (hW : ChapterE.indexedWeakClosure V (T : Subgroup G) 0 ≤ centralizer (V : Set G))
    (hN : normalizer (ChapterE.indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤
      s.marking.M) : PointControl s.marking :=
  pointControl_of_separation s.marking hcore (point_orbit_separation s geometry hW hN)

/-- Original 12.5.9(4): correct the conjugator inside C_G(z), then use the
elementary point span to obtain commutation. The conclusion also holds when
the original conjugator already normalizes V. -/
theorem point_conjugate_and_commutator (s : SylowExteriorMarking D)
    (geometry : PointSylowGeometry s) (hcore : V ≤ (s.marking.Gi 1).pCoreIn 2)
    (hW : ChapterE.indexedWeakClosure V (T : Subgroup G) 0 ≤ centralizer (V : Set G))
    (hN : normalizer (ChapterE.indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤
      s.marking.M) (g : G) (hg : s.marking.Vi 1 ≤ V.map (MulAut.conj g).toMonoidHom) :
    (∃ c ∈ s.marking.Gi 1, V.map (MulAut.conj c).toMonoidHom =
      V.map (MulAut.conj g).toMonoidHom) ∧
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  have p := pointControl_of_weakClosure s geometry hcore hW hN
  obtain ⟨c, hc⟩ := exists_centralizer_conjugator_of_element_fusion
    (fun x hx => by
      obtain ⟨l, hl, he⟩ := p.fusion x hx
      exact ⟨l, D.normalizes hl, he.symm⟩) (hg p.point_mem)
  have hcG : (c : G) ∈ s.marking.Gi 1 := p.point_centralizer.symm ▸ c.property
  refine ⟨⟨c, hcG, hc⟩, ?_⟩
  have hAU : V.map (MulAut.conj g).toMonoidHom ≤ s.marking.U := by
    rw [← hc]
    rintro x ⟨v, hv, rfl⟩
    exact subset_closure ⟨c, hcG, v, hv, rfl⟩
  let : IsElementaryAbelian 2 (conjugateSpanBy V (s.marking.Gi 1)) :=
    elementary_point_span s hcore hW
  apply le_bot_iff.mp
  exact (commutator_mono (le_conjugateSpanBy V (s.marking.Gi 1)) hAU).trans_eq
    (commutator_self_eq_bot_iff.mpr inferInstance)

/-- The terminal source argument now needs the local point Sylow calculation
and the genuine zeroth weak-closure conclusions, rather than PointControl. -/
theorem exterior_contradiction_of_weakClosure_and_terminal (s : SylowExteriorMarking D)
    (geometry : PointSylowGeometry s) (hcore : V ≤ (s.marking.Gi 1).pCoreIn 2)
    (hW : ChapterE.indexedWeakClosure V (T : Subgroup G) 0 ≤ centralizer (V : Set G))
    (hN : normalizer (ChapterE.indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤
      s.marking.M) (d : TerminalConfiguration s.marking) : False :=
  exterior_contradiction_of_point_and_terminal s.marking
    (pointControl_of_weakClosure s geometry hcore hW hN) d

end CFSG.Quasithin.Chapter12.Section05.NaturalSource

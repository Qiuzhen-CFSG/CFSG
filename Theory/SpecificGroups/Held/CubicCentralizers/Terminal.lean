module
public import Theory.SpecificGroups.Held.CubicCentralizers.Fusion
public import Theory.SpecificGroups.Held.CubicCentralizers.Sevens
public import Theory.SpecificGroups.Held.CubicCentralizers.GraphBounds
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.OrbitalPreservation
/-! Every cubic in the literal Held carrier is conjugate to one of two
certified Sylow-three words. Their graph-centralizer upper bounds and explicit
commuting seven-elements imply that neither centralizer order is divisible by
960. The central Sylow word also centralizes the whole subgroup of order 27.
This is the precise order obstruction used by the faithful alternating-five
block in Aschbacher–Smith 2.4.25, printed pp.542–543. -/
public section
namespace Held.CubicCentralizers
open Subgroup OddCubeCandidates
open scoped Pointwise

private theorem normalForm_fused (t : Fin 27) (ht : t ≠ 0) :
    IsConj x (normalForm t) ∨ IsConj z (normalForm t) := by
  fin_cases t
  · exact (ht rfl).elim
  · exact Or.inl fusion1
  · exact Or.inl fusion2
  · exact Or.inl fusion3
  · exact Or.inr fusion4
  · exact Or.inr fusion5
  · exact Or.inl fusion6
  · exact Or.inr fusion7
  · exact Or.inr fusion8
  · exact Or.inr fusion9
  · exact Or.inl fusion10
  · exact Or.inl fusion11
  · exact Or.inl fusion12
  · exact Or.inr fusion13
  · exact Or.inr fusion14
  · exact Or.inl fusion15
  · exact Or.inr fusion16
  · exact Or.inr fusion17
  · exact Or.inr fusion18
  · exact Or.inl fusion19
  · exact Or.inl fusion20
  · exact Or.inl fusion21
  · exact Or.inr fusion22
  · exact Or.inr fusion23
  · exact Or.inl fusion24
  · exact Or.inr fusion25
  · exact Or.inr fusion26

/-- Every actual Held cubic is conjugate to one of the two certified seeds. -/
theorem cubic_fusion (v : He) (hv : orderOf v = 3) : IsConj x v ∨ IsConj z v := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Q : Sylow 3 He := three_sylow.1.toSylow three_sylow.2
  have hP : IsPGroup 3 (zpowers v) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers,hv]; rfl)
  obtain ⟨R,hR⟩ := hP.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq He R Q
  let e := MulAut.conj g
  have hm : (R:Subgroup He).map e.toMonoidHom = three := congrArg Sylow.toSubgroup hg
  have hmem : e v ∈ three := hm ▸ mem_map_of_mem e.toMonoidHom (hR (mem_zpowers v))
  obtain ⟨t,ht⟩ := normalForm_cover hmem
  have ht0 : t ≠ 0 := by
    intro hz
    have he : e v = 1 := ht.symm.trans (by simp [hz,normalForm])
    have hv1 : v = 1 := e.injective (he.trans (map_one e).symm)
    simp only [hv1,orderOf_one] at hv
    omega
  have he : IsConj v (e v) := isConj_iff.mpr ⟨g,rfl⟩
  rcases normalForm_fused t ht0 with hf | hf
  · exact Or.inl ((ht ▸ hf).trans he.symm)
  · exact Or.inr ((ht ▸ hf).trans he.symm)

private theorem centralizer_card_le_graph (v : He) (p : Equiv.Perm (Fin 2058))
    (hp : representation v = p) :
    Nat.card (centralizer ({v} : Set He)) ≤ Nat.card (graphCentralizer p) := by
  let f : centralizer ({v} : Set He) → graphCentralizer p := fun g =>
    ⟨representation g.val,NormalizerGraph.Orbital.held_le_preservingGroup g.val.property,by
      apply mem_centralizer_singleton_iff.mpr
      have hh := congrArg representation (mem_centralizer_singleton_iff.mp g.property)
      simpa only [map_mul,hp] using hh⟩
  apply Nat.card_le_card_of_injective f
  intro a b h
  have hh : representation a.val = representation b.val :=
    congrArg (fun z : graphCentralizer p => z.val) h
  exact Subtype.ext (representation_injective hh)

private theorem seven_dvd_centralizer (v : He)
    (h : ∃ g : He, orderOf g = 7 ∧ Commute g v) :
    7 ∣ Nat.card (centralizer ({v} : Set He)) := by
  obtain ⟨g,hg,hc⟩ := h
  have hm : zpowers g ≤ centralizer ({v} : Set He) :=
    zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hc.eq)
  rw [←hg,←Nat.card_zpowers]
  exact card_dvd_of_le hm

private theorem seedX_not_dvd : ¬ 960 ∣ Nat.card (centralizer ({x} : Set He)) := by
  intro hd
  have h7 := seven_dvd_centralizer x exists_seven_centralizing_x
  have hc := Nat.lcm_dvd hd h7
  norm_num at hc
  have hlo := Nat.le_of_dvd (Nat.card_pos (α := centralizer ({x} : Set He))) hc
  have hhi := (centralizer_card_le_graph x _ representation_x).trans graph_threeX_card_le
  omega

private theorem seedZ_not_dvd : ¬ 960 ∣ Nat.card (centralizer ({z} : Set He)) := by
  intro hd
  have h7 := seven_dvd_centralizer z exists_seven_centralizing_z
  have hc := Nat.lcm_dvd (Nat.lcm_dvd hd h7) twenty_seven_dvd_centralizer_z
  norm_num at hc
  have hlo := Nat.le_of_dvd (Nat.card_pos (α := centralizer ({z} : Set He))) hc
  have hhi := (centralizer_card_le_graph z _ representation_z).trans graph_threeZ_card_le
  omega

private theorem conjugate_centralizer_card {u v : He} (h : IsConj u v) :
    Nat.card (centralizer ({u} : Set He)) = Nat.card (centralizer ({v} : Set He)) := by
  obtain ⟨g,hg⟩ := isConj_iff.mp h
  let e := MulAut.conj g
  have he : (centralizer ({u} : Set He)).map e.toMonoidHom = centralizer ({v} : Set He) := by
    have hu : e u = v := hg
    rw [←hu]
    ext w
    rw [mem_map_equiv,mem_centralizer_singleton_iff,mem_centralizer_singleton_iff]
    constructor
    · intro hw
      simpa only [map_mul,e.apply_symm_apply] using congrArg e hw
    · intro hw
      apply e.injective
      simpa only [map_mul,e.apply_symm_apply] using hw
  rw [←he,card_map_of_injective e.injective]

/-- The order of an actual Held cubic centralizer is not divisible by 960. -/
theorem not_960_dvd_centralizer (v : He) (hv : orderOf v = 3) :
    ¬ 960 ∣ Nat.card (centralizer ({v} : Set He)) := by
  rcases cubic_fusion v hv with hx | hz
  · rw [←conjugate_centralizer_card hx]
    exact seedX_not_dvd
  · rw [←conjugate_centralizer_card hz]
    exact seedZ_not_dvd
end Held.CubicCentralizers

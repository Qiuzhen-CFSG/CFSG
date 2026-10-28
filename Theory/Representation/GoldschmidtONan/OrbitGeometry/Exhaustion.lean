module

public import Theory.Representation.GoldschmidtONan.OrbitGeometry.Suborbits
public import Theory.Representation.GoldschmidtONan.OrbitGeometry.Swapped
public import Theory.Representation.GoldschmidtONan.OrbitGeometry.Complement
public import Theory.Representation.GoldschmidtONan.OrbitGeometry.Transitive

/-!
# Exhaustion of the Goldschmidt–O’Nan geometric cases

If every nonfixed orbit member lies in the moved space, compare the spans
obtained by omitting two conjugate orbit members. A proper moved-space member
would make one omitted span all of V, while the conjugate span lies in the
proper moved space. Hence the orbit has exactly two complementary members.
Otherwise the proved suborbit geometry supplies either the complement case
or the two witnesses for the transitive case. This assembles both source steps.

Source: GLS, Number 2, Chapter C, Proposition 14.2, Steps 1–2,
`refs/KGroup/GLS2/ChapterC.tex`, especially equation (14.6).
-/

public section

namespace Representation.GoldschmidtONan
open BinaryOffender RegularCyclicNormalClosure

variable {X V : Type*} [Group X] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) X V} {Y : Subgroup X}

private def orbitSpanExcept (P : Submodule (ZMod 2) V) : Submodule (ZMod 2) V :=
  ⨆ (U : Submodule (ZMod 2) V) (_ : U ∈ fixedOrbit ρ Y) (_ : U ≠ P), U

private theorem le_orbitSpanExcept {P U : Submodule (ZMod 2) V}
    (hU : U ∈ fixedOrbit ρ Y) (hne : U ≠ P) : U ≤ orbitSpanExcept (ρ := ρ) (Y := Y) P :=
  le_iSup_of_le U (le_iSup_of_le hU (le_iSup_of_le hne le_rfl))

private theorem orbitSpanExcept_map_le (P : Submodule (ZMod 2) V) (x : X) :
    (orbitSpanExcept (ρ := ρ) (Y := Y) P).map (ρ x) ≤
      orbitSpanExcept (ρ := ρ) (Y := Y) (P.map (ρ x)) := by
  simp only [orbitSpanExcept, Submodule.map_iSup]
  apply iSup_le
  intro U
  apply iSup_le
  intro hU
  apply iSup_le
  intro hne
  exact le_orbitSpanExcept (map_mem_fixedOrbit hU x)
    (fun he => hne (orbit_map_injective x he))

private theorem orbitSpanExcept_map (P : Submodule (ZMod 2) V) (x : X) :
    (orbitSpanExcept (ρ := ρ) (Y := Y) P).map (ρ x) =
      orbitSpanExcept (ρ := ρ) (Y := Y) (P.map (ρ x)) := by
  apply le_antisymm (orbitSpanExcept_map_le P x)
  have hi := orbitSpanExcept_map_le (ρ := ρ) (Y := Y) (P.map (ρ x)) x⁻¹
  have hback : (P.map (ρ x)).map (ρ x⁻¹) = P := by
    rw [← orbit_map_mul, inv_mul_cancel, orbit_map_one]
  rw [hback] at hi
  have hh := Submodule.map_mono (f := ρ x) hi
  simpa only [← orbit_map_mul, mul_inv_cancel, orbit_map_one] using hh

private theorem Input.two_space_of_all_nonfixed_le_moved [Finite X] [Finite V]
    (h : Input ρ Y) {W : Submodule (ZMod 2) V}
    (hW : W ∈ fixedOrbit ρ Y) (hWF : W ≠ fixedSpace ρ Y)
    (hWD : W ≤ displacementSpan ρ Y ⊤)
    (hall : ∀ U ∈ fixedOrbit ρ Y, U ≠ fixedSpace ρ Y →
      U ≤ displacementSpan ρ Y ⊤) :
    fixedOrbit ρ Y = {fixedSpace ρ Y, W} := by
  classical
  let F := fixedSpace ρ Y
  let D := displacementSpan ρ Y ⊤
  have hWD' : W = D := by
    by_contra hne
    obtain ⟨v, hvD, hvW⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hWD hne)
    let S := orbitSpanExcept (ρ := ρ) (Y := Y) W
    have hout (d : V) (hdD : d ∈ D) (hdW : d ∉ W) : d ∈ S := by
      have hd0 : d ≠ 0 := fun he => hdW (he ▸ W.zero_mem)
      have hc := (h.suborbit_of_le_moved hW hWD).1
      have hu : d ∈ nonzeroSuborbitUnion ρ Y W := by
        rw [hc]
        exact ⟨hdD, hd0⟩
      obtain ⟨_, y, hy⟩ := hu
      have hn : W.map (ρ y) ≠ W := fun he => hdW (he ▸ hy)
      exact le_orbitSpanExcept (map_mem_fixedOrbit hW y) hn hy
    have hDS : D ≤ S := by
      intro d hd
      by_cases hdW : d ∈ W
      · have hvS := hout v hvD hvW
        have hdv : d + v ∉ W := by
          intro hh
          have hh' := W.sub_mem hh hdW
          exact hvW (by simpa only [add_sub_cancel_left] using hh')
        have hsum := hout (d + v) (D.add_mem hd hvD) hdv
        have hh := S.sub_mem hsum hvS
        simpa only [add_sub_cancel_right] using hh
      · exact hout d hd hdW
    have hFS : F ≤ S := le_orbitSpanExcept fixed_mem_fixedOrbit hWF.symm
    have hStop : S = ⊤ := top_unique (h.split.sup_eq_top ▸ sup_le hFS hDS)
    have hSF : orbitSpanExcept (ρ := ρ) (Y := Y) F ≤ D := by
      apply iSup_le
      intro U
      apply iSup_le
      intro hU
      apply iSup_le
      intro hUF
      exact hall U hU hUF
    obtain ⟨x, hx⟩ := exists_map_eq_of_mem_fixedOrbit fixed_mem_fixedOrbit hW
    have hmap : (orbitSpanExcept (ρ := ρ) (Y := Y) F).map (ρ x) = S := by
      rw [orbitSpanExcept_map, hx]
    have hdim : Module.finrank (ZMod 2) V ≤ Module.finrank (ZMod 2) D := by
      calc
        Module.finrank (ZMod 2) V = Module.finrank (ZMod 2) S := by
          rw [hStop, finrank_top]
        _ = Module.finrank (ZMod 2) (orbitSpanExcept (ρ := ρ) (Y := Y) F) := by
          rw [← hmap]
          exact (Submodule.equivMapOfInjective (ρ x) (action_injective x) _).finrank_eq.symm
        _ ≤ Module.finrank (ZMod 2) D := Submodule.finrank_mono hSF
    let : Nontrivial F := Submodule.nontrivial_iff_ne_bot.mpr h.fixed_nontrivial
    have hf : 0 < Module.finrank (ZMod 2) F := Module.finrank_pos
    have hs := Submodule.finrank_add_eq_of_isCompl h.split
    change Module.finrank (ZMod 2) F + Module.finrank (ZMod 2) D =
      Module.finrank (ZMod 2) V at hs
    omega
  ext U
  constructor
  · intro hU
    by_cases hUF : U = F
    · exact Or.inl hUF
    have hUD := hall U hU hUF
    have hUeq : U = W := by
      by_contra hne
      have hd := h.ti U hU W hW hne
      have hUW : U ≤ W := hWD' ▸ hUD
      exact h.orbit_ne_bot hU ((disjoint_self.mp (hd.mono_right hUW)))
    exact Or.inr hUeq
  · rintro (rfl | rfl)
    · exact fixed_mem_fixedOrbit
    · exact hW

theorem Input.geometric_alternatives [Finite X] [Finite V] (h : Input ρ Y) :
    SingletonCase ρ Y ∨ SwappedCase ρ Y ∨ ComplementCase ρ Y ∨ TransitiveGeometry ρ Y := by
  classical
  by_cases hs : fixedOrbit ρ Y = {fixedSpace ρ Y}
  · left
    refine ⟨hs, ?_⟩
    intro x
    have hx : (fixedSpace ρ Y).map (ρ x) ∈ fixedOrbit ρ Y := ⟨x, rfl⟩
    exact Set.mem_singleton_iff.mp (hs ▸ hx)
  by_cases hm : ∃ W ∈ fixedOrbit ρ Y,
      W ≠ fixedSpace ρ Y ∧ W ≤ displacementSpan ρ Y ⊤
  · obtain ⟨W, hW, hWF, hWD⟩ := hm
    by_cases hall : ∀ U ∈ fixedOrbit ρ Y, U ≠ fixedSpace ρ Y →
        U ≤ displacementSpan ρ Y ⊤
    · exact Or.inr (Or.inl (h.swappedCase_of_two_space
        (h.two_space_of_all_nonfixed_le_moved hW hWF hWD hall) hWF hWD))
    · push Not at hall
      obtain ⟨U, hU, hUF, hUD⟩ := hall
      rcases h.suborbitGeometry U hU hUF with hu | hu
      · exact (hUD hu.1).elim
      · exact Or.inr (Or.inr (Or.inr
          (h.transitiveGeometry_of_mixed_suborbits hW hWD hU hUF hu.1)))
  · exact Or.inr (Or.inr (Or.inl (h.complementCase_of_no_moved_orbit hs
      (fun U hU hUF hUD => hm ⟨U, hU, hUF, hUD⟩))))

theorem Input.orbitGeometry [Finite X] [Finite V] (h : Input ρ Y) :
    SuborbitGeometry ρ Y ∧
      (SingletonCase ρ Y ∨ SwappedCase ρ Y ∨ ComplementCase ρ Y ∨ TransitiveGeometry ρ Y) :=
  ⟨h.suborbitGeometry, h.geometric_alternatives⟩

end Representation.GoldschmidtONan

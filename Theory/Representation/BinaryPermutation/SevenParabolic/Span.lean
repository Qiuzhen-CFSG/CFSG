module
public import Theory.Representation.BinaryPermutation.SevenParabolic.Conjugation
public import Mathlib.Algebra.Module.ZMod
/-!
# The full ordinary second-parabolic span

The fixed space of (12)(34) is exactly ⟨e₁₂₃₄,e₁₂₅₆,e₅₆,e₅₇⟩.
The second parabolic preserves it. The complementary three-cycle generates
the last two vectors from e₁₂₅₆, proving equality with the full orbit span.
An equivariant chart transports this equality to the original conjugate
span in a group. The only exhaustive vector check has 128 binary words.

Source: Aschbacher--Smith, original14.6.10(5), printed p.1029.
-/

@[expose] public section
open Subgroup Equiv BinaryPermutation
open BinaryPermutation.SevenParabolic
namespace BinaryPermutation.SevenParabolic.Ordinary

def plane : Submodule (ZMod 2) Space := Submodule.span (ZMod 2) {firstFour,secondFour}
def secondSpace : Submodule (ZMod 2) Space :=
  Submodule.span (ZMod 2) {firstFour,secondFour,pair56,pair57}
def fixedSpace : Submodule (ZMod 2) Space := (action doubleSwap - LinearMap.id).ker
lemma mem_fixedSpace (v : Space) : v ∈ fixedSpace ↔ action doubleSwap v = v := by
  simp [fixedSpace,LinearMap.mem_ker,sub_eq_zero]
private lemma decomposition (v : Space) (hv : action doubleSwap v = v) :
    v = v.val 2 • firstFour + (v.val 0 + v.val 2) • secondFour +
      (v.val 5 + v.val 0 + v.val 2) • pair56 + v.val 6 • pair57 := by
  have h01 : v.val 0 = v.val 1 := by
    have h := congrArg (fun w : Space => w.val 1) hv
    exact h
  have h23 : v.val 2 = v.val 3 := by
    have h := congrArg (fun w : Space => w.val 3) hv
    exact h
  have hf : ∀ w : Full (Fin 7), (∑ i, w i) = 0 → w 0 = w 1 → w 2 = w 3 →
      w = w 2 • (![1,1,1,1,0,0,0] : Full (Fin 7)) +
        (w 0 + w 2) • ![1,1,0,0,1,1,0] +
        (w 5 + w 0 + w 2) • ![0,0,0,0,1,1,0] + w 6 • ![0,0,0,0,1,0,1] := by
    decide +kernel
  apply Subtype.ext
  exact hf v.val v.property h01 h23
lemma secondSpace_eq_fixedSpace : secondSpace = fixedSpace := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro v hv
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> apply (mem_fixedSpace _).mpr <;> decide
  · intro v hv
    rw [decomposition v ((mem_fixedSpace v).mp hv)]
    have h (x : Space) (hx : x ∈ ({firstFour,secondFour,pair56,pair57} : Set Space)) : x ∈ secondSpace :=
      Submodule.subset_span hx
    apply Submodule.add_mem
    · apply Submodule.add_mem
      · apply Submodule.add_mem
        · exact Submodule.smul_mem _ _ (h _ (by simp))
        · exact Submodule.smul_mem _ _ (h _ (by simp))
      · exact Submodule.smul_mem _ _ (h _ (by simp))
    · exact Submodule.smul_mem _ _ (h _ (by simp))
lemma plane_le_secondSpace : plane ≤ secondSpace := by
  apply Submodule.span_mono
  intro v hv
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hv ⊢
  tauto
lemma secondSpace_invariant (g : Perm7) (hg : g ∈ theta) (v : Space)
    (hv : v ∈ secondSpace) : action g v ∈ secondSpace := by
  rw [secondSpace_eq_fixedSpace,mem_fixedSpace] at hv ⊢
  have hc := mem_centralizer_singleton_iff.mp hg
  calc
    action doubleSwap (action g v) = action (doubleSwap*g) v := by rw [map_mul,Module.End.mul_apply]
    _ = action (g*doubleSwap) v := by rw [hc]
    _ = action g v := by rw [map_mul,Module.End.mul_apply,hv]
lemma pair56_expression : pair56 = action complementCycle secondFour + action (complementCycle^2) secondFour := by
  decide +kernel
lemma pair57_expression : pair57 = secondFour + action complementCycle secondFour := by
  decide +kernel
end BinaryPermutation.SevenParabolic.Ordinary
namespace BinaryPermutation.SevenParabolic.Ordinary
/-- The full second-parabolic orbit span, with the component's even image retained. -/
def orbitSpan (J : Subgroup Perm7) : Submodule (ZMod 2) Space :=
  Submodule.span (ZMod 2) {v | ∃ g ∈ J ⊓ theta, ∃ w ∈ plane, action g w = v}
lemma orbitSpan_eq_secondSpace (J : Subgroup Perm7) (hJ : alternatingGroup (Fin 7) ≤ J) :
    orbitSpan J = secondSpace := by
  have hi (v : Space) (hv : v ∈ plane) : v ∈ orbitSpan J := by
    apply Submodule.subset_span
    exact ⟨1,⟨J.one_mem,theta.one_mem⟩,v,hv,by simp⟩
  have hw : secondFour ∈ plane := Submodule.subset_span (by simp)
  have hc (i : ℕ) : action (complementCycle^i) secondFour ∈ orbitSpan J := by
    apply Submodule.subset_span
    exact ⟨complementCycle^i,⟨J.pow_mem (hJ complementCycle_mem.2) i,
      theta.pow_mem complementCycle_mem.1 i⟩,secondFour,hw,rfl⟩
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨g,hg,w,hw,rfl⟩
    exact secondSpace_invariant g hg.2 w (plane_le_secondSpace hw)
  · apply Submodule.span_le.mpr
    intro v hv
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact hi firstFour (Submodule.subset_span (by simp))
    · exact hi secondFour hw
    · rw [pair56_expression]
      exact Submodule.add_mem _ (by simpa using hc 1) (hc 2)
    · rw [pair57_expression]
      exact Submodule.add_mem _ (hi secondFour hw) (by simpa using hc 1)
end BinaryPermutation.SevenParabolic.Ordinary
namespace BinaryPermutation.SevenParabolic.Ordinary.Chart
open Subgroup
variable {G : Type*} [Group G] {J C W : Subgroup G} (c : Chart J C W)
/-- The actual image of an ambient subgroup in the chart's whole module. -/
def image (B : Subgroup G) : Submodule (ZMod 2) Space :=
  AddSubgroup.toZModSubmodule 2 ((B.subgroupOf W).map c.moduleEquiv.toMonoidHom).toAddSubgroup'
lemma mem_image (B : Subgroup G) (v : W) :
    (c.moduleEquiv v).toAdd ∈ c.image B ↔ v.val ∈ B := by
  constructor
  · rintro ⟨w,hw,he⟩
    exact c.moduleEquiv.injective he ▸ hw
  · intro hv
    exact ⟨v,hv,rfl⟩
lemma mem_image_lift (B : Subgroup G) (v : Space) :
    v ∈ c.image B ↔ (c.lift v : G) ∈ B := by
  simpa only [c.coordinate_lift] using c.mem_image B (c.lift v)

/-- The exact full second span under the original equivariant chart. -/
theorem second_span_image (V P : Subgroup G) (hVW : V ≤ W) (hPJ : P ≤ J)
    (hV : c.image V = plane)
    (hP : (P.subgroupOf J).map c.actor = c.actor.range ⊓ theta) :
    c.image (conjugateSpanBy V P) = secondSpace := by
  have htheta (p : J) (hp : p ∈ P.subgroupOf J) : c.actor p ∈ theta := by
    have hh := mem_map_of_mem c.actor hp
    rw [hP] at hh
    exact hh.2
  let X : Subgroup W := secondSpace.toAddSubgroup.toSubgroup.comap c.moduleEquiv.toMonoidHom
  have hVX : V ≤ X.map W.subtype := by
    intro v hv
    refine ⟨⟨v,hVW hv⟩,?_,rfl⟩
    apply plane_le_secondSpace
    rw [←hV]
    exact (c.mem_image V _).mpr hv
  have hPX : P ≤ normalizer (X.map W.subtype : Set G) := by
    apply le_normalizer_iff.mpr
    rintro p hp _ ⟨v,hv,rfl⟩
    let j : J := ⟨p,hPJ hp⟩
    refine ⟨⟨p*v.val*p⁻¹,le_normalizer_iff.mp c.normalized p (hPJ hp) v v.property⟩,?_,rfl⟩
    change (c.moduleEquiv _).toAdd ∈ secondSpace
    rw [c.equivariant j v]
    exact secondSpace_invariant _ (htheta j hp) _ hv
  have hspan := conjugateSpanBy_le hVX hPX
  have hp0 (v : Space) (hv : v ∈ plane) : v ∈ c.image (conjugateSpanBy V P) := by
    rw [c.mem_image_lift]
    apply le_conjugateSpanBy V P
    apply (c.mem_image_lift V v).mp
    rwa [hV]
  have hw : secondFour ∈ plane := Submodule.subset_span (by simp)
  have hcycle : complementCycle ∈ (P.subgroupOf J).map c.actor := by
    rw [hP]
    refine ⟨?_,complementCycle_mem.1⟩
    apply map_le_range c.actor (C.subgroupOf J)
    rw [c.component_image]
    exact complementCycle_mem.2
  obtain ⟨g,hg,hgc⟩ := hcycle
  have hc (i : ℕ) : action (complementCycle^i) secondFour ∈ c.image (conjugateSpanBy V P) := by
    rw [c.mem_image_lift,←hgc,←map_pow,c.lift_action]
    apply subset_closure
    refine ⟨g.val^i,P.pow_mem hg i,(c.lift secondFour : G),?_,rfl⟩
    apply (c.mem_image_lift V secondFour).mp
    rwa [hV]
  apply le_antisymm
  · rintro v ⟨w,hw,rfl⟩
    obtain ⟨x,hx,hxw⟩ := hspan hw
    exact (show x = w from Subtype.ext hxw) ▸ hx
  · apply Submodule.span_le.mpr
    intro v hv
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact hp0 firstFour (Submodule.subset_span (by simp))
    · exact hp0 secondFour hw
    · rw [pair56_expression]
      exact Submodule.add_mem _ (by simpa using hc 1) (hc 2)
    · rw [pair57_expression]
      exact Submodule.add_mem _ (hp0 secondFour hw) (by simpa using hc 1)
end BinaryPermutation.SevenParabolic.Ordinary.Chart

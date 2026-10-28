module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellSelection.OrbitPair
/-!
# One characteristic pair for all original marked overgroups

The family consists of the pulled-back F-subgroups of actual C.1.17 groups
for which [O²(H),O₂(H)] is not contained in Campbell V. Because B is finite,
choose one member of largest order, then form its two automorphism spans.
The choice precedes every finite H and every original marking e. CoreEscape
handles the omitted residual-layer case; maximality and Theorem B handle
all different F-orbits, while Theorem A handles the selected orbit.

The only explicit earlier-source inputs are the automorphism commutator
conclusion of Campbell II.6–7 and recognition of the actual residual layer
as the C.1.18 block. Their independent source producers discharge them in
final assembly; no uniform pair or per-overgroup classification is assumed.

Source: Campbell II.8, printed pp.36–38; Aschbacher–Smith C.1.17–19.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
universe u v
variable {B : Type u} [Group B] [Finite B] [Nontrivial B]

theorem exists_uniform_pair_of_automorphism_commutator
    (hp : IsPGroup 2 B) (hB : IsBaumannFixed B)
    (hA : ∀ (H : Type v) [Group H] [Finite H] (e : B →* H), InLocalClass e →
      (∀ a : MulAut B, ((Campbell.V H).comap e |>.map a.toMonoidHom).map e ≤ pCore 2 H) →
      ∀ a : MulAut B,
        ⁅Campbell.J (⊤ : Subgroup H),((Campbell.F H).comap e |>.map a.toMonoidHom).map e⁆ ≤ Campbell.F H) :
    ∃ D : CharacteristicPair B,
      ∀ (H : Type v) [Group H] [Finite H] (e : B →* H), InLocalClass e →
        D.first.map e ≤ center H ∨ (D.second.map e).Normal ∨
          ⁅pResidual 2 H,pCore 2 H⁆ ≤ Campbell.V H := by
  classical
  let family : Set (Subgroup B) := {U | ∃ (H : Type v) (_ : Group H) (_ : Finite H)
      (e : B →* H), InLocalClass e ∧ ¬ ⁅pResidual 2 H,pCore 2 H⁆ ≤ Campbell.V H ∧
      U = (Campbell.F H).comap e}
  by_cases hf : family.Nonempty
  · let : Fintype (Subgroup B) := Fintype.ofFinite _
    let fs := Finset.univ.filter (fun U => U ∈ family)
    have hfs : fs.Nonempty := by
      obtain ⟨U,hU⟩ := hf
      exact ⟨U,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hU⟩⟩
    obtain ⟨U,hU,hmax⟩ := fs.exists_max_image (fun U => Nat.card U) hfs
    obtain ⟨H₀,_,_,e₀,h₀,_hn₀,rfl⟩ := (Finset.mem_filter.mp hU).2
    refine ⟨h₀.selectionPair hB,?_⟩
    intro H _ _ e h
    by_cases hn : ⁅pResidual 2 H,pCore 2 H⁆ ≤ Campbell.V H
    · exact Or.inr (Or.inr hn)
    · have hcard := hmax ((Campbell.F H).comap e) (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,H,inferInstance,inferInstance,e,h,hn,rfl⟩)
      have hall : ∀ a : MulAut B,
          ((Campbell.V H).comap e |>.map a.toMonoidHom).map e ≤ pCore 2 H := by
        intro a
        have hv := h.transferred_V_le_core_of_no_residual_bound (h.precomp_equiv a.symm) hB hn
        rwa [pull_precomp_inverse] at hv
      rcases h.selectionPair_alternative_of_maximum h₀ hB hn hcard (hA H e h hall) with hc | hc
      · exact Or.inl hc
      · exact Or.inr (Or.inl hc)
  · obtain ⟨D⟩ := nonempty_characteristicPair hp
    refine ⟨D,?_⟩
    intro H _ _ e h
    right; right
    by_contra hn
    exact hf ⟨(Campbell.F H).comap e,H,inferInstance,inferInstance,e,h,hn,rfl⟩

theorem exists_universal_pair_of_campbell_inputs
    (hp : IsPGroup 2 B) (hB : IsBaumannFixed B)
    (hA : ∀ (H : Type v) [Group H] [Finite H] (e : B →* H), InLocalClass e →
      (∀ a : MulAut B, ((Campbell.V H).comap e |>.map a.toMonoidHom).map e ≤ pCore 2 H) →
      ∀ a : MulAut B,
        ⁅Campbell.J (⊤ : Subgroup H),((Campbell.F H).comap e |>.map a.toMonoidHom).map e⁆ ≤ Campbell.F H)
    (hblock : ∀ (H : Type v) [Group H] [Finite H] (e : B →* H), InLocalClass e →
      ⁅pResidual 2 H,pCore 2 H⁆ ≤ Campbell.V H → BlockAlternative H) :
    ∃ D : CharacteristicPair B, D.Universal.{u,v} := by
  obtain ⟨D,hD⟩ := exists_uniform_pair_of_automorphism_commutator hp hB hA
  refine ⟨D,?_⟩
  intro H _ _ e h
  rcases hD H e h with hc | hn | hb
  · exact Or.inl hc
  · exact Or.inr (Or.inl hn)
  · exact Or.inr (Or.inr (hblock H e h hb))
end CFSG.Quasithin.ChapterC.GlaubermanNiles

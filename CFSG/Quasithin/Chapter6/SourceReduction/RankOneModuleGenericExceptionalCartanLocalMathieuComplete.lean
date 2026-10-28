module
public import Theory.Mathieu.M23.Properties.SolvableActors
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalMathieuWitness

/-!
# The selected M₂₃ Cartan escape without an action premise

The original Cartan--Sylow join is solvable. Its action on the same
selected component quotient contains the full inner Sylow. The native
M₂₃ solvable-actor theorem therefore proves that the original odd Cartan
image is a three-group, excluding every other prime-action row.

This discharges the extra premise in the existing cubic construction and
inversion. The resulting complete LocalCartanWitness gives the original
whole-W conclusion, with both Hall conditions, the original Sylow and all
literal quotient maps unchanged. The component is relocated to the omega
centralizer by the existing witness recognition theorem.

The selected M₂₃ row is complete. Exhaustive component selection,
solvable-radical and nonquasisimple reduction, and the surviving binary
triality exclusion remain separate obligations of SourceLocalCartanEscape.
Source: Aschbacher--Smith 5.1.13, printed pp.636--638, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
variable {G : Type*} [Group G] [Finite G]

/-- The original action on the same selected M₂₃ quotient is a three-group;
all other odd primes are excluded using the source's solvable Sylow join. -/
theorem mathieu_twentyThree_action_isPGroup
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) [C.Normal] (hRC : (residual H).subgroupOf Y ≤ C)
    (hm : Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M23)) :
    IsPGroup 3 ((A.subgroupOf Y).map (normalQuotientAction C (pCore 2 C))) := by
  obtain ⟨_,ho,_,_,_,_⟩ := cartan_action_escape h hH hgen c hY hescape C hRC
  let f₀ := normalQuotientAction C (pCore 2 C)
  let e := hm.some
  let i := MulAut.congr e
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hfC (x : C) : i (f₀ (x : Y)) = MulAut.conj (q x) := by
    rw [normalQuotientAction_inner,MulAut.congr_conj]
    rfl
  have hTY := hH.1.1.2.trans hY.2
  let S := T.subtype hTY
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal C
  let J := (A.subgroupOf Y).map f₀ ⊔ ((T : Subgroup G).subgroupOf Y).map f₀
  let D := (A.subgroupOf Y).map f₀
  let : Group.IsSolvable J := h.cartan_sylow_action_isSolvable c hTY f₀
  have hPj : ((P.mapSurjective hq : Sylow 2 Sporadic.Mathieu.M23) : Subgroup _).map
      MulAut.conj ≤ J.map i.toMonoidHom := by
    rintro _ ⟨x,⟨y,hy,rfl⟩,rfl⟩
    rw [←hfC]
    exact mem_map_of_mem i.toMonoidHom
      (mem_sup_right (mem_map_of_mem f₀ (by rw [hP] at hy; exact hy)))
  have hs : Group.IsSolvable (J.map i.toMonoidHom) :=
    Group.isSolvable_of_surjective (i.toMonoidHom.subgroupMap_surjective J)
  have hp := Sporadic.Mathieu.M23SolvableActors.odd_aut_isPGroup
    (P.mapSurjective hq) (J.map i.toMonoidHom) (D.map i.toMonoidHom) hPj hs
    (map_mono le_sup_left) (by rwa [card_map_of_injective i.injective])
  exact hp.of_equiv (i.subgroupMap D).symm

/-- The selected M₂₃ row supplies the entire original witness, with no
additional restriction on the original Cartan action. -/
theorem mathieu_twentyThree_local_witness
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKT : K ⊔ (T : Subgroup G) = H)
    (hKL : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hKC : K ≤ C.map Y.subtype)
    (hm : Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M23)) :
    ∃ D : Subgroup G, LocalCartanWitness T H A Y (C.map Y.subtype) D := by
  obtain ⟨hKR,_,_⟩ := normal_mathieu_twentyTwo_twentyThree_residual_and_hall
    h hH hgen c hKL hKT horbit hY hescape C hC hKC (.inr hm)
  have hRX : residual H ≤ C.map Y.subtype := hKR ▸ hKC
  have hRC : (residual H).subgroupOf Y ≤ C := by
    have hh := comap_mono (f := Y.subtype) hRX
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hh
  exact mathieu_twentyThree_local_witness_of_three_action
    h hH hgen c hKT hKL horbit hY hescape C hC hKC hm
    (mathieu_twentyThree_action_isPGroup h hH hgen c hY hescape C hRC hm)

/-- The full original-W conclusion in the selected M₂₃ component. The
three-group action condition and every witness field are now discharged. -/
theorem mathieu_twentyThree_cartan_exceptional
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKT : K ⊔ (T : Subgroup G) = H)
    (hKL : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hKC : K ≤ C.map Y.subtype)
    (hm : Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M23)) :
    n = 2 ∧ CartanExceptionalConclusion T L W H := by
  obtain ⟨D,d⟩ := mathieu_twentyThree_local_witness
    h hH hgen c hKT hKL horbit hY hescape C hC hKC hm
  exact localCartan_escape_of_witness h hH hgen c hY d

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve

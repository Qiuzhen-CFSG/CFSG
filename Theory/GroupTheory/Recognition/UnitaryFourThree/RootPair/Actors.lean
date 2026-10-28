module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.HyperbolicData

/-!
# Genuine quotient reflections from the original two cores

Conjugation by selected elements of the two extraspecial cores normalizes
the actual root product R. Their squares centralize R, their actions on E
are the two different transpositions, and the no-shear theorem identifies
exactly the factor fixed modulo E. These are the actor premises of the
hyperbolic recognition theorem, now obtained from original IsType.
Source: Aschbacher, *Sporadic Groups* (1994), 8.15(6),45.3, pp.29–30,243.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G : Type*} [Group G] [Finite G] {z : G}
namespace RootPair
variable (P : RootPair z)

private theorem actor_on_R (h : IsType z) (s : G) (hs : s ∈ P.N) :
    s ∈ normalizer (P.R : Set G) := by
  have hRN : P.R ≤ P.N := by
    change P.R ≤ normalizer (P.E : Set G)
    rw [P.R_eq_centralizer_E h]
    exact centralizer_le_normalizer _
  exact (normal_subgroupOf_iff_le_normalizer hRN).mp (P.R_normal_in_N h) hs

private theorem actor_square (h : IsType z) (s : G) (hs : s ∈ P.N)
    (hs2 : s^2∈P.E) :
    (P.R.normalizerMonoidHom ⟨s,P.actor_on_R h s hs⟩)^2=1 := by
  have hsC : s^2 ∈ Subgroup.centralizer (P.R : Set G) :=
    P.centralizer_R_eq_E h ▸ hs2
  have hsKer : (⟨s,P.actor_on_R h s hs⟩ : normalizer (P.R : Set G))^2 ∈
      P.R.normalizerMonoidHom.ker := by
    rw [normalizerMonoidHom_ker]
    exact hsC
  change P.R.normalizerMonoidHom ((⟨s,P.actor_on_R h s hs⟩ : normalizer (P.R : Set G))^2)=1 at hsKer
  simpa only [map_pow] using hsKer

private theorem actor_fixed_iff (h : IsType z) (s : G) (hs : s ∈ P.N)
    (x : P.R) :
    P.R.normalizerMonoidHom ⟨s,P.actor_on_R h s hs⟩ x * x⁻¹ ∈ center P.R ↔
      ⁅s,(x:G)⁆∈P.E := by
  have hval : ((P.R.normalizerMonoidHom ⟨s,P.actor_on_R h s hs⟩ x * x⁻¹ : P.R):G) =
      ⁅s,(x:G)⁆ := by
    rfl
  rw [← P.R_center h]
  constructor
  · intro hx
    exact ⟨_,hx,hval⟩
  · rintro ⟨v,hv,hveq⟩
    have he : v = P.R.normalizerMonoidHom ⟨s,P.actor_on_R h s hs⟩ x * x⁻¹ :=
      Subtype.ext (hveq.trans hval.symm)
    exact he ▸ hv

private def first_actor (h : IsType z) (s : G) (hs : s ∈ core z)
    (hsz : s*z*s⁻¹=z) (hsu : s*P.u*s⁻¹=z*P.u) :
    (P.hyperbolicFactors h).FirstActor := by
  have hsN : s ∈ P.N := P.core_le_N h hs
  have hsA : s ∉ P.leftCore := by
    intro hh
    have hcomm := mem_centralizer_singleton_iff.mp hh.2
    have he : P.u = z*P.u := by
      calc
        P.u = s*P.u*s⁻¹ := by rw [hcomm,mul_inv_cancel_right]
        _ = z*P.u := hsu
    have hz1 : z=1 := mul_right_cancel (by simpa only [one_mul] using he.symm)
    have hz2 := h.involution
    simp [hz1] at hz2
  let α := P.R.normalizerMonoidHom ⟨s,P.actor_on_R h s hsN⟩
  refine { aut := α
           square := ?_
           map_z := ?_
           map_u := ?_
           fixed_iff := ?_ }
  · apply P.actor_square h s hsN
    have hh : s^2∈zpowers z := h.toCentralizerHypothesis.core_center ▸
      mem_map_of_mem (core z).subtype
        (h.toCentralizerHypothesis.coreData.square_mem_center ⟨s,hs⟩)
    exact (le_sup_left : zpowers z ≤ P.E) hh
  · apply Subtype.ext
    exact hsz
  · apply Subtype.ext
    exact hsu
  · intro x
    rw [P.actor_fixed_iff h s hsN]
    exact P.reflection_fixed_coset_iff h s hs hsA x x.property

private def second_actor (h : IsType z) (s : G) (hs : s ∈ P.conjugateCore)
    (hsz : s*z*s⁻¹=z*P.u) (hsu : s*P.u*s⁻¹=P.u) :
    (P.hyperbolicFactors h).SecondActor := by
  have hsN : s ∈ P.N := P.conjugateCore_le_N h hs
  have hsB : s ∉ P.rightCore := by
    intro hh
    have hcomm := mem_centralizer_singleton_iff.mp hh.2
    have he : z=z*P.u := by
      calc
        z = s*z*s⁻¹ := by rw [hcomm,mul_inv_cancel_right]
        _ = z*P.u := hsz
    have hu1 : P.u=1 := mul_left_cancel (by simpa only [mul_one] using he.symm)
    have hu2 := P.u_order h
    simp [hu1] at hu2
  let α := P.R.normalizerMonoidHom ⟨s,P.actor_on_R h s hsN⟩
  refine { aut := α
           square := ?_
           map_z := ?_
           map_u := ?_
           fixed_iff := ?_ }
  · apply P.actor_square h s hsN
    let : IsExtraspecial 2 P.conjugateCore := P.conjugateCore_extraspecial h
    have hh : s^2∈zpowers P.u := P.conjugateCore_center h ▸
      mem_map_of_mem P.conjugateCore.subtype
        (IsExtraspecial.square_mem_center (⟨s,hs⟩:P.conjugateCore))
    exact (le_sup_right : zpowers P.u ≤ P.E) hh
  · apply Subtype.ext
    exact hsz
  · apply Subtype.ext
    exact hsu
  · intro x
    rw [P.actor_fixed_iff h s hsN]
    exact P.returning_reflection_fixed_coset_iff h s hs hsB x x.property

/-- Both original core transpositions induce the two marked quotient reflections. -/
theorem exists_hyperbolic_actors (h : IsType z) :
    Nonempty ((P.hyperbolicFactors h).FirstActor × (P.hyperbolicFactors h).SecondActor) := by
  obtain ⟨a,ha,b,hb,haz,hau,hbz,hbu⟩ := P.exists_center_transpositions h
  exact ⟨P.first_actor h a ha haz hau,P.second_actor h b hb hbz hbu⟩

/-- The reflection records retain their original ambient core conjugators. -/
theorem exists_hyperbolic_actors_marked (h : IsType z) :
    ∃ a ∈ core z, ∃ b ∈ P.conjugateCore,
      ∃ α : (P.hyperbolicFactors h).FirstActor,
      ∃ β : (P.hyperbolicFactors h).SecondActor,
        (∀ x : P.R, (α.aut x : G)=a*x*a⁻¹) ∧
        (∀ x : P.R, (β.aut x : G)=b*x*b⁻¹) := by
  obtain ⟨a,ha,b,hb,haz,hau,hbz,hbu⟩ := P.exists_center_transpositions h
  refine ⟨a,ha,b,hb,P.first_actor h a ha haz hau,
    P.second_actor h b hb hbz hbu,?_,?_⟩
  · intro x
    rfl
  · intro x
    rfl

end RootPair
end Theory.GroupTheory.Recognition.UnitaryFourThree

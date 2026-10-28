module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo
public import Theory.GroupTheory.PPerfectHom
public import Theory.SpecificGroups.SymmetricSix.Parabolics

/-!
# A moving four-group detects the A₆ fixed space without a shortness premise

The actual moving plane puts the residual actor inside the syntheme
parabolic of order24. If its order had no factor3 it would be a two-group;
two-perfection would then make it trivial, contradicting movement of the
plane. Thus the parabolic recognition and fixed-space calculation apply
without a two-group assumption on the original actor kernel.

Source: Aschbacher–Smith 13.6.22, printed p.932.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly
open BinaryRankTwo

/-- The actual moving plane, rather than an actor-kernel assumption,
retains the cubic part of the two-perfect source residual. -/
theorem six_movingPlane_three_dvd
    (S : Sylow 2 (alternatingGroup (Fin 6)))
    (D : Subgroup (alternatingGroup (Fin 6))) (hp : IsPPerfect 2 D)
    (e : MovingPlane (BinaryPermutation.alternatingNaturalRepresentation (Ω := Fin 6)) S D) :
    3 ∣ Nat.card D := by
  have hplace : ∃ g : alternatingGroup (Fin 6),
      D ⊔ (S : Subgroup (alternatingGroup (Fin 6))) ≤
        AlternatingAction.parabolic.map (MulAut.conj g).toMonoidHom := by
    apply alternating_plane_placement (S := S) (E := e.plane)
    · exact le_sup_right
    · exact e.dimension
    · exact e.invariant
  obtain ⟨g,hg⟩ := hplace
  have hd := Subgroup.card_dvd_of_le ((show D ≤ D ⊔ (S : Subgroup _) from le_sup_left).trans hg)
  have hc : Nat.card (AlternatingAction.parabolic.map (MulAut.conj g).toMonoidHom) = 24 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact Theory.SpecificGroups.SymmetricSix.a6SynthemeStabilizer_order
  rw [hc] at hd
  by_contra h3
  have hcop : Nat.Coprime (Nat.card D) 3 := (Nat.prime_three.coprime_iff_not_dvd.mpr h3).symm
  have ht : IsPGroup 2 D := IsPGroup.of_card_dvd_pow (n := 3)
    (hcop.dvd_of_dvd_mul_left (show Nat.card D ∣ 3 * 2 ^ 3 from hd))
  have hid := hp.hom_eq_one_of_isPGroup ht (MonoidHom.id D)
  have hb : D = ⊥ := by
    apply bot_unique
    intro x hx
    exact mem_bot.mpr (congrArg Subtype.val (congrArg (fun f : D →* D => f ⟨x,hx⟩) hid))
  have he := e.moved
  conv at he => lhs; arg 3; rw [hb]
  have hebot : subspaceCommutator
      (BinaryPermutation.alternatingNaturalRepresentation (Ω := Fin 6)) e.plane (⊥ : Subgroup _) = ⊥ := by
    apply (subspaceCommutator_eq_bot_iff
      (BinaryPermutation.alternatingNaturalRepresentation (Ω := Fin 6)) e.plane
      (⊥ : Subgroup (alternatingGroup (Fin 6)))).mpr
    intro w hw a
    have ha' : a.val = (1 : alternatingGroup (Fin 6)) :=
      Subgroup.mem_bot.mp a.property
    change (BinaryPermutation.alternatingNaturalRepresentation (Ω := Fin 6)) a.val w = w
    rw [ha']
    simp
  rw [hebot] at he
  have hh := e.dimension
  rw [←he] at hh
  simp at hh

variable {G : Type*} [Group G] [Finite G]
  {K U D T l : Subgroup G}

/-- The original moving four-group gives C_U(D)=C_U(K), retaining the
literal central quotient and without identifying the actor kernel. -/
theorem six_fixed_eq_of_moving_four
    (m : ConjugationQuotientModel K U
      (BinaryPermutation.alternatingNaturalRepresentation (Ω := Fin 6)))
    (hf : Function.Surjective m.actor)
    (S : Sylow 2 K) (hS : (S : Subgroup K) = T.subgroupOf K)
    (hDK : D ≤ K) (hp : IsPPerfect 2 D)
    (hn : T ≤ normalizer (D : Set G))
    (hlU : l ≤ U) (hl : ⁅l,D⁆ = l) (hc : Nat.card l = 4)
    (hline : D ⊔ T ≤ normalizer (l : Set G)) :
    U ⊓ centralizer (D : Set G) = U ⊓ centralizer (K : Set G) := by
  let e := SourcePlane.movingPlane m hf T S hS hDK hlU hl hc hline
  have hpi := SourceActors.image_perfect m.actor hDK hp
  have hni : ((S.mapSurjective hf : Sylow 2 (alternatingGroup (Fin 6))) : Subgroup _) ≤
      normalizer ((D.subgroupOf K).map m.actor : Set (alternatingGroup (Fin 6))) := by
    rw [SourceActors.sylow_image m.actor hf S hS]
    exact SourceActors.image_normalizes m.actor hn
  obtain ⟨g,_,ha⟩ := alternating_movingPlane_recognition_of_three_dvd
    (S.mapSurjective hf) _ hpi hni (six_movingPlane_three_dvd _ _ hpi e) e
  apply m.centralizer_eq D hDK
  intro w hw
  apply G2Action.conjugate_fixed_eq_zero
    (BinaryPermutation.alternatingNaturalRepresentation (Ω := Fin 6))
    AlternatingAction.actor AlternatingAction.cubic_fixed_eq_zero g w
  obtain ⟨k,hk,he⟩ := ha
  rw [←he]
  exact hw ⟨k,hk⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly

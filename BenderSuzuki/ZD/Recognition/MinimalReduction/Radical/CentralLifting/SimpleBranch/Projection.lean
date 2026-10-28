module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.CentralLifting.Reduction

/-!
# The projection of a simple covering component

Simplicity makes the surjective projection onto the nontrivial derived Bender
factor injective. Thus it is an actual group equivalence, along which the
concrete Bender model transports.

Source: GLS4, Chapter 2, Lemma 4.5, final paragraph, printed p. 35.
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The simple cover is isomorphic to the derived quotient via its projection. -/
public theorem central_quotient_simple_cover_projection_equiv
    (hgen : Subgroup.closure Z = ⊤) (hodd : pPrimeCore 2 G = ⊥)
    (A : Subgroup G) [A.Normal] (hAc : A ≤ Subgroup.center G) (hAcard : Nat.card A = 2)
    (hs : StructureConclusion ((QuotientGroup.mk' A) '' Z) (M.map (QuotientGroup.mk' A)))
    (hK : IsSimpleGroup
      (centralLiftComponent (QuotientGroup.mk' A) (commutator (G ⧸ A)))) :
    ∃ e : centralLiftComponent (QuotientGroup.mk' A) (commutator (G ⧸ A)) ≃*
        commutator (G ⧸ A),
      ∀ x, e x = centralLiftProjection (QuotientGroup.mk' A) (commutator (G ⧸ A)) x := by
  let q := QuotientGroup.mk' A
  let D := commutator (G ⧸ A)
  let K := centralLiftComponent q D
  let : IsSimpleGroup K := hK
  have hD : IsSimpleBenderGroup D := central_quotient_derived_model hgen hodd A hAc hAcard hs
  let f := centralLiftProjection q D
  have hsurj : Function.Surjective f := centralLiftProjection_surjective q
    (QuotientGroup.mk'_surjective A) D hD
  have hker : f.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker inferInstance with hh | hh
    · exact hh
    · have htriv (d : D) : d = 1 := by
        obtain ⟨k, rfl⟩ := hsurj d
        exact (show k ∈ f.ker from hh ▸ Subgroup.mem_top k)
      exact (hD.not_commutative (fun x y => by rw [htriv x, htriv y])).elim
  exact ⟨MulEquiv.ofBijective f ⟨(MonoidHom.ker_eq_bot_iff f).mp hker, hsurj⟩, fun _ => rfl⟩

/-- The actual simple Bender model on the covering component. -/
public theorem central_quotient_simple_cover_model
    (hgen : Subgroup.closure Z = ⊤) (hodd : pPrimeCore 2 G = ⊥)
    (A : Subgroup G) [A.Normal] (hAc : A ≤ Subgroup.center G) (hAcard : Nat.card A = 2)
    (hs : StructureConclusion ((QuotientGroup.mk' A) '' Z) (M.map (QuotientGroup.mk' A)))
    (hK : IsSimpleGroup
      (centralLiftComponent (QuotientGroup.mk' A) (commutator (G ⧸ A)))) :
    IsSimpleBenderGroup
      (centralLiftComponent (QuotientGroup.mk' A) (commutator (G ⧸ A))) := by
  obtain ⟨e, _⟩ := central_quotient_simple_cover_projection_equiv hgen hodd A hAc hAcard hs hK
  exact (central_quotient_derived_model hgen hodd A hAc hAcard hs).map_mulEquiv e.symm

end BenderSuzuki.ZD

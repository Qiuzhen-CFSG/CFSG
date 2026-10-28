module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Setup
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Radical
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Levi
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.ParabolicReduction
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement
public import Theory.Representation.BinaryOffender.PermutationConjugacy

/-!
# Reduction of the binary SL₅ end-node support sieve

Conjugate the elementary offender into the standard full-flag Sylow subgroup,
which lies in both end-node parabolics. Conjugation preserves cubicity, rank and
fixed codimension. Apply the relative normal-subgroup reduction inside each
parabolic to obtain either a radical offender or a quotient offender on its
radical fixed space. The two branch estimates then force the restricted support
to have at most one node. Their concrete radical and Levi producers, together
with the existing SL₄ displacement theorem, are assembled in `end_node_sieve`.
No dimension cutoff, absolute irreducibility or module catalogue is assumed.

Source: Guralnick–Malle, *Classification of 2F-modules, II*, author manuscript,
Propositions 2.4 and 4.7, pp.6 and 25–26; Aschbacher–Smith K.3.2,
printed pp.454–455.
-/

public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode
open Representation Representation.BinaryOffender

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (σ : Representation (ZMod 2) SL5TenDimensional.Group V)

private theorem cubic_map_conj {G : Type*} [Group G]
    (ρ : Representation (ZMod 2) G V) {B : Subgroup G}
    (hc : IsCubic ρ B) (g : G) :
    IsCubic ρ (B.map (MulAut.conj g).toMonoidHom) := by
  have he (a : G) (w : V) :
      displacement ρ ((MulAut.conj g) a) (ρ g w) = ρ g (displacement ρ a w) := by
    simp only [displacement, LinearMap.sub_apply, LinearMap.id_apply,
      MulAut.conj_apply, map_mul, Module.End.mul_apply, inv_self_apply, map_sub]
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hcc, rfl⟩ w
  obtain ⟨z, rfl⟩ := (ρ.apply_bijective g).surjective w
  change displacement ρ ((MulAut.conj g) a)
    (displacement ρ ((MulAut.conj g) b)
      (displacement ρ ((MulAut.conj g) c) (ρ g z))) = 0
  rw [he, he, he, hc a ha b hb c hcc z, map_zero]

/-- An actual SL₅ offender gives an offender in the relative radical, or
in the actual quotient on the radical fixed space. Cubicity is preserved. -/
theorem parabolic_alternative [FiniteDimensional (ZMod 2) V]
    (e : Fin 2) (B : Subgroup SL5TenDimensional.Group)
    (hB : IsElementaryTwo B) (hc : IsCubic σ B)
    (hsmall : fixedCodim σ B ≤ 2 * rank B) :
    (∃ C : Subgroup (parabolic e), C ≤ radical e ∧ IsElementaryTwo C ∧
      IsCubic (σ.comp (parabolic e).subtype) C ∧
      fixedCodim (σ.comp (parabolic e).subtype) C ≤ 2 * rank C) ∨
    (∃ A : Subgroup (parabolic e ⧸ radical e), IsElementaryTwo A ∧
      IsCubic (quotientRepresentation σ e) A ∧
      fixedCodim (quotientRepresentation σ e) A ≤ 2 * rank A) := by
  obtain ⟨g, hg⟩ := exists_conjugate_le_parabolics B hB
  let D := B.map (MulAut.conj g).toMonoidHom
  have hD : IsElementaryTwo D := hB.map_conj g
  have hDc : IsCubic σ D := cubic_map_conj σ hc g
  have hDs : fixedCodim σ D ≤ 2 * rank D := by
    simpa only [D, fixedCodim_map_conj, rank_map_conj] using hsmall
  let C := D.subgroupOf (parabolic e)
  have hmap : C.map (parabolic e).subtype = D :=
    Subgroup.map_subgroupOf_eq_of_le (hg e)
  let : IsElementaryAbelian 2 D := hD.2
  have hC : IsElementaryTwo C := by
    refine ⟨?_, IsElementaryAbelian.subgroupOf (hg e)⟩
    intro hbot
    exact hD.1 (by rw [← hmap, hbot, Subgroup.map_bot])
  have hrank : rank C = rank D := by
    rw [← rank_map_injective (parabolic e).subtype (parabolic e).subtype_injective, hmap]
  have hcodim : fixedCodim (σ.comp (parabolic e).subtype) C = fixedCodim σ D := by
    unfold fixedCodim
    rw [fixedSpace_comp_map, hmap]
  have hCc : IsCubic (σ.comp (parabolic e).subtype) C := by
    intro a ha b hb c hcc w
    exact hDc a ha b hb c hcc w
  have hCs : fixedCodim (σ.comp (parabolic e).subtype) C ≤ 2 * rank C := by
    simpa only [hrank, hcodim] using hDs
  rcases normal_offender_alternative (σ.comp (parabolic e).subtype) (radical e)
    hC hCc hCs with h | h
  · obtain ⟨A, _, hAU, hA, hAc, hAs⟩ := h
    exact Or.inl ⟨A, hAU, hA, hAc, hAs⟩
  · exact Or.inr ⟨C.map (QuotientGroup.mk' (radical e)), h⟩

/-- Conditional assembly of the two missing mathematical branches. Actor
placement and conjugacy preserve the original representation and highest vector.
The unconditional producer must still discharge both explicit estimates. -/
theorem end_node_sieve_of_estimates [FiniteDimensional (ZMod 2) V]
    (hradical : RadicalEstimate σ) (hquotient : QuotientEstimate σ) :
    EndNodeSieve σ := by
  intro J v hv hhighest _ B hB hc _ hsmall
  have h (e : Fin 2) : (J.erase (node e)).card ≤ 1 := by
    by_contra hnot
    have hcard : 2 ≤ (J.erase (node e)).card := by omega
    rcases parabolic_alternative σ e B hB hc hsmall with hr | hq
    · obtain ⟨C, hCU, hC, hCc, hCs⟩ := hr
      exact (not_lt_of_ge hCs) (hradical e J v hv hhighest hcard C hCU hC hCc)
    · obtain ⟨A, hA, hAc, hAs⟩ := hq
      exact (not_lt_of_ge hAs) (hquotient e J v hv hhighest
        (by simpa only [restrictedSupport_card] using hcard) A hA hAc)
  exact ⟨by simpa [node] using h 0, by simpa [node] using h 1⟩

private theorem four_displacement_input [FiniteDimensional (ZMod 2) V] :
    FourDisplacementInput σ := by
  intro e τ hτ hτi
  exact CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.multiple_support_displacement
    τ hτ hτi

/-- The binary SL₅ end-node support sieve for every faithful irreducible module.

The radical and Levi branches are discharged by their respective geometric
estimates; the Levi branch uses the already-proved binary SL₄ displacement
theorem on the literal radical fixed spaces. -/
theorem end_node_sieve [FiniteDimensional (ZMod 2) V]
    (hfaithful : Function.Injective σ) (hirreducible : Representation.IsIrreducible σ) :
    EndNodeSieve σ := by
  exact end_node_sieve_of_estimates σ
    (radical_estimate σ hfaithful hirreducible)
    (quotient_estimate_of_four σ hfaithful hirreducible
      (four_displacement_input σ))

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode

module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicMarking.RootConjugacy
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicMarking.RootSeed
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicSections
public import Theory.Representation.BinaryOffender.PermutationConjugacy

/-!
# The normalized cyclic actor and the marked commutator vector

The rank-one quadratic bound gives W = I and a commutator two-space by
`cyclic_sections`. Faithfulness of the lower factor and natural head gives
fixed codimension one on the head. Hence the actor placed in the marked
plane radical is a transvection. A plane-preserving conjugator moves it
to the intrinsic center of the specified Sylow subgroup, preserving the
larger actor's radical containment.

The central-root seed calculation then puts every nonzero Sylow-fixed
seed vector in this conjugated actor's full commutator space. The chosen
head intertwiner, plane, flag, and adjusted left conjugator are retained.
The center equality is supplied both in GL₄(2) and in the original actor
group, using the ambient image of each intrinsic subgroup center.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, 13.8.25, printed p.962 (PDF p.979).
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicMarking
open Subgroup Representation Representation.BinaryOffender ChiefFactors
open CriticalTransfer.MarkedGeometry BinaryLinear.MiddleParabolic

private theorem ambient_center_map {H K : Type*} [Group H] [Group K]
    (e : H ≃* K) (S : Subgroup H) :
    ((center S).map S.subtype).map e.toMonoidHom =
      (center (S.map e.toMonoidHom)).map (S.map e.toMonoidHom).subtype := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨⟨e z, mem_map_of_mem _ z.property⟩, mem_center_iff.mpr ?_, rfl⟩
    intro t
    obtain ⟨b, hb, he⟩ := t.property
    apply Subtype.ext
    change (t : K) * e z = e z * (t : K)
    rw [← he]
    have hc : b * (z : H) = (z : H) * b :=
      congrArg Subtype.val (mem_center_iff.mp hz ⟨b, hb⟩)
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg e hc
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨a, ha, he⟩ := z.property
    refine ⟨a, ⟨⟨a, ha⟩, mem_center_iff.mpr ?_, rfl⟩, he⟩
    intro b
    apply Subtype.ext
    apply e.injective
    have hc := congrArg Subtype.val
      (mem_center_iff.mp hz ⟨e b, mem_map_of_mem _ b.property⟩)
    change e b * (z : K) = (z : K) * e b at hc
    change e (b * a) = e (a * b)
    simpa only [map_mul, ← he, MulEquiv.coe_toMonoidHom] using hc

variable {H U : Type*} [Group H] [Finite H] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]

/-- Normalize the actual order-two actor and place the fixed seed vector in its
commutator space. Only the preceding cyclic bound, compatible module conclusions,
and marked parabolic geometry are inputs; centrality and commutator membership
are proved. Left conjugation uses the explicitly adjusted element `eH.symm k * g₀`. -/
theorem normalized_center_and_vector
    (ρ : Representation (ZMod 2) H U) (seed : GeneratingSeed ρ)
    (I W : Subrepresentation ρ) (hI : IsAtom I) (hIW : I ≤ W) (hW : W ≠ ⊤)
    (eH : H ≃* BinaryLinear.GL NaturalSpace) (hchief : ChiefFactorsNaturalOrDual ρ eH)
    (e : (U ⧸ W.toSubmodule) ≃ₗ[ZMod 2] NaturalSpace)
    (he : ∀ a u, e (W.quotientRepresentation a u) = eH a (e u))
    (L F : Submodule (ZMod 2) NaturalSpace)
    (hLP : L ≤ headPlane ρ seed W e) (hPF : headPlane ρ seed W e ≤ F)
    (hL : Module.finrank (ZMod 2) L = 1) (hF : Module.finrank (ZMod 2) F = 3)
    (hpar : seed.parabolic.map eH.toMonoidHom = BinaryLinear.parabolic (headPlane ρ seed W e))
    (T : Sylow 2 H) (hT : (T : Subgroup H) = seed.sylow)
    (hsyl : seed.sylow.map eH.toMonoidHom = borel L (headPlane ρ seed W e) F)
    (A B : Subgroup H) (hAB : A ≤ B) (hA : IsElementaryTwo A) (hrank : rank A = 1)
    (hbound : fixedCodim ρ A ≤ 2 * rank A) (g₀ : H)
    (hrad : (B.map (MulAut.conj g₀).toMonoidHom).map eH.toMonoidHom ≤
      BinaryLinear.radical (headPlane ρ seed W e))
    (v : U) (hv : v ∈ seed.space.toSubmodule ⊓ fixedSpace ρ seed.sylow) (hv0 : v ≠ 0) :
    ∃ k : BinaryLinear.GL NaturalSpace, k ∈ BinaryLinear.parabolic (headPlane ρ seed W e) ∧
      let g := eH.symm k * g₀
      (A.map (MulAut.conj g).toMonoidHom).map eH.toMonoidHom =
        (center (borel L (headPlane ρ seed W e) F)).map
          (borel L (headPlane ρ seed W e) F).subtype ∧
      A.map (MulAut.conj g).toMonoidHom = (center seed.sylow).map seed.sylow.subtype ∧
      (B.map (MulAut.conj g).toMonoidHom).map eH.toMonoidHom ≤
        BinaryLinear.radical (headPlane ρ seed W e) ∧
      v ∈ commSpace ρ (A.map (MulAut.conj g).toMonoidHom) ∧ v ∉ W.toSubmodule := by
  have hhead : IsNatural W.quotientRepresentation eH := ⟨e, he⟩
  obtain ⟨hWI, _, hcomm⟩ := cyclic_sections ρ eH hchief I W hI hIW hhead A hA hrank hbound
  have hWat : IsAtom W := hWI ▸ hI
  have hWfaith := AxisExclusions.naturalOrDual_faithful _ eH
    (AxisExclusions.naturalOrDual_atom ρ eH hchief W hWat)
  obtain ⟨_, hheadcodim, _⟩ := faithful_sections_of_fixedCodim_le_two ρ W hWfaith
    (AxisExclusions.natural_faithful _ eH hhead) hA.1 (by simpa [hrank] using hbound)
  have hcard : Nat.card A = 2 := by rw [hA.card_eq_two_pow_rank, hrank]; rfl
  let A₀ := (A.map (MulAut.conj g₀).toMonoidHom).map eH.toMonoidHom
  have hcard₀ : Nat.card A₀ = 2 := by
    dsimp [A₀]
    rw [Subgroup.card_map_of_injective eH.injective,
      Subgroup.card_map_of_injective (MulAut.conj g₀).injective, hcard]
  have hrad₀ : A₀ ≤ BinaryLinear.radical (headPlane ρ seed W e) :=
    (Subgroup.map_mono (Subgroup.map_mono hAB)).trans hrad
  let σ := naturalAction (MulEquiv.refl (BinaryLinear.GL NaturalSpace))
  have hfix : fixedSpace σ A₀ = BinaryLinear.fixedSpace A₀ := by
    ext u
    exact ⟨fun h a ha => h ⟨a, ha⟩, fun h a => h a a.property⟩
  have hcodim : fixedCodim σ A₀ = 1 := by
    rw [← fixedCodim_map_equivariant W.quotientRepresentation σ eH.toMonoidHom e he,
      fixedCodim_map_conj, hheadcodim]
  have hfixdim : Module.finrank (ZMod 2) (BinaryLinear.fixedSpace A₀) = 3 := by
    have hd := fixedCodim_add_finrank σ A₀
    rw [hfix, hcodim] at hd
    have hdim : Module.finrank (ZMod 2) NaturalSpace = 4 := by simp
    omega
  obtain ⟨t, ht, httrans⟩ := RootConjugacy.exists_transvection_of_order_two_fixed_codimension_one
    (headPlane ρ seed W e) A₀ hcard₀ hrad₀ hfixdim
  obtain ⟨a', ⟨a, ha, rfl⟩, rfl⟩ := ht
  let S := T.mapSurjective (f := eH.toMonoidHom) eH.surjective
  have hS : (S : Subgroup (BinaryLinear.GL NaturalSpace)) = borel L (headPlane ρ seed W e) F := by
    change (T : Subgroup H).map eH.toMonoidHom = _
    rw [hT, hsyl]
  obtain ⟨k, hk, hcenter, hrad'⟩ := RootConjugacy.exists_adjusted_conjugator eH g₀
    L (headPlane ρ seed W e) F hLP hPF hL (headPlane_finrank ρ seed W hW e) hF
    S hS A B hAB hcard hrad ⟨a, ha, httrans⟩
  rw [hS] at hcenter
  let Aα := A.map (MulAut.conj (eH.symm k * g₀)).toMonoidHom
  have hAc : Aα = ((center (borel L (headPlane ρ seed W e) F)).map
      (borel L (headPlane ρ seed W e) F).subtype).comap eH.toMonoidHom := by
    rw [← hcenter, Subgroup.comap_map_eq_self_of_injective eH.injective]
  have hcardα : Nat.card Aα = 2 :=
    (Subgroup.card_map_of_injective (MulAut.conj _).injective).trans hcard
  have hcommα : Module.finrank (ZMod 2) (commSpace ρ Aα) = 2 :=
    (conjugate_commSpace_finrank ρ A _).trans hcomm
  have hcenterH : Aα = (center seed.sylow).map seed.sylow.subtype := by
    apply Subgroup.map_injective (f := eH.toMonoidHom) eH.injective
    rw [ambient_center_map, hsyl]
    exact hcenter
  exact ⟨k, hk, hcenter, hcenterH, hrad',
    RootSeed.fixed_seed_le_commSpace ρ seed W hW hWat eH hchief e he L F
      hLP hPF hL hF hpar hsyl Aα hAc hcardα hcommα hv,
    fun hvW => hv0 ((Submodule.disjoint_def.mp (seed.disjoint_proper ρ W hW)) v hv.1 hvW)⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicMarking

module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.OrbitMatching.NaturalPair
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Modules

/-!
# The singular diagonal orbit in the literal source section

The natural-plus-dual action moves every nonzero vector. In the original
source a component lies in the generalized Fitting preimage, so movement
there forces movement by the two-core. The central-line lifting lemma
therefore turns the coordinate diagonal orbit into an exact Mc-orbit.
If one diagonal lift is conjugate to the original point, all diagonal
lifts are. This is the diagonal exclusion used at both critical endpoints.

Source: Aschbacher--Smith, 14.6.24(4), printed p.1041, using 14.6.1(5).
The genuine component and its marked section remain explicit inputs.
-/

public section
open Subgroup Theory.GroupTheory Representation
open BinaryNaturalDual BinaryNaturalDual.ModelOrbits
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.OrbitMatching
variable {G : Type*} [Group G]

/-- Equality in the specified coordinate action gives a match modulo the
literal section kernel, with the matching element in that actor. -/
theorem section_match_mod_point
    {A B Z : Subgroup G} {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    {ρ : Representation (ZMod 2) A E} (c : BinaryConjugationSection A B Z ρ)
    (v w : B) (a : A) (ha : ρ a (c.coordinates v).toAdd = (c.coordinates w).toAdd) :
    (MulAut.conj (a : G)) (v : G) * (w : G)⁻¹ ∈ Z := by
  let v' : B := ⟨(a : G) * v * (a : G)⁻¹,
    (mem_normalizer_iff.mp (c.normalized a.property) v).mp v.property⟩
  have he : c.coordinates v' = c.coordinates w :=
    Multiplicative.toAdd.injective ((c.equivariant a v).trans ha)
  apply (c.coordinates_eq_one_iff (v' * w⁻¹)).mp
  rw [map_mul,map_inv,he,mul_inv_cancel]

/-- The literal full natural-plus-dual section has no nonzero fixed vectors. -/
theorem natural_dual_section_moves
    (K B Z : Subgroup G) (f : K →* BinaryLinear.GL (Fin 3 → ZMod 2))
    (hf : Function.Surjective f)
    (c : BinaryConjugationSection K B Z (naturalDualRepresentation.comp f))
    (v : B) (hv : (v : G) ∉ Z) : ¬ K ≤ centralizer ({(v : G)} : Set G) := by
  intro hc
  have hfixed (g : BinaryLinear.GL (Fin 3 → ZMod 2)) :
      naturalDualRepresentation g (c.coordinates v).toAdd = (c.coordinates v).toAdd := by
    obtain ⟨k,rfl⟩ := hf g
    have he : (k : G) * v * (k : G)⁻¹ = (v : G) := by
      rw [mem_centralizer_singleton_iff.mp (hc k.property)]
      simp [mul_assoc]
    have hh := c.equivariant k v
    rw [show (⟨(k : G) * v * (k : G)⁻¹,_⟩ : B) = v from Subtype.ext he] at hh
    exact hh.symm
  have hd : 2 ≤ Module.finrank (ZMod 2) (Fin 3 → ZMod 2) := by simp
  have hv1 : (c.coordinates v).toAdd.1 = 0 :=
    VectorStabilizers.natural_fixed_eq_zero hd (fun g => by
      simpa only [naturalDualRepresentation_apply] using congrArg Prod.fst (hfixed g))
  have hv2 : (c.coordinates v).toAdd.2 = 0 := by
    apply VectorStabilizers.dual_fixed_eq_zero hd
    intro g x
    have he := congrArg (fun w : Space (Fin 3 → ZMod 2) => w.2 x) (hfixed g.symm)
    simpa only [naturalDualRepresentation_apply, LinearEquiv.dualMap_apply,
      LinearEquiv.symm_symm] using he
  exact hv ((c.coordinates_eq_one_iff v).mp
    (Multiplicative.toAdd.injective (Prod.ext hv1 hv2)))

variable [Finite G]
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (K B : Subgroup G) (hK : K ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc)
    (hBU : B ≤ conjugateSpanBy (localModule T M) Mc)
    (f : K →* BinaryLinear.GL (Fin 3 → ZMod 2)) (hf : Function.Surjective f)
    (c : BinaryConjugationSection K B (centralInvolutions T) (naturalDualRepresentation.comp f))

include hG hempty hM hunique hmany hcard e hab hK hBU hf c in
/-- Two lifts in the singular diagonal class are exactly Mc-conjugate.
Core movement is proved from the actual component action, not assumed. -/
theorem source_diagonal_match (v w : B)
    (hv : IsSingularDiagonal (c.coordinates v).toAdd)
    (hw : IsSingularDiagonal (c.coordinates w).toAdd) :
    ∃ x ∈ Mc, (MulAut.conj x) (v : G) = (w : G) := by
  let h := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  have hvz : (v : G) ∉ centralInvolutions T := by
    intro hz
    have he := (c.coordinates_eq_one_iff v).mpr hz
    exact hv.1 (congrArg (fun a : Multiplicative (Space (Fin 3 → ZMod 2)) => a.toAdd.1) he)
  have hm := source_core_moves_of_fitting_moves hG T hempty hM hunique hmany hcard e hab Mc
    (ComponentSupports.terminal_outside hG T hempty hM hunique hmany hcard e)
    K hK v (hBU v.property) (natural_dual_section_moves K B _ f hf c v hvz)
  apply match_of_match_mod_point h v (hBU v.property) hm w
  obtain ⟨g,hg⟩ := exists_naturalDual_eq hv.1 hw.1 hv.2.1 hw.2.1 (hv.2.2.trans hw.2.2.symm)
  obtain ⟨x,hx⟩ := hf g
  refine ⟨x,(hK.trans (map_subtype_le _)) x.property,section_match_mod_point c v w x ?_⟩
  change naturalDualRepresentation (f x) (c.coordinates v).toAdd = _
  rw [hx,hg]

include hG hempty hM hunique hmany hcard e hab hK hBU hf c in
/-- One point-class diagonal lift puts every lift of that diagonal orbit in
the ambient point class. The point and the section kernel are the original Z. -/
theorem source_diagonal_isConj_point
    (z : G) (v w : B)
    (hv : IsSingularDiagonal (c.coordinates v).toAdd)
    (hw : IsSingularDiagonal (c.coordinates w).toAdd) (hwz : IsConj (w : G) z) :
    IsConj (v : G) z := by
  obtain ⟨x,_,he⟩ := source_diagonal_match hG T hempty hM hunique hmany hcard e hab
    K B hK hBU f hf c v w hv hw
  exact (isConj_iff.mpr ⟨x,by simpa only [MulAut.conj_apply] using he⟩).trans hwz

end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.OrbitMatching

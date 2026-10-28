module

public import CFSG.Quasithin.ChapterB.Section04.G2.Extensions
public import Theory.Representation.G2NaturalExtensions.FixedSpaces
public import Theory.Representation.BinaryOffender.Basic

/-!
# B.4.6 fixed spaces on the original natural extension

For V = [V,E(L)] with its actual natural quotient V/C_V(L), perfectness of the
components gives derived generation. The universal Weyl quotient and its norm
then show that every element fixing a quotient vector fixes every representative.
Thus C_V(A) is the full preimage of C_{V/C_V(L)}(A) for all A ≤ L. This proves
B.4.6(7) and preserves exact fixed codimensions, the offender family and its
local generated groups used in part (13).

These are statements about the original L-action and its literal quotient.
No additional geometric conclusion is supplied as an input. The finite ambient
extension and its generalized Fitting hypothesis are unnecessary for these
particular assertions. The other parabolic and fusion clauses of B.4.6 remain
separate results. Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma B.4.6(7), printed p.88, and its offender applications on pp.89–90.
-/

@[expose] public section

open Representation Atlas.G2.Natural

namespace CFSG.Quasithin.ChapterB.Section04.G2
open Representation.OneCohomology Representation.BinaryOffender
variable {F L V : Type*} [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]
  [Group L] [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- A fixed vector in the literal natural quotient has all its representatives
fixed by the same element of L. The source hypothesis V = [V,E(L)] supplies
derived generation; neither a root-type assumption nor an involution hypothesis
is needed. -/
theorem fixed_of_naturalQuotient_fixed
    (σ : Representation (ZMod 2) L V)
    (hgen : Coinvariants.ker (σ.comp (Theory.GroupTheory.componentLayer L).subtype) = ⊤)
    (eL : L ≃* Atlas.G2.Model F)
    (eN : (V ⧸ fixed σ) ≃ₗ[ZMod 2] Space F)
    (he : ∀ g v, eN (naturalQuotientAction σ g v) = action F (eL g) (eN v))
    (g : L) (v : V)
    (hv : naturalQuotientAction σ g ((fixed σ).mkQ v) = (fixed σ).mkQ v) :
    σ g v = v := by
  let σM := σ.comp eL.symm.toMonoidHom
  let p := eN.toLinearMap.comp (fixed σ).mkQ
  have hp : Function.Surjective p := eN.surjective.comp (fixed σ).mkQ_surjective
  have hfixed : p.ker ≤ fixed σM := by
    intro v hv g
    have hz : (fixed σ).mkQ v = 0 := eN.injective (by simpa [p] using hv)
    exact ((Submodule.Quotient.mk_eq_zero _).mp hz) (eL.symm g)
  have hE : Theory.GroupTheory.componentLayer L ≤ commutator L := by
    apply sSup_le
    intro K hK
    have : Theory.GroupTheory.IsQuasisimple K := hK.2
    calc
      K = ⁅K, K⁆ := Subgroup.commutator_eq_self.symm
      _ ≤ commutator L := Subgroup.commutator_mono le_top le_top
  have hgenM : Coinvariants.ker (σM.comp (commutator (Atlas.G2.Model F)).subtype) = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, v⟩, rfl⟩
    have hg : eL g.val ∈ commutator (Atlas.G2.Model F) := by
      have hm := Subgroup.mem_map_of_mem eL.toMonoidHom (hE g.property)
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr eL.surjective] at hm
      exact hm
    have hh := Coinvariants.sub_mem_ker
      (ρ := σM.comp (commutator (Atlas.G2.Model F)).subtype) ⟨eL g.val, hg⟩ v
    simpa [σM] using hh
  have heM (a : Atlas.G2.Model F) (w : V) : p (σM a w) = action F a (p w) := by
    simpa [p, σM, naturalQuotientAction] using he (eL.symm a) ((fixed σ).mkQ w)
  have hnat : action F (eL g) (p v) = p v := by
    change action F (eL g) (eN ((fixed σ).mkQ v)) = eN ((fixed σ).mkQ v)
    rw [← he, hv]
  simpa [σM] using Extensions.fixed_of_natural_fixed σM p hp hfixed hgenM heM (eL g) v hnat
end CFSG.Quasithin.ChapterB.Section04.G2

namespace CFSG.Quasithin.ChapterB.Section04.G2
open Representation.OneCohomology Representation.BinaryOffender
variable {F L V : Type*} [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]
  [Group L] [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
variable (σ : Representation (ZMod 2) L V)
    (hgen : Coinvariants.ker (σ.comp (Theory.GroupTheory.componentLayer L).subtype) = ⊤)
    (eL : L ≃* Atlas.G2.Model F)
    (eN : (V ⧸ fixed σ) ≃ₗ[ZMod 2] Space F)
    (he : ∀ g v, eN (naturalQuotientAction σ g v) = action F (eL g) (eN v))

include hgen eL eN he

/-- Fixed spaces on the original module are the full inverse images of those
on the literal natural quotient. -/
theorem fixedSpace_naturalQuotient_comap (A : Subgroup L) :
    (fixedSpace (naturalQuotientAction σ) A).comap (fixed σ).mkQ = fixedSpace σ A := by
  ext v
  constructor
  · intro hv a
    exact fixed_of_naturalQuotient_fixed σ hgen eL eN he a v (hv a)
  · intro hv a
    change (fixed σ).mkQ (σ a v) = (fixed σ).mkQ v
    exact congrArg (fixed σ).mkQ (hv a)

/-- B.4.6(7): fixed vectors lift through V → V/C_V(L). This stronger subgroup
version specializes to every involution by taking its cyclic subgroup. -/
theorem fixedSpace_naturalQuotient_map (A : Subgroup L) :
    (fixedSpace σ A).map (fixed σ).mkQ = fixedSpace (naturalQuotientAction σ) A := by
  rw [← fixedSpace_naturalQuotient_comap σ hgen eL eN he A]
  exact Submodule.map_comap_eq_of_surjective (fixed σ).mkQ_surjective _

/-- Passage to the natural quotient preserves the exact binary codimension
of every subgroup fixed space. -/
theorem fixedCodim_naturalQuotient_eq (A : Subgroup L) :
    fixedCodim σ A = fixedCodim (naturalQuotientAction σ) A := by
  let q := (fixedSpace σ A).mapQ (fixedSpace (naturalQuotientAction σ) A)
    (fixed σ).mkQ (fixedSpace_naturalQuotient_comap σ hgen eL eN he A).ge
  have hq : Function.Bijective q := by
    constructor
    · apply LinearMap.ker_eq_bot.mp
      apply le_antisymm _ bot_le
      intro x hx
      obtain ⟨v, rfl⟩ := (fixedSpace σ A).mkQ_surjective x
      have hv : (fixed σ).mkQ v ∈ fixedSpace (naturalQuotientAction σ) A :=
        (Submodule.Quotient.mk_eq_zero _).mp hx
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact (fixedSpace_naturalQuotient_comap σ hgen eL eN he A).le hv
    · intro y
      obtain ⟨z, rfl⟩ := (fixedSpace (naturalQuotientAction σ) A).mkQ_surjective y
      obtain ⟨v, rfl⟩ := (fixed σ).mkQ_surjective z
      exact ⟨(fixedSpace σ A).mkQ v, rfl⟩
  exact (LinearEquiv.ofBijective q hq).finrank_eq

/-- The offender inequality for the original source module is exactly the
inequality on its literal natural quotient. -/
theorem offender_naturalQuotient_iff (A : Subgroup L) :
    IsOffender σ A ↔ IsOffender (naturalQuotientAction σ) A := by
  rw [IsOffender, IsOffender, fixedCodim_naturalQuotient_eq σ hgen eL eN he A]

/-- The source family P(L,V) is unchanged on passing to V/C_V(L). Weight
comparisons are preserved even when the two modules have different dimensions. -/
theorem bestOffender_naturalQuotient_iff (A : Subgroup L) :
    IsBestOffender σ A ↔ IsBestOffender (naturalQuotientAction σ) A := by
  have hweight (B C : Subgroup L) :
      weight σ B ≤ weight σ C ↔
        weight (naturalQuotientAction σ) B ≤ weight (naturalQuotientAction σ) C := by
    have hB := fixedCodim_add_finrank σ B
    have hC := fixedCodim_add_finrank σ C
    have hBq := fixedCodim_add_finrank (naturalQuotientAction σ) B
    have hCq := fixedCodim_add_finrank (naturalQuotientAction σ) C
    rw [fixedCodim_naturalQuotient_eq σ hgen eL eN he B] at hB
    rw [fixedCodim_naturalQuotient_eq σ hgen eL eN he C] at hC
    unfold weight
    omega
  simp only [IsBestOffender, hweight]

/-- The local offender-generated groups used in B.4.6(13) are unchanged on
passing to the natural quotient. This applies to every H ≤ L, including the
parabolic radicals and the Sylow intersection in the source. -/
theorem generatedBy_bestOffenders_naturalQuotient_eq (H : Subgroup L) :
    generatedBy {A | IsBestOffender σ A} H =
      generatedBy {A | IsBestOffender (naturalQuotientAction σ) A} H := by
  congr 1
  ext A
  exact bestOffender_naturalQuotient_iff σ hgen eL eN he A

end CFSG.Quasithin.ChapterB.Section04.G2

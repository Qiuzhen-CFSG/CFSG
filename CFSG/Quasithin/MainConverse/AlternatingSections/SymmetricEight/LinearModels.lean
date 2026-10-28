module

public import CFSG.Quasithin.MainConverse.AlternatingSections.SymmetricEight.Basic
public import Stellmacher.Recognition.ConversePSL2Prime
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168

/-!
# The linear models in permutation degrees seven and eight

The actual PSL₂(7) matrix group is minimal simple by the prime-field
converse proved from Dickson's subgroup theorem. Its simple sections are
therefore prime cyclic or isomorphic to PSL₂(7). The checked common-action
comparison `psl2SevenEquivPsl3Two` transfers this result to PSL₃(2), and
likewise to SL₃(2). No recognition from the number 168 is used.

These are the exceptional model facts for the degree-eight K calculation
in Aschbacher–Smith, Theorem 0.1.2(3), printed pp.4 and 482. They do not
assert that every primitive permutation subgroup has one of these models.
The comparison's ATLAS attribution and license are retained in its owning
module `Theory.AtlasPort.ExceptionalIsomorphisms.Order168`.
-/

namespace CFSG.Quasithin.MainConverse

open CFSG.KnownSimple
open scoped MatrixGroups

private theorem psl2_prime_isKGroup (F : Type) [Field F] [Finite F]
    (p : ℕ) (hp : p.Prime) (hF : Nat.card F = p) (hpgt : 3 < p)
    (hpmod : p % 5 = 2 ∨ p % 5 = 3) :
    IsKGroup IsConstructedCarrier (PSL(2, F)) := by
  have hm : IsMinimalSimple (PSL(2, F)) :=
    Stellmacher.Recognition.isMinimalSimple_psl2_prime (F := F) hp hF hpgt hpmod
  apply SymmetricEight.minimalSimple_isKGroup_constructed hm
  apply IsConstructedCarrier.classical
  apply IsClassicalModel.linear 2 p
  · exact ⟨hp.isPrimePow, by decide, fun _ => hpgt⟩
  · exact ⟨F, inferInstance, inferInstance, hF, ⟨MulEquiv.refl _⟩⟩

-- Fix the prime instance before elaborating the concrete field and matrix
-- structures, so the generic theorem uses the same instances as the model.
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- Every simple section of the actual PSL₂(7) belongs to the catalogue. -/
public theorem psl2Seven_isKGroup_constructed :
    IsKGroup IsConstructedCarrier (PSL(2, ZMod 7)) :=
  psl2_prime_isKGroup (ZMod 7) 7 (by decide) (by simp) (by decide) (by decide)

/-- The actual PSL₃(2) has the same section property via the checked comparison. -/
public theorem psl3Two_isKGroup_constructed :
    IsKGroup IsConstructedCarrier (PSL(3, ZMod 2)) :=
  SymmetricEight.isKGroup_constructed_of_injective psl2Seven_isKGroup_constructed
    Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two.symm.toMonoidHom
    Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two.symm.injective

/-- The binary special linear model is covered by the same action comparison. -/
public theorem sl3Two_isKGroup_constructed :
    IsKGroup IsConstructedCarrier (SL(3, ZMod 2)) :=
  SymmetricEight.isKGroup_constructed_of_injective psl2Seven_isKGroup_constructed
    Atlas.Comparisons.Exceptional.psl2SevenEquivSl3Two.symm.toMonoidHom
    Atlas.Comparisons.Exceptional.psl2SevenEquivSl3Two.symm.injective

/-- Sections of any actual copy of PSL₂(7), with an arbitrary-universe target. -/
public theorem psl2Seven_simple_section_constructed {G S : Type*}
    [Group G] [Group S] [IsSimpleGroup S] (e : G ≃* PSL(2, ZMod 7))
    (U : Subgroup G) (f : U →* S) (hf : Function.Surjective f) :
    IsConstructedCarrier S :=
  SymmetricEight.constructed_section_of_isKGroup
    (SymmetricEight.isKGroup_constructed_of_injective
      psl2Seven_isKGroup_constructed e.toMonoidHom e.injective) U f hf

/-- Sections of any actual copy of PSL₃(2), with an arbitrary-universe target. -/
public theorem psl3Two_simple_section_constructed {G S : Type*}
    [Group G] [Group S] [IsSimpleGroup S] (e : G ≃* PSL(3, ZMod 2))
    (U : Subgroup G) (f : U →* S) (hf : Function.Surjective f) :
    IsConstructedCarrier S :=
  SymmetricEight.constructed_section_of_isKGroup
    (SymmetricEight.isKGroup_constructed_of_injective
      psl3Two_isKGroup_constructed e.toMonoidHom e.injective) U f hf

end CFSG.Quasithin.MainConverse

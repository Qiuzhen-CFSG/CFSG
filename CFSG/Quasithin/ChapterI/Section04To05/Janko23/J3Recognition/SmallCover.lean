module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.SourceGenerators.LinearSubgroup
public import Theory.SpecificGroups.Janko3.SourceRecognition.SmallCoverFactorization
public import Theory.SpecificGroups.Janko3.SourceRecognition.ModelQuotientGenerators

/-!
# Recognition from a genuine bounded cover and original local subgroups

The bounded cover first supplies an actual surjection from the concrete model.
Its generators therefore provide the order-nineteen divisor in the target.
The original involution centralizer, order-243 subgroup and sixteen-field
embedding supply the other divisors, giving the independent lower bound.
The same model map is consequently an isomorphism.

The cover, its bound and its two generating surjections are still explicit
inputs. No finite abstract ATLAS presentation or pre-existing ATLAS pair in
the original target is assumed.
-/

public noncomputable section
namespace CFSG.Quasithin.Janko23.J3Recognition

/-- Actual original local subgroups turn a bounded cover into a model
equivalence, retaining the specified maps out of that cover. -/
theorem equiv_of_small_cover_and_local_subgroups
    {E G : Type*} [Group E] [Group G] [Finite E] [Finite G] [Nontrivial G]
    (htype : J3Type G) (hcenter : Subgroup.center G = ⊥)
    (P : Subgroup G) (hP : Nat.card P = 243)
    (k : Theory.PSL2.BinaryFourFieldExtension.Model →* G) (hk : Function.Injective k)
    (f : E →* Sporadic.Janko3.Model) (hf : Function.Surjective f)
    (q : E →* G) (hq : Function.Surjective q) (hbound : Nat.card E ≤ 150698880) :
    ∃ e : Sporadic.Janko3.Model ≃* G, e.toMonoidHom.comp f = q := by
  obtain ⟨r,hr,hcomp⟩ :=
    Sporadic.Janko3.SourceRecognition.exists_model_factor_of_small_cover f hf q hq hcenter hbound
  have hgen := Sporadic.Janko3.SourceRecognition.hasGenerators_of_model_surjection r hr
  have hlower := LinearSubgroup.card_lower_bound_of_embedding htype hgen P hP k hk
  have hb : Nat.card Sporadic.Janko3.Model ≤ Nat.card G := by
    simpa only [Sporadic.Janko3.model_card] using hlower
  exact ⟨MulEquiv.ofBijective r (hr.bijective_of_nat_card_le hb),hcomp⟩

end CFSG.Quasithin.Janko23.J3Recognition

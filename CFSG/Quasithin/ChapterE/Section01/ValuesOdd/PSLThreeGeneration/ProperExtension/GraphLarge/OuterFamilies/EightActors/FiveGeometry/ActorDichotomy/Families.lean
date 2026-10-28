module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveGeometry.ActorDichotomy.Transport
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveSourceAudit.MonomialWitness.Solvability
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveSourceAudit.MonomialWitness.SylowPlacement

/-!
# Reduction to two concrete calculations in PSL₃(5):2

If an invariant eight-only family contains an actor outside the specified
matrix actor's conjugacy class, a conjugate of that actor must supply the
quotient alternative. Otherwise the family's weak closure equals that of
the specified class. The trivial subgroup contributes nothing. This is an
equality argument, since normalizers are not monotone in their subgroups.

Two finite calculations remain explicit: monomial/normalizer generation for
the specified class at one Sylow, and quotient reselection outside that class.
The theorems here transport the first calculation to every Sylow and assemble
arbitrary invariant families from those inputs. They do not assert either
finite calculation or the unconditional source theorem.

Source: Aschbacher--Smith E.1.5 and E.1.14(7), pp.210 and 214.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.ActorDichotomy
open FiveSourceAudit PSUThreeGeneration
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The missing generation calculation at a single actual Sylow in the
literal split monomial overgroup. Merely escaping the normalizer is weaker. -/
@[expose] def MonomialJoin : Prop :=
  ∃ S : Sylow 2 Model, (S : Subgroup Model) ≤ monomialOvergroup ∧
    monomialOvergroup ⊔ normalizer (weakClosure (S : Subgroup Model) family : Set Model) = ⊤

/-- Reselection retains the entire original actor and an actual ambient
conjugator. Its position is measured in the literal residual quotient. -/
@[expose] def ReselectionAt (T : Sylow 2 Model) (z : Model) : Prop :=
  ∀ A : Subgroup Model, IsElementaryAbelian 2 A → A ≤ (T : Subgroup Model) →
    Nat.card A = 8 → A ∉ family → ∃ g : Model,
      A.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup Model) ∧
      QuotientActor (centralizerResidualOvergroup T z) (A.map (MulAut.conj g).toMonoidHom)

/-- The remaining concrete reselection theorem, independent of the first
orbit's normalizer calculation. Its model premise is supplied separately. -/
@[expose] def ModelReselection : Prop :=
  ∀ (T : Sylow 2 Model) (z : Model), orderOf z = 2 → z ∈ FiveSourceAudit.inner →
    (T : Subgroup Model) ≤ centralizer ({z} : Set Model) →
    (let K := centralizerResidualOvergroup T z
     Nonempty ((K ⧸ solvableRadical K) ≃* Equiv.Perm (Fin 5))) → ReselectionAt T z


/-- One actor in the specified conjugacy class forces the whole class into
an invariant family. -/
theorem family_subset_of_common_actor {Ω : Set (Subgroup Model)}
    (hΩ : IsElementaryFamily Ω) {A : Subgroup Model} (hA : A ∈ Ω) (ha : A ∈ family) :
    family ⊆ Ω := by
  obtain ⟨g, rfl⟩ := ha
  have ha0 := hΩ.2 g⁻¹ _ hA
  have hi : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id Model := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [map_map, hi, map_id] at ha0
  rintro B ⟨b, rfl⟩
  exact hΩ.2 b actor ha0

/-- The identity subgroup does not change weak closure; all nonidentity
members may be compared with the fixed orbit. -/
theorem weakClosure_eq_family (T : Sylow 2 Model) {Ω : Set (Subgroup Model)}
    (hΩ : IsElementaryFamily Ω) {A : Subgroup Model} (hA : A ∈ Ω) (ha : A ∈ family)
    (honly : ∀ B ∈ Ω, B ≤ (T : Subgroup Model) → B ≠ ⊥ → B ∈ family) :
    weakClosure (T : Subgroup Model) Ω = weakClosure (T : Subgroup Model) family := by
  apply le_antisymm
  · apply sSup_le
    rintro B ⟨hB, hBT⟩
    by_cases hb : B = ⊥
    · simp [hb]
    · exact le_sSup ⟨honly B hB hBT hb, hBT⟩
  · apply sSup_le
    rintro B ⟨hB, hBT⟩
    exact le_sSup ⟨family_subset_of_common_actor hΩ hA ha hB, hBT⟩

/-- Sylow conjugacy promotes one monomial generation calculation to a
solvable generating overgroup at every Sylow, with the same family. -/
theorem solvable_join_at_every_sylow (hjoin : MonomialJoin) (T : Sylow 2 Model) :
    ∃ H : Subgroup Model, (T : Subgroup Model) ≤ H ∧ Group.IsSolvable H ∧
      H ⊔ normalizer (weakClosure (T : Subgroup Model) family : Set Model) = ⊤ := by
  obtain ⟨S, hSH, hj⟩ := hjoin
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Model S T
  let e := MulAut.conj g
  have hST : (S : Subgroup Model).map (e : Model →* Model) = (T : Subgroup Model) :=
    congrArg (fun P : Sylow 2 Model => (P : Subgroup Model)) hg
  have hf : {B : Subgroup Model | B.map (e : Model →* Model) ∈ family} = family := by
    ext B
    constructor
    · intro hB
      have hb := family_elementary.2 g⁻¹ _ hB
      have he : (MulAut.conj g⁻¹).toMonoidHom.comp (e : Model →* Model) = MonoidHom.id Model := by
        ext x
        simp [e, MulAut.conj_apply, mul_assoc]
      simpa only [map_map, he, map_id] using hb
    · exact family_elementary.2 g B
  have hw : (weakClosure (S : Subgroup Model) family).map (e : Model →* Model) =
      weakClosure (T : Subgroup Model) family := by
    simpa only [MulEquiv.toMonoidHom_eq_coe, hf, hST] using map_weakClosure_equiv e (S : Subgroup Model) family
  let _ := monomialOvergroup_solvable
  refine ⟨monomialOvergroup.map (e : Model →* Model), hST ▸ map_mono hSH,
    Group.isSolvable_of_surjective ((e : Model →* Model).subgroupMap_surjective monomialOvergroup), ?_⟩
  have hn := (weakClosure (S : Subgroup Model) family).map_normalizer_eq_of_bijective
    (f := (e : Model →* Model)) e.bijective
  rw [hw] at hn
  rw [← hn, ← Subgroup.map_sup, hj, map_top_of_surjective _ e.surjective]

/-- Assemble any eight-only invariant family from the two concrete model
calculations. The quotient actor is a genuine member of that same family. -/
theorem unmarked_model_of_calculations (hjoin : MonomialJoin)
    (T : Sylow 2 Model) (Ω : Set (Subgroup Model)) (hΩ : IsElementaryFamily Ω)
    (hEight : ∀ B ∈ Ω, B ≤ (T : Subgroup Model) → B ≠ ⊥ → Nat.card B = 8)
    (A : Subgroup Model) (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup Model))
    (hcard : Nat.card A = 8) (z : Model) (hreselect : ReselectionAt T z) :
    UnmarkedFiveGeometryAt (ZMod 5) T Ω z := by
  classical
  by_cases hbad : ∃ B ∈ Ω, B ≤ (T : Subgroup Model) ∧ B ≠ ⊥ ∧ B ∉ family
  · obtain ⟨B, hB, hBT, hne, hnot⟩ := hbad
    obtain ⟨g, hBgT, hq⟩ := hreselect B (hΩ.1 B hB) hBT (hEight B hB hBT hne) hnot
    exact Or.inr ⟨B.map (MulAut.conj g).toMonoidHom, hΩ.2 g B hB, hBgT, hq⟩
  · have honly (B : Subgroup Model) (hB : B ∈ Ω) (hBT : B ≤ (T : Subgroup Model))
        (hne : B ≠ ⊥) : B ∈ family := by
      by_contra hn
      exact hbad ⟨B, hB, hBT, hne, hn⟩
    have hne : A ≠ ⊥ := by
      intro he
      have hc := (eq_bot_iff_card A).mp he
      omega
    have hw := weakClosure_eq_family T hΩ hA (honly A hA hAT hne) honly
    obtain ⟨H, hTH, hs, hj⟩ := solvable_join_at_every_sylow hjoin T
    exact Or.inl ⟨H, hTH, hs, by rw [hw]; exact hj⟩

/-- The conditional model calculation has the requested marked consumer;
the independent S₅ model premise remains explicit. -/
theorem fiveGeometry_model_of_calculations (hjoin : MonomialJoin)
    (T : Sylow 2 Model) (Ω : Set (Subgroup Model)) (hΩ : IsElementaryFamily Ω)
    (hEight : ∀ B ∈ Ω, B ≤ (T : Subgroup Model) → B ≠ ⊥ → Nat.card B = 8)
    (A : Subgroup Model) (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup Model))
    (hcard : Nat.card A = 8) (z : Model) (hreselect : ReselectionAt T z)
    (hmodel : let K := centralizerResidualOvergroup T z
      Nonempty ((K ⧸ solvableRadical K) ≃* Equiv.Perm (Fin 5))) :
    FiveGeometryAt (ZMod 5) T Ω z :=
  fiveGeometryAt_of_unmarked (ZMod 5) T Ω z
    (unmarked_model_of_calculations hjoin T Ω hΩ hEight A hA hAT hcard z hreselect) hmodel

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.ActorDichotomy

module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.ModelBounds.Scalar
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.ModelBounds.Normalizer
public import Theory.Representation.BinaryOffender.NormalizerRank
public import Mathlib.RingTheory.LittleWedderburn

/-!
# Intrinsic bounds for irreducible moved quotients

Schur's lemma and the finite division-ring theorem make the commutant a
field. The perfect opposite component therefore centralizes the quotient;
full commutator generation removes its central kernel. Elementary subgroups
of the full linear normalizer inject into the component automorphism group.
Consequently a dimension larger than that two-rank plus two supplies every
large-module bound required by the small-offender contradiction.

The binary-three recognition is an actual consumer. Irreducibility remains
a genuine earlier source condition, not an assertion about every setup.
Source: Aschbacher–Smith 10.1.1–2 and 10.2.12, printed pp.741–742,754.
-/

@[expose] public noncomputable section
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- A perfect opposite component acts trivially on an irreducible moved quotient. -/
theorem crossed_of_irreducible_marking
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {J V : Type*} [Group J] [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (σ : Representation (ZMod 2) J V) (hi : σ.IsIrreducible)
    (e : (L ⧸ pCore 2 L) ≃* J)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
      (σ.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) := by
  classical
  let : σ.IsIrreducible := hi
  let F := Module.End (MonoidAlgebra (ZMod 2) J) σ.asModule
  let : Finite σ.asModule := Finite.of_equiv V σ.asModuleEquiv.symm.toEquiv
  let : Finite F := Finite.of_injective
    (fun f : F => (f : σ.asModule → σ.asModule)) DFunLike.coe_injective
  let : Field F := inferInstance
  let : Module F V := (inferInstance : Module F σ.asModule)
  apply crossed_of_scalar_commutant (F := F) D σ e s ?_ ht htn
  intro f hf
  let f' : σ.IntertwiningMap σ := {
    toLinearMap := f
    isIntertwining' j := LinearMap.ext (hf j) }
  refine ⟨(IntertwiningMap.equivAlgEnd (ρ := σ) f' : F),?_⟩
  intro v
  rfl

/-- Large irreducible quotients are controlled by the full component automorphism group. -/
theorem large_bounds_of_irreducible_marking
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {J V : Type*} [Group J] [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (σ : Representation (ZMod 2) J V) (hf : Function.Injective σ) (hi : σ.IsIrreducible)
    (e : (L ⧸ pCore 2 L) ≃* J)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
      (σ.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {m r : ℕ} (hm : 3 < m) (hcard : Nat.card V = 2 ^ m)
    (hr : primeRank 2 (MulAut J) ≤ r) (hrm : r < m - 2) :
    Nonempty (LargeModuleBounds D) := by
  let : Finite J := Finite.of_equiv (L ⧸ pCore 2 L) e.toEquiv
  have h := primeRank_linearNormalizer_le σ hi
  let f : J ≃* actionImage σ :=
    MonoidHom.ofInjective (fun _ _ h => hf (congrArg Units.val h))
  rw [←primeRank_equiv 2 (MulAut.congr f)] at h
  exact large_bounds_of_marked_normalizer D σ e s hn
    (fun _ ht htn => crossed_of_irreducible_marking D σ hi e s ht htn)
    hm hcard (h.trans hr) hrm

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition

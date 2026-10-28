module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlaneQuotient
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPointCentralizers

/-!
# The paired four-group and its local S₃ quotient on the chosen orbit

The original seed and conjugator give all vector–functional pairs of
pairing one in W. Each resulting subgroup has order four. Its pointwise
centralizer induces S₃ on W, and the map from N_G(L) ∩ C_G(U) has precisely
C_G(W) as its relative kernel. The induced group has trivial two-core.

This supplies the literal local quotient at the start of source §7.7.2.
The ambient containment C_G(U) ≤ N_G(L), the local preimage two-core,
and the final exclusion remain with qt-d-1222-nonff-doubled.
Source: Aschbacher–Smith, printed p.704, in `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryLinearThree
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE
open DoubledBinaryPlanes DoubledBinaryPlaneQuotient
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The literal paired-plane quotient on the original seed orbit is S₃.
All planes use the same original conjugator and coordinate marking. -/
theorem sourceOrbit_binary_pairedPlane_quotient
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) :
    ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
      ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] NaturalDual.Space,
        (∀ w, (E w).2 = 0 ↔ (w.toMul : G) ∈ V) ∧
        (∀ w, (E w).1 = 0 ↔ (w.toMul : G) ∈ V.map (MulAut.conj t).toMonoidHom) ∧
        ∀ v : Vector, ∀ f : Module.Dual (ZMod 2) Vector, f v = 1 →
          Nat.card (ambientPlane D.sourceOrbit E v f) = 4 ∧
          Nonempty (inducedAutomizer D.sourceOrbit
            (centralizer (ambientPlane D.sourceOrbit E v f : Set G)) ≃* Equiv.Perm (Fin 3)) ∧
          pCore 2 (inducedAutomizer D.sourceOrbit
            (centralizer (ambientPlane D.sourceOrbit E v f : Set G))) = ⊥ ∧
          ∃ π : (normalizer (L : Set G) ⊓
            centralizer (ambientPlane D.sourceOrbit E v f : Set G) : Subgroup G) →*
              Equiv.Perm (Fin 3), Function.Surjective π ∧
              π.ker = (centralizer (D.sourceOrbit : Set G)).subgroupOf
                (normalizer (L : Set G) ⊓ centralizer (ambientPlane D.sourceOrbit E v f : Set G)) := by
  obtain ⟨t,ht,hnt,q,hq,E,a,hE,ha,_,hcov,hV,hVt⟩ :=
    D.sourceOrbit_binary_automizer_model h hd F hF hmodel
  refine ⟨t,ht,hnt,E,hV,hVt,?_⟩
  intro v f hfv
  have he := ambientPlane_equiv D.sourceOrbit L D.sourceOrbit_component_normalizes
    q hq E hE a ha hcov v f hfv
  refine ⟨ambientPlane_card D.sourceOrbit E v f hfv,he,
    twoCore_eq_bot_of_symmetricThree he,?_⟩
  have hh := centralizer_quotient D.sourceOrbit (ambientPlane D.sourceOrbit E v f) he
  rwa [D.sourceOrbit_normalizer_eq_of_markedDoubled h hd] at hh

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

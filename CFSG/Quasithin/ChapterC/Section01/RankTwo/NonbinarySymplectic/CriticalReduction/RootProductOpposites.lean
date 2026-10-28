module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootProductClosureLayer
public import Glauberman.BaumannRankOneGeneration

/-!
# Opposite Baumann generators in the original rank-one closure

The original Baumann normal closure has full Sylow image at the unchanged
field degree. Its actual Sylow is the product of its original Baumann
subgroup and its whole two-core. A conjugator in its own two-residual gives
two Baumann conjugates generating modulo that core. Their Thompson central
omegas meet exactly in their full central part. The same Baumann subgroup
supplements the whole residual, so all generators remain in the original
closure, with every central attachment retained.

The proof applies the normalizer-invariant SL₂ Sylow theorem to the native
closure already constructed on the characteristic replacement. This supplies
opposite generators for the Baumann step in MS93 (5.1), printed p.913.
Core centralization, the Baumann-Sylow equality, the selected-path generation
needed by Niles and the terminal distance exclusions remain to be proved.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit CentralRootGeometry.SmallMovers
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The original Baumann subgroup supplies full Sylow images and opposite
residual generators in its native closure at the unchanged field degree. -/
theorem Input.replacement_root_product_baumann_opposites
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (E₁ E₂ : Subgroup (FreeAmalgam d.radical))
    (hE₁ : E₁ ≤ Q d.radical t) (hE₂ : E₂ ≤ Q d.radical t)
    (hc₁ : (Q d.radical a).relIndex E₁ = Nat.card F)
    (hc₂ : (Q d.radical a).relIndex E₂ = Nat.card F)
    (hi₁ : (centralizer (E₁ : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) = Nat.card F)
    (hi₂ : (centralizer (E₂ : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) = Nat.card F)
    (hprod : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F ^ 2) : Set (FreeAmalgam d.radical)) ⊆
      (E₁ : Set (FreeAmalgam d.radical)) * (E₂ : Set (FreeAmalgam d.radical))) :
    ∃ E : BinaryField, E.degree = n ∧
      ∃ I : Subgroup (FreeAmalgam d.radical), I ≤ stabilizer d.radical a ∧
      ∃ S : Sylow 2 I,
        (S : Subgroup I).map I.subtype =
          Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) (Nat.card F ^ 2) ∧
      let N := normalClosure (Glauberman.baumannSubgroup (S : Subgroup I) : Set I)
      N ⊔ pCore 2 I = ⊤ ∧
      Nonempty ((N ⧸ pCore 2 N) ≃* Matrix.SpecialLinearGroup (Fin 2) E.Carrier) ∧
      generalizedFitting N = pCore 2 N ∧
      (pResidual 2 N).map N.subtype = pResidual 2 I ∧
      ∃ P : Sylow 2 N,
        ((Glauberman.baumannSubgroup (P : Subgroup N)).map N.subtype).map I.subtype =
          Glauberman.baumannSubgroup (Q d.radical t) ∧
        ((omegaCenterIn (thompsonSubgroup (P : Subgroup N))).map N.subtype).map I.subtype =
          omegaCenterIn (thompsonSubgroup (Q d.radical t)) ∧
        Order.HasUniqueMaximalOver (P : Subgroup N) ⊤ ∧
        normalClosure (Glauberman.baumannSubgroup (P : Subgroup N) : Set N) = ⊤ ∧
        centralizer (normalClosure (omegaCenterIn (P : Subgroup N) : Set N) : Set N) = pCore 2 N ∧
        Glauberman.baumannSubgroup (P : Subgroup N) ⊔ pCore 2 N = (P : Subgroup N) ∧
        pResidual 2 N ⊔ Glauberman.baumannSubgroup (P : Subgroup N) = ⊤ ∧
        ∃ x : N, x ∈ pResidual 2 N ∧
          (Glauberman.baumannSubgroup (P : Subgroup N) ⊔
            (Glauberman.baumannSubgroup (P : Subgroup N)).map (MulAut.conj x).toMonoidHom) ⊔
              pCore 2 N = ⊤ ∧
          omegaCenterIn (thompsonSubgroup (P : Subgroup N)) ⊓
            (omegaCenterIn (thompsonSubgroup (P : Subgroup N))).map (MulAut.conj x).toMonoidHom =
            omegaCenterIn (thompsonSubgroup (P : Subgroup N)) ⊓ center N := by
  obtain ⟨E,hE,I,hI,hQI,S,hS,hBa,hWB,hgen,⟨eN⟩,hcores,hfit,hres,hU,
    P,hP,hunique,hOm,hBP,hBgen,hZe,hmove,hseed,hVe,hVQ,hVm,hVs,hVomega,hVC,hOmegaC⟩ :=
    h.replacement_root_product_native_baumann_closure d geometry hb ha hat
      E₁ E₂ hE₁ hE₂ hc₁ hc₂ hi₁ hi₂ hprod
  let := finite_stabilizer d.radical a
  let : Finite I := Finite.of_injective (inclusion hI) (inclusion_injective hI)
  let N := normalClosure (Glauberman.baumannSubgroup (S : Subgroup I) : Set I)
  let q := eN.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 N))
  have hq : Function.Surjective q := eN.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 N := by
    change eN.toMonoidHom.ker.comap (QuotientGroup.mk' (pCore 2 N)) = _
    rw [eN.toMonoidHom.ker_eq_bot eN.injective,MonoidHom.comap_bot,QuotientGroup.ker_mk']
  obtain ⟨hsupp,hressupp,x,hx,hopp,hinter⟩ :=
    Glauberman.baumann_rank_one_opposites_of_generation P q hq hk hBgen
  exact ⟨E,hE,I,hI,S,hS,hgen,⟨eN⟩,hfit,hres,P,hBP,hOm,hunique,hBgen,hVC,
    hsupp,hressupp,x,hx,hopp,hinter⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

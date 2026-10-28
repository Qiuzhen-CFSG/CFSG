module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ReciprocalRoots.Centralizers
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ReciprocalRoots.SmallActors

/-!
# Reciprocal long roots on the actual conjugate module

Conjugating C_V(D) back by g⁻¹ gives an elementary subgroup of N_G(V).
The double-centralizer identity transports through that same map and gives
fixed codimension 2n. The small-actor theorem therefore constructs an inner
root homomorphism. Transporting it forward realizes conjugation on the
original Vᵍ, with kernel exactly C_{C_V(D)}(Vᵍ).

Source consumes this theorem for every root in the recognized q³ actor.
The full original module and both centralizer kernels remain in the action
formula. This does not assert containment of the full third flag preimage
in Vᵍ. Source: Aschbacher--Smith 11.2.2(5), printed p.768. Final central
containment and plane reconstruction belong to
qt-d-1222-natural-weak-closure-source.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterE

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ReciprocalRoots
open Atlas.G2 Atlas.G2.Natural
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))

omit [Finite G] in
private theorem conjugate_cancel (U : Subgroup G) (g : G) :
    (U.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = U := by
  rw [map_map]
  have he : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp [MulAut.conj_apply,mul_assoc]
  rw [he,map_id]

theorem reciprocal_root_actor (g : G)
    (a : (V.map (MulAut.conj g).toMonoidHom) →* Model S.field.Carrier)
    (hact : ∀ (x : V.map (MulAut.conj g).toMonoidHom) (v : D.space),
      (D.spaceEquiv (Multiplicative.ofAdd (Preliminary.markedAction D m (a x) v)) : G) =
        (x : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (x : G)⁻¹)
    (ha : a.range = EvenTwoRank.elementary S.field.Carrier)
    (hr : (2*S.field.degree : ℕ∞) < globalR V)
    (Z : Subgroup (Model S.field.Carrier))
    (hZ : Z ∈ RootCentralizers.longRoots S.field.Carrier) :
    let E := V ⊓ centralizer (RootPullback.rootPreimage _ a Z : Set G)
    ∃ (b : E →* Model S.field.Carrier) (u : Model S.field.Carrier),
      (∀ (x : E) (v : D.space),
        MulAut.conj g (D.spaceEquiv (Multiplicative.ofAdd (Preliminary.markedAction D m (b x) v)) : G) =
          (x : G) * MulAut.conj g (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (x : G)⁻¹) ∧
      b.ker = (centralizer (V.map (MulAut.conj g).toMonoidHom : Set G)).subgroupOf E ∧
      b.range ≤ LieParabolicSetup.highestRoot.map (MulAut.conj u).toMonoidHom := by
  let := D.elementary
  let A := V.map (MulAut.conj g).toMonoidHom
  let E := V ⊓ centralizer (RootPullback.rootPreimage A a Z : Set G)
  let e := MulAut.conj g⁻¹
  let B := E.map e.toMonoidHom
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le (show E ≤ V from inf_le_left)
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map e.toMonoidHom
  have hAV : A.map e.toMonoidHom = V := conjugate_cancel V g
  have hBN : B ≤ normalizer (V : Set G) := by
    have hh := map_mono (f:=e.toMonoidHom) (rootCentralizer_normalizes D S g a ha hr Z hZ)
    rwa [map_equiv_normalizer_eq,hAV] at hh
  have hcmap : (A ⊓ centralizer (E : Set G)).map e.toMonoidHom =
      V ⊓ centralizer (B : Set G) := by
    rw [map_inf _ _ _ e.injective,Theory.GroupTheory.map_centralizer_equiv,hAV]
    rfl
  have hcor : subgroupCorank V (V ⊓ centralizer (B : Set G)) = 2*S.field.degree := by
    have hi := relIndex_map_map_of_injective (A ⊓ centralizer (E : Set G)) A (f:=e.toMonoidHom) e.injective
    rw [hcmap,hAV] at hi
    exact (congrArg (Nat.log 2) hi).trans (reciprocal_corank D S m A a hact ha Z hZ)
  obtain ⟨b,u,hb,hbk,hbr⟩ := small_ambient_actor_root D S m B hBN hcor.le
  let b' := b.comp (e.subgroupMap E).toMonoidHom
  refine ⟨b',u,?_,?_,?_⟩
  · intro x v
    have hh := congrArg (MulAut.conj g) (hb (e.subgroupMap E x) v)
    change MulAut.conj g (D.spaceEquiv (Multiplicative.ofAdd (Preliminary.markedAction D m (b' x) v)) : G) =
      MulAut.conj g ((e x : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (e x : G)⁻¹) at hh
    simpa only [map_mul,map_inv,show ∀ y : G, MulAut.conj g (e y) = y from
      fun y => by simp [e,MulAut.conj_apply,mul_assoc]] using hh
  · have hC : (centralizer (A : Set G)).map e.toMonoidHom = centralizer (V : Set G) := by
      rw [Theory.GroupTheory.map_centralizer_equiv]
      change centralizer (A.map e.toMonoidHom : Set G) = centralizer (V : Set G)
      rw [hAV]
    ext x
    change b (e.subgroupMap E x) = 1 ↔ (x : G) ∈ centralizer (A : Set G)
    rw [←MonoidHom.mem_ker,hbk]
    change e (x : G) ∈ centralizer (V : Set G) ↔ (x : G) ∈ centralizer (A : Set G)
    rw [←hC,mem_map_equiv]
    simp only [MulEquiv.symm_apply_apply]
  · rintro _ ⟨x,rfl⟩
    exact hbr ⟨e.subgroupMap E x,rfl⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ReciprocalRoots

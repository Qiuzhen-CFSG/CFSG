module

public import Theory.SpecificGroups.PSL3.RadicalParabolicTwoSignalizers.Centralizers
public import Theory.SpecificGroups.PSL3.RadicalParabolicTwoSignalizers.Extension
public import Theory.SpecificGroups.PSL3.RadicalParabolicTwoSignalizers.MarkedRecognition
public import Theory.SpecificGroups.PSL3.RadicalParabolicTwoSignalizers.AutomorphismSignalizers

/-!
# Marked parabolic radicals and two-signalizer transport for PSL₃(5)

The extension action is faithful under O₂(H) = 1, normal K ≃ PSL₃(5),
and two-group quotient H/K. The full-automorphism model theorem therefore
kills every two-subgroup of H normalized by a parabolic radical in K.
Conjugate radicals are handled by changing the marked equivalence.

Recognition moves a marked normal elementary kernel, its order and its
actual SL₂(5) quotient through an ambient equivalence. The final theorem
combines recognition and signalizer vanishing without either as an extra
premise. Its maps retain the specified kernel in K and then in H, so it
applies to H = (Y_C R)/O₂(Y_C R) and the image R* in the source.

Source: Aschbacher–Smith, `refs/quasithin.pdf`, proof of 1.3.8,
printed p.513, final paragraph establishing C(G,R) ≤ M.
-/

public section

open scoped MatrixGroups
open Subgroup Matrix.PSL3.RootPlaneGeometry

namespace Matrix.PSL3.RadicalParabolicTwoSignalizers

/-- The extension hypotheses themselves force faithful action on the model. -/
theorem faithful_extension_action
    {H : Type*} [Group H] (K : Subgroup H) [K.Normal] (e : K ≃* Model)
    (hquot : IsPGroup 2 (H ⧸ K)) (hcore : pCore 2 H = ⊥) :
    Function.Injective (normalConjThrough K e) :=
  normalConjThrough_injective_of_centerless_quotient 2 K e center_eq_bot hquot hcore

/-- Transfer a full-automorphism two-signalizer theorem to a marked extension. -/
theorem twoSignalizer_eq_bot_of_automorphism_radicals
    (hAut : ∀ (point : Bool) (U : Subgroup (MulAut Model)), IsPGroup 2 U →
      (rootPlane (ZMod 5) point).map (MulAut.conj : Model →* MulAut Model) ≤
        normalizer (U : Set (MulAut Model)) → U = ⊥)
    {H : Type*} [Group H] (K : Subgroup H) [K.Normal] (e : K ≃* Model)
    (hquot : IsPGroup 2 (H ⧸ K)) (hcore : pCore 2 H = ⊥)
    (Q : Subgroup K) (hQ : IsParabolicRadical (Q.map e.toMonoidHom))
    (S : Subgroup H) (hS : IsPGroup 2 S)
    (hn : Q.map K.subtype ≤ normalizer (S : Set H)) : S = ⊥ := by
  obtain ⟨point, g, hg⟩ := hQ
  let e' := e.trans (MulAut.conj g).symm
  have hQ' : Q.map e'.toMonoidHom = rootPlane (ZMod 5) point := by
    change Q.map ((MulAut.conj g).symm.toMonoidHom.comp e.toMonoidHom) = _
    rw [← Subgroup.map_map, ← hg, Subgroup.map_map]
    have hid : (MulAut.conj g).symm.toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id Model := by
      ext x
      exact (MulAut.conj g).symm_apply_apply x
    rw [hid, Subgroup.map_id]
  apply twoSignalizer_eq_bot_of_model K e' center_eq_bot hquot hcore Q _ S hS hn
  intro U hU hnorm
  apply hAut point U hU
  simpa only [hQ'] using hnorm

/-- Transport a model recognition theorem with the specified kernel and quotient
equivalence. -/
theorem markedKernel_recognition_of_model
    (recognize : ∀ (B : Subgroup Model) (P : Subgroup B) [P.Normal],
      IsElementaryAbelian 5 P → Nat.card P = 25 →
      (B ⧸ P) ≃* SL(2, ZMod 5) → IsParabolicRadical (P.map B.subtype))
    {A : Type*} [Group A] (e : A ≃* Model)
    (B : Subgroup A) (P : Subgroup B) [P.Normal]
    (helem : IsElementaryAbelian 5 P) (hcard : Nat.card P = 25)
    (quotientEquiv : (B ⧸ P) ≃* SL(2, ZMod 5)) :
    IsParabolicRadical ((P.map B.subtype).map e.toMonoidHom) := by
  let B' := B.map e.toMonoidHom
  let eB : B ≃* B' := e.subgroupMap B
  let P' : Subgroup B' := P.map eB.toMonoidHom
  let : P'.Normal := Subgroup.Normal.map inferInstance _ eB.surjective
  have helem' : IsElementaryAbelian 5 P' := by
    let := helem
    exact IsElementaryAbelian.map eB.toMonoidHom
  have hcard' : Nat.card P' = 25 := by
    rw [show P' = P.map eB.toMonoidHom from rfl, card_map_of_injective eB.injective]
    exact hcard
  let eq : (B' ⧸ P') ≃* SL(2, ZMod 5) :=
    (QuotientGroup.congr P P' eB rfl).symm.trans quotientEquiv
  have hr := recognize B' P' helem' hcard' eq
  have hm : P'.map B'.subtype = (P.map B.subtype).map e.toMonoidHom := by
    change (P.map eB.toMonoidHom).map B'.subtype = _
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  rwa [hm] at hr

/-- Recognition through an actual model equivalence preserves the marked kernel. -/
theorem markedKernel_recognition
    {A : Type*} [Group A] (e : A ≃* Model)
    (B : Subgroup A) (P : Subgroup B) [P.Normal]
    (helem : IsElementaryAbelian 5 P) (hcard : Nat.card P = 25)
    (quotientEquiv : (B ⧸ P) ≃* SL(2, ZMod 5)) :
    IsParabolicRadical ((P.map B.subtype).map e.toMonoidHom) :=
  markedKernel_recognition_of_model markedKernel_isParabolicRadical
    e B P helem hcard quotientEquiv

/-- In an extension with trivial two-core and two-group quotient over PSL₃(5),
every two-subgroup normalized by a marked parabolic radical is trivial.
The faithful action and the full-automorphism model assertion are both proved. -/
theorem twoSignalizer_eq_bot
    {H : Type*} [Group H] (K : Subgroup H) [K.Normal] (e : K ≃* Model)
    (hquot : IsPGroup 2 (H ⧸ K)) (hcore : pCore 2 H = ⊥)
    (Q : Subgroup K) (hQ : IsParabolicRadical (Q.map e.toMonoidHom))
    (S : Subgroup H) (hS : IsPGroup 2 S)
    (hn : Q.map K.subtype ≤ normalizer (S : Set H)) : S = ⊥ :=
  twoSignalizer_eq_bot_of_automorphism_radicals automorphism_normalized_twoSubgroup_eq_bot
    K e hquot hcore Q hQ S hS hn

/-- The marked extension B/P ≃ SL₂(5), with P elementary of order 25,
already implies two-signalizer vanishing. No parabolic recognition or
automorphism vanishing hypothesis remains. -/
theorem twoSignalizer_eq_bot_of_markedKernel
    {H : Type*} [Group H] (K : Subgroup H) [K.Normal] (e : K ≃* Model)
    (hquot : IsPGroup 2 (H ⧸ K)) (hcore : pCore 2 H = ⊥)
    (B : Subgroup K) (P : Subgroup B) [P.Normal]
    (helem : IsElementaryAbelian 5 P) (hcard : Nat.card P = 25)
    (quotientEquiv : (B ⧸ P) ≃* SL(2, ZMod 5))
    (S : Subgroup H) (hS : IsPGroup 2 S)
    (hn : (P.map B.subtype).map K.subtype ≤ normalizer (S : Set H)) : S = ⊥ :=
  twoSignalizer_eq_bot K e hquot hcore (P.map B.subtype)
    (markedKernel_recognition e B P helem hcard quotientEquiv) S hS hn

/-- The same assertion for subgroups P ≤ B of K, with normality relative to B.
This form retains the source's ambient marking P.map K.subtype. -/
theorem twoSignalizer_eq_bot_of_markedSubgroup
    {H : Type*} [Group H] (K : Subgroup H) [K.Normal] (e : K ≃* Model)
    (hquot : IsPGroup 2 (H ⧸ K)) (hcore : pCore 2 H = ⊥)
    (B P : Subgroup K) (hPB : P ≤ B) [(P.subgroupOf B).Normal]
    (helem : IsElementaryAbelian 5 P) (hcard : Nat.card P = 25)
    (quotientEquiv : (B ⧸ P.subgroupOf B) ≃* SL(2, ZMod 5))
    (S : Subgroup H) (hS : IsPGroup 2 S)
    (hn : P.map K.subtype ≤ normalizer (S : Set H)) : S = ⊥ := by
  let : IsElementaryAbelian 5 P := helem
  have hcard' : Nat.card (P.subgroupOf B) = 25 :=
    (Nat.card_congr (subgroupOfEquivOfLe hPB).toEquiv).trans hcard
  apply twoSignalizer_eq_bot_of_markedKernel K e hquot hcore B (P.subgroupOf B)
    (IsElementaryAbelian.subgroupOf hPB) hcard' quotientEquiv S hS
  simpa only [map_subgroupOf_eq_of_le hPB] using hn

end Matrix.PSL3.RadicalParabolicTwoSignalizers

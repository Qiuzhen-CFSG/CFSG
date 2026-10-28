module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuTwentyThree.Envelope
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.LocalCore

/-!
# The concrete local factor for the M23 envelope

Pull back the stabilizer of the projected involution's fixed heptad, keeping
its embedding into L and G. The concrete split extension gives this factor a
nontrivial self-centralizing two-core and a surjection onto A7 with two-group
kernel. It contains L ∩ S. Centerlessness makes the projection fixed by N_S(L);
an automorphism-invariance theorem for the model stabilizer then gives the
normalization required for the S-orbit construction.

The automorphism-invariance premise is explicit. These are local-factor
results, not the construction of the full-S envelope.

Source: Aschbacher–Smith, 1.1.5(3)(f) and 2.3.9(7)(f), printed pp.502 and
525–526, combined manuscript of 1 March 2004.
-/

@[expose] public section

open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M23Geometry
open scoped Pointwise
namespace CFSG.Quasithin.Chapter2.ComponentRefinement
variable {G : Type*} [Group G]

noncomputable def mathieuTwentyThreeHeptadSubgroup {L : Subgroup G}
    (e : L ≃* M23) (t : L) : Subgroup G :=
  ((MulAction.stabilizer M23 (fixedHeptad (e t))).comap e.toMonoidHom).map L.subtype

theorem mathieuTwentyThreeHeptadSubgroup_le {L : Subgroup G}
    (e : L ≃* M23) (t : L) : mathieuTwentyThreeHeptadSubgroup e t ≤ L := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

noncomputable def mathieuTwentyThreeHeptadSubgroupEquiv {L : Subgroup G}
    (e : L ≃* M23) (t : L) :
    mathieuTwentyThreeHeptadSubgroup e t ≃* MulAction.stabilizer M23 (fixedHeptad (e t)) := by
  let K := MulAction.stabilizer M23 (fixedHeptad (e t))
  let P := K.comap e.toMonoidHom
  have he : P.map e.toMonoidHom = K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨e.symm x, by change e (e.symm x) ∈ K; simpa using hx, e.apply_symm_apply x⟩
  exact (P.equivMapOfInjective L.subtype Subtype.val_injective).symm.trans
    ((e.subgroupMap P).trans (MulEquiv.subgroupCongr he))

theorem mathieuTwentyThreeHeptadSubgroup_local_structure {L : Subgroup G}
    (e : L ≃* M23) {t : L} (ht2 : orderOf t = 2) :
    pCore 2 (mathieuTwentyThreeHeptadSubgroup e t) ≠ ⊥ ∧
      centralizer (pCore 2 (mathieuTwentyThreeHeptadSubgroup e t) :
        Set (mathieuTwentyThreeHeptadSubgroup e t)) ≤
        pCore 2 (mathieuTwentyThreeHeptadSubgroup e t) ∧
      ∃ f : mathieuTwentyThreeHeptadSubgroup e t →* alternatingGroup (Fin 7),
        Function.Surjective f ∧ IsPGroup 2 f.ker := by
  apply heptad_stabilizer_local_structure
    (fixedHeptad_mem ((e.orderOf_eq t).trans ht2))
    (mathieuTwentyThreeHeptadSubgroupEquiv e t)

theorem mathieuTwentyThreeHeptadSubgroup_contains_component_sylow
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (e : L ≃* M23) {t : L}
    (ht : IsConjugationProjection L z t) :
    L ⊓ (S : Subgroup H).map H.subtype ≤ mathieuTwentyThreeHeptadSubgroup e t := by
  rintro x ⟨hxL, hxS⟩
  refine ⟨⟨x, hxL⟩, ?_, rfl⟩
  change e ⟨x, hxL⟩ ∈ MulAction.stabilizer M23 (fixedHeptad (e t))
  apply centralizer_le_fixedHeptad_stabilizer
  apply mem_centralizer_singleton_iff.mpr
  have he := ht ⟨x, hxL⟩
  change z * x * z⁻¹ = (t : G) * x * (t : G)⁻¹ at he
  rw [← h.central x hxS, mul_inv_cancel_right] at he
  have hc : (⟨x, hxL⟩ : L) * t = t * ⟨x, hxL⟩ :=
    Subtype.ext (mul_inv_eq_iff_eq_mul.mp he.symm).symm
  simpa only [map_mul] using congrArg e hc
theorem mathieuTwentyThree_center_eq_bot {L : Subgroup G} (e : L ≃* M23) : center L = ⊥ := by
  apply bot_unique
  intro x hx
  have he : e x ∈ center M23 := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨y, rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hx y)
  rw [m23_center_eq_bot, mem_bot] at he
  exact mem_bot.mpr (e.injective (he.trans (map_one e).symm))

theorem LocalSetup.normalizer_fixes_projection {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (hZ : center L = ⊥) {t : L}
    (ht : IsConjugationProjection L z t) {s : G}
    (hs : s ∈ (S : Subgroup H).map H.subtype) (hsN : s ∈ normalizer (L : Set G)) :
    L.normalizerMonoidHom ⟨s, hsN⟩ t = t := by
  let a := L.normalizerMonoidHom ⟨s, hsN⟩
  have hz : L.normalizerMonoidHom ⟨z, h.normalizes⟩ = MulAut.conj t := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    exact ht x
  have hc : Commute a (MulAut.conj t) := by
    rw [← hz]
    apply Commute.map _ L.normalizerMonoidHom
    exact Subtype.ext (h.central s hs)
  apply conj_injective_of_center_eq_bot hZ
  apply MulEquiv.ext
  intro x
  have he := congrArg (fun b : MulAut L => b (a.symm x)) hc.eq
  simpa only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply] using he

/-- An automorphism-invariance theorem for the concrete heptad stabilizer
transports to normalization by the actual normalizer of the component in S. -/
theorem mathieuTwentyThreeHeptadSubgroup_normalized_of_aut_invariant
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (e : L ≃* M23) {t : L}
    (ht : IsConjugationProjection L z t)
    (hinv : ∀ α : MulAut M23, α (e t) = e t →
      (MulAction.stabilizer M23 (fixedHeptad (e t))).map α.toMonoidHom =
        MulAction.stabilizer M23 (fixedHeptad (e t))) :
    (S : Subgroup H).map H.subtype ⊓ normalizer (L : Set G) ≤
      normalizer (mathieuTwentyThreeHeptadSubgroup e t : Set G) := by
  rintro s ⟨hs, hsN⟩
  let a : MulAut L := L.normalizerMonoidHom ⟨s, hsN⟩
  let b : MulAut M23 := e.symm.trans (a.trans e)
  have hat : a t = t := h.normalizer_fixes_projection
    (mathieuTwentyThree_center_eq_bot e) ht hs hsN
  have hbt : b (e t) = e t := by simp [b, hat]
  let K := MulAction.stabilizer M23 (fixedHeptad (e t))
  let P := K.comap e.toMonoidHom
  have hK : K.map b.toMonoidHom = K := hinv b hbt
  have hP : P.map a.toMonoidHom = P := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change e (a x) ∈ K
      have hb : b (e x) ∈ K.map b.toMonoidHom := ⟨e x, hx, rfl⟩
      rw [hK] at hb
      simpa [b] using hb
    · intro hy
      have hm : e y ∈ K.map b.toMonoidHom := hK.symm ▸ hy
      obtain ⟨v, hv, he⟩ := hm
      refine ⟨e.symm v, ?_, ?_⟩
      · change e (e.symm v) ∈ K
        simpa using hv
      · apply e.injective
        exact he
  have hcompat : (MulAut.conj s).toMonoidHom.comp L.subtype =
      L.subtype.comp a.toMonoidHom := by
    ext x
    rfl
  rw [mem_normalizer_iff_map_conj_eq]
  change (P.map L.subtype).map (MulAut.conj s).toMonoidHom = P.map L.subtype
  rw [map_map, hcompat, ← map_map, hP]

end CFSG.Quasithin.Chapter2.ComponentRefinement

end

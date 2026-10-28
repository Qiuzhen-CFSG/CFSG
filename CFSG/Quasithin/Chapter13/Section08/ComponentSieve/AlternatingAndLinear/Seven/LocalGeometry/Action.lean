module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Basic
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.ConjugateObstruction
public import Theory.Alternating.Aut
public import Theory.GroupTheory.GeneralizedFitting.SimpleTwoQuotient
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# The faithful seven-point action in the A₇ branch

Conjugation on a relatively normal component, transport through its actual
quotient equivalence, and S₇ ≃ Aut(A₇) construct the action of H/O₂(H).
The two-group supplement in H = KT makes the quotient by K* a two-group.
Consequently the centralizer of K* is a normal two-subgroup and is trivial.
The restriction to K is computed on representatives, so this action uses
the specified equivalence K/O₂(K) ≃ A₇, not an unrelated family label.

The component, relative normality, and H = KT inputs are precisely the
parts of 13.8.16(1) and 13.8.21(3) used here. The construction applies to
any original H for which these earlier source conclusions are supplied;
it imposes no minimality or additional H = KL₁T hypothesis.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.8.24, printed p.958, and 13.8.16/21, printed pp.952/955–957
(combined manuscript, 1 March 2004).
-/

@[expose] public section

open Subgroup Equiv
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.LocalGeometry
noncomputable section

/-- The inverse of this equivalence realizes automorphisms on seven points. -/
def symmetricAutEquiv : S7 ≃* MulAut (alternatingGroup (Fin 7)) :=
  MulEquiv.ofBijective MulAut.conjNormal
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by decide) (by decide))

variable {J : Type*} [Group J]

/-- The permutation action obtained from conjugation on the actual normal subgroup. -/
def permutationAction (D : Subgroup J) [D.Normal]
    (e : D ≃* alternatingGroup (Fin 7)) : J →* S7 :=
  symmetricAutEquiv.symm.toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := D)))

/-- On the normal subgroup the action is the supplied alternating inclusion. -/
theorem permutationAction_on_subgroup (D : Subgroup J) [D.Normal]
    (e : D ≃* alternatingGroup (Fin 7)) (x : D) :
    permutationAction D e x = e x := by
  apply symmetricAutEquiv.injective
  change symmetricAutEquiv (symmetricAutEquiv.symm _) = MulAut.conjNormal (e x).val
  rw [symmetricAutEquiv.apply_symm_apply]
  apply MulEquiv.ext
  intro y
  apply Subtype.ext
  change (e (x * e.symm y * x⁻¹)).val = (e x).val * y.val * (e x).val⁻¹
  simp

/-- The image of the normal subgroup is the whole alternating subgroup. -/
theorem permutationAction_map (D : Subgroup J) [D.Normal]
    (e : D ≃* alternatingGroup (Fin 7)) :
    D.map (permutationAction D e) = alternatingGroup (Fin 7) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [show permutationAction D e x = (e ⟨x, hx⟩).val from
      permutationAction_on_subgroup D e ⟨x, hx⟩]
    exact (e ⟨x, hx⟩).property
  · intro x hx
    obtain ⟨k, hk⟩ := e.surjective ⟨x, hx⟩
    exact ⟨k, k.property, (permutationAction_on_subgroup D e k).trans (congrArg Subtype.val hk)⟩

/-- The only kernel is the actual centralizer of the normal subgroup. -/
theorem permutationAction_ker (D : Subgroup J) [D.Normal]
    (e : D ≃* alternatingGroup (Fin 7)) :
    (permutationAction D e).ker = centralizer (D : Set J) := by
  ext x
  have hi : Function.Injective
      (symmetricAutEquiv.symm.toMonoidHom.comp (MulAut.congr e).toMonoidHom) :=
    symmetricAutEquiv.symm.injective.comp (MulAut.congr e).injective
  change ((symmetricAutEquiv.symm.toMonoidHom.comp (MulAut.congr e).toMonoidHom)
      (MulAut.conjNormal (H := D) x) = 1) ↔ _
  rw [map_eq_one_iff _ hi]
  constructor
  · intro h y hy
    have hh := congrArg (fun f : MulAut D => (f ⟨y, hy⟩).val) h
    change x * y * x⁻¹ = y at hh
    exact ((mul_inv_eq_iff_eq_mul).mp hh).symm
  · intro h
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    change x * y.val * x⁻¹ = y.val
    exact (mul_inv_eq_iff_eq_mul).mpr ((mem_centralizer_iff.mp h) y y.property).symm

/-- A two-group supplement surjects onto the quotient by the normal subgroup. -/
theorem quotient_two_of_sup (D S : Subgroup J) [D.Normal]
    (hS : IsPGroup 2 S) (hsup : D ⊔ S = ⊤) : IsPGroup 2 (J ⧸ D) := by
  let q := QuotientGroup.mk' D
  have hm : S.map q = ⊤ := by
    have h := congrArg (map q) hsup
    rw [Subgroup.map_sup, map_top_of_surjective _ (QuotientGroup.mk'_surjective D)] at h
    have hd : D.map q = ⊥ := by
      apply (Subgroup.map_eq_bot_iff _).mpr
      rw [QuotientGroup.ker_mk']
    simpa only [hd, bot_sup_eq] using h
  exact (hS.map q).of_surjective (S.map q).subtype (by
    intro x
    exact ⟨⟨x, hm.symm ▸ mem_top x⟩, rfl⟩)

/-- The trivial two-core kills the centralizer and makes the action faithful. -/
theorem permutationAction_injective (D : Subgroup J) [D.Normal]
    (e : D ≃* alternatingGroup (Fin 7)) (S : Subgroup J)
    (hS : IsPGroup 2 S) (hsup : D ⊔ S = ⊤) (hcore : pCore 2 J = ⊥) :
    Function.Injective (permutationAction D e) := by
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by norm_num)
  let : IsSimpleGroup D := e.isSimpleGroup
  have ha : ¬ IsMulCommutative D := by
    intro h
    let := h
    have hc : IsMulCommutative (alternatingGroup (Fin 7)) :=
      ⟨⟨fun x y => e.symm.injective (by simp only [map_mul]; exact mul_comm _ _)⟩⟩
    have hh := alternatingGroup.isMulCommutative_iff_card_le_three.mp hc
    norm_num at hh
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [permutationAction_ker]
  exact Theory.GroupTheory.centralizer_eq_bot_of_simple_two_quotient D ha
    (quotient_two_of_sup D S hS hsup) hcore

variable {G : Type*} [Group G] [Finite G]

/-- Compare K/O₂(K) with K* before transporting to the concrete A₇. -/
def starAlternatingEquiv (H K : Subgroup G) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) :
    Source.starImage H K ≃* alternatingGroup (Fin 7) :=
  (Components.componentStarEquiv H K hKH hK).symm.trans e

omit [Finite G] in
/-- Images preserve joins for subgroups actually contained in H. -/
theorem starImage_sup (H K T : Subgroup G) (hK : K ≤ H) (hT : T ≤ H) :
    Source.starImage H (K ⊔ T) = Source.starImage H K ⊔ Source.starImage H T := by
  simp only [Source.starImage, subgroupOf_sup hK hT, Subgroup.map_sup]

omit [Finite G] in
/-- The image of H in its own two-core quotient is the whole quotient. -/
theorem starImage_self (H : Subgroup G) : Source.starImage H H = ⊤ := by
  simp only [Source.starImage, subgroupOf_self,
    map_top_of_surjective _ (QuotientGroup.mk'_surjective (pCore 2 H))]

omit [Finite G] in
/-- Normality is required only inside H and passes to its quotient. -/
theorem starImage_normal (H K : Subgroup G) (hKn : (K.subgroupOf H).Normal) :
    (Source.starImage H K).Normal := by
  let := hKn
  exact Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)

/-- Construct the compatible faithful action from the earlier component conclusions.
The last clause certifies its value on every representative from K. -/
theorem source_action_exists (H K T : Subgroup G) (hKH : K ≤ H) (hTH : T ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (hKn : (K.subgroupOf H).Normal)
    (hT : IsPGroup 2 T) (hKT : K ⊔ T = H)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) :
    ∃ φ : Source.Hstar H →* S7, Function.Injective φ ∧
      (Source.starImage H K).map φ = alternatingGroup (Fin 7) ∧
      ∀ k : K, φ (QuotientGroup.mk' (pCore 2 H) ⟨k, hKH k.property⟩) =
        (e (QuotientGroup.mk' (pCore 2 K) k)).val := by
  let := starImage_normal H K hKn
  let a := starAlternatingEquiv H K hKH hK e
  let φ := permutationAction (Source.starImage H K) a
  have hS : IsPGroup 2 (Source.starImage H T) :=
    (hT.of_equiv (subgroupOfEquivOfLe hTH).symm).map _
  have hsup : Source.starImage H K ⊔ Source.starImage H T = ⊤ := by
    rw [← starImage_sup H K T hKH hTH, hKT, starImage_self]
  refine ⟨φ, permutationAction_injective _ a _ hS hsup
    (Subgroup.pCore_quotient_pCore_eq_bot 2), permutationAction_map _ a, ?_⟩
  intro k
  rw [← Components.componentStarEquiv_mk H K hKH hK k]
  rw [permutationAction_on_subgroup]
  simp only [a, starAlternatingEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
end
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.LocalGeometry

end

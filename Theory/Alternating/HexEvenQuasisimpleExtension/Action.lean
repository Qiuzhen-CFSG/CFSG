module

public import Theory.Alternating.HexEvenQuasisimpleExtension.SylowAction
public import Theory.GroupTheory.GeneralizedFitting.InnerAutomorphisms

/-!
# The literal symmetric quotient of a natural A₆ extension

A natural central-quotient action lifts uniquely through the faithful
conjugation map S₆ → Aut(A₆). Self-centralization of F*(G) identifies its
kernel with the embedded component center and the inverse image of A₆
with the original perfect component. A proper extension is surjective,
and its derived subgroup is that component. The split Sylow producer in
`SylowAction` supplies the naturality hypothesis used here.

Source: GLS3 5.2.1, 5.2.7; Aschbacher–Smith F.6.18(8), printed p.310.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Equiv GLS3.Chapter5
namespace Theory.HexEvenExtension
variable {G : Type*} [Group G] [Finite G]

/-- Conjugation identifies S₆ with its actual natural automorphism image. -/
@[expose] def naturalEquiv : Perm (Fin 6) ≃* naturalAlternatingAutomorphismSubgroup :=
  MonoidHom.ofInjective (GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6 (by decide))

/-- The unique symmetric lift of the actual conjugation action. -/
@[expose] def action (K : Subgroup G) [K.Normal]
    (e : K ⧸ center K ≃* alternatingGroup (Fin 6))
    (hn : ∀ g : G, quotientAction K e g ∈ naturalAlternatingAutomorphismSubgroup) :
    G →* Perm (Fin 6) :=
  naturalEquiv.symm.toMonoidHom.comp
    ((quotientAction K e).codRestrict naturalAlternatingAutomorphismSubgroup hn)

omit [Finite G] in
lemma conj_action (K : Subgroup G) [K.Normal]
    (e : K ⧸ center K ≃* alternatingGroup (Fin 6))
    (hn : ∀ g : G, quotientAction K e g ∈ naturalAlternatingAutomorphismSubgroup) (g : G) :
    MulAut.conjNormal (action K e hn g) = quotientAction K e g := by
  exact congrArg Subtype.val (naturalEquiv.apply_symm_apply
    ⟨quotientAction K e g, hn g⟩)

omit [Finite G] in
/-- Component elements have their literal alternating quotient images. -/
lemma action_on_subgroup (K : Subgroup G) [K.Normal]
    (e : K ⧸ center K ≃* alternatingGroup (Fin 6))
    (hn : ∀ g : G, quotientAction K e g ∈ naturalAlternatingAutomorphismSubgroup) (k : K) :
    action K e hn k = (e (QuotientGroup.mk' (center K) k) : Perm (Fin 6)) := by
  apply GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6 (by decide)
  rw [conj_action]
  change MulAut.centralQuotientAction e (MulAut.conjNormal (k : G)) = _
  rw [MulAut.conjNormal_val, MulAut.centralQuotientAction_conj, MulAut.conjNormal_val]

/-- Self-centralization detects the original component in the quotient. -/
lemma action_preimage (K : Subgroup G) [K.Normal] [Group.IsPerfect K]
    (hF : generalizedFitting G = K)
    (e : K ⧸ center K ≃* alternatingGroup (Fin 6))
    (hn : ∀ g : G, quotientAction K e g ∈ naturalAlternatingAutomorphismSubgroup) :
    (alternatingGroup (Fin 6)).comap (action K e hn) = K := by
  have hC : centralizer (K : Set G) ≤ K := hF ▸ centralizer_generalizedFitting_le G
  ext g
  constructor
  · intro hg
    let a : alternatingGroup (Fin 6) := ⟨action K e hn g, hg⟩
    have ha : MulAut.centralQuotientAction e (MulAut.conjNormal g : MulAut K) = MulAut.conj a :=
      (conj_action K e hn g).symm.trans (MulAut.conjNormal_val (h := a))
    obtain ⟨k, hk⟩ := (MulAut.centralQuotientAction_inner_iff e _).mp ⟨a, ha⟩
    have hi : g ∈ (MulAut.innerSubgroup K).comap MulAut.conjNormal := ⟨k, hk.symm⟩
    rw [MulAut.conjNormal_comap_innerSubgroup] at hi
    exact (sup_le le_rfl hC) hi
  · intro hg
    change action K e hn (⟨g, hg⟩ : K) ∈ alternatingGroup (Fin 6)
    rw [action_on_subgroup]
    exact (e (QuotientGroup.mk' (center K) ⟨g, hg⟩)).property

/-- The action kernel is exactly the center of the component inside G. -/
lemma action_ker (K : Subgroup G) [K.Normal] [Group.IsPerfect K]
    (hF : generalizedFitting G = K)
    (e : K ⧸ center K ≃* alternatingGroup (Fin 6))
    (hn : ∀ g : G, quotientAction K e g ∈ naturalAlternatingAutomorphismSubgroup) :
    (action K e hn).ker = (center K).map K.subtype := by
  have hC : centralizer (K : Set G) ≤ K := hF ▸ centralizer_generalizedFitting_le G
  have he : (action K e hn).ker = (quotientAction K e).ker := by
    ext g
    change action K e hn g = 1 ↔ quotientAction K e g = 1
    rw [← conj_action K e hn g, ← map_one (MulAut.conjNormal : Perm (Fin 6) →* _)]
    exact (GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6 (by decide)).eq_iff.symm
  rw [he, quotientAction,
    MonoidHom.ker_comp_of_injective _ _ (MulAut.centralQuotientAction_injective e),
    MulAut.conjNormal_ker_eq_centralizer]
  ext g
  constructor
  · intro hg
    refine ⟨⟨g, hC hg⟩, ?_, rfl⟩
    change (⟨g, hC hg⟩ : K) ∈ center K
    rw [mem_center_iff]
    intro k
    exact Subtype.ext (hg k k.property)
  · rintro ⟨k, hk, rfl⟩ l hl
    exact congrArg Subtype.val (mem_center_iff.mp hk ⟨l, hl⟩)

/-- A proper extension has the full symmetric group as its image. -/
lemma action_surjective (K : Subgroup G) [K.Normal] [Group.IsPerfect K]
    (hF : generalizedFitting G = K) (hne : K ≠ ⊤)
    (e : K ⧸ center K ≃* alternatingGroup (Fin 6))
    (hn : ∀ g : G, quotientAction K e g ∈ naturalAlternatingAutomorphismSubgroup) :
    Function.Surjective (action K e hn) := by
  let f := action K e hn
  have heven : ∀ a : alternatingGroup (Fin 6), ∃ k : K, f k = a := by
    intro a
    obtain ⟨q, hq⟩ := e.surjective a
    obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective (center K) q
    exact ⟨k, (action_on_subgroup K e hn k).trans (congrArg Subtype.val (by rw [hk, hq]))⟩
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ K := by
    by_contra! h
    exact hne (top_unique (fun g _ => h g))
  have hodd : Perm.sign (f g) = -1 := by
    rcases Int.units_eq_one_or (Perm.sign (f g)) with he | he
    · exfalso
      apply hg
      rw [← action_preimage K hF e hn]
      exact he
    · exact he
  intro σ
  rcases Int.units_eq_one_or (Perm.sign σ) with hs | hs
  · obtain ⟨k, hk⟩ := heven ⟨σ, hs⟩
    exact ⟨k, hk⟩
  · have hpar : σ * (f g)⁻¹ ∈ alternatingGroup (Fin 6) := by
      change Perm.sign (σ * (f g)⁻¹) = 1
      rw [map_mul, map_inv, hs, hodd]
      decide
    obtain ⟨k, hk⟩ := heven ⟨σ * (f g)⁻¹, hpar⟩
    refine ⟨k * g, ?_⟩
    rw [map_mul, hk, inv_mul_cancel_right]

/-- The original perfect component is the full ambient derived subgroup. -/
lemma derived_eq (K : Subgroup G) [K.Normal] [Group.IsPerfect K]
    (hF : generalizedFitting G = K)
    (e : K ⧸ center K ≃* alternatingGroup (Fin 6))
    (hn : ∀ g : G, quotientAction K e g ∈ naturalAlternatingAutomorphismSubgroup) :
    commutator G = K := by
  have hker : (Perm.sign.comp (action K e hn)).ker = K := action_preimage K hF e hn
  apply le_antisymm
  · rw [← hker]
    exact Abelianization.commutator_subset_ker _
  · rw [← Subgroup.commutator_eq_self (H := K)]
    exact Subgroup.commutator_mono le_top le_top

end Theory.HexEvenExtension

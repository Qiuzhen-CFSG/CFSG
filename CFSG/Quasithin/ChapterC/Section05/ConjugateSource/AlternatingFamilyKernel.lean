module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingCommutator
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.ElementaryAbelian.Join

/-!
# Elementary cores and their opposite in the A₅ branch

The common commutator plane identifies both mutual fixed subgroups. Thus
the source centralizer D is disjoint from both U and Uˣ. Once Φ(D)=1,
the two products UD and UˣD are elementary of the same order, and D
centralizes S. These are the literal candidates for the four-member
maximum elementary family, not assumed enumeration data.

Source: Aschbacher–Smith, C.5.6(5),(7), printed pp.157–159.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

theorem AlternatingPairSetup.conjugate_fixed_eq_intersection
    (h : AlternatingPairSetup R K L) (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let U := sourceModule K
    let V := U.map (MulAut.conj x⁻¹).toMonoidHom
    V ⊓ centralizer (U : Set G) = U ⊓ V := by
  let U := sourceModule K
  let V := U.map (MulAut.conj x⁻¹).toMonoidHom
  have hU : IsElementaryAbelian 2 U := by
    let := h.block.2.1.elementary
    exact IsElementaryAbelian.map K.subtype
  let := hU
  have hVcard : Nat.card V = 16 := by
    rw [card_map_of_injective (MulAut.conj x⁻¹).injective]
    exact h.module_card
  have hi := relIndex_mul_relIndex (⊥ : Subgroup G)
    (V ⊓ centralizer (U : Set G)) V bot_le inf_le_left
  rw [relIndex_bot_left, relIndex_bot_left, inf_relIndex_left,
    h.conjugate_action_index x hx hnc, hVcard] at hi
  have hX : Nat.card (V ⊓ centralizer (U : Set G) : Subgroup G) = 4 := by omega
  have hc := h.commutator_eq_fixed x hx hnc
  have hUV : Nat.card (U ⊓ V : Subgroup G) = 4 := by
    rw [← hc.2, hc.1]
    exact h.conjugate_fixed_card x hx hnc
  change V ⊓ centralizer (U : Set G) = U ⊓ V
  symm
  exact eq_of_le_of_card_ge (le_inf inf_le_right (inf_le_left.trans (le_centralizer U)))
    (by rw [hX, hUV])

theorem AlternatingPairSetup.centralizer_disjoint_conjugate_module
    (h : AlternatingPairSetup R K L) (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    Disjoint (ChapterB.baumann R ⊓ centralizer (K : Set G))
      ((sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom) := by
  let U := sourceModule K
  let D := ChapterB.baumann R ⊓ centralizer (K : Set G)
  let V := U.map (MulAut.conj x⁻¹).toMonoidHom
  have hd : Disjoint U D := alternatingModule_disjoint_of_commuting K D h.block inf_le_right
  apply disjoint_iff_inf_le.mpr
  intro v hv
  have hh : v ∈ V ⊓ centralizer (U : Set G) :=
    ⟨hv.2, (inf_le_right.trans (centralizer_le (map_subtype_le _))) hv.1⟩
  have he : V ⊓ centralizer (U : Set G) = U ⊓ V := h.conjugate_fixed_eq_intersection x hx hnc
  rw [he] at hh
  exact hd.le_bot ⟨hh.1, hv.1⟩

theorem AlternatingPairSetup.elementary_factor_pair
    (h : AlternatingPairSetup R K L) (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G))
    (hphi : let D := ChapterB.baumann R ⊓ centralizer (K : Set G)
      (frattini D).map D.subtype = ⊥) :
    let S := ChapterB.baumann R
    let U := sourceModule K
    let V := U.map (MulAut.conj x⁻¹).toMonoidHom
    let Q := (K ⊔ S).pCoreIn 2
    let D := S ⊓ centralizer (K : Set G)
    IsElementaryAbelian 2 Q ∧ IsElementaryAbelian 2 (V ⊔ D : Subgroup G) ∧
      Nat.card (V ⊔ D : Subgroup G) = Nat.card Q ∧ D ≤ centralizer (S : Set G) := by
  let S := ChapterB.baumann R
  let U := sourceModule K
  let V := U.map (MulAut.conj x⁻¹).toMonoidHom
  let Q := (K ⊔ S).pCoreIn 2
  let D := S ⊓ centralizer (K : Set G)
  have hprod : Q = U ⊔ D := h.product
  have hcore : Q = S ⊓ centralizer (U : Set G) := h.core
  have hDV : D ≤ centralizer (V : Set G) := h.centralizer_centralizes_conjugate x hx hnc
  have hDU : D ≤ centralizer (U : Set G) :=
    inf_le_right.trans (centralizer_le (map_subtype_le _))
  have hDtwo : IsPGroup 2 D := h.twoGroup.to_le (inf_le_left.trans inf_le_left)
  let : Fact (IsPGroup 2 D) := ⟨hDtwo⟩
  have hf : frattini D = ⊥ := (map_injective D.subtype_injective)
    (hphi.trans (map_bot D.subtype).symm)
  let : IsElementaryAbelian 2 D := (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hf
  let : IsElementaryAbelian 2 U := by
    let := h.block.2.1.elementary
    exact IsElementaryAbelian.map K.subtype
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map (MulAut.conj x⁻¹).toMonoidHom
  have hQ : IsElementaryAbelian 2 Q := hprod ▸ IsElementaryAbelian.sup_of_le_centralizer hDU
  have hW : IsElementaryAbelian 2 (V ⊔ D : Subgroup G) := IsElementaryAbelian.sup_of_le_centralizer hDV
  have hdisj : Disjoint U D := alternatingModule_disjoint_of_commuting K D h.block inf_le_right
  have hdisj' : Disjoint V D := (h.centralizer_disjoint_conjugate_module x hx hnc).symm
  have hcard (A : Subgroup G) (hc : D ≤ centralizer (A : Set G)) (hd : Disjoint A D) :
      Nat.card (A ⊔ D : Subgroup G) = Nat.card A * Nat.card D := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes A D
      (hc.trans (Subgroup.centralizer_le_normalizer _))
    rw [hd.eq_bot] at hh
    simp only [Nat.card_unique, one_mul] at hh
    exact hh.symm
  have hcV : Nat.card V = Nat.card U := card_map_of_injective (MulAut.conj x⁻¹).injective
  have hc : Nat.card (V ⊔ D : Subgroup G) = Nat.card Q := by
    rw [hprod, hcard V hDV hdisj', hcard U hDU hdisj, hcV]
  refine ⟨hQ, hW, hc, ?_⟩
  let := hQ
  apply le_centralizer_iff.mpr
  have hQS : S ≤ V ⊔ Q := (h.first_factorization x hx hnc).le
  apply hQS.trans
  apply sup_le (le_centralizer_iff.mp hDV)
  apply le_centralizer_iff.mp
  exact (hprod ▸ le_sup_right).trans (le_centralizer Q)
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource

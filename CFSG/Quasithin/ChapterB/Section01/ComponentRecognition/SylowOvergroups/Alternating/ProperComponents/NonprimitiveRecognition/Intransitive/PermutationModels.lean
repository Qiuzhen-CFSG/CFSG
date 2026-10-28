module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.Alternating.ProperComponents.NonprimitiveRecognition.OrbitImages

/-!
# Component recognition in permutation images

A perfect component has trivial sign, so it remains a component in the
alternating intersection. Transporting that intersection to the standard
finite carrier makes the smaller-degree induction hypothesis applicable.
At degree seven, a symmetric Sylow subgroup supplies a transposition;
prime-degree transitivity and Jordan's theorem force the whole symmetric
group, whose component is the alternating group. This prevents a smaller
PSL₃(2) exception from propagating to a larger ambient degree.

The orbit-Sylow hypotheses are supplied by `Intransitive.OrbitSylows`, and
`Intransitive` applies this result to the literal orbit images.

Source: Aschbacher–Smith B.1.13, printed p.74 (PDF p.85), final paragraph.
-/

public section
open Subgroup Equiv MulAction Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups

private theorem all_models_transport {α : Type*} [Fintype α] [DecidableEq α]
    (h : AlternatingAllSylowComponentModels (Fintype.card α))
    (S : Sylow 2 (alternatingGroup α)) (X : Subgroup (alternatingGroup α))
    (hS : (S : Subgroup _) ≤ X) (D : Subgroup X) (hD : IsComponent X D) :
    AlternatingSubgroupModels (Fintype.card α) D := by
  let e := (Fintype.equivFin α).altCongrHom
  let eX := e.subgroupMap X
  let T : Sylow 2 (alternatingGroup (Fin (Fintype.card α))) :=
    S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hs : (T : Subgroup (alternatingGroup (Fin (Fintype.card α)))) ≤
      X.map e.toMonoidHom := by
    simpa [T] using map_mono (f := e.toMonoidHom) hS
  exact (h T (X.map e.toMonoidHom) hs
    (D.map eX.toMonoidHom) (hD.map_equiv eX)).of_mulEquiv (eX.subgroupMap D)

private theorem component_sign {α : Type*} [Fintype α] [DecidableEq α]
    (R : Subgroup (Perm α)) (D : Subgroup R) (hD : IsComponent R D) :
    D ≤ (alternatingGroup α).subgroupOf R := by
  let := hD.2
  let f := Perm.sign.comp (R.subtype.comp D.subtype)
  intro d hd
  exact Abelianization.commutator_subset_ker f
    (Group.IsPerfect.mem_commutator (g := (⟨d, hd⟩ : D)))

private def intersectionEquiv {G : Type*} [Group G] (A B : Subgroup G) :
    A.subgroupOf B ≃* B.subgroupOf A where
  toFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem component_models_of_alternating_sylow {α : Type*}
    [Fintype α] [DecidableEq α]
    (h : AlternatingAllSylowComponentModels (Fintype.card α))
    (R : Subgroup (Perm α))
    (S : Sylow 2 (alternatingGroup α))
    (hS : (S : Subgroup (alternatingGroup α)) ≤ R.subgroupOf (alternatingGroup α))
    (D : Subgroup R) (hD : IsComponent R D) :
    AlternatingSubgroupModels (Fintype.card α) D := by
  let A := (alternatingGroup α).subgroupOf R
  have hd : D ≤ A := component_sign R D hD
  let e := intersectionEquiv (alternatingGroup α) R
  let d := (subgroupOfEquivOfLe hd).symm.trans (e.subgroupMap (D.subgroupOf A))
  exact (all_models_transport h S (R.subgroupOf _) hS _
    ((hD.subgroupOf hd).map_equiv e)).of_mulEquiv d

private theorem sylow_contains_swap {α : Type*} [Fintype α] [DecidableEq α]
    [Nontrivial α] (S : Sylow 2 (Perm α)) : ∃ t ∈ S, Perm.IsSwap t := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  have htP : IsPGroup 2 (zpowers (swap a b)) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one (show (swap a b) ^ 2 = 1 by simp [pow_two])
  obtain ⟨Q, hQ⟩ := htP.exists_le_sylow
  obtain ⟨g, hg⟩ := exists_smul_eq (Perm α) Q S
  let u : ↥(g • Q : Sylow 2 (Perm α)) := Q.equivSMul g ⟨swap a b, hQ (mem_zpowers _)⟩
  refine ⟨u, hg ▸ u.property, ?_⟩
  apply Perm.card_support_eq_two.mp
  change (g * swap a b * g⁻¹).support.card = 2
  rw [Perm.card_support_conj, Perm.card_support_swap hab]

private theorem component_equiv_alternating_of_le {α : Type*} [Fintype α] [DecidableEq α]
    (hα : 5 ≤ Nat.card α) (R : Subgroup (Perm α)) (hR : alternatingGroup α ≤ R)
    (D : Subgroup R) (hD : IsComponent R D) : Nonempty (D ≃* alternatingGroup α) := by
  let A := (alternatingGroup α).subgroupOf R
  have hd : D ≤ A := component_sign R D hD
  let e : A ≃* alternatingGroup α := subgroupOfEquivOfLe hR
  let : IsQuasisimple (alternatingGroup α) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top hα⟩
    simple := by
      let : IsSimpleGroup (alternatingGroup α) := alternatingGroup.isSimpleGroup hα
      exact ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by omega))).trans
          QuotientGroup.quotientBot).isSimpleGroup }
  let : IsQuasisimple A := IsQuasisimple.of_mulEquiv e.symm
  have ht : IsComponent A ⊤ :=
    ⟨IsSubnormal.top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩
  have he := (hD.subgroupOf hd).eq_of_le ht le_top
  exact ⟨(subgroupOfEquivOfLe hd).symm.trans
    ((MulEquiv.subgroupCongr he).trans (topEquiv.trans e))⟩

/-- Components of a transitive permutation group containing an alternating Sylow
subgroup satisfy degree induction. At degree seven the additional symmetric
Sylow subgroup forces the full symmetric group, excluding the exceptional model. -/
theorem alternating_permutation_component_models_of_induction {α : Type*}
    [Fintype α] [DecidableEq α]
    {m : ℕ} (hn : Fintype.card α < m)
    (ih : ∀ n < m, AlternatingAllSylowComponentModels n)
    (R : Subgroup (Perm α)) (ht : IsPretransitive R α)
    (hA : ∃ S : Sylow 2 (alternatingGroup α),
      (S : Subgroup (alternatingGroup α)) ≤ R.subgroupOf (alternatingGroup α))
    (h7 : Nat.card α = 7 → ∃ S : Sylow 2 (Perm α), (S : Subgroup (Perm α)) ≤ R)
    (D : Subgroup R) (hD : IsComponent R D) : AlternatingSubgroupModels m D := by
  by_cases hseven : Nat.card α = 7
  · let : Nontrivial α := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨S, hS⟩ := h7 hseven
    obtain ⟨t, htS, hswap⟩ := sylow_contains_swap S
    let : IsPretransitive R α := ht
    have hp : IsPreprimitive R α := IsPreprimitive.of_prime_card (hseven ▸ (by decide))
    have hR : R = ⊤ := Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem hp t hswap (hS htS)
    obtain ⟨e⟩ := component_equiv_alternating_of_le (by omega) R (hR ▸ le_top) D hD
    exact Or.inl ⟨Fintype.card α,
      by simpa [Nat.card_eq_fintype_card] using (show 3 ≤ Nat.card α by omega),
      hn.le, ⟨e.trans (Fintype.equivFin α).altCongrHom⟩⟩
  · obtain ⟨S, hS⟩ := hA
    rcases component_models_of_alternating_sylow (ih _ hn) R S hS D hD with
      ⟨n, hn3, hnn, he⟩ | ⟨he, _⟩
    · exact Or.inl ⟨n, hn3, hnn.trans hn.le, he⟩
    · exact (hseven ((Nat.card_eq_fintype_card).trans he)).elim

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups

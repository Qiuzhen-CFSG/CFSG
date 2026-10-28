module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.Supercritical
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections

/-!
# Sylow and action transport for invariant Ξ embeddings

The additional hypothesis that T is Sylow in H restricts to a relatively
normal component L and descends through O₂(L). The equality PT = TP also
restricts and descends. The odd complement embeds in L/O₂(L), and its
Frattini quotient intertwines the actual normalizer action. In an SQTK
overgroup, both the complement image and the component quotient have
p-rank two.

These are preparations for the model sieve, not its classification. In
particular, the Sylow hypothesis is explicit and is not inferred from
`LocalInput`. The arbitrary-two-group obstruction remains valid.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of
Proposition 1.3.4, printed pp.510–511 (PDF pp.527–528).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree
universe u
variable {G : Type u} [Group G]

theorem complement_mul_two_group {p : ℕ} {T X P H : Subgroup G}
    (h : LocalInput p T X P H) :
    (P : Set G) * (T : Set G) = (X ⊔ T : Subgroup G) := by
  have hPX : P ≤ X := le_sup_right.trans h.complement.le
  have hQT : X.pCoreIn 2 ≤ T := le_sup_left.trans h.normalizer_factor.ge
  have hPN : P ≤ normalizer (X.pCoreIn 2 : Set G) :=
    hPX.trans (X.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))
  have hX : (X : Set G) = (P : Set G) * (X.pCoreIn 2 : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ hPN, sup_comm, h.complement]
  rw [coe_mul_of_right_le_normalizer_left _ _ h.invariant, hX, mul_assoc]
  congr 1
  symm
  apply Set.Subset.antisymm
  · exact Subgroup.mul_subset hQT le_rfl
  · intro t ht
    exact ⟨1, one_mem _, t, ht, one_mul t⟩

theorem complement_two_group_permute {p : ℕ} {T X P H : Subgroup G}
    (h : LocalInput p T X P H) : (P : Set G) * (T : Set G) = T * P := by
  have hi := congrArg (fun s : Set G => s⁻¹) (complement_mul_two_group h)
  simp only [mul_inv_rev, inv_coe_set] at hi
  exact (complement_mul_two_group h).trans hi.symm

theorem complement_intersection_permute {p : ℕ} {T X P H L : Subgroup G}
    (h : LocalInput p T X P H) (hPL : P ≤ L) :
    (P.subgroupOf L : Set L) * (T.subgroupOf L : Set L) =
      (T.subgroupOf L : Set L) * (P.subgroupOf L : Set L) := by
  have hf : Function.Injective (fun s : Set L => L.subtype '' s) :=
    Set.image_injective.mpr L.subtype_injective
  apply hf
  simp only [Set.image_mul, ← coe_map, map_subgroupOf_eq_of_le hPL,
    subgroupOf_map_subtype]
  rw [Subgroup.mul_inf_assoc _ _ _ hPL, inf_comm T L,
    Subgroup.inf_mul_assoc _ _ _ hPL, complement_two_group_permute h, Set.inter_comm]

theorem component_sylow [Finite G] {T H L : Subgroup G}
    (hT : IsSylowIn 2 T H) (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal) :
    ∃ S : Sylow 2 L, (S : Subgroup L) = T.subgroupOf L := by
  obtain ⟨S, hS⟩ := Section02.IndexTwo.isSylowIn_inf_of_subnormal hT hLH hLn.isSubnormal
  refine ⟨S, map_injective L.subtype_injective ?_⟩
  rw [hS, subgroupOf_map_subtype]

theorem component_quotient_sylow [Finite G] {T H L : Subgroup G}
    (hT : IsSylowIn 2 T H) (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal) :
    ∃ S : Sylow 2 (XiQuotient L), (S : Subgroup (XiQuotient L)) = quotientImage L T := by
  obtain ⟨S, hS⟩ := component_sylow hT hLH hLn
  exact ⟨S.mapSurjective (f := QuotientGroup.mk' (pCore 2 L))
    (QuotientGroup.mk'_surjective _), congrArg (map _) hS⟩

theorem component_quotient_permute {p : ℕ} {T X P H L : Subgroup G}
    (h : LocalInput p T X P H) (hPL : P ≤ L) :
    (quotientImage L P : Set (XiQuotient L)) * (quotientImage L T : Set (XiQuotient L)) =
      (quotientImage L T : Set (XiQuotient L)) * (quotientImage L P : Set (XiQuotient L)) := by
  have hh := congrArg (fun s : Set L => (QuotientGroup.mk' (pCore 2 L)) '' s)
    (complement_intersection_permute h hPL)
  simpa only [quotientImage, coe_map, Set.image_mul] using hh

noncomputable def complementEquiv {p : ℕ} {T X P H L : Subgroup G}
    (h : LocalInput p T X P H) (hPL : P ≤ L) : P ≃* quotientImage L P := by
  let _ : Fact p.Prime := ⟨h.prime⟩
  let R := P.subgroupOf L
  let q := QuotientGroup.mk' (pCore 2 L)
  have hd : Disjoint (pCore 2 L) R :=
    pCore_isPGroup.disjoint_of_coprime h.odd_complement.isPGroup.comap_subtype
      (Nat.coprime_two_left.mpr h.odd)
  have hi : Function.Injective (q.subgroupMap R) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro a ha
    have hc : (a : L) ∈ pCore 2 L := (QuotientGroup.eq_one_iff _).mp
      (congrArg Subtype.val ha)
    exact Subtype.ext (hd.le_bot ⟨hc, a.property⟩)
  exact (subgroupOfEquivOfLe hPL).symm.trans
    (MulEquiv.ofBijective (q.subgroupMap R) ⟨hi, q.subgroupMap_surjective R⟩)

theorem component_quotient_sqtk [Finite G] {κ : GroupClass.{u}} {H L : Subgroup G}
    (hH : IsSQTK κ H) (hLH : L ≤ H) : IsSQTK κ (XiQuotient L) := by
  have hL : IsSQTK κ L :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hLH)).mp (hH.subgroup (L.subgroupOf H))
  exact ⟨quotient_stronglyQuasithin hL.stronglyQuasithin, hL.isKGroup.quotient _⟩

theorem component_quotient_rank [Finite G] {p : ℕ} {T X P H L : Subgroup G}
    (h : LocalInput p T X P H) (hH : IsStronglyQuasithin H)
    (hLH : L ≤ H) (hPL : P ≤ L) :
    primeRank p (quotientImage L P) = 2 ∧ primeRank p (XiQuotient L) = 2 := by
  let _ : Fact p.Prime := ⟨h.prime⟩
  have hL : IsStronglyQuasithin L :=
    hH.of_injective (inclusion hLH) (inclusion_injective hLH)
  have hQ := quotient_stronglyQuasithin hL p h.prime h.odd
  have hP := h.odd_complement.of_mulEquiv (complementEquiv h hPL)
  have hu := (primeRank_subgroup_le p (quotientImage L P)).trans hQ
  have hl : ¬ primeRank p (quotientImage L P) ≤ 1 := by
    intro hr
    apply hP.not_isCyclic
    apply hP.isPGroup.isCyclic_of_odd_of_elementary_card_le h.odd
    intro E he
    let _ := he
    exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hr E
  have he : primeRank p (quotientImage L P) = 2 := by omega
  exact ⟨he, le_antisymm hQ (he.ge.trans (primeRank_subgroup_le p _))⟩

def componentAction {T L : Subgroup G} (hTL : T ≤ normalizer L) :
    T →* MulAut (XiQuotient L) :=
  (quotientAut (pCore 2 L)).comp (L.normalizerMonoidHom.comp (inclusion hTL))

noncomputable def normalizerAction {p : ℕ} {T X P H L : Subgroup G}
    (h : LocalInput p T X P H) (hPL : P ≤ L) :
    (T ⊓ normalizer P : Subgroup G) →* MulAut (quotientImage L P) :=
  (MulAut.congr (complementEquiv h hPL)).toMonoidHom.comp
    (P.normalizerMonoidHom.comp (inclusion inf_le_right))

theorem normalizerAction_coe {p : ℕ} {T X P H L : Subgroup G}
    (h : LocalInput p T X P H) (hPL : P ≤ L) (hTL : T ≤ normalizer L)
    (s : (T ⊓ normalizer P : Subgroup G)) (a : quotientImage L P) :
    (normalizerAction h hPL s a : XiQuotient L) =
      componentAction hTL ⟨s, s.property.1⟩ a := by
  obtain ⟨a, rfl⟩ := (complementEquiv h hPL).surjective a
  simp only [normalizerAction, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  change QuotientGroup.mk' (pCore 2 L) _ =
    quotientAut (pCore 2 L) _ (QuotientGroup.mk' (pCore 2 L) _)
  rw [quotientAut_apply_mk]
  rfl

private theorem map_frattini_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (frattini A).map e.toMonoidHom = frattini B := by
  apply le_antisymm
  · exact map_le_iff_le_comap.mpr (frattini_le_comap_frattini_of_surjective e.surjective)
  · intro b hb
    exact ⟨e.symm b, frattini_le_comap_frattini_of_surjective
      (φ := e.symm.toMonoidHom) e.symm.surjective hb, e.apply_symm_apply b⟩

noncomputable def complementFrattiniEquiv {p : ℕ} {T X P H L : Subgroup G}
    (h : LocalInput p T X P H) (hPL : P ≤ L) :
    (P ⧸ frattini P) ≃*
      (quotientImage L P ⧸ frattini (quotientImage L P)) :=
  QuotientGroup.congr _ _ (complementEquiv h hPL) (by exact map_frattini_equiv _)

theorem complementFrattiniEquiv_apply_mk {p : ℕ} {T X P H L : Subgroup G}
    (h : LocalInput p T X P H) (hPL : P ≤ L) (a : P) :
    complementFrattiniEquiv h hPL (QuotientGroup.mk' (frattini P) a) =
      QuotientGroup.mk' (frattini (quotientImage L P)) (complementEquiv h hPL a) := rfl

theorem complementFrattiniEquiv_equivariant {p : ℕ} {T X P H L : Subgroup G}
    (h : LocalInput p T X P H) (hPL : P ≤ L)
    (s : (T ⊓ normalizer P : Subgroup G)) (a : P ⧸ frattini P) :
    complementFrattiniEquiv h hPL
      (frattiniConjugationAction _ _ inf_le_right s a) =
    quotientAut (frattini (quotientImage L P)) (normalizerAction h hPL s)
      (complementFrattiniEquiv h hPL a) := by
  induction a using QuotientGroup.induction_on with | H a =>
    change complementFrattiniEquiv h hPL
        (frattiniConjugationAction _ _ inf_le_right s (QuotientGroup.mk' _ a)) =
      quotientAut (frattini (quotientImage L P)) (normalizerAction h hPL s)
        (complementFrattiniEquiv h hPL (QuotientGroup.mk' _ a))
    simp only [frattiniConjugationAction, MonoidHom.comp_apply,
      complementFrattiniEquiv_apply_mk, quotientAut_apply_mk]
    congr 1
    simp only [normalizerAction, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rfl

theorem component_normalizer_irreducible {p : ℕ} {T X P H L : Subgroup G}
    (h : LocalInput p T X P H) (hPL : P ≤ L) :
    ∀ A : Subgroup (quotientImage L P ⧸ frattini (quotientImage L P)),
      (∀ s : (T ⊓ normalizer P : Subgroup G), ∀ a ∈ A,
        quotientAut (frattini (quotientImage L P)) (normalizerAction h hPL s) a ∈ A) →
      A = ⊥ ∨ A = ⊤ := by
  intro A hA
  let e := complementFrattiniEquiv h hPL
  have hinv : ∀ s : (T ⊓ normalizer P : Subgroup G), ∀ a ∈ A.comap e.toMonoidHom,
      frattiniConjugationAction _ _ inf_le_right s a ∈ A.comap e.toMonoidHom := by
    intro s a ha
    change e (frattiniConjugationAction _ _ inf_le_right s a) ∈ A
    rw [complementFrattiniEquiv_equivariant]
    exact hA s _ ha
  rcases h.irreducible (A.comap e.toMonoidHom) hinv with hb | ht
  · left
    have hm := congrArg (Subgroup.map e.toMonoidHom) hb
    simpa only [map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective,
      Subgroup.map_bot] using hm
  · right
    have hm := congrArg (Subgroup.map e.toMonoidHom) ht
    simpa only [map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective,
      map_top_of_surjective e.toMonoidHom e.surjective] using hm

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree

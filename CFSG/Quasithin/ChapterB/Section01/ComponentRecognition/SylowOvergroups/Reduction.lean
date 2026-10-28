module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.GroupTheory.PGroup.Subnormal
public import Theory.GroupAction.SylowPointwiseInner
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# Sylow and proper-overgroup reductions for B.1.13

The actual conjugation image of K in Aut(L) vanishes if it fixes a Sylow
subgroup and the pointwise fixer is a two-group: a perfect group has no
nontrivial solvable image, and an order-three group has no two-group image.
Automorphisms of a perfect central cover inject into the automorphisms of
its central quotient, so this formulation retains odd central factors.

The source intersection X = L ∩ (K ∨ T) contains the literal restricted
Sylow subgroup and is proper if K < L. A subnormal quasisimple or order-three
subgroup belongs to F*(X). Under F*(X) ≤ O₂(X)(X ∩ Z(L)), its image modulo
the displayed central factor is a two-group and hence trivial. The source
identity [L,K] = L excludes centrality and forces K = L.

The two model properties below are explicit remaining mathematical inputs,
not recognition results. Model calculations and the arbitrary-degree
alternating overgroup classification must still be supplied to finish B.1.13.
Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.1.13,
printed p.74 (PDF p.85).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups
variable {G L A B : Type*} [Group G] [Group L] [Group A] [Group B]

/-- The pointwise automorphism fixer of each Sylow two-subgroup is a two-group. -/
@[expose] def SylowFixerIsTwoGroup (L : Type*) [Group L] : Prop :=
  ∀ S : Sylow 2 L, IsPGroup 2 (fixingSubgroup (MulAut L) (S : Set L))

/-- Proper Sylow overgroups have no generalized-Fitting factors beyond their
two-core and the centre of the original group. -/
@[expose] def ProperSylowFittingBound (L : Type*) [Group L] : Prop :=
  ∀ (S : Sylow 2 L) (X : Subgroup L), (S : Subgroup L) ≤ X → X ≠ ⊤ →
    generalizedFitting X ≤ pCore 2 X ⊔ (center L).subgroupOf X

private theorem hom_eq_one_of_twoGroup_range [Finite A] [Finite B]
    (f : A →* B) (hA : Group.IsPerfect A ∨ Nat.card A = 3)
    (hp : IsPGroup 2 f.range) (a : A) : f a = 1 := by
  rcases hA with hA | hA
  · let := hA
    let : Group.IsPerfect f.range := Group.IsPerfect.range f
    let : Group.IsNilpotent f.range := hp.isNilpotent
    have hs : Subsingleton f.range := by
      by_contra! hn
      exact Group.IsPerfect.not_isSolvable f.range inferInstance
    exact congrArg f.range.subtype (hs.elim (f.rangeRestrict a) 1)
  · have hthree : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by simpa using hA)
    have hd := hp.disjoint_of_coprime
      (hthree.of_surjective f.rangeRestrict f.rangeRestrict_surjective) (by decide)
    exact Subgroup.disjoint_def.mp hd ⟨a, rfl⟩ ⟨a, rfl⟩

/-- Conjugation by the Sylow subgroup supplies a two-group containing its pointwise fixer. -/
theorem fixer_twoGroup_of_inner [Finite L]
    (hinner : ∀ (S : Sylow 2 L) (a : MulAut L),
      (∀ x ∈ S, a x = x) → ∃ x ∈ S, a = MulAut.conj x) :
    SylowFixerIsTwoGroup L := by
  intro S
  apply (S.isPGroup'.map (MulAut.conj : L →* MulAut L)).to_le
  intro a ha
  obtain ⟨x, hx, he⟩ := hinner S a ((mem_fixingSubgroup_iff _).mp ha)
  exact ⟨x, hx, he.symm⟩

/-- The faithful automorphism action on a perfect central quotient lifts the fixer bound. -/
theorem fixer_twoGroup_of_centralQuotient [Finite L] [Group.IsPerfect L]
    (e : L ⧸ center L ≃* B) (hB : SylowFixerIsTwoGroup B) :
    SylowFixerIsTwoGroup L := by
  intro S
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hf : Function.Surjective f :=
    e.surjective.comp (QuotientGroup.mk'_surjective (center L))
  let Q := S.mapSurjective hf
  let F := fixingSubgroup (MulAut L) (S : Set L)
  let D := fixingSubgroup (MulAut B) (Q : Set B)
  let j : F →* D := ((MulAut.centralQuotientAction e).comp F.subtype).codRestrict D (by
    intro a
    apply (mem_fixingSubgroup_iff _).mpr
    rintro y ⟨x, hx, rfl⟩
    change MulAut.centralQuotientAction e a.val (e (QuotientGroup.mk' (center L) x)) = _
    rw [MulAut.centralQuotientAction_apply]
    have ha := (mem_fixingSubgroup_iff _).mp a.property x hx
    change a.val x = x at ha
    rw [ha]
    rfl)
  exact (hB Q).of_injective j (fun a b h => Subtype.ext
    (MulAut.centralQuotientAction_injective e (congrArg Subtype.val h)))

/-- The actual conjugation image of K vanishes when it lies in a two-group Sylow fixer. -/
theorem centralizes_of_sylow_fixer_twoGroup [Finite G]
    (K L : Subgroup G) (S : Sylow 2 L)
    (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hKN : K ≤ normalizer (L : Set G))
    (hKS : K ≤ centralizer ((S : Subgroup L).map L.subtype : Set G))
    (hfix : SylowFixerIsTwoGroup L) : K ≤ centralizer (L : Set G) := by
  let f : K →* MulAut L := L.normalizerMonoidHom.comp (inclusion hKN)
  have hle : f.range ≤ fixingSubgroup (MulAut L) (S : Set L) := by
    rintro a ⟨k, rfl⟩
    apply (mem_fixingSubgroup_iff _).mpr
    intro x hx
    apply Subtype.ext
    change k.val * x.val * k.val⁻¹ = x.val
    rw [← hKS k.property x.val (mem_map_of_mem L.subtype hx), mul_inv_cancel_right]
  have he (k : K) : f k = 1 := hom_eq_one_of_twoGroup_range f
    (hkind.imp (fun h => by let := h; infer_instance) id) ((hfix S).to_le hle) k
  intro k hk l hl
  have hh := congrArg (fun a : MulAut L => (a ⟨l, hl⟩ : G)) (he ⟨k, hk⟩)
  change k * l * k⁻¹ = l at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- The source local alternative forces containment once the model fixer bound is known. -/
theorem le_component_of_local_dichotomy [Finite G]
    (K L : Subgroup G) (T : Sylow 2 G)
    (hL : IsComponent G L) (hLK : ⁅L, K⁆ = L)
    (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hKN : K ≤ normalizer (L : Set G))
    (hd : K ≤ L ∨ ⁅K, L ⊓ (K ⊔ (T : Subgroup G))⁆ = ⊥)
    (hfix : SylowFixerIsTwoGroup L) : K ≤ L := by
  rcases hd with h | h
  · exact h
  obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_subnormal L hL.1
  have hSL : (S : Subgroup L).map L.subtype ≤ L ⊓ (K ⊔ (T : Subgroup G)) := by
    rw [hS, subgroupOf_map_subtype]
    exact le_inf inf_le_right (inf_le_left.trans le_sup_right)
  have hc := centralizes_of_sylow_fixer_twoGroup K L S hkind hKN
    ((commutator_eq_bot_iff_le_centralizer.mp h).trans (centralizer_le hSL)) hfix
  have hb : L = ⊥ := hLK.symm.trans
    ((commutator_comm L K).trans (commutator_eq_bot_iff_le_centralizer.mpr hc))
  let := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  exact ((nontrivial_iff_ne_bot L).mp inferInstance hb).elim

/-- For quasisimple K the existing component calculus discharges the local alternative. -/
theorem quasisimple_le_component [Finite G]
    (K L : Subgroup G) (T : Sylow 2 G) [IsQuasisimple K]
    (hL : IsComponent G L) (hLK : ⁅L, K⁆ = L)
    (hK : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal)
    (hKN : K ≤ normalizer (L : Set G)) (hfix : SylowFixerIsTwoGroup L) : K ≤ L :=
  le_component_of_local_dichotomy K L T hL hLK (Or.inl inferInstance) hKN
    (quasisimple_local_dichotomy K L T hL hK) hfix

private theorem subnormal_le_center_of_fitting_bound [Finite G]
    (A Z : Subgroup G) [Z.Normal] (hA : A.IsSubnormal)
    (hkind : IsQuasisimple A ∨ Nat.card A = 3)
    (hfit : generalizedFitting G ≤ pCore 2 G ⊔ Z) : A ≤ Z := by
  have hAF : A ≤ generalizedFitting G := by
    rcases hkind with hk | hk
    · exact component_le_generalizedFitting G A ⟨hA, hk⟩
    · have hp : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by simpa using hk)
      have hcore := isPGroup_le_pCoreAmbient_of_isSubnormalIn ⊤ A 3 le_top
        hA.subgroupOf hp
      have he : (pCore 3 (⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype = pCore 3 G :=
        pCore_map_iso 3 Subgroup.topEquiv
      rw [he] at hcore
      exact hcore.trans ((pCore_le_fitting G 3).trans (fitting_le_generalizedFitting G))
  let q := QuotientGroup.mk' Z
  let f : A →* G ⧸ Z := q.comp A.subtype
  have hr : f.range ≤ (pCore 2 G).map q := by
    have hh := map_mono (f := q) (hAF.trans hfit)
    change (q.comp A.subtype).range ≤ _
    rw [MonoidHom.range_comp, range_subtype]
    simpa only [q, Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq] using hh
  have he (a : A) : f a = 1 := hom_eq_one_of_twoGroup_range f
    (hkind.imp (fun h => by let := h; infer_instance) id)
    (((pCore_isPGroup (p := 2) (G := G)).map q).to_le hr) a
  intro a ha
  exact (QuotientGroup.eq_one_iff a).mp (he ⟨a, ha⟩)

/-- The actual local intersection, expressed intrinsically in L, is a proper
Sylow overgroup. The marked image remains exactly L ∩ (K ∨ T). -/
theorem local_intersection_sylow [Finite G]
    (K L : Subgroup G) (T : Sylow 2 G) (hL : IsComponent G L)
    (hLK : ⁅L, K⁆ = L)
    (hK : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal) (hKL : K < L) :
    ∃ S : Sylow 2 L,
      (S : Subgroup L) ≤ (K ⊔ (T : Subgroup G)).subgroupOf L ∧
      (K ⊔ (T : Subgroup G)).subgroupOf L ≠ ⊤ ∧
      ((K ⊔ (T : Subgroup G)).subgroupOf L).map L.subtype =
        L ⊓ (K ⊔ (T : Subgroup G)) := by
  obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_subnormal L hL.1
  refine ⟨S, ?_, ?_, by rw [subgroupOf_map_subtype, inf_comm]⟩
  · rw [hS]
    exact comap_mono le_sup_right
  · intro he
    have hm := congrArg (Subgroup.map L.subtype) he
    have hlt := local_intersection_lt K L T hL hLK hK hKL
    apply hlt.ne
    simpa only [subgroupOf_map_subtype, ← MonoidHom.range_eq_map, range_subtype, inf_comm] using hm

/-- The corrected Fitting bound for proper Sylow overgroups forces K = L.
The odd central factor is retained and is killed by [L,K] = L. -/
theorem eq_component_of_proper_sylow_fitting_bound [Finite G]
    (K L : Subgroup G) (T : Sylow 2 G) (hL : IsComponent G L)
    (hLK : ⁅L, K⁆ = L)
    (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hK : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal)
    (hKL : K ≤ L) (hbound : ProperSylowFittingBound L) : K = L := by
  by_contra hne
  let H := K ⊔ (T : Subgroup G)
  let X : Subgroup L := H.subgroupOf L
  let D : Subgroup X := (K.subgroupOf L).subgroupOf X
  let Z : Subgroup X := (center L).subgroupOf X
  have hDX : K.subgroupOf L ≤ X := comap_mono le_sup_left
  let e : D ≃* K := (subgroupOfEquivOfLe hDX).trans (subgroupOfEquivOfLe hKL)
  have hDkind : IsQuasisimple D ∨ Nat.card D = 3 := by
    rcases hkind with hq | hc
    · let := hq
      exact Or.inl (IsQuasisimple.of_mulEquiv e.symm)
    · exact Or.inr ((Nat.card_congr e.toEquiv).trans hc)
  have hDsub : D.IsSubnormal := by
    let f : X →* H := {
      toFun x := ⟨x.val.val, x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    exact hK.comap f
  obtain ⟨S, hSX, hX, _⟩ := local_intersection_sylow K L T hL hLK hK (lt_of_le_of_ne hKL hne)
  have hDZ : D ≤ Z := subnormal_le_center_of_fitting_bound D Z hDsub hDkind
    (hbound S X hSX hX)
  have hc : K ≤ centralizer (L : Set G) := by
    intro k hk l hl
    let x : X := ⟨⟨k, hKL hk⟩, (show K ≤ H from le_sup_left) hk⟩
    have hx : x ∈ D := hk
    have hz := hDZ hx
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨l, hl⟩)
  have hb : L = ⊥ := hLK.symm.trans
    ((commutator_comm L K).trans (commutator_eq_bot_iff_le_centralizer.mpr hc))
  let := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  exact (nontrivial_iff_ne_bot L).mp inferInstance hb

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups

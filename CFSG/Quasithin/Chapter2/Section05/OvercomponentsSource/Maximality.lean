module
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.PersistenceAtT
public import Theory.GroupTheory.ConjugateKernelObstruction
public import Theory.GroupTheory.DisjointConjugateCenter
public import Theory.GroupTheory.TwoGroupSquareChoice

/-!
# The two maximal-centralizer choices in the overcomponent argument

Choose an involution i in C_S(K) for which K is not a component of C_G(i),
first maximizing the order of R=C_S(i)∩C_S(K), then that of C_S(i).
An index-two subgroup R₂ of R, invariant under C_S(i), has disjoint
conjugate under the outside-square actor chosen in either source case.
Otherwise their intersection contains an involution centralizing a strictly
larger two-subgroup, contradicting one of the two maximality choices.
The disjoint conjugates force |R|≤4. If this bound fails, i is central
in N_S(K); source persistence then proves that K is nonnormal in H.

This is the first claim in Aschbacher–Smith 2.5.19, printed pp.562–563.
The preceding containing-component inspection supplies R₂, its index and
its centralizer obstruction. Those precise source inputs remain explicit.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.OvercomponentsSource
open ComponentRefinement ComponentSelection Overcomponents
variable {G : Type*} [Group G] [Finite G]

@[expose] def BadInvolution (S K : Subgroup G) (i : G) : Prop :=
  i ∈ S ⊓ centralizer (K : Set G) ∧ orderOf i = 2 ∧
    ¬ IsComponentIn K (centralizer ({i} : Set G))

@[expose] def MaximalBadInvolution (S K : Subgroup G) (i : G) : Prop :=
  BadInvolution S K i ∧
  (∀ j, BadInvolution S K j →
    Nat.card ((S ⊓ centralizer (K : Set G)) ⊓ centralizer ({j} : Set G) : Subgroup G) ≤
      Nat.card ((S ⊓ centralizer (K : Set G)) ⊓ centralizer ({i} : Set G) : Subgroup G)) ∧
  (∀ j, BadInvolution S K j →
    Nat.card ((S ⊓ centralizer (K : Set G)) ⊓ centralizer ({j} : Set G) : Subgroup G) =
      Nat.card ((S ⊓ centralizer (K : Set G)) ⊓ centralizer ({i} : Set G) : Subgroup G) →
    Nat.card (S ⊓ centralizer ({j} : Set G) : Subgroup G) ≤
      Nat.card (S ⊓ centralizer ({i} : Set G) : Subgroup G))

theorem exists_maximal_bad_involution (S K : Subgroup G)
    (h : ∃ i, BadInvolution S K i) : ∃ i, MaximalBadInvolution S K i := by
  let B := {i : G | BadInvolution S K i}
  let f := fun i : G => Nat.card
    ((S ⊓ centralizer (K : Set G)) ⊓ centralizer ({i} : Set G) : Subgroup G)
  obtain ⟨i,hi,hmax⟩ := Set.exists_max_image B f B.toFinite h
  let D := {j : G | j ∈ B ∧ f j = f i}
  obtain ⟨j,hj,hjmax⟩ := Set.exists_max_image D
    (fun j => Nat.card (S ⊓ centralizer ({j} : Set G) : Subgroup G))
    D.toFinite ⟨i,hi,rfl⟩
  refine ⟨j,hj.1,?_,?_⟩
  · intro k hk
    change f k ≤ f j
    rw [hj.2]
    exact hmax k hk
  · intro k hk he
    exact hjmax k ⟨hk,he.trans hj.2⟩

private theorem disjoint_of_relative_maximal_centralizer
    (P R D : Subgroup G) (hP : IsPGroup 2 P) (hRP : R ≤ P) (hDR : D ≤ R)
    (hDn : R ≤ normalizer (D : Set G)) (y : G) (hyP : y ∈ P)
    (hyR : y ∈ normalizer (R : Set G)) (hyout : y ∉ R) (hy2 : y ^ 2 ∈ R)
    (hmax : ∀ j : G, j ∈ D → orderOf j = 2 → R ≤ centralizer ({j} : Set G) →
      Nat.card (P ⊓ centralizer ({j} : Set G) : Subgroup G) ≤ Nat.card R) :
    Disjoint D (D.conjBy y) := by
  let f := (MulAut.conj y).toMonoidHom
  let X := D ⊓ D.map f
  let J := R ⊔ zpowers y
  have hJ : J ≤ P := sup_le hRP (zpowers_le.mpr hyP)
  have hXJ : X ≤ J := inf_le_left.trans (hDR.trans le_sup_left)
  have hyD2 : (D.map f).map f = D := by
    rw [map_map]
    have he : f.comp f = (MulAut.conj (y ^ 2)).toMonoidHom := by
      ext x
      simp [f, MulAut.conj_apply, pow_two, mul_assoc]
    rw [he]
    exact mem_normalizer_iff_map_conj_eq.mp (hDn hy2)
  have hyX : y ∈ normalizer (X : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq]
    change (D ⊓ D.map f).map f = D ⊓ D.map f
    rw [map_inf _ _ f (MulAut.conj y).injective, hyD2, inf_comm]
  have hRnD' : R ≤ normalizer (D.map f : Set G) := by
    have hyReq : R.map f = R := mem_normalizer_iff_map_conj_eq.mp hyR
    rw [← hyReq]
    exact (map_mono hDn).trans (le_normalizer_map f)
  have hJnX : J ≤ normalizer (X : Set G) :=
    sup_le ((le_inf hDn hRnD').trans inf_normalizer_le_normalizer_inf) (zpowers_le.mpr hyX)
  by_contra hdis
  have hne : X ≠ ⊥ := fun h => hdis (disjoint_iff.mpr h)
  let XJ := X.subgroupOf J
  let : XJ.Normal := (normal_subgroupOf_iff_le_normalizer hXJ).mpr hJnX
  let : Nontrivial XJ := by
    have : Nontrivial X := (nontrivial_iff_ne_bot _).mpr hne
    exact (subgroupOfEquivOfLe hXJ).toEquiv.nontrivial
  let : Fact (IsPGroup 2 J) := ⟨hP.to_le hJ⟩
  obtain ⟨Z, _, hZX, hZcard, hZcentral⟩ :=
    exists_central_subgroup_card_eq_prime_in_normal (p := 2) XJ inferInstance
  obtain ⟨j, hj⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 (hZcard ▸ dvd_rfl)
  have hjG : orderOf ((j : J) : G) = 2 := by simpa only [orderOf_coe] using hj
  have hcent : J ≤ centralizer ({((j : J) : G)} : Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp (hZcentral j.property) ⟨x, hx⟩))
  have hRJ : R < J := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro heq
    have hyJ : y ∈ J := (le_sup_right : zpowers y ≤ J) (mem_zpowers y)
    exact hyout (heq.symm ▸ hyJ)
  have hlt : Nat.card R < Nat.card J := lt_of_not_ge (fun h =>
    hRJ.ne (eq_of_le_of_card_ge hRJ.le h))
  have hle : Nat.card J ≤ Nat.card R :=
    (card_le_of_le (le_inf hJ hcent)).trans
      (hmax _ (hZX j.property).1 hjG (le_sup_left.trans hcent))
  exact (not_lt_of_ge hle) hlt

private theorem card_le_four_of_disjoint_half
    (R D : Subgroup G) (hDR : D ≤ R) (hi : (D.subgroupOf R).index = 2)
    (s : G) (hs : s ∈ normalizer (R : Set G)) (hd : Disjoint D (D.conjBy s)) :
    Nat.card R ≤ 4 := by
  have hc : Nat.card R = 2 * Nat.card D := by
    rw [card_eq_card_quotient_mul_card_subgroup (D.subgroupOf R)]
    rw [← index_eq_card, hi, Nat.card_congr (subgroupOfEquivOfLe hDR).toEquiv]
  have hb := card_le_two_of_disjoint_conjugate hDR hs hd hc
  omega

/-- The two maximality choices on p.563 force a four-group unless the bad
involution is central in the component normalizer inside the original Sylow.
The subgroup D is the source R₂: only its local normality, index, and the
specified overcomponent obstruction for its involutions are needed. -/
theorem maximal_bad_involution_dichotomy (S K : Subgroup G) (hS : IsPGroup 2 S)
    (i : G) (hi : MaximalBadInvolution S K i)
    (hCiN : S ⊓ centralizer ({i} : Set G) ≤ normalizer (K : Set G))
    (D : Subgroup G)
    (hDR : D ≤ (S ⊓ centralizer (K : Set G)) ⊓ centralizer ({i} : Set G))
    (hDn : S ⊓ centralizer ({i} : Set G) ≤ normalizer (D : Set G))
    (hindex : (D.subgroupOf ((S ⊓ centralizer (K : Set G)) ⊓
      centralizer ({i} : Set G))).index = 2)
    (hbad : ∀ j, j ∈ D → orderOf j = 2 → ¬ IsComponentIn K (centralizer ({j} : Set G))) :
    Nat.card ((S ⊓ centralizer (K : Set G)) ⊓ centralizer ({i} : Set G) : Subgroup G) ≤ 4 ∨
      i ∈ centerIn (S ⊓ normalizer (K : Set G)) := by
  let P := S ⊓ centralizer (K : Set G)
  let R := P ⊓ centralizer ({i} : Set G)
  let C := S ⊓ centralizer ({i} : Set G)
  let N := S ⊓ normalizer (K : Set G)
  have hRC : R ≤ C := inf_le_inf_right _ inf_le_left
  have hCN : C ≤ N := le_inf inf_le_left hCiN
  have hD_bad (j : G) (hj : j ∈ D) (hj2 : orderOf j = 2) : BadInvolution S K j :=
    ⟨(hDR hj).1,hj2,hbad j hj hj2⟩
  by_cases hRP : R = P
  · by_cases hiz : i ∈ centerIn N
    · exact Or.inr hiz
    · have hCNlt : C < N := by
        refine lt_of_le_of_ne hCN ?_
        intro he
        apply hiz
        refine ⟨⟨hi.1.1.1,Subgroup.centralizer_le_normalizer _ hi.1.1.2⟩,?_⟩
        intro a ha
        exact mem_centralizer_singleton_iff.mp ((he.symm ▸ ha : a ∈ C)).2
      obtain ⟨s,hsN,hsC,hsNC,hs2⟩ := exists_outside_normalizer_square_mem C N
        (hS.to_le inf_le_left) hCNlt
      have hsR : s ∈ normalizer (R : Set G) := by
        rw [hRP]
        exact inf_normalizer_le_normalizer_inf
          ⟨S.le_normalizer hsN.1,normalizer_le_normalizer_centralizer K hsN.2⟩
      have hd : Disjoint D (D.conjBy s) := by
        apply disjoint_of_relative_maximal_centralizer S C D hS inf_le_left
          (hDR.trans hRC) hDn s hsN.1 hsNC hsC hs2
        intro j hj hj2 hCj
        apply hi.2.2 j (hD_bad j hj hj2)
        have hPj : P ≤ centralizer ({j} : Set G) := (hRP ▸ hRC).trans hCj
        change Nat.card (P ⊓ centralizer ({j} : Set G) : Subgroup G) = Nat.card R
        rw [inf_eq_left.mpr hPj,hRP]
      exact Or.inl (card_le_four_of_disjoint_half R D hDR hindex s hsR hd)
  · have hRP_lt : R < P := lt_of_le_of_ne inf_le_left hRP
    obtain ⟨s,hsP,hsR,hsNR,hs2⟩ := exists_outside_normalizer_square_mem R P
      (hS.to_le inf_le_left) hRP_lt
    have hd : Disjoint D (D.conjBy s) := by
      apply disjoint_conjugate_of_maximal_centralizer P R D (hS.to_le inf_le_left)
        inf_le_left hDR (hRC.trans hDn) s hsP hsNR hsR hs2
      intro j hj hj2
      exact hi.2.1 j (hD_bad j hj hj2)
    exact Or.inl (card_le_four_of_disjoint_half R D hDR hindex s hsNR hd)

/-- A bad involution cannot be central in the original Sylow: it would lie
in the two-core and source 2.5.18 would preserve the component. -/
theorem source_bad_involution_not_central
    {H K M : Subgroup G} {S : Sylow 2 H} {z : G}
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (i : G) (hi : BadInvolution ((S : Subgroup H).map H.subtype) K i) :
    i ∉ centerIn ((S : Subgroup H).map H.subtype) := by
  intro hiz
  let Y := (S : Subgroup H).map H.subtype
  have hHC : H ≤ centralizer ({i} : Set G) := by
    rw [hgen]
    exact sup_le (fun k hk => mem_centralizer_singleton_iff.mpr (hi.1.2 k hk))
      (fun s hs => mem_centralizer_singleton_iff.mpr (hiz.2 s hs))
  have hcore : zpowers i ≤ twoCore H := by
    apply le_pCoreIn_of_normalizes
    · exact IsPGroup.of_card (n := 1) (by simpa only [Nat.card_zpowers,pow_one] using hi.2.1)
    · exact zpowers_le.mpr (map_subtype_le _ hi.1.1)
    · rw [normalizer_zpowers_eq_centralizer_of_order_two i hi.2.1]
      exact hHC
  exact hi.2.2 (source_component_in_centralizer_t c hG hempty hgen hb hstar
    i hi.2.1 (hcore (mem_zpowers i)) hiz)

/-- The actual first claim of the maximal-R argument, retaining the original
source marks: if |R| exceeds four then K is nonnormal in H and i is central
in N_S(K). R₂ is the literal index-two subgroup supplied by the preceding
containing-component inspection. -/
theorem source_maximal_bad_involution_dichotomy
    {H K M : Subgroup G} {S : Sylow 2 H} {z : G}
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (i : G) (hi : MaximalBadInvolution ((S : Subgroup H).map H.subtype) K i)
    (hCiN : (S : Subgroup H).map H.subtype ⊓ centralizer ({i} : Set G) ≤
      normalizer (K : Set G))
    (D : Subgroup G)
    (hDR : D ≤ (((S : Subgroup H).map H.subtype ⊓ centralizer (K : Set G)) ⊓
      centralizer ({i} : Set G)))
    (hDn : (S : Subgroup H).map H.subtype ⊓ centralizer ({i} : Set G) ≤ normalizer (D : Set G))
    (hindex : (D.subgroupOf (((S : Subgroup H).map H.subtype ⊓ centralizer (K : Set G)) ⊓
      centralizer ({i} : Set G))).index = 2)
    (hbad : ∀ j, j ∈ D → orderOf j = 2 → ¬ IsComponentIn K (centralizer ({j} : Set G))) :
    Nat.card ((((S : Subgroup H).map H.subtype ⊓ centralizer (K : Set G)) ⊓
      centralizer ({i} : Set G)) : Subgroup G) ≤ 4 ∨
      (¬ (K.subgroupOf H).Normal ∧
        i ∈ centerIn ((S : Subgroup H).map H.subtype ⊓ normalizer (K : Set G))) := by
  rcases maximal_bad_involution_dichotomy ((S : Subgroup H).map H.subtype) K
    (S.isPGroup'.map H.subtype) i hi hCiN D hDR hDn hindex hbad with h | hiz
  · exact Or.inl h
  · refine Or.inr ⟨?_,hiz⟩
    intro hn
    have hYN : (S : Subgroup H).map H.subtype ≤ normalizer (K : Set G) :=
      (map_subtype_le _).trans ((normal_subgroupOf_iff_le_normalizer c.component_le).mp hn)
    rw [inf_eq_left.mpr hYN] at hiz
    exact source_bad_involution_not_central c hG hempty hgen hb hstar i hi.1 hiz

end CFSG.Quasithin.Chapter2.Section05.OvercomponentsSource

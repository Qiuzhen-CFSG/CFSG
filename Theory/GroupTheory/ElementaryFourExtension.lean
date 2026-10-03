module
public import Theory.GroupTheory.PGroup.IsolatedFour
public import Theory.GroupTheory.InvolutionElementaryEight

/-!
# Extending four-groups in finite simple groups

If a finite simple group contains an elementary abelian two-subgroup of order
at least eight, every elementary four-group extends to such a subgroup. Inside
an involution centralizer the extension can be chosen in that centralizer: either the four
already contains the central involution, or adjoining it gives an eight.

We use the general centralizer argument of GLS, volume 4, Chapter 2,
Lemma 18.1 (before its K-properness assumption), together with involution
placement. For a maximal elementary four-group V, choose a Sylow two-subgroup
Q of C(V). Each involution x of V lies in an elementary eight, so Q extends
to a rank-three Sylow subgroup of C(x). The local normal-four geometry says
that every square involution of Q equals x. V has distinct involutions, so
Q has exponent two and Q = V. The involution-centralizer-four theorem then
contradicts rank three in C(x). This proves the no-isolated-vertex assertion
used in GLS, Lemma 18.3(b), without classification or global connectivity.
-/

namespace Subgroup
open scoped IsMulCommutative

private theorem rank_three_in_sylow
    {G : Type*} [Group G] [Finite G]
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (S : Sylow 2 G) :
    ∃ B : Subgroup S, IsElementaryAbelian 2 B ∧ 8 ≤ Nat.card B := by
  obtain ⟨T, hAT⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  let AT := A.subgroupOf (T : Subgroup G)
  let : IsElementaryAbelian 2 AT := IsElementaryAbelian.subgroupOf hAT
  let f := (T.equiv S).toMonoidHom
  refine ⟨AT.map f, IsElementaryAbelian.map f, ?_⟩
  rw [card_map_of_injective (T.equiv S).injective]
  change 8 ≤ Nat.card (A.subgroupOf (T : Subgroup G))
  rwa [Nat.card_congr (subgroupOfEquivOfLe hAT).toEquiv]

private theorem maximal_four_subgroupOf
    {G : Type*} [Group G]
    (V P : Subgroup G) [IsElementaryAbelian 2 V] (hVP : V ≤ P)
    (hmax : ∀ B : Subgroup G, IsElementaryAbelian 2 B → V ≤ B → B ≤ V) :
    ∀ B : Subgroup P, IsElementaryAbelian 2 B → V.subgroupOf P ≤ B →
      B ≤ V.subgroupOf P := by
  intro B hB hVB b hb
  let : IsElementaryAbelian 2 B := hB
  apply hmax (B.map P.subtype) IsElementaryAbelian.map_subtype
  · intro v hv
    exact mem_map.mpr ⟨⟨v, hVP hv⟩, hVB hv, rfl⟩
  · exact mem_map.mpr ⟨b, hb, rfl⟩

private theorem centralizer_overgroup
    {G : Type*} [Group G] [Finite G]
    (V Q : Subgroup G) [IsElementaryAbelian 2 V]
    (hQ : IsPGroup 2 Q) (hVQ : V ≤ Q) (hQC : Q ≤ centralizer (V : Set G))
    (hQmax : ∀ R : Subgroup G, IsPGroup 2 R → Q ≤ R →
      R ≤ centralizer (V : Set G) → R ≤ Q)
    (x : G) (hx : x ∈ V)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A) (hxA : x ∈ A) :
    ∃ P : Subgroup G, IsPGroup 2 P ∧ Q ≤ P ∧ P ≤ centralizer ({x} : Set G) ∧
      (∃ B : Subgroup P, IsElementaryAbelian 2 B ∧ 8 ≤ Nat.card B) ∧
      centralizer (V.subgroupOf P : Set P) ≤ Q.subgroupOf P := by
  let C := centralizer ({x} : Set G)
  have hQCx : Q ≤ C := fun q hq => mem_centralizer_singleton_iff.mpr ((hQC hq) x hx).symm
  have hAC : A ≤ C := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm (⟨a, ha⟩ : A) ⟨x, hxA⟩))
  have hQsub : IsPGroup 2 (Q.subgroupOf C) := by
    exact hQ.of_injective (subgroupOfEquivOfLe hQCx).toMonoidHom
      (subgroupOfEquivOfLe hQCx).injective
  obtain ⟨S, hQS⟩ := hQsub.exists_le_sylow
  let P : Subgroup G := (S : Subgroup C).map C.subtype
  have hQP : Q ≤ P := by
    intro q hq
    exact mem_map.mpr ⟨⟨q, hQCx hq⟩, hQS hq, rfl⟩
  have hPC : P ≤ C := map_subtype_le _
  have hP : IsPGroup 2 P := S.isPGroup'.map C.subtype
  have hVP : V ≤ P := hVQ.trans hQP
  refine ⟨P, hP, hQP, hPC, ?_, ?_⟩
  · let : IsElementaryAbelian 2 (A.subgroupOf C) := IsElementaryAbelian.subgroupOf hAC
    obtain ⟨B, hBe, hBc⟩ := rank_three_in_sylow (A.subgroupOf C)
      (by simpa only [Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv] using hA) S
    let : IsElementaryAbelian 2 B := hBe
    let f : S →* G := C.subtype.comp (S : Subgroup C).subtype
    let D := B.map f
    have hf : Function.Injective f := Subtype.coe_injective.comp Subtype.coe_injective
    have hDP : D ≤ P := by
      rintro d ⟨b, hb, rfl⟩
      exact mem_map.mpr ⟨b, b.property, rfl⟩
    let : IsElementaryAbelian 2 D := IsElementaryAbelian.map f
    refine ⟨D.subgroupOf P, IsElementaryAbelian.subgroupOf hDP, ?_⟩
    rw [Nat.card_congr (subgroupOfEquivOfLe hDP).toEquiv, card_map_of_injective hf]
    exact hBc
  · let R := (centralizer (V.subgroupOf P : Set P)).map P.subtype
    have hR : IsPGroup 2 R := (hP.to_subgroup _).map P.subtype
    have hQR : Q ≤ R := by
      intro q hq
      refine mem_map.mpr ⟨⟨q, hQP hq⟩, ?_, rfl⟩
      intro v hv
      apply Subtype.ext
      exact hQC hq v hv
    have hRC : R ≤ centralizer (V : Set G) := by
      rintro r ⟨p, hp, rfl⟩ v hv
      exact congrArg Subtype.val (hp (⟨v, hVP hv⟩ : P) hv)
    have hRQ := hQmax R hR hQR hRC
    intro p hp
    exact hRQ (mem_map.mpr ⟨p, hp, rfl⟩)

private theorem squares_trivial_of_square_involutions_trivial
    {G : Type*} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (hs : ∀ t : G, (t ^ 2) ^ 2 = 1 → t ^ 2 = 1) : ∀ t : G, t ^ 2 = 1 := by
  intro t
  obtain ⟨n, hn⟩ := hG.exists_orderOf_eq_pow t
  have hnle : n ≤ 1 := by
    by_contra hh
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ n by omega)
    let u := t ^ (2 ^ k)
    have hu : (u ^ 2) ^ 2 = 1 := by
      dsimp [u]
      rw [← pow_mul, ← pow_mul]
      convert pow_orderOf_eq_one t using 2
      rw [hn]
      ring
    have hu1 := hs u hu
    have hne : t ^ (2 ^ (k + 1)) ≠ 1 := by
      apply pow_ne_one_of_lt_orderOf (by positivity)
      rw [hn]
      exact Nat.pow_lt_pow_right (by decide) (by omega)
    apply hne
    calc
      t ^ (2 ^ (k + 1)) = (t ^ (2 ^ k)) ^ 2 := by rw [pow_succ, pow_mul]
      _ = 1 := hu1
  interval_cases n
  · have ht : t = 1 := orderOf_eq_one_iff.mp (by simpa using hn)
    simp [ht]
  · have ht := pow_orderOf_eq_one t
    simpa only [hn, pow_one] using ht

/-- If every involution of a finite group lies in an elementary eight, every
four-group extends to an elementary subgroup of order at least eight. -/
public theorem exists_elementary_eight_above_four_of_involution_placement
    {G : Type*} [Group G] [Finite G]
    (hplace : ∀ t : G, orderOf t = 2 →
      ∃ A : Subgroup G, IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A ∧ t ∈ A)
    (V : Subgroup G) [IsElementaryAbelian 2 V] (hV : Nat.card V = 4) :
    ∃ B : Subgroup G, IsElementaryAbelian 2 B ∧ 8 ≤ Nat.card B ∧ V ≤ B := by
  classical
  by_contra hno
  have hmax : ∀ B : Subgroup G, IsElementaryAbelian 2 B → V ≤ B → B ≤ V := by
    intro B hBe hVB
    have hBsmall : Nat.card B < 8 := by
      by_contra h
      exact hno ⟨B, hBe, by omega, hVB⟩
    have hdiv := card_dvd_of_le hVB
    rw [hV] at hdiv
    obtain ⟨k, hk⟩ := hdiv
    have hBpos := Nat.card_pos (α := B)
    exact (eq_of_le_of_card_ge hVB (by omega)).ge
  have hVC : V ≤ centralizer (V : Set G) := by
    intro v hv w hw
    exact congrArg Subtype.val (mul_comm (⟨w, hw⟩ : V) ⟨v, hv⟩)
  let C := centralizer (V : Set G)
  let : IsElementaryAbelian 2 (V.subgroupOf C) := IsElementaryAbelian.subgroupOf hVC
  obtain ⟨S, hVS⟩ := (IsElementaryAbelian.isPGroup 2 (V.subgroupOf C)).exists_le_sylow
  let Q : Subgroup G := (S : Subgroup C).map C.subtype
  have hQ : IsPGroup 2 Q := S.isPGroup'.map C.subtype
  have hQC : Q ≤ C := map_subtype_le _
  have hVQ : V ≤ Q := by
    intro v hv
    exact mem_map.mpr ⟨⟨v, hVC hv⟩, hVS hv, rfl⟩
  have hQmax : ∀ R : Subgroup G, IsPGroup 2 R → Q ≤ R → R ≤ C → R ≤ Q := by
    intro R hR hQR hRC
    have hRsub : IsPGroup 2 (R.subgroupOf C) :=
      hR.of_injective (subgroupOfEquivOfLe hRC).toMonoidHom
        (subgroupOfEquivOfLe hRC).injective
    have hSR : (S : Subgroup C) ≤ R.subgroupOf C := by
      intro s hs
      exact hQR (mem_map.mpr ⟨s, hs, rfl⟩)
    have heq := S.is_maximal' hRsub hSR
    intro r hr
    exact mem_map.mpr ⟨⟨r, hRC hr⟩, heq ▸ hr, rfl⟩
  have hover (x : G) (hx : x ∈ V) (hx1 : x ≠ 1) :
      ∃ P : Subgroup G, IsPGroup 2 P ∧ Q ≤ P ∧ P ≤ centralizer ({x} : Set G) ∧
        (∃ B : Subgroup P, IsElementaryAbelian 2 B ∧ 8 ≤ Nat.card B) ∧
        centralizer (V.subgroupOf P : Set P) ≤ Q.subgroupOf P := by
    obtain ⟨A, hAe, hAc, hxA⟩ := hplace x
      (orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian x hx) hx1)
    let : IsElementaryAbelian 2 A := hAe
    exact centralizer_overgroup V Q hQ hVQ hQC hQmax x hx A hAc hxA
  have hsquare (x : G) (hx : x ∈ V) (hx1 : x ≠ 1)
      (t : Q) (ht : (t ^ 2) ^ 2 = 1) : (t : G) ^ 2 = 1 ∨ (t : G) ^ 2 = x := by
    obtain ⟨P, hP, hQP, hPC, ⟨A, hAe, hAc⟩, -⟩ := hover x hx hx1
    have hVP := hVQ.trans hQP
    let : IsElementaryAbelian 2 A := hAe
    let : IsElementaryAbelian 2 (V.subgroupOf P) := IsElementaryAbelian.subgroupOf hVP
    have htV : (t : G) ^ 2 ∈ V := involution_mem_of_maximal_elementary_four V hmax
      ((t : G) ^ 2) (congrArg Subtype.val ht) (hQC (Q.pow_mem t.property 2))
    have hxZ : (⟨x, hVP hx⟩ : P) ∈ center P := by
      rw [mem_center_iff]
      intro p
      exact Subtype.ext (mem_centralizer_singleton_iff.mp (hPC p.property))
    have hh := square_eq_one_or_central_involution_of_maximal_four hP A
      (V.subgroupOf P) hAc
      (by simpa only [Nat.card_congr (subgroupOfEquivOfLe hVP).toEquiv] using hV)
      (maximal_four_subgroupOf V P hVP hmax)
      ⟨x, hVP hx⟩ hx (by simpa using hx1) hxZ
      ⟨t, hQP t.property⟩ htV
    rcases hh with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x, hx1⟩ := exists_ne (1 : V)
  have hxne : (x : G) ≠ 1 := by simpa using hx1
  have hxorder : orderOf (x : G) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (x : G) x.property) hxne
  have hnot : ¬ V ≤ zpowers (x : G) := by
    intro h
    have hc := card_le_of_le h
    rw [Nat.card_zpowers, hxorder, hV] at hc
    omega
  obtain ⟨y, hy, hyout⟩ := SetLike.not_le_iff_exists.mp hnot
  have hy1 : y ≠ 1 := fun h => hyout (h ▸ one_mem _)
  have hxy : (x : G) ≠ y := fun h => hyout (h ▸ mem_zpowers (x : G))
  have hs : ∀ t : Q, t ^ 2 = 1 := by
    apply squares_trivial_of_square_involutions_trivial hQ
    intro t ht
    rcases hsquare x x.property hxne t ht with h | h
    · exact Subtype.ext h
    rcases hsquare y hy hy1 t ht with h' | h'
    · exact Subtype.ext h'
    exact (hxy (h.symm.trans h')).elim
  let : IsElementaryAbelian 2 Q := {
    toIsMulCommutative := isMulCommutative_iff.mpr (by
      have hi (a : Q) : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hs a)
      intro a b
      simpa only [mul_inv_rev, hi a, hi b] using (hi (a * b)).symm)
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }
  have hQV : Q ≤ V := hmax Q inferInstance hVQ
  obtain ⟨P, hP, hQP, hPC, ⟨A, hAe, hAc⟩, hcent⟩ := hover x x.property hxne
  have hVP := hVQ.trans hQP
  let : IsElementaryAbelian 2 A := hAe
  let : IsElementaryAbelian 2 (V.subgroupOf P) := IsElementaryAbelian.subgroupOf hVP
  have hxZ : (⟨x, hVP x.property⟩ : P) ∈ center P := by
    rw [mem_center_iff]
    intro p
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hPC p.property))
  apply centralizer_ne_self_of_four_of_central_involution hP A (V.subgroupOf P) hAc
    (by simpa only [Nat.card_congr (subgroupOfEquivOfLe hVP).toEquiv] using hV)
    ⟨x, hVP x.property⟩ x.property (by simpa using hxne) hxZ
  apply le_antisymm
  · intro p hp
    exact hQV (hcent hp)
  · intro v hv w hw
    apply Subtype.ext
    exact congrArg (fun z : V => (z : G))
      (mul_comm (⟨w, hw⟩ : V) ⟨v, hv⟩)

/-- In a finite simple group with elementary binary rank at least three,
every elementary four-group lies in an elementary subgroup of order at least eight.
The overgroup is an ambient subgroup, with no preselected Sylow restriction. -/
public theorem exists_elementary_eight_above_four_of_simple
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (A V : Subgroup G) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 V]
    (hA : 8 ≤ Nat.card A) (hV : Nat.card V = 4) :
    ∃ B : Subgroup G, IsElementaryAbelian 2 B ∧ 8 ≤ Nat.card B ∧ V ≤ B :=
  exists_elementary_eight_above_four_of_involution_placement
    (Sylow.exists_elementary_eight_of_simple A hA) V hV

/-- Every four-group in an involution centralizer of a finite simple group
of binary rank at least three extends to an elementary eight in that centralizer.
Adjoin the central involution if necessary; otherwise ambient extension already
centralizes it. This does not impose a chosen Sylow on the extension. -/
public theorem exists_elementary_eight_above_four_in_involution_centralizer_of_simple
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (A V : Subgroup G) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 V]
    (hA : 8 ≤ Nat.card A) (hV : Nat.card V = 4)
    (t : G) (ht : orderOf t = 2) (hVC : V ≤ centralizer ({t} : Set G)) :
    ∃ B : Subgroup G, IsElementaryAbelian 2 B ∧ 8 ≤ Nat.card B ∧
      V ≤ B ∧ B ≤ centralizer ({t} : Set G) := by
  classical
  by_cases htV : t ∈ V
  · obtain ⟨B, hBe, hB, hVB⟩ := exists_elementary_eight_above_four_of_simple A V hA hV
    let : IsElementaryAbelian 2 B := hBe
    refine ⟨B, hBe, hB, hVB, ?_⟩
    intro b hb
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm' (⟨b, hb⟩ : B) ⟨t, hVB htV⟩))
  · let T := zpowers t
    let : IsElementaryAbelian 2 T := IsElementaryAbelian.zpowers_of_pow_eq_one
      (by rw [← ht]; exact pow_orderOf_eq_one t)
    have hTC : T ≤ centralizer (V : Set G) := by
      apply zpowers_le.mpr
      intro v hv
      exact mem_centralizer_singleton_iff.mp (hVC hv)
    let : IsElementaryAbelian 2 (V ⊔ T : Subgroup G) :=
      IsElementaryAbelian.sup_of_le_centralizer hTC
    refine ⟨V ⊔ T, inferInstance, ?_, le_sup_left, ?_⟩
    · have hlt : 4 < Nat.card (V ⊔ T : Subgroup G) := by
        by_contra h
        have heq : V = V ⊔ T := eq_of_le_of_card_ge le_sup_left (by omega)
        exact htV (heq ▸ (le_sup_right : T ≤ V ⊔ T) (mem_zpowers t))
      have hdiv := card_dvd_of_le (show V ≤ V ⊔ T from le_sup_left)
      rw [hV] at hdiv
      obtain ⟨k, hk⟩ := hdiv
      omega
    · exact sup_le hVC (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))

end Subgroup

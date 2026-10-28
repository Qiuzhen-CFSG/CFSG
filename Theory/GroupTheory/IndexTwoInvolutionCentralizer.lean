module

public import Theory.GroupTheory.SylowCentralizerConjugacy
public import Theory.GroupTheory.PGroup.Omega

/-!
# Index-two involution centralizers

Suppose a Sylow two-subgroup has a unique central involution `z`, and the
centralizer of an involution `i` has index two in it. If `i` is not conjugate
to `z`, this centralizer is Sylow in the full involution centralizer.

A larger two-subgroup of the full centralizer would have the order of an
ambient Sylow subgroup. Sylow conjugacy would then send `i` to the unique
central involution of the chosen Sylow subgroup, contradicting nonconjugacy.

Source: Janko–Thompson, Math. Z. 113 (1970), Lemma 3.1, p.387,
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
-/

open Subgroup
open scoped Pointwise
private theorem unique_central_involution
    {P : Type*} [Group P] [Finite P]
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (x z : P) (hxC : x ∈ center P) (hzC : z ∈ center P)
    (hx : orderOf x = 2) (hz : orderOf z = 2) : x = z := by
  let O := omega₁ (center P) (p := 2)
  have hm (y : P) (hyC : y ∈ center P) (hy : orderOf y = 2) :
      (⟨y, hyC⟩ : center P) ∈ O := by
    apply Subgroup.subset_closure
    apply Subtype.ext
    change y ^ 2 = 1
    simpa only [hy] using pow_orderOf_eq_one y
  let a : O := ⟨⟨x, hxC⟩, hm x hxC hx⟩
  let b : O := ⟨⟨z, hzC⟩, hm z hzC hz⟩
  have ha : a ≠ 1 := by
    intro h
    have he : x = 1 := congrArg (fun u : O => ((u : center P) : P)) h
    simp [he] at hx
  have hb : b ≠ 1 := by
    intro h
    have he : z = 1 := congrArg (fun u : O => ((u : center P) : P)) h
    simp [he] at hz
  obtain ⟨c, _, hc⟩ := (Nat.card_eq_two_iff' (1 : O)).mp hZ
  exact congrArg (fun u : O => ((u : center P) : P)) ((hc a ha).trans (hc b hb).symm)

private theorem isConj_central_involution
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (z : S) (hzC : z ∈ center S) (hz : orderOf z = 2)
    (i : G) (hi : orderOf i = 2)
    (R : Sylow 2 G) (hiR : i ∈ R) (hRC : (R : Subgroup G) ≤ centralizer ({i} : Set G)) :
    IsConj i (z : G) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R S
  let f : G ≃* G := MulAut.conj g
  have hmap : (R : Subgroup G).map f.toMonoidHom = (S : Subgroup G) := by
    exact congrArg Sylow.toSubgroup hg
  let y : S := ⟨f i, by
    change f i ∈ (S : Subgroup G)
    rw [← hmap]
    exact mem_map_of_mem f.toMonoidHom hiR⟩
  have hyC : y ∈ center S := by
    apply mem_center_iff.mpr
    intro s
    have hs : (s : G) ∈ (R : Subgroup G).map f.toMonoidHom := by rw [hmap]; exact s.property
    obtain ⟨r, hr, he⟩ := hs
    apply Subtype.ext
    change (s : G) * f i = f i * (s : G)
    rw [← he]
    change f r * f i = f i * f r
    simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp (hRC hr))
  have hy : orderOf y = 2 :=
    (orderOf_coe y).symm.trans ((f.orderOf_eq i).trans hi)
  have he : y = z := unique_central_involution hZ y z hyC hzC hy hz
  have hconj : IsConj i (y : G) := isConj_iff.mpr ⟨g, rfl⟩
  simpa only [he] using hconj

/-- An index-two involution centralizer in a Sylow subgroup is Sylow in the
ambient centralizer if the involution avoids the central involution class. -/
public theorem Sylow.exists_sylow_centralizer_eq_of_index_two_of_not_isConj
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (z : S) (hzC : z ∈ center S) (hz : orderOf z = 2)
    (i : S) (hi : orderOf i = 2)
    (hiZ : ¬ IsConj (i : G) (z : G))
    (hidx : (centralizer ({i} : Set S)).index = 2) :
    ∃ T : Sylow 2 (centralizer ({(i : G)} : Set G)),
      (T : Subgroup (centralizer ({(i : G)} : Set G))) =
      (S : Subgroup G).subgroupOf (centralizer ({(i : G)} : Set G)) := by
  let C := centralizer ({(i : G)} : Set G)
  let P := (S : Subgroup G).subgroupOf C
  let D := centralizer ({i} : Set S)
  have hP : IsPGroup 2 P := S.isPGroup'.comap_subtype
  obtain ⟨T, hPT⟩ := hP.exists_le_sylow
  refine ⟨T, ?_⟩
  by_contra hne
  have hlt : Nat.card P < Nat.card T := by
    by_contra! h
    exact hne (eq_of_le_of_card_ge hPT h).symm
  let K := (T : Subgroup C).map C.subtype
  obtain ⟨R, hKR⟩ := (T.isPGroup'.map C.subtype).exists_le_sylow
  have hRS : Nat.card R = Nat.card S := Nat.card_congr (R.equiv S).toEquiv
  have hKcard : Nat.card K = Nat.card T := card_map_of_injective C.subtype_injective
  have hPcard : Nat.card P = Nat.card D := by
    have he : P.map C.subtype = D.map (S : Subgroup G).subtype := by
      rw [subgroupOf_map_subtype, map_subtype_centralizer_singleton]
    have hh := congrArg (fun U : Subgroup G => Nat.card U) he
    simpa only [card_map_of_injective C.subtype_injective,
      card_map_of_injective (S : Subgroup G).subtype_injective] using hh
  have hDcard : Nat.card D * 2 = Nat.card S := by
    change D.index = 2 at hidx
    simpa only [hidx] using D.card_mul_index
  have hKeq : K = (R : Subgroup G) := by
    apply eq_of_le_of_card_ge hKR
    have he : Nat.card R = Nat.card K := Nat.eq_of_dvd_of_lt_two_mul Nat.card_pos.ne'
      (card_dvd_of_le hKR) (by rw [hRS, hKcard]; omega)
    exact he.le
  have hRC : (R : Subgroup G) ≤ C := hKeq ▸ map_subtype_le (T : Subgroup C)
  have hiR : (i : G) ∈ R := by
    apply hKR
    have hiC : (i : G) ∈ C := mem_centralizer_singleton_iff.mpr rfl
    exact mem_map_of_mem C.subtype (hPT (show (⟨i, hiC⟩ : C) ∈ P from i.property))
  exact hiZ (isConj_central_involution S hZ z hzC hz i ((orderOf_coe i).trans hi) R hiR hRC)

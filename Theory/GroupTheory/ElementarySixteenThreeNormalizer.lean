module

public import Theory.GroupAction.CoprimeNormalizerDecomposition
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Three-subgroup normalizers on an elementary sixteen

An order-three automorphism subgroup fixes either one or four elements.
In the latter case, coprime splitting embeds its normalizer in the product
of two automorphism groups of elementary fours, of total order 36.
In the fixed-point-free case every nonidentity two-element in its centralizer
fixes exactly four elements: its fixed subgroup has even order and order
congruent to one modulo three. Burnside's lemma therefore excludes a subgroup
of order eight in that centralizer. Conjugation on the three-subgroup bounds
the remaining normalizer factor by two.

Source: Parrott, A Characterization of the Tits' Simple Group (1972),
printed p.673, property (4). The proof uses no classification assumptions.
-/

open scoped IsMulCommutative
open Subgroup

private instance elementary_subgroup
    {V : Type*} [Group V] [IsElementaryAbelian 2 V] (K : Subgroup V) :
    IsElementaryAbelian 2 K where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := (Monoid.exponent_dvd_of_monoidHom K.subtype K.subtype_injective).trans
    (IsElementaryAbelian.exponent_dvd_p 2 V)

private theorem fixed_card_one_or_four
    {V : Type*} [Group V] [Finite V]
    (hV : Nat.card V = 16) (D : Subgroup (MulAut V)) (hD : Nat.card D = 3) :
    Nat.card (FixedPoints.subgroup D V) = 1 ∨
      Nat.card (FixedPoints.subgroup D V) = 4 := by
  let F := FixedPoints.subgroup D V
  have hmod := (IsPGroup.of_card (p := 3) (G := D) (n := 1)
    (by simpa using hD)).card_modEq_card_fixedPoints V
  change Nat.card V % 3 = Nat.card F % 3 at hmod
  rw [hV] at hmod
  have hdiv : Nat.card F ∣ 16 := hV ▸ F.card_subgroup_dvd_card
  have hproper : Nat.card F ≠ 16 := by
    intro hh
    have htop : F = ⊤ := F.eq_top_of_card_eq (hh.trans hV.symm)
    have hbot : D = ⊥ := by
      apply eq_bot_iff.mpr
      intro d hd
      apply mem_bot.mpr
      apply MulEquiv.ext
      intro x
      have hx : x ∈ F := htop ▸ mem_top x
      exact hx ⟨d, hd⟩
    rw [hbot, card_bot] at hD
    omega
  have hmem := Nat.mem_divisors.mpr ⟨hdiv, by decide⟩
  have hdivs : (16 : ℕ).divisors = {1, 2, 4, 8, 16} := by decide
  rw [hdivs] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  change Nat.card F = 1 ∨ Nat.card F = 4
  omega

private theorem not_eight_dvd_centralizer_of_fixed_free
    {V : Type*} [Group V] [Finite V]
    (hV : Nat.card V = 16) (D : Subgroup (MulAut V)) (hD : Nat.card D = 3)
    (hfixed : Nat.card (FixedPoints.subgroup D V) = 1) :
    ¬ 8 ∣ Nat.card (centralizer (D : Set (MulAut V))) := by
  classical
  intro hdiv
  let C := centralizer (D : Set (MulAut V))
  obtain ⟨P₀, hP₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := C) 2 (n := 3) hdiv
  let P := P₀.map C.subtype
  have hP : Nat.card P = 8 := (card_map_of_injective C.subtype_injective).trans hP₀
  have hPC : P ≤ C := by
    rintro _ ⟨c, _, rfl⟩
    exact c.property
  have hp : IsPGroup 2 P := IsPGroup.of_card (n := 3) hP
  have hd : IsPGroup 3 D := IsPGroup.of_card (n := 1) (by simpa using hD)
  have hbot : FixedPoints.subgroup D V = ⊥ := (card_eq_one.mp hfixed)
  have hc (c : P) (hcne : c ≠ 1) : Nat.card (MulAction.fixedBy V c) = 4 := by
    let Q := zpowers c
    let K := FixedPoints.subgroup Q V
    have hK (x : V) : x ∈ K ↔ c • x = x := by
      constructor
      · intro hx
        exact hx ⟨c, mem_zpowers c⟩
      · intro hx q
        exact smul_eq_self_of_mem_zpowers q.property hx
    have hcomm (d : D) (x : V) : c • (d • x) = d • (c • x) := by
      change (c : MulAut V) ((d : MulAut V) x) = (d : MulAut V) ((c : MulAut V) x)
      exact congrArg (fun a : MulAut V => a x)
        ((mem_centralizer_iff.mp (hPC c.property)) d d.property).symm
    let : IsInvariant D V K := ⟨by
      intro d x
      rw [hK, hK, hcomm]
      exact (smul_left_cancel_iff d).symm⟩
    have hKfixed : FixedPoints.subgroup D K = ⊥ := by
      apply bot_unique
      intro x hx
      apply mem_bot.mpr
      apply Subtype.ext
      have hh : (x : V) ∈ FixedPoints.subgroup D V := by
        intro d
        exact congrArg Subtype.val (hx d)
      exact mem_bot.mp (hbot ▸ hh)
    have hmod3 := hd.card_modEq_card_fixedPoints K
    change Nat.card K % 3 = Nat.card (FixedPoints.subgroup D K) % 3 at hmod3
    rw [hKfixed, card_bot] at hmod3
    have hmod2 := (hp.to_subgroup Q).card_modEq_card_fixedPoints V
    change Nat.card V % 2 = Nat.card K % 2 at hmod2
    rw [hV] at hmod2
    have hKdiv : Nat.card K ∣ 16 := hV ▸ K.card_subgroup_dvd_card
    have hproper : Nat.card K ≠ 16 := by
      intro heq
      have htop : K = ⊤ := K.eq_top_of_card_eq (heq.trans hV.symm)
      apply hcne
      apply Subtype.ext
      apply MulEquiv.ext
      intro x
      exact (hK x).mp (htop ▸ mem_top x)
    have hmem := Nat.mem_divisors.mpr ⟨hKdiv, by decide⟩
    have hdivs : (16 : ℕ).divisors = {1, 2, 4, 8, 16} := by decide
    rw [hdivs] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    have hKcard : Nat.card K = 4 := by omega
    have he : K ≃ MulAction.fixedBy V c :=
      Equiv.subtypeEquivRight hK
    exact (Nat.card_congr he).symm.trans hKcard
  let : Fintype V := Fintype.ofFinite V
  let : Fintype P := Fintype.ofFinite P
  let : Fintype (Quotient (MulAction.orbitRel P V)) := Fintype.ofFinite _
  have hcount (c : P) : Fintype.card (MulAction.fixedBy V c) =
      4 + if c = 1 then 12 else 0 := by
    by_cases heq : c = 1
    · subst c
      rw [if_pos rfl]
      have he : MulAction.fixedBy V (1 : P) ≃ V := {
        toFun := Subtype.val
        invFun := fun x => ⟨x, one_smul P x⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
      rw [Fintype.card_congr he, ← Nat.card_eq_fintype_card, hV]
    · rw [if_neg heq, add_zero, ← Nat.card_eq_fintype_card, hc c heq]
  have hsum := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group P V
  simp_rw [hcount] at hsum
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hsum
  rw [← Nat.card_eq_fintype_card, hP] at hsum
  omega

/-- Sixty-four does not divide the order of the normalizer of an order-three
subgroup of the automorphism group of an elementary abelian sixteen. -/
public theorem not_sixtyfour_dvd_card_normalizer_of_elementary_sixteen_three
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 16) (D : Subgroup (MulAut V)) (hD : Nat.card D = 3) :
    ¬ 64 ∣ Nat.card (normalizer (D : Set (MulAut V))) := by
  rcases fixed_card_one_or_four hV D hD with hF | hF
  · let : IsCyclic D := isCyclic_of_prime_card hD
    have hAut : Nat.card (MulAut D) = 2 := by
      rw [IsCyclic.card_mulAut, hD]
      decide
    let f := D.normalizerMonoidHom
    have hrange : Nat.card f.range ∣ 2 := hAut ▸ f.range.card_subgroup_dvd_card
    have hker : ¬ 8 ∣ Nat.card f.ker := by
      have heq : Nat.card f.ker = Nat.card (centralizer (D : Set (MulAut V))) := by
        rw [normalizerMonoidHom_ker,
          Nat.card_congr (subgroupOfEquivOfLe
            (centralizer_le_normalizer (D : Set (MulAut V)))).toEquiv]
      rw [heq]
      exact not_eight_dvd_centralizer_of_fixed_free hV D hD hF
    have hprod := f.ker.card_mul_index
    rw [index_ker] at hprod
    intro h64
    have hh : 64 ∣ Nat.card f.ker * 2 := by
      rw [← hprod] at h64
      exact h64.trans (Nat.mul_dvd_mul_left _ hrange)
    obtain ⟨k, hk⟩ := hh
    apply hker
    exact ⟨4 * k, by omega⟩
  · have hcop : Nat.Coprime (Nat.card D) (Nat.card V) := by rw [hD, hV]; decide
    have hcompl :=
      isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
        (G := V) (A := D) (Group.isSolvable_of_comm (fun a b : V => mul_comm a b))
        hcop inferInstance
    have hprod := card_sup_eq_mul_of_normalizes_of_disjoint (FixedPoints.subgroup D V)
      (commutatorAction D V) (by rw [normalizer_eq_top]; exact le_top) hcompl.disjoint
    rw [hcompl.sup_eq_top, card_top, hV, hF] at hprod
    have hC : Nat.card (commutatorAction D V) = 4 := by omega
    have hAutF : Nat.card (MulAut (FixedPoints.subgroup D V)) = 6 := by
      rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow _ 2 (by simpa using hF)]
      decide
    have hAutC : Nat.card (MulAut (commutatorAction D V)) = 6 := by
      rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow _ 2 (by simpa using hC)]
      decide
    obtain ⟨B, _, hdiv⟩ := exists_restricted_coprime_normalizer D hcop
    have hBdiv : Nat.card (normalizer (B : Set (MulAut (commutatorAction D V)))) ∣ 6 :=
      hAutC ▸ (normalizer (B : Set (MulAut (commutatorAction D V)))).card_subgroup_dvd_card
    rw [hAutF] at hdiv
    intro h64
    have hh : 64 ∣ 36 := h64.trans (hdiv.trans (Nat.mul_dvd_mul_left 6 hBdiv))
    norm_num at hh

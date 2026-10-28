module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Pair
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.CartanGeometry.Torus
public import Mathlib.Algebra.CharP.CharAndCard
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.GroupTheory.PrimeOrderClosure
public import Theory.Quasithin.CoprimeRank
public import Theory.GroupTheory.PResidual.PrimeToSubnormal
public import Theory.NumberTheory.BinaryTorusParity

/-!
# The source order-generated identity for the point-radical argument

The full Cartan has prime rank two at each prime dividing q-1. A normal
prime-order closure therefore has rank two as well. Its image modulo O₂(L)
cannot lie in the cyclic center of the quasisimple quotient. Perfectness of L
then kills the remaining two-group quotient and gives prime-order generation.

For odd-degree SL₃, the genuine 11.0.4 residual equalities make the index of L
prime to q-1; this gives the opposite containment for every allowed order.
For even-degree SL₃ its order-three clause supplies that containment. In the
Sp₄(4) row, comparison of actual model Sylow orders forces the chosen field
to have degree two, and O^{3′}(M)=L handles the cubic generators.

The resulting theta(M)=L is applied to the existing Cartan--TI assembly.
Only the genuine preceding 11.0.4 residual and cubic-containment clauses are
retained from `qt-d-1222-natural-preliminary-source`.
The fixed-summand owner retains scalar
geometry, centralizer control and the exceptional exclusion; final assembly
of those earlier inputs remains with `qt-d-1222-natural-normalizer-source`.
Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.0.4 and the final paragraph of 11.1.5, printed pp.760,766.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Pair
variable {G : Type*} [Group G] [Finite G]

private theorem prime_closure_eq_top [Group.IsPerfect G]
    [IsQuasisimple (G ⧸ pCore 2 G)] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hr : 2 ≤ primeRank p G)
    (hz : primeRank p (center (G ⧸ pCore 2 G)) ≤ 1) :
    closure {x : G | orderOf x = p} = ⊤ := by
  let C : Subgroup G := closure {x : G | orderOf x = p}
  have hnormal : (⊤ : Subgroup G) ≤ normalizer (C : Set G) := by
    apply le_normalizer_closure_iff.mpr
    intro g _ x hx
    exact subset_closure ((MulAut.conj g).orderOf_eq x |>.trans hx)
  let : C.Normal := normalizer_eq_top_iff.mp (top_unique hnormal)
  let q := QuotientGroup.mk' (pCore 2 G)
  let : (C.map q).Normal := (inferInstance : C.Normal).map q (QuotientGroup.mk'_surjective _)
  have himage : C.map q = ⊤ := by
    rcases IsQuasisimple.normal_le_center_or_eq_top (C.map q) with hc | ht
    · let f : C →* center (G ⧸ pCore 2 G) :=
        (q.comp C.subtype).codRestrict _ (fun x => hc (mem_map_of_mem q x.property))
      have hk : IsPGroup 2 f.ker := by
        have he : f.ker = (pCore 2 G).comap C.subtype := by
          ext x
          change (⟨q x, _⟩ : center (G ⧸ pCore 2 G)) = 1 ↔ (x : G) ∈ pCore 2 G
          rw [Subtype.ext_iff]
          exact QuotientGroup.eq_one_iff _
        rw [he]
        exact pCore_isPGroup.comap_of_injective _ C.subtype_injective
      have hcop : Nat.Coprime p (Nat.card f.ker) := by
        obtain ⟨n, hn⟩ := hk.exists_card_eq
        rw [hn]
        exact (Nat.coprime_two_right.mpr ho).pow_right n
      have hCr : primeRank p C = primeRank p G := by
        have hh := primeRank_primeOrderClosure p (⊤ : Subgroup G)
        have hs : {x : G | x ∈ (⊤ : Subgroup G) ∧ orderOf x = p} =
            {x : G | orderOf x = p} := by ext; simp
        rw [hs, primeRank_congr p Subgroup.topEquiv] at hh
        exact hh
      have hle := (primeRank_le_of_coprime_ker p f hcop).trans hz
      rw [hCr] at hle
      omega
    · exact ht
  have hsup : C ⊔ pCore 2 G = ⊤ := by
    have hh := congrArg (comap q) himage
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using hh
  let r := QuotientGroup.mk' C
  have hmap : (pCore 2 G).map r = ⊤ := by
    have hh := congrArg (map r) hsup
    simpa only [Subgroup.map_sup, r, QuotientGroup.map_mk'_self, bot_sup_eq,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using hh
  have hp : IsPGroup 2 (⊤ : Subgroup (G ⧸ C)) := hmap ▸ pCore_isPGroup.map r
  let : Group.IsNilpotent (G ⧸ C) := (hp.of_equiv topEquiv).isNilpotent
  by_contra hne
  let : Nontrivial (G ⧸ C) := QuotientGroup.nontrivial_iff.mpr hne
  exact Group.IsPerfect.not_isSolvable (G ⧸ C) inferInstance

private theorem sylow_card_congr {A B : Type*} [Group A] [Group B]
    [Finite A] [Finite B] (e : A ≃* B) (P : Sylow 2 A) (Q : Sylow 2 B) :
    Nat.card P = Nat.card Q := by
  let R := P.mapSurjective (f := e.toMonoidHom) e.surjective
  exact (Nat.card_congr ((P : Subgroup A).equivMapOfInjective e.toMonoidHom e.injective).toEquiv).trans
    (Nat.card_congr (Sylow.equiv R Q).toEquiv)

private theorem sl3_not_sp4_four {F K : Type*} [Field F] [Finite F] [CharP F 2]
    [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2^n) (hK : Nat.card K = 4)
    (e : Matrix.SpecialLinearGroup (Fin 3) F ≃* Matrix.symplecticGroup (Fin 2) K) : False := by
  have hk : Nat.card K = 2^2 := by omega
  have hc := sylow_card_congr e
    (Matrix.PSL3.CartanActions.BorelQuotient.unipotentSLSylow F hn hF)
    (Theory.SpecificGroups.SymplecticFour.unipotentSylow hk (by decide))
  change Nat.card (Matrix.PSL3.LinearThree.unipotentSL F) =
    Nat.card (Theory.SpecificGroups.SymplecticFour.unipotent (F := K)) at hc
  rw [Matrix.PSL3.LinearThree.card_unipotentSL,
    Theory.SpecificGroups.SymplecticFour.card_unipotent,
    hF, hk, ← pow_mul, ← pow_mul] at hc
  have he := (Nat.pow_right_injective (by decide : 1 < 2)) hc
  omega

private theorem sl_center_rank {F : Type*} [Field F] [Finite F]
    (p : ℕ) [Fact p.Prime] :
    primeRank p (center (Matrix.SpecialLinearGroup (Fin 3) F)) ≤ 1 := by
  let e := Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (R := F) (0 : Fin 3)
  let : IsCyclic (center (Matrix.SpecialLinearGroup (Fin 3) F)) :=
    e.isCyclic.mpr inferInstance
  exact (Sylow.nonempty.some : Sylow p (center (Matrix.SpecialLinearGroup (Fin 3) F))).primeRank_le_one_of_isCyclic inferInstance

omit [Finite G] in
private theorem le_theta_of_prime_generation {L M : Subgroup G} {Δ : Set ℕ} {p : ℕ}
    (hLM : L ≤ M) (hp : p ∈ Δ)
    (hgen : closure {x : L | orderOf x = p} = ⊤) : L ≤ theta Δ M := by
  have hm := congrArg (map L.subtype) hgen
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, range_subtype] at hm
  rw [← hm]
  apply Subgroup.closure_mono
  rintro x ⟨y, hy, rfl⟩
  refine ⟨hLM y.property, ?_⟩
  change orderOf (y : G) ∈ Δ
  rwa [L.orderOf_coe y, hy]

omit [Finite G] in
private theorem theta_le_of_index_coprime {L M : Subgroup G}
    [(L.subgroupOf M).Normal] {m : ℕ}
    (hc : Nat.Coprime m (L.subgroupOf M).index) :
    theta {d : ℕ | d ∣ m} M ≤ L := by
  apply (closure_le _).mpr
  rintro x ⟨hx, hd⟩
  let y : M := ⟨x, hx⟩
  let q := QuotientGroup.mk' (L.subgroupOf M)
  have h1 : q y = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes hc
    · apply orderOf_dvd_of_pow_eq_one
      have hy : y ^ m = 1 := orderOf_dvd_iff_pow_eq_one.mp
        ((M.orderOf_coe y) ▸ hd)
      simpa only [map_pow, map_one] using congrArg q hy
    · exact _root_.orderOf_dvd_natCard _
  exact (QuotientGroup.eq_one_iff y).mp h1

private theorem predecessor_odd {n : ℕ} (hn : 0 < n) : Odd (2 ^ n - 1) :=
  Nat.Even.sub_odd (Nat.one_le_pow _ _ (by decide))
    (even_two.pow_of_ne_zero (Nat.ne_of_gt hn)) odd_one

private theorem odd_torus_prime_gt_three {n p : ℕ} (hn : Odd n)
    (hp : p.Prime) (hd : p ∣ 2^n-1) : 3 < p := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero (by intro he; simp [he] at hn)
  have hp2 : p ≠ 2 := fun he => (predecessor_odd hnpos).not_two_dvd_nat (he ▸ hd)
  have hp3 : p ≠ 3 := fun he =>
    Nat.prime_three.coprime_iff_not_dvd.mp
      (Nat.BinaryTorusParity.coprime_three_sub_one hn) (he ▸ hd)
  have := hp.two_le
  omega

variable {T : Sylow 2 G} {L V : Subgroup G}

/-- Source 11.0.4 implies the theta equality in the full SL3 block row.
The order-p generation is proved here from the actual Cartan and the
quasisimple two-core quotient; it is not a hypothesis. -/
theorem sl3_theta_eq_of_source_residuals
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (c : Coordinates D S.field)
    (hsl : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree))
    (hres : ∀ p : ℕ, p.Prime → p ∣ 2 ^ S.field.degree - 1 → 3 < p →
      primeToResidual p (normalizer (L : Set G)) = L.subgroupOf (normalizer (L : Set G)))
    (hcubic : Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L) :
    theta (sourceOrders L S.field.degree) (normalizer (L : Set G)) = L := by
  classical
  let M := normalizer (L : Set G)
  let : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect S.source.maximal_faithful.1.1
  let : IsQuasisimple (L ⧸ pCore 2 L) := S.source.quasisimple
  obtain ⟨F, iF, fF, hF, ⟨e⟩⟩ := hsl
  let : Field F := iF
  let : Finite F := fF
  have hz (p : ℕ) [Fact p.Prime] : primeRank p (center (L ⧸ pCore 2 L)) ≤ 1 := by
    rw [primeRank_congr p (Subgroup.centerCongr e)]
    exact sl_center_rank (F := F) p
  obtain ⟨X, hX⟩ := exists_cartan D
  have hr (p : ℕ) (hp : p.Prime) (hd : p ∣ 2^S.field.degree-1) :
      2 ≤ primeRank p L := by
    have hh := Theory.GroupTheory.primeRank_le_of_injective p (inclusion (hX.1.trans inf_le_left))
      (inclusion_injective (hX.1.trans inf_le_left))
    rw [c.cartan_primeRank hX hp hd] at hh
    exact hh
  by_cases hn : Odd S.field.degree
  · have horders : sourceOrders L S.field.degree = {d : ℕ | d ∣ 2 ^ S.field.degree - 1} := by
      unfold sourceOrders
      rw [if_pos ⟨⟨F, iF, fF, hF, ⟨e⟩⟩, hn⟩]
    rw [horders]
    apply le_antisymm
    · apply theta_le_of_index_coprime
      apply Nat.coprime_of_dvd
      intro p hp hd
      let : Fact p.Prime := ⟨hp⟩
      have hi := primeToResidual_index_coprime (G := M) p
      rw [hres p hp hd (odd_torus_prime_gt_three hn hp hd)] at hi
      exact hp.coprime_iff_not_dvd.mp hi
    · have hlarge : 1 < 2 ^ S.field.degree - 1 := by
        have hpow : 2^2 ≤ 2^S.field.degree := Nat.pow_le_pow_right (by decide) S.nonbinary
        omega
      obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (by omega : 2 ^ S.field.degree - 1 ≠ 1)
      let : Fact p.Prime := ⟨hp⟩
      have ho : Odd p := Odd.of_dvd_nat (predecessor_odd S.field.degree_pos) hd
      exact le_theta_of_prime_generation L.le_normalizer hd
        (prime_closure_eq_top ho (hr p hp hd) (hz p))
  · have he : Even S.field.degree := Nat.not_odd_iff_even.mp hn
    have horders : sourceOrders L S.field.degree = {3} := by
      unfold sourceOrders
      rw [if_neg (fun h => hn h.2)]
    rw [horders]
    apply le_antisymm
    · exact (closure_le _).mpr (fun x hx => hcubic he x hx.1 hx.2)
    · have hd := (Nat.BinaryTorusParity.three_dvd_sub_one_iff _).mpr he
      exact le_theta_of_prime_generation L.le_normalizer (Set.mem_singleton 3)
        (prime_closure_eq_top (by decide : Odd 3) (hr 3 Nat.prime_three hd) (hz 3))

/-- The actual Sp4(4) block cannot have a marking over a different field.
The comparison uses the orders of the literal model Sylow two-subgroups. -/
theorem sp4_block_field_degree
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (c : Coordinates D S.field) (hb : ChapterC.IsSp4FourBlock L) :
    S.field.degree = 2 := by
  obtain ⟨_, F, inst, fin, hF, ρ, ⟨model⟩, _⟩ := hb
  let : Field F := inst
  let : Finite F := fin
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by simpa only [Nat.card_eq_fintype_card, show (2:ℕ)^2 = 4 from rfl] using hF)
  have hk : Nat.card F = 2^2 := by omega
  cases c with
  | sl3 m =>
    exact (sl3_not_sp4_four S.field.degree_pos S.field.card_eq hF
      (m.groupEquiv.symm.trans model.quotientIso)).elim
  | sp4 m =>
    have hc := sylow_card_congr (m.groupEquiv.symm.trans model.quotientIso)
      (Theory.SpecificGroups.SymplecticFour.unipotentSylow S.field.card_eq S.field.degree_pos)
      (Theory.SpecificGroups.SymplecticFour.unipotentSylow hk (by decide))
    change Nat.card (Theory.SpecificGroups.SymplecticFour.unipotent (F := S.field.Carrier)) =
      Nat.card (Theory.SpecificGroups.SymplecticFour.unipotent (F := F)) at hc
    rw [Theory.SpecificGroups.SymplecticFour.card_unipotent,
      Theory.SpecificGroups.SymplecticFour.card_unipotent,
      S.field.card_eq, hk, ← pow_mul, ← pow_mul] at hc
    have he := (Nat.pow_right_injective (by decide : 1 < 2)) hc
    omega
  | g2 m =>
    have hc := sylow_card_congr (m.groupEquiv.symm.trans model.quotientIso)
      Atlas.G2.LieParabolicSetup.sylow
      (Theory.SpecificGroups.SymplecticFour.unipotentSylow hk (by decide))
    change Nat.card (Atlas.G2.unipotent (K := S.field.Carrier)) =
      Nat.card (Theory.SpecificGroups.SymplecticFour.unipotent (F := F)) at hc
    rw [Atlas.G2.card_unipotent, Theory.SpecificGroups.SymplecticFour.card_unipotent,
      S.field.card_eq, hk, ← pow_mul, ← pow_mul] at hc
    have he := (Nat.pow_right_injective (by decide : 1 < 2)) hc
    omega

/-- The full source theta identity, with exactly the preceding 11.0.4
residual and cubic-containment clauses left explicit. Both generation and
the field comparison are discharged on the actual chosen setup. -/
theorem chosen_theta_eq_of_source_residuals
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (c : Coordinates D S.field)
    (hb : ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L)
    (hres : ∀ p : ℕ, p.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          p ∣ 2 ^ S.field.degree - 1 ∧ 3 < p) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          p ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual p (normalizer (L : Set G)) = L.subgroupOf (normalizer (L : Set G)))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L) :
    theta (sourceOrders L S.field.degree) (normalizer (L : Set G)) = L := by
  classical
  rcases hb with hb | hb
  · obtain ⟨_, _, F, inst, fin, hF, hmodel⟩ := hb
    have hsl : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) :=
      ⟨F, inst, fin, hF, hmodel.quotient_iso⟩
    exact sl3_theta_eq_of_source_residuals D S c hsl
      (fun p hp hd hl => hres p hp (Or.inl ⟨hsl, hd, hl⟩)) (hcubic hsl)
  · have hn := sp4_block_field_degree D S c hb
    have horders : sourceOrders L S.field.degree = {3} := by
      unfold sourceOrders
      rw [if_neg (by rw [hn]; simp)]
    rw [horders]
    obtain ⟨_, F, inst, fin, hF, ρ, ⟨model⟩, _⟩ := hb
    let : Field F := inst
    let : Finite F := fin
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
      (by simpa only [Nat.card_eq_fintype_card, show (2:ℕ)^2 = 4 from rfl] using hF)
    have hsp : Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) :=
      ⟨F, inst, fin, by simpa only [hn, show (2:ℕ)^2 = 4 from rfl] using hF,
        ⟨model.quotientIso⟩⟩
    have hres3 := hres 3 Nat.prime_three (Or.inr ⟨hsp, by rw [hn]; decide⟩)
    let : Group.IsPerfect L := Chapter1.mem_L_isPerfect S.source.maximal_faithful.1.1
    let : IsQuasisimple (L ⧸ pCore 2 L) := S.source.quasisimple
    have hz : primeRank 3 (center (L ⧸ pCore 2 L)) ≤ 1 := by
      rw [primeRank_congr 3 (Subgroup.centerCongr model.quotientIso),
        Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot]
      exact (Sylow.nonempty.some : Sylow 3 (⊥ : Subgroup (Matrix.symplecticGroup (Fin 2) F))).primeRank_le_one_of_isCyclic inferInstance
    obtain ⟨X, hX⟩ := exists_cartan D
    have hr : 2 ≤ primeRank 3 L := by
      have hh := Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion (hX.1.trans inf_le_left))
        (inclusion_injective (hX.1.trans inf_le_left))
      rw [c.cartan_primeRank hX Nat.prime_three (by rw [hn]; decide)] at hh
      exact hh
    apply le_antisymm
    · apply (closure_le _).mpr
      rintro x ⟨hx, hx3⟩
      have hm : (⟨x, hx⟩ : normalizer (L : Set G)) ∈ primeToResidual 3 (normalizer (L : Set G)) := by
        apply mem_primeToResidual_of_pow (n := 1)
        apply Subtype.ext
        simpa only [coe_pow, coe_one, pow_one, show orderOf x = 3 from hx3] using pow_orderOf_eq_one x
      rwa [hres3] at hm
    · exact le_theta_of_prime_generation L.le_normalizer (Set.mem_singleton 3)
        (prime_closure_eq_top (by decide : Odd 3) hr hz)

/-- The source identity is applied to the published Cartan--TI consumer.
The fixed-summand owner retains centralizer control and scalar geometry;
the preliminary-source owner supplies the two genuine 11.0.4 clauses. -/
theorem pairConstruction_of_source_residuals
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hres : ∀ p : ℕ, p.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          p ∣ 2 ^ S.field.degree - 1 ∧ 3 < p) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          p ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual p (normalizer (L : Set G)) = L.subgroupOf (normalizer (L : Set G)))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L)
    (hcontrol : (¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) →
      V = Source.conjugateSpan (normalizer (L : Set G)) V →
      (ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L) →
      radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L →
      ∀ U : Subgroup G, U ≤ radicalFixedCenter (f.Ri 0) L → U ≠ ⊥ →
      centralizer (U : Set G) ≤ normalizer (L : Set G))
    (hgeometry : CartanGeometry D S f) : PairConstruction D S f :=
  pairConstruction_of_geometry D S f
    (fun hb => chosen_theta_eq_of_source_residuals D S c hb hres hcubic) hcontrol hgeometry

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Pair

module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveModelsInputs
public import Theory.GroupAction.PerfectFixedCover

/-!
# Excluding the split-diagonal cover in the nonblock source argument

The torus acts trivially on K₂/O₂(K₂). Coprime fixed-point lifting therefore
makes its fixed subgroup surject onto that quotient, and the perfect residual
of the fixed subgroup still surjects. Each torus prime divides this perfect
cover's order, so its image survives the prime-to-p core of the root normalizer.
Thus the component centralizer of every torus element in that star quotient
contains a nontrivial perfect subgroup and cannot be cyclic.

An actual outside cubic torus element remains outside the star component.
A.3.18(3b)'s conjugacy clause would conjugate its subgroup to the distinguished
complement, whose component centralizer is cyclic. This proves the exclusion
on the literal star map. Together with the residual and theta exclusions, it
reduces explicit A.3.18 alternatives to the projective alternative. The latter
reduction is conditional: no A.3.18 theorem or SourceAlternatives is asserted.
The nonblock discharge and final four-row assembly remain with
qt-d-1222-nonblock-endgame-sieve.

Source: Aschbacher–Smith, A.3.18(3b), pp.51–53, and the paragraph preceding
original 4.3.12, p.617. Coprime lifting is independent finite-group theory.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

private theorem prime_actor_not_mem_starComponent
    {H : Type*} [Group H] [Finite H] (B : Subgroup H) [B.Normal]
    {p : ℕ} (hp : p.Prime) (a : H) (ha : orderOf a = p) (han : a ∉ B) :
    ChapterA.Section03.OddPrime.SourceModels.starMap p H a ∉
      ChapterA.Section03.OddPrime.SourceModels.starComponent p B := by
  let : Fact p.Prime := ⟨hp⟩
  let O := pPrimeCore p H
  let r := QuotientGroup.mk' B
  intro ham
  obtain ⟨b, hb, hba⟩ := ham
  have hw : a / b ∈ O := QuotientGroup.eq_iff_div_mem.mp hba.symm
  have hrb : r b = 1 := (QuotientGroup.eq_one_iff b).mpr hb
  have hra : r a ∈ O.map r := by
    exact mem_map.mpr ⟨a / b, hw, by rw [map_div, hrb, div_one]⟩
  let x : O.map r := ⟨r a, hra⟩
  have hx : x ^ p = 1 := by
    apply Subtype.ext
    change r a ^ p = 1
    rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  have hcop : Nat.Coprime p (Nat.card (O.map r)) :=
    (pPrimeCore_coprime_card (p := p) (G := H)).of_dvd_right (O.card_map_dvd r)
  have hx1 : x = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hx)
      (orderOf_dvd_natCard x))
  exact han ((QuotientGroup.eq_one_iff a).mp (congrArg Subtype.val hx1))

private theorem cyclic_centralizer_of_conjugate_prime_subgroup
    {H : Type*} [Group H] (B : Subgroup H) (a x : H) (l : B)
    (he : (zpowers a).map (MulAut.conj (l : H)).toMonoidHom = zpowers x)
    (hcyc : IsCyclic ((centralizer ({x} : Set H)).comap B.subtype)) :
    IsCyclic ((centralizer ({a} : Set H)).comap B.subtype) := by
  let C := (centralizer ({a} : Set H)).comap B.subtype
  let D := (centralizer ({x} : Set H)).comap B.subtype
  let e := MulAut.conj l
  let f : C →* D := (e.toMonoidHom.comp C.subtype).codRestrict D (by
    intro b
    change ((e b.val : B) : H) ∈ centralizer ({x} : Set H)
    have hb : ((b.val : B) : H) ∈ centralizer (zpowers a : Set H) := by
      rw [zpowers_eq_closure, centralizer_closure]
      exact b.property
    have hx : x ∈ (zpowers a).map (MulAut.conj (l : H)).toMonoidHom :=
      he.ge (mem_zpowers x)
    obtain ⟨y, hy, hxy⟩ := hx
    intro z hz
    have hz' : z = x := Set.mem_singleton_iff.mp hz
    rw [hz', ← hxy]
    simpa only [map_mul, e, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Subgroup.coe_mul, Subgroup.coe_inv]
      using congrArg (MulAut.conj (l : H)) (hb y hy))
  let : IsCyclic D := hcyc
  exact isCyclic_of_injective f (fun b d hd => Subtype.ext
    (e.injective (congrArg (fun z : D => (z : B)) hd)))

/-- A perfect subgroup centralizing the original torus covers K₂/O₂(K₂). -/
theorem SecondaryData.exists_torus_fixed_perfect_cover (s : SecondaryData c n)
    (hn : 0 < n) :
    ∃ P : Subgroup (secondary c), Group.IsPerfect P ∧
      P.map (secondary c).subtype ≤ centralizer (s.torus : Set G) ∧
      Function.Surjective ((QuotientGroup.mk' (pCore 2 (secondary c))).comp P.subtype) := by
  let A := s.torus
  let B := secondary c
  let N := pCore 2 B
  let : MulDistribMulAction A B :=
    conjMulDistribMulActionOfLeNormalizer A B (SecondaryData.torus_normalizes_secondary s)
  let : IsInvariant A B N := isInvariant_of_characteristic N
  let : Group.IsNilpotent N := (pCore_isPGroup (p := 2) (G := B)).isNilpotent
  have hodd : Odd (Nat.card A) := by
    rw [s.torus_card, Nat.odd_iff]
    have hmod := Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega : n ≠ 0))
    have hpos : 0 < 2 ^ n := Nat.pow_pos (by decide)
    omega
  have hcop : Nat.Coprime (Nat.card A) (Nat.card N) := by
    obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := B)).exists_card_eq
    rw [hk]
    exact (Nat.coprime_two_right.mpr hodd).pow_right k
  have htriv (a : A) (g : B) : g⁻¹ * (a • g) ∈ N := by
    have hm := s.torus_secondary (commutator_mem_commutator
      (B.inv_mem g.property) a.property)
    simp only [commutatorElement_def, inv_inv] at hm
    obtain ⟨z, hz, he⟩ := hm
    change (z : G) = (g : G)⁻¹ * (a : G) * (g : G) * (a : G)⁻¹ at he
    have he' : z = g⁻¹ * (a • g) := Subtype.ext (by
      change (z : G) = (g : G)⁻¹ * ((a : G) * (g : G) * (a : G)⁻¹)
      simpa only [mul_assoc] using he)
    exact he' ▸ hz
  let C := FixedPoints.subgroup A B
  let q := QuotientGroup.mk' N
  let f := q.comp C.subtype
  have hf : Function.Surjective f :=
    Theory.GroupAction.fixedPoint_quotient_surjective_of_solvable_coprime_displacement
      N inferInstance hcop htriv
  let := secondary_perfect c
  let : Group.IsPerfect (B ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let P := (solvableResidual C).map C.subtype
  have hP : P.map q = ⊤ := by
    rw [map_map, map_solvableResidual_eq f hf, solvableResidual_eq_top]
  refine ⟨P, Group.IsPerfect.map _, ?_, ?_⟩
  · rintro z ⟨b, hb, rfl⟩
    have hc : b ∈ C := (map_subtype_le _) hb
    intro a ha
    have he := congrArg (fun x : B => (x : G)) (hc (⟨a, ha⟩ : A))
    change a * (b : G) * a⁻¹ = b at he
    exact (mul_inv_eq_iff_eq_mul.mp he)
  · rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, range_subtype]
    exact hP

/-- The actual prime-to-p core quotient cannot have a cyclic component
centralizer for a torus element. A perfect fixed cover survives that core. -/
theorem SecondaryData.star_torus_centralizer_not_cyclic (s : SecondaryData c n)
    (hn : 0 < n) {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (a : rootNormalizer c) (ha : (a : G) ∈ s.torus) :
    ¬ IsCyclic
      ((centralizer ({ChapterA.Section03.OddPrime.SourceModels.starMap p
          (rootNormalizer c) a} : Set _)).comap
        (ChapterA.Section03.OddPrime.SourceModels.starComponent p s.component).subtype) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP, hc, hsur⟩ := SecondaryData.exists_torus_fixed_perfect_cover s hn
  let := hP
  have hdQ : p ∣ Nat.card (secondary c ⧸ pCore 2 (secondary c)) := by
    by_contra hnot
    have hz := PrimeRank.eq_zero_iff_not_dvd_card.mpr hnot
    rw [primeRank_quotient_eq_of_isTwoGroup p ho _ pCore_isPGroup,
      SecondaryData.secondary_primeRank_eq_one s hp ho hd] at hz
    omega
  have hdP : p ∣ Nat.card P := hdQ.trans (card_dvd_of_surjective _ hsur)
  let N := rootNormalizer c
  let q := ChapterA.Section03.OddPrime.SourceModels.starMap p N
  let j : P →* N := s.component.subtype.comp
    ((SecondaryData.secondaryToComponent s).comp P.subtype)
  have hj : Function.Injective j :=
    s.component.subtype_injective.comp
      ((SecondaryData.secondaryToComponent_injective s).comp P.subtype_injective)
  let f := q.comp j
  have hne : f.range ≠ ⊥ := by
    intro hb
    have hker (x : P) : j x ∈ pPrimeCore p N := by
      apply (QuotientGroup.eq_one_iff _).mp
      exact mem_bot.mp (hb ▸ (show f x ∈ f.range from ⟨x, rfl⟩))
    let k : P →* pPrimeCore p N := j.codRestrict _ hker
    have hki : Function.Injective k := fun x y he =>
      hj (congrArg (fun z : pPrimeCore p N => (z : N)) he)
    exact (hp.coprime_iff_not_dvd.mp (pPrimeCore_coprime_card (p := p) (G := N)))
      (hdP.trans (card_dvd_of_injective k hki))
  let C := (centralizer ({q a} : Set _)).comap
    (ChapterA.Section03.OddPrime.SourceModels.starComponent p s.component).subtype
  let k : f.range →* C :=
    { toFun := fun x => ⟨⟨x, by
        obtain ⟨b, hb⟩ := x.property
        rw [← hb]
        exact mem_map.mpr ⟨j b, (SecondaryData.secondaryToComponent s b.val).property, rfl⟩⟩, by
        obtain ⟨b, hb⟩ := x.property
        change (x : ChapterA.Section03.OddPrime.SourceModels.Star p N) ∈
          centralizer ({q a} : Set _)
        rw [← hb]
        intro y hy
        have hy' : y = q a := Set.mem_singleton_iff.mp hy
        rw [hy']
        change q a * q (j b) = q (j b) * q a
        rw [← map_mul, ← map_mul]
        apply congrArg q
        apply Subtype.ext
        exact hc (mem_map.mpr ⟨b.val, b.property, rfl⟩) a ha⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  intro hcyclic
  let : IsCyclic C := hcyclic
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  let : Nontrivial f.range := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  exact Group.IsPerfect.not_isSolvable f.range
    (Group.isSolvable_of_isSolvable_injective (f := k)
      (fun x y he => Subtype.ext (congrArg (fun z : C => z.val.val) he)))

/-- A.3.18(3b) is impossible on the literal source star quotient. Its
outside-subgroup conjugacy clause would make the torus actor's component
centralizer cyclic, contrary to the surviving perfect fixed cover. -/
theorem SecondaryData.not_splitDiagonalAlternative (s : SecondaryData c n)
    (hn : 0 < n) (hd : 3 ∣ 2 ^ n - 1) :
    ¬ ChapterA.Section03.OddPrime.SourceModels.SplitDiagonalAlternative
      (ChapterA.Section03.OddPrime.SourceModels.starComponent 3 s.component) := by
  obtain ⟨a, hat, ha, han⟩ := SecondaryData.exists_outside_prime_actor s Nat.prime_three hd
  let := s.normal
  let q := ChapterA.Section03.OddPrime.SourceModels.starMap 3 (rootNormalizer c)
  let B := ChapterA.Section03.OddPrime.SourceModels.starComponent 3 s.component
  have hao : q a ∉ B := prime_actor_not_mem_starComponent s.component Nat.prime_three a ha han
  have hap : orderOf (q a) = 3 := by
    apply orderOf_eq_prime
    · have ha3 : a ^ 3 = 1 := by simpa only [ha] using pow_orderOf_eq_one a
      rw [← map_pow, ha3, map_one]
    · intro he
      exact hao (he ▸ B.one_mem)
  rintro ⟨u, q0, hcong, hmodel, x, α, hx, hα, houter, hdiag, hres, hdisj, hcyc, hcard, hconj⟩
  obtain ⟨l, hl⟩ := hconj (zpowers (q a)) (by rw [Nat.card_zpowers, hap])
    (fun hle => hao (hle (mem_zpowers (q a))))
  exact SecondaryData.star_torus_centralizer_not_cyclic s hn Nat.prime_three (by decide) hd a hat
    (cyclic_centralizer_of_conjugate_prime_subgroup B (q a) x l hl hcyc)

/-- Once the genuine A.3.18 alternatives are supplied, the source setup
eliminates its first and third rows. The surviving projective alternative
retains its exact prime-core quotient and residual models. The remaining
A.3.18 premise remains unproved here; its nonblock discharge and the four-row
assembly remain with qt-d-1222-nonblock-endgame-sieve. -/
theorem SecondaryData.projective_of_A318_alternatives (s : SecondaryData c n)
    (hn : 0 < n) {p : ℕ} (hp : p.Prime) (hd : p ∣ 2 ^ n - 1)
    (hm : ChapterA.Section03.OddPrime.SourceModels.Alternatives p s.component) :
    ChapterA.Section03.OddPrime.SourceModels.ProjectiveAlternative p s.component := by
  rcases hm with hr | hpj | ⟨rfl, _, ht | hs⟩
  · exact (SecondaryData.component_ne_primeToResidual s hp hd hr).elim
  · exact hpj
  · exact (SecondaryData.component_ne_theta s hd ht).elim
  · exact (SecondaryData.not_splitDiagonalAlternative s hn hd hs).elim

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve

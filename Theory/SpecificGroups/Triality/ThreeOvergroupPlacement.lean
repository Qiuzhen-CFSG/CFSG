module

public import Theory.SpecificGroups.Triality.TwoLocalCover
public import Theory.SpecificGroups.Triality.ParabolicGeometry
public import Theory.SpecificGroups.Triality.ParabolicLocalStructure
public import Theory.GroupTheory.SubgroupProductCard
public import Theory.GroupTheory.PResidual.SubnormalSupplement
public import Theory.GroupTheory.SolvableSmallThreeCore
public import Theory.SpecificGroups.Triality.ConcreteBruhat.CartanNormalizer
public import Theory.SpecificGroups.SL2.SylowUniqueMaximal
public import Theory.SpecificGroups.SymplecticFour.Sylow.SolvableParabolic.RankOne
public import GorensteinWalter.PSL2PerfectOfCard

/-!
# Placement of a solvable three-by-Sylow overgroup in triality

The product of the two marked subgroups is a genuine subgroup because the
factors permute.  Its order has only the primes two and three.  Once the
three-part is bounded by 27, the small-three-core argument gives a nontrivial
normal two-subgroup.  The concrete triality hexagon then puts the normalizer
of that subgroup in a root parabolic.  Sylow conjugacy inside that parabolic,
together with the actual root normalizer, removes the conjugating element.

The source odd-complement catalogue supplies the order bound on the mapped
three-subgroup.  It is displayed as a hypothesis here so this module does not
reconstruct a source encoding from the weaker numerical rank statement.

Source: Aschbacher--Smith, `refs/quasithin.pdf`, printed p.511 (PDF p.528),
and GLS3, `refs/KGroup/GLS3/chapter2.tex`, §§2.3--2.6.
-/

@[expose] public section

open Subgroup
open scoped Pointwise MatrixGroups

namespace Triality.Standard.ThreeOvergroupPlacement

open Triality.Standard Parabolics TwoLocalCover

private theorem projective_solvable_sylow_normalizes
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (_hF : 2 < Nat.card F) (T : Sylow 2 PSL(2, F)) (H : Subgroup PSL(2, F))
    (hsolv : Group.IsSolvable H) (hTH : (T : Subgroup PSL(2, F)) ≤ H)
    (hproper : H ≠ ⊤) : H ≤ normalizer (T : Set PSL(2, F)) := by
  let e := Theory.PSL2.sl2QuotientEquiv F
  have hesurj : Function.Surjective (e.symm.toMonoidHom) := by
    intro x
    obtain ⟨y, hy⟩ := e.symm.surjective x
    exact ⟨y, hy⟩
  let T' : Sylow 2 SL(2, F) := T.mapSurjective (f := e.symm.toMonoidHom) hesurj
  let H' : Subgroup SL(2, F) := H.map e.symm.toMonoidHom
  let _ : Group.IsSolvable H := hsolv
  have hsolv' : Group.IsSolvable H' :=
    Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective e.symm.toMonoidHom H)
  have hproper' : H' ≠ ⊤ := by
    intro hh
    apply hproper
    have htop := congrArg (Subgroup.map e.toMonoidHom) hh
    simpa [H', Subgroup.map_map] using htop
  have hT'H' : (T' : Subgroup SL(2, F)) ≤ H' := by
    change (T : Subgroup PSL(2, F)).map e.symm.toMonoidHom ≤ H.map e.symm.toMonoidHom
    exact Subgroup.map_mono hTH
  let _ : Group.IsSolvable H' := hsolv'
  have hn' := Theory.SpecificGroups.SymplecticFour.SolvableParabolic.proper_sylow_overgroup
    T' H' hproper' hT'H'
  have hmap := Subgroup.map_mono (f := e.toMonoidHom) hn'
  have hmap' : H'.map e.toMonoidHom ≤
      normalizer (((T' : Subgroup SL(2, F)).map e.toMonoidHom : Subgroup (PSL(2, F))) :
        Set (PSL(2, F))) := by
    rw [← Subgroup.map_equiv_normalizer_eq (T' : Subgroup SL(2, F)) e]
    exact hmap
  have hTmap : (T' : Subgroup SL(2, F)).map e.toMonoidHom = T := by
    rw [show (T' : Subgroup SL(2, F)) =
        (T : Subgroup (PSL(2, F))).map e.symm.toMonoidHom from
      Sylow.coe_mapSurjective hesurj T]
    rw [Subgroup.map_map]
    simp
  rw [hTmap] at hmap'
  simpa [H', Subgroup.map_map] using hmap'

private theorem normalizes_of_projection {G : Type*} [Group G] [Finite G]
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : 3 < Nat.card F) (f : G →* PSL(2, F)) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (T : Sylow 2 G) (H : Subgroup G)
    [Group.IsSolvable H] (hTH : (T : Subgroup G) ≤ H) :
    H ≤ normalizer (T : Set G) := by
  let Tq := T.mapSurjective hf
  have hsol : Group.IsSolvable (H.map f) :=
    Group.isSolvable_of_surjective (f.subgroupMap_surjective H)
  have hproper : H.map f ≠ ⊤ := by
    intro ht
    let _ := hsol
    let _ : Group.IsPerfect (PSL(2, F)) :=
      GorensteinWalter.psl2_isPerfect_of_card_gt_three F hF
    have hPSL : Group.IsSolvable (PSL(2, F)) :=
      Group.isSolvable_of_surjective (f := (H.map f).subtype)
        (by rw [ht]; exact topEquiv.surjective)
    exact Group.IsPerfect.not_isSolvable _ hPSL
  let _ := hsol
  have hnorm := projective_solvable_sylow_normalizes (by omega) Tq (H.map f) hsol
    (map_mono hTH) hproper
  have hker : f.ker ≤ (T : Subgroup G) := hk.le_sylow_of_normal T
  have hpre := (map_le_iff_le_comap.mp hnorm).trans
    ((Tq : Subgroup (PSL(2, F))).le_normalizer_comap f)
  simpa only [Tq, Sylow.coe_mapSurjective, comap_map_eq_self hker, Sylow.coe_coe] using hpre

private theorem normalizes_of_intermediate
    {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (L H : Subgroup G) (hTL : (T : Subgroup G) ≤ L)
    (hLN : L ≤ normalizer (T : Set G)) (hHL : H ≤ normalizer (L : Set G)) :
    H ≤ normalizer (T : Set G) := by
  let S := T.subtype hTL
  have hSN : S.Normal := (normal_subgroupOf_iff_le_normalizer hTL).mpr hLN
  have hSC : S.Characteristic := S.characteristic_of_normal hSN
  apply Subgroup.le_normalizer_iff.mpr
  intro h hh t ht
  let a := L.normalizerMonoidHom ⟨h, hHL hh⟩
  have hfix := hSC.fixed a
  have hmem : a ⟨t, hTL ht⟩ ∈ (S : Subgroup L) := by
    change (⟨t, hTL ht⟩ : L) ∈ (S : Subgroup L).comap a.toMonoidHom
    rw [hfix]
    exact ht
  exact hmem

private theorem normalizes_of_local_factor_projection
    {G : Type*} [Group G] [Finite G]
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : 3 < Nat.card F) (K H : Subgroup G)
    (f : K →* PSL(2, F)) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H) (hTK : (T : Subgroup G) ≤ K)
    [Group.IsSolvable H] (hHK : H ≤ normalizer (K : Set G)) :
    H ≤ normalizer (T : Set G) := by
  have hsol : Group.IsSolvable (H.subgroupOf K) := by
    let j : H.subgroupOf K →* H :=
      { toFun := fun x => ⟨x.val.val, x.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact Group.isSolvable_of_isSolvable_injective (f := j)
      (fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : H => (x : G)) h)))
  let _ := hsol
  have hlocal := normalizes_of_projection hF f hf hk (T.subtype hTK)
    (H.subgroupOf K) (fun _ hx => hTH hx)
  have hLN : H ⊓ K ≤ normalizer (T : Set G) := by
    intro x hx
    have hh := hlocal (show (⟨x, hx.2⟩ : K) ∈ H.subgroupOf K from hx.1)
    change (⟨x, hx.2⟩ : K) ∈ normalizer ((T : Subgroup G).subgroupOf K) at hh
    rw [← subgroupOf_normalizer_eq hTK] at hh
    exact hh
  exact normalizes_of_intermediate T (H ⊓ K) H (le_inf hTH hTK) hLN
    ((le_inf H.le_normalizer hHK).trans inf_normalizer_le_normalizer_inf)

private theorem normalizes_of_local_factor
    (P : Parameters) (hp : P.prime = 2) (hq : 3 < P.q) (a : Node)
    (T : Sylow 2 (Carrier P)) (H : Subgroup (Carrier P))
    (hsolv : Group.IsSolvable H) (hTH : (T : Subgroup (Carrier P)) ≤ H)
    (hTK : (T : Subgroup (Carrier P)) ≤ localFactor P a)
    (hHK : H ≤ normalizer (localFactor P a : Set (Carrier P))) :
    H ≤ normalizer (T : Set (Carrier P)) := by
  let _ : Group.IsSolvable H := hsolv
  cases a with
  | arms =>
      let _ : CharP (ExtensionField P) 2 := hp ▸ inferInstance
      let e := localFactorArmsQuotientEquivPSL2 P hp
      let qmk := QuotientGroup.mk' (pCore 2 (localFactor P .arms))
      let f := e.toMonoidHom.comp qmk
      have hf : Function.Surjective f := by
        exact e.surjective.comp (QuotientGroup.mk'_surjective _)
      have hker : f.ker = pCore 2 (localFactor P .arms) := by
        change (e.toMonoidHom.comp qmk).ker = _
        rw [MonoidHom.ker_comp_of_injective qmk e.toMonoidHom e.injective,
          QuotientGroup.ker_mk']
      have hF : 3 < Nat.card (ExtensionField P) := by
        rw [card_extensionField]
        exact lt_of_lt_of_le hq (Nat.le_pow (a := P.q) (b := 3) (by omega))
      apply normalizes_of_local_factor_projection hF (localFactor P .arms) H f hf
        (hker ▸ pCore_isPGroup) T hTH hTK
      exact hHK
  | central =>
      let _ : CharP (GaloisField P.prime P.exponent) 2 := hp ▸ inferInstance
      let e := localFactorCentralQuotientEquivPSL2 P hp
      let qmk := QuotientGroup.mk' (pCore 2 (localFactor P .central))
      let f := e.toMonoidHom.comp qmk
      have hf : Function.Surjective f := by
        exact e.surjective.comp (QuotientGroup.mk'_surjective _)
      have hker : f.ker = pCore 2 (localFactor P .central) := by
        change (e.toMonoidHom.comp qmk).ker = _
        rw [MonoidHom.ker_comp_of_injective qmk e.toMonoidHom e.injective,
          QuotientGroup.ker_mk']
      have hF : 3 < Nat.card (GaloisField P.prime P.exponent) := by
        simpa only [card_baseField] using hq
      apply normalizes_of_local_factor_projection hF (localFactor P .central) H f hf
        (hker ▸ pCore_isPGroup) T hTH hTK
      exact hHK

private theorem product_card
    {G : Type*} [Group G] [Finite G]
    (A U : Subgroup G) (hperm : (A : Set G) * (U : Set G) = (U : Set G) * (A : Set G))
    (hdisj : Disjoint A U) :
    Nat.card (A ⊔ U : Subgroup G) = Nat.card A * Nat.card U := by
  have hc := Subgroup.card_set_mul_mul_card_inf A U
  rw [hdisj.eq_bot, Subgroup.card_bot, mul_one] at hc
  rw [← coe_sup_of_set_mul_comm A U hperm] at hc
  exact hc

private theorem product_prime_divisors
    {G : Type*} [Group G] [Finite G]
    (A U : Subgroup G) (hperm : (A : Set G) * (U : Set G) = (U : Set G) * (A : Set G))
    (hdisj : Disjoint A U) (hA : IsPGroup 3 A) (hU : IsPGroup 2 U)
    {p : ℕ} (hp : p.Prime) (hd : p ∣ Nat.card (A ⊔ U : Subgroup G)) :
    p = 2 ∨ p = 3 := by
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [product_card A U hperm hdisj] at hd
  rcases hp.dvd_mul.mp hd with hAcard | hUcard
  · obtain ⟨n, hn⟩ := hA.exists_card_eq
    rw [hn] at hAcard
    exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp
      (hp.dvd_of_dvd_pow hAcard) |>.resolve_left hp.ne_one)
  · obtain ⟨n, hn⟩ := hU.exists_card_eq
    rw [hn] at hUcard
    exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp
      (hp.dvd_of_dvd_pow hUcard) |>.resolve_left hp.ne_one)

private theorem two_core_ne_bot
    {G : Type*} [Group G] [Finite G]
    (A U : Subgroup G)
    (hperm : (A : Set G) * (U : Set G) = (U : Set G) * (A : Set G))
    (hdisj : Disjoint A U) (hA : IsPGroup 3 A) (hU : IsPGroup 2 U)
    (hsolv : Group.IsSolvable (A ⊔ U : Subgroup G))
    (hAcard : Nat.card A ≤ 27) (h64 : 64 ∣ Nat.card (A ⊔ U : Subgroup G)) :
    pCore 2 (A ⊔ U : Subgroup G) ≠ ⊥ := by
  let H := A ⊔ U
  have hthree : Nat.card (pCore 3 H) ≤ 27 := by
    have hd := (pCore 3 H).card_subgroup_dvd_card
    have hcop := IsPGroup.coprime_card_of_ne 3 2 (by decide)
      (pCore 3 H) U pCore_isPGroup hU
    have hdiv : Nat.card (pCore 3 H) ∣ Nat.card A := by
      rw [show Nat.card H = Nat.card A * Nat.card U by
        exact product_card A U hperm hdisj] at hd
      exact hcop.dvd_of_dvd_mul_right (by simpa [H] using hd)
    exact (Nat.le_of_dvd Nat.card_pos hdiv).trans hAcard
  exact twoCore_ne_bot_of_solvable_small_three_core hsolv
    (fun p hp hd => product_prime_divisors A U hperm hdisj hA hU hp hd)
    hthree h64

private theorem remove_conjugator
    {G : Type*} [Group G] [Finite G]
    (P : Subgroup G) (U : Subgroup G) (H : Subgroup G)
    (S : Sylow 2 G) (hSU : (S : Subgroup G) = U)
    (hSP : (S : Subgroup G) ≤ P) (hHP : U ≤ H)
    {g : G} (hg : H.map (MulAut.conj g).toMonoidHom ≤ P)
    (hNP : normalizer (U : Set G) ≤ P) : H ≤ P := by
  let Sg : Sylow 2 G := S.mapSurjective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).surjective
  have hSgP : (Sg : Subgroup G) ≤ P := by
    change (S : Subgroup G).map (MulAut.conj g).toMonoidHom ≤ P
    rw [hSU]
    exact (Subgroup.map_mono hHP).trans hg
  let Sp : Sylow 2 P := S.subtype hSP
  let Sgp : Sylow 2 P := Sg.subtype hSgP
  obtain ⟨p, hp⟩ := MulAction.exists_smul_eq P Sgp Sp
  have hps : p • Sg = S := by
    apply Sylow.subtype_injective (N := P)
    calc
      (p • Sg).subtype _ = p • Sgp := (Sylow.smul_subtype hSgP p).symm
      _ = Sp := hp
  have hconjS : (Sg : Subgroup G).map (MulAut.conj (p : G)).toMonoidHom =
      (S : Subgroup G) := by
    have hh := congrArg Sylow.toSubgroup hps
    change (MulAut.conj (p : G) • (Sg : Subgroup G)) = (S : Subgroup G) at hh
    exact hh
  have hmap : (U : Subgroup G).map
      ((MulAut.conj (p : G)).toMonoidHom.comp (MulAut.conj g).toMonoidHom) = U := by
    rw [← hSU]
    rw [← map_map]
    have hsg : (Sg : Subgroup G) =
        (S : Subgroup G).map (MulAut.conj g).toMonoidHom := by
      change (S.mapSurjective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).surjective : Subgroup G) = _
      exact Sylow.coe_mapSurjective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).surjective S
    rw [← hsg]
    exact hconjS
  have hpg : (p : G) * g ∈ normalizer (U : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hcomp :
        (MulAut.conj (p : G)).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
          (MulAut.conj ((p : G) * g)).toMonoidHom := by
      ext x
      change (p : G) * (g * x * g⁻¹) * (p : G)⁻¹ =
        ((p : G) * g) * x * ((p : G) * g)⁻¹
      simp [mul_assoc]
    change U.map (MulAut.conj ((p : G) * g)).toMonoidHom = U
    rw [← hcomp]
    exact hmap
  have hgp : g ∈ P := by
    have hpgP : (p : G) * g ∈ P := hNP hpg
    simpa only [inv_mul_cancel_left] using P.mul_mem (P.inv_mem p.property) hpgP
  intro x hx
  have hconj : g * x * g⁻¹ ∈ P := hg (Subgroup.mem_map_of_mem
    (MulAut.conj g).toMonoidHom hx)
  simpa [mul_assoc] using
    P.mul_mem (P.mul_mem (P.inv_mem hgp) hconj) hgp

/-- A solvable overgroup with a nontrivial two-core lies in a genuine root
parabolic.  The order bound on the three-subgroup is the source
odd-complement catalogue premise. -/
theorem le_parabolic
    (f : ℕ) (hf : 0 < f) (A : Subgroup (Carrier (binaryParameters f hf)))
    (hA : IsPGroup 3 A) (_hArank : primeRank 3 A = 2) (hAcard : Nat.card A ≤ 27)
    (hperm : (A : Set (Carrier (binaryParameters f hf))) *
      (unipotent (binaryParameters f hf) : Set _) =
      (unipotent (binaryParameters f hf) : Set _) * (A : Set _))
    (hsolv : Group.IsSolvable (A ⊔ unipotent (binaryParameters f hf) : Subgroup _))
    (_hproper : A ⊔ unipotent (binaryParameters f hf) ≠ ⊤) :
    ∃ a : Node, A ⊔ unipotent (binaryParameters f hf) ≤ parabolic (binaryParameters f hf) a := by
  let P := binaryParameters f hf
  let U := unipotent P
  let H := A ⊔ U
  have hU : IsPGroup 2 U := unipotent_isPGroup_binary P rfl
  have hdisj : Disjoint A U := hA.disjoint_of_coprime hU (by decide)
  have h64 : 64 ∣ Nat.card H := by
    have hcardU : Nat.card U = P.q ^ 12 := card_unipotent_binary P rfl
    have hq : 2 ∣ P.q := by
      rw [show P.q = 2 ^ f by rfl]
      exact dvd_pow_self 2 (by omega)
    rw [show Nat.card H = Nat.card A * Nat.card U by
      exact product_card A U hperm hdisj, hcardU]
    apply dvd_mul_of_dvd_right
    have hpow : 2 ^ 6 ∣ P.q ^ 6 := pow_dvd_pow_of_dvd hq 6
    rw [show (12 : ℕ) = 6 + 6 by decide, pow_add]
    exact dvd_mul_of_dvd_left hpow _
  have hcore : pCore 2 H ≠ ⊥ := two_core_ne_bot A U hperm hdisj hA hU hsolv hAcard h64
  let R := (pCore 2 H).map H.subtype
  have hR : R ≠ ⊥ := by
    intro hR
    apply hcore
    exact ((pCore 2 H).map_eq_bot_iff_of_injective H.subtype_injective).mp hR
  have hRtwo : IsPGroup 2 R := pCore_isPGroup.map H.subtype
  have hHN : H ≤ normalizer (R : Set (Carrier P)) := by
    have hh := (pCore 2 H).le_normalizer_map H.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  obtain ⟨g, a, hg⟩ := normalizer_cover f hf R hR hRtwo
  have hS : (unipotentSylow P rfl : Subgroup (Carrier P)) = U :=
    coe_unipotentSylow P rfl
  have hSUH : (unipotentSylow P rfl : Subgroup (Carrier P)) ≤ H := by
    rw [hS]
    exact le_sup_right
  have hSP : (unipotentSylow P rfl : Subgroup (Carrier P)) ≤ parabolic P a := by
    rw [hS]
    exact (unipotent_le_borel P).trans (borel_le_parabolic P a)
  have hHg : H.map (MulAut.conj g).toMonoidHom ≤ parabolic P a :=
    (map_mono hHN).trans hg
  refine ⟨a, ?_⟩
  apply remove_conjugator (parabolic P a) U H (unipotentSylow P rfl) hS hSP hSUH hHg
  change normalizer (unipotent P : Set _) ≤ parabolic P a
  rw [ConcreteBruhat.normalizer_unipotent_eq_borel P rfl]
  exact borel_le_parabolic P a

/-- The placed parabolic is one of the proper genuine root parabolics. -/
theorem le_proper_parabolic
    (f : ℕ) (hf : 0 < f) (A : Subgroup (Carrier (binaryParameters f hf)))
    (hA : IsPGroup 3 A) (hArank : primeRank 3 A = 2) (hAcard : Nat.card A ≤ 27)
    (hperm : (A : Set (Carrier (binaryParameters f hf))) *
      (unipotent (binaryParameters f hf) : Set _) =
      (unipotent (binaryParameters f hf) : Set _) * (A : Set _))
    (hsolv : Group.IsSolvable (A ⊔ unipotent (binaryParameters f hf) : Subgroup _))
    (hproper : A ⊔ unipotent (binaryParameters f hf) ≠ ⊤) :
    ∃ a : Node,
      A ⊔ unipotent (binaryParameters f hf) ≤ parabolic (binaryParameters f hf) a ∧
        parabolic (binaryParameters f hf) a ≠ ⊤ := by
  obtain ⟨a, ha⟩ := le_parabolic f hf A hA hArank hAcard hperm hsolv hproper
  exact ⟨a, ha, parabolic_ne_top_binary (binaryParameters f hf) rfl a⟩

/-- Over fields of order at least four, the solvable overgroup is in the Borel. -/
theorem le_borel
    (f : ℕ) (hf : 0 < f) (hf2 : 2 ≤ f)
    (A : Subgroup (Carrier (binaryParameters f hf)))
    (hA : IsPGroup 3 A) (hArank : primeRank 3 A = 2) (hAcard : Nat.card A ≤ 27)
    (hperm : (A : Set (Carrier (binaryParameters f hf))) *
      (unipotent (binaryParameters f hf) : Set _) =
      (unipotent (binaryParameters f hf) : Set _) * (A : Set _))
    (hsolv : Group.IsSolvable (A ⊔ unipotent (binaryParameters f hf) : Subgroup _))
    (hproper : A ⊔ unipotent (binaryParameters f hf) ≠ ⊤) :
    A ⊔ unipotent (binaryParameters f hf) ≤ borel (binaryParameters f hf) := by
  let P := binaryParameters f hf
  let U := unipotent P
  let H := A ⊔ U
  have hq4 : 4 ≤ P.q := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by decide) hf2
      _ = P.q := by rfl
  have hq3 : 3 < P.q := lt_of_lt_of_le (by decide) hq4
  obtain ⟨a, hpar⟩ := le_parabolic f hf A hA hArank hAcard hperm hsolv hproper
  have hS : (unipotentSylow P rfl : Subgroup (Carrier P)) = U :=
    coe_unipotentSylow P rfl
  have hSUH : (unipotentSylow P rfl : Subgroup (Carrier P)) ≤ H := by
    rw [hS]
    exact le_sup_right
  have hSK : (unipotentSylow P rfl : Subgroup (Carrier P)) ≤ localFactor P a :=
    unipotentSylow_le_localFactor P rfl a
  have hHK : H ≤ normalizer (localFactor P a : Set (Carrier P)) :=
    hpar.trans (Subgroup.le_normalizer_of_normal_subgroupOf
      (localFactor_le_parabolic (binaryParameters f hf) a))
  have hnorm := normalizes_of_local_factor P rfl hq3 a
    (unipotentSylow P rfl) H hsolv hSUH hSK hHK
  change (A ⊔ U : Subgroup (Carrier P)) ≤
    normalizer ((unipotentSylow P rfl : Subgroup (Carrier P)) : Set (Carrier P)) at hnorm
  have hnormU : H ≤ normalizer (U : Set (Carrier P)) := by
    simpa only [hS] using hnorm
  rw [ConcreteBruhat.normalizer_unipotent_eq_borel P rfl] at hnormU
  simpa [P, H, U] using hnormU

end Triality.Standard.ThreeOvergroupPlacement

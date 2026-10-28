module

public import CFSG.Quasithin.ChapterE.Defs
public import CFSG.Quasithin.ChapterE.Section01.MinimalSupplement
public import CFSG.Quasithin.ChapterE.Section01.MinimalStructure.Frattini
public import CFSG.Quasithin.ChapterE.Section01.MinimalStructure.Kernel
public import Theory.GroupTheory.Hall.Existence
public import Theory.GroupTheory.PiCore
public import Mathlib.Algebra.Group.PUnit

/-!
# Odd-prime core series of minimal supplements

For a minimal supplement `K` over a Sylow two-subgroup `T`, suppose the
actual image of `K ∩ X` in `G/Y` is a two-group extended by a `p`-group,
where `p` is odd. Then `K = O₂,p,₂(K)`, expressed by the intrinsic quotient
by its two-core and then its `p`-core being a two-group.

The image of `K` is solvable and has only the primes two and `p` in its
order. Kernel solvability and Hall's theorem produce a Hall `{2,p}`
subgroup containing the prescribed Sylow subgroup. Its image is all of
`Kbar`, so minimality forces it to be `K`. Next, the Sylow intersection
in `K ∩ X` maps into `O₂(Kbar)`. The Frattini preimage theorem makes this
intersection normal in `K`, hence contained in `O₂(K)`. Thus the image
of `K ∩ X` in `K/O₂(K)` is a normal `p`-group; the final quotient is the
image of `T`.

All cores are intrinsic to their indicated groups, and normality of `K`
in the ambient group is not assumed.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.10(3), printed p.211.
-/

public section
namespace CFSG.Quasithin.ChapterE
open Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem pi_of_pGroup {r : ℕ} [Fact r.Prime] {π : Set Nat.Primes}
    (h : IsPGroup r G) (hr : (⟨r, Fact.out⟩ : Nat.Primes) ∈ π) : IsPiGroup π G := by
  rw [IsPiGroup_iff]
  intro s hs
  obtain ⟨n, hn⟩ := h.exists_card_eq
  have he : s.val = r := (Nat.prime_dvd_prime_iff_eq s.property Fact.out).mp
    (s.property.dvd_of_dvd_pow (hn ▸ hs))
  exact (show s = ⟨r, Fact.out⟩ from Subtype.ext he) ▸ hr

private theorem pGroup_of_twoPrime_odd {p : ℕ} [Fact p.Prime]
    (h : IsPiGroup {r : Nat.Primes | r.val = 2 ∨ r.val = p} G)
    (hodd : ¬ 2 ∣ Nat.card G) : IsPGroup p G := by
  apply (isPGroup_iff_primeFactors_card_subset (Fact.out : p.Prime).ne_zero).mpr
  intro r hr
  have hrp := Nat.prime_of_mem_primeFactors hr
  have hrd := Nat.dvd_of_mem_primeFactors hr
  have he := (IsPiGroup_iff _ G).mp h ⟨r, hrp⟩ hrd
  rcases he with he | he
  · exact (hodd (he ▸ hrd)).elim
  · change r = p at he
    subst r
    exact Nat.mem_primeFactors.mpr ⟨Fact.out, dvd_rfl, (Fact.out : p.Prime).ne_zero⟩

omit [Finite G] in
private theorem two_subgroup_le_core_of_odd_quotient {p : ℕ} [Fact p.Prime]
    (hp : 2 ≠ p) {N H : Subgroup G} [N.Normal]
    (hN : IsPGroup p (N ⧸ pCore 2 N)) {P : Subgroup H}
    (hP : IsPGroup 2 P) (hPN : P.map H.subtype ≤ N) :
    P ≤ pCore 2 H := by
  let q := QuotientGroup.mk' (pCore 2 N)
  let D := (P.map H.subtype).subgroupOf N
  have hD : IsPGroup 2 D := (hP.map H.subtype).comap_of_injective
    N.subtype N.subtype_injective
  have hbot : D.map q = ⊥ :=
    disjoint_self.mp (IsPGroup.disjoint_of_ne 2 p hp _ _ (hD.map q)
      (hN.to_subgroup (D.map q)))
  have hle : D ≤ pCore 2 N := by
    have hh := Subgroup.map_le_iff_le_comap.mp (le_of_eq hbot)
    simpa only [q, MonoidHom.comap_bot, QuotientGroup.ker_mk'] using hh
  have hPD : P.map H.subtype ≤ (pCore 2 N).map N.subtype := by
    rw [← map_subgroupOf_eq_of_le hPN]
    exact map_mono hle
  have hc : ((pCore 2 N).map N.subtype).subgroupOf H ≤ pCore 2 H :=
    le_sSup ⟨inferInstance, (pCore_isPGroup.map N.subtype).comap_of_injective
      H.subtype H.subtype_injective⟩
  intro x hx
  exact hc (hPD ⟨x, hx, rfl⟩)

/-- The image is a solvable `{2,p}`-group by the normal-product identity. -/
private theorem image_solvable_and_twoPrime (T : Sylow 2 G)
    {X Y K : Subgroup G} [X.Normal] [Y.Normal]
    (h : IsMinimalSupplement (T : Subgroup G) X Y K) (hYX : Y ≤ X)
    {p : ℕ} [Fact p.Prime]
    (hp : IsPGroup p (((K ⊓ X).map (QuotientGroup.mk' Y)) ⧸
      pCore 2 ((K ⊓ X).map (QuotientGroup.mk' Y)))) :
    Group.IsSolvable (K.map (QuotientGroup.mk' Y)) ∧
    IsPiGroup {r : Nat.Primes | r.val = 2 ∨ r.val = p}
      (K.map (QuotientGroup.mk' Y)) := by
  let q := QuotientGroup.mk' Y
  let A := (K ⊓ X).map q
  let R := (T : Subgroup G).map q
  let π : Set Nat.Primes := {r | r.val = 2 ∨ r.val = p}
  have hA : A = X.map q := h.map_inf_eq hYX
  have : A.Normal := hA ▸ Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective Y)
  have he : K.map q = A ⊔ R := by
    conv_lhs => rw [h.eq_inf_sup]
    exact Subgroup.map_sup _ _ _
  have hR2 : IsPGroup 2 R := T.isPGroup'.map q
  let : Group.IsNilpotent (pCore 2 A) := pCore_isPGroup.isNilpotent
  let : Group.IsNilpotent (A ⧸ pCore 2 A) := hp.isNilpotent
  let : Group.IsSolvable A := (Group.isSolvable_iff_subgroup_quotient (pCore 2 A)).mpr
    ⟨inferInstance, inferInstance⟩
  let : Group.IsNilpotent R := hR2.isNilpotent
  have hApi : IsPiGroup π A := IsPiGroup.of_normal_subgroup_and_quotient
    (pCore 2 A) ((pi_of_pGroup pCore_isPGroup (Or.inl rfl)).isPiSubgroup _)
    (pi_of_pGroup hp (Or.inr rfl))
  have hRpi : IsPiGroup π R := pi_of_pGroup hR2 (Or.inl rfl)
  constructor
  · rw [he]
    exact Group.isSolvable_sup_of_normal_left A R
  · rw [he]
    exact (IsPiSubgroup.sup_of_normal_right (hRpi.isPiSubgroup R)
      (hApi.isPiSubgroup A)).isPiGroup (R ⊔ A) |>.of_equiv
      (MulEquiv.subgroupCongr (sup_comm A R))

/-- A Hall subgroup containing the prescribed Sylow subgroup covers the
image, so minimality makes the whole supplement a `{2,p}`-group. -/
private theorem IsMinimalSupplement.twoPrime_of_image (T : Sylow 2 G)
    {X Y K : Subgroup G} [Y.Normal]
    (h : IsMinimalSupplement (T : Subgroup G) X Y K) {p : ℕ}
    (hs : Group.IsSolvable (K.map (QuotientGroup.mk' Y)))
    (hi : IsPiGroup {r : Nat.Primes | r.val = 2 ∨ r.val = p}
      (K.map (QuotientGroup.mk' Y))) :
    IsPiGroup {r : Nat.Primes | r.val = 2 ∨ r.val = p} K := by
  classical
  let f := (QuotientGroup.mk' Y).subgroupMap K
  have hf := (QuotientGroup.mk' Y).subgroupMap_surjective K
  have hker : f.ker = Y.subgroupOf K := by
    ext k
    change (f k = 1) ↔ (k : G) ∈ Y
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff (k : G)
  let : Group.IsSolvable f.ker := hker ▸ h.isSolvable_kernel T
  let : Group.IsSolvable (K.map (QuotientGroup.mk' Y)) := hs
  have hsolv : Group.IsSolvable K := Group.isSolvable_of_ker_le_range
    f.ker.subtype f (by rw [f.ker.range_subtype])
  let S : Sylow 2 K := T.subtype h.1.1
  let π : Set Nat.Primes := {r | r.val = 2 ∨ r.val = p}
  let : MulDistribMulAction Unit K := {
    smul _ x := x
    one_smul _ := rfl
    mul_smul _ _ _ := rfl
    smul_one _ := rfl
    smul_mul _ _ _ := rfl }
  have hSinv : IsInvariant Unit K (S : Subgroup K) := ⟨fun _ _ => Iff.rfl⟩
  obtain ⟨L, hL, _, hSL⟩ := exists_isHallSubgroup_isInvariant_of_isPiSubgroup
    (A := Unit) hsolv (by simp) π (S : Subgroup K)
    ((pi_of_pGroup S.isPGroup' (Or.inl rfl)).isPiSubgroup _) hSinv
  have hLf : L.map f = ⊤ := by
    apply Subgroup.index_eq_one.mp
    apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
    intro r hr hrd
    have hmem := (IsPiGroup_iff _ _).mp hi ⟨r, hr⟩
      (hrd.trans (L.map f).index_dvd_card)
    exact hL.p_in_pi_of_p_dvd_index ⟨r, hr⟩ (hrd.trans (L.index_map_dvd hf)) hmem
  have hLtop : L = ⊤ := h.eq_top_of_map_eq_top L hSL hLf
  apply (IsPiGroup_iff _ _).mpr
  intro r hr
  exact hL.p_in_pi_of_p_dvd_card r (by simpa [hLtop] using hr)

/-- The Sylow intersection in `K ∩ X` is normal in `K`: it is the
intersection with `X` of the normal Sylow subgroup in the two-core preimage. -/
private theorem IsMinimalSupplement.normal_sylow_inf_X (T : Sylow 2 G)
    {X Y K : Subgroup G} [X.Normal] [Y.Normal]
    (h : IsMinimalSupplement (T : Subgroup G) X Y K) (hYX : Y ≤ X)
    {p : ℕ} [Fact p.Prime] (hpne : 2 ≠ p)
    (hp : IsPGroup p (((K ⊓ X).map (QuotientGroup.mk' Y)) ⧸
      pCore 2 ((K ⊓ X).map (QuotientGroup.mk' Y)))) :
    ((T : Subgroup G).subgroupOf K ⊓ X.subgroupOf K).Normal := by
  let q := QuotientGroup.mk' Y
  let I := K.map q
  let A := (K ⊓ X).map q
  let f := q.subgroupMap K
  let S : Sylow 2 K := T.subtype h.1.1
  let W := X.subgroupOf K
  let P := (S : Subgroup K) ⊓ W
  let Z := (pCore 2 I).comap f
  have hA : A = X.map q := h.map_inf_eq hYX
  have : A.Normal := hA ▸ Subgroup.Normal.map inferInstance q
    (QuotientGroup.mk'_surjective Y)
  have hP2 : IsPGroup 2 P := S.isPGroup'.to_le inf_le_left
  have hPA : (P.map f).map I.subtype ≤ A := by
    rintro _ ⟨b, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨(k : G), ⟨k.property, hk.2⟩, rfl⟩
  have hPZ : P ≤ Z := Subgroup.map_le_iff_le_comap.mp
    (two_subgroup_le_core_of_odd_quotient hpne hp (hP2.map f) hPA)
  have hn : ((S : Subgroup K) ⊓ Z).Normal :=
    h.normal_inf_preimage T (pCore 2 I) pCore_isPGroup
  have he : P = ((S : Subgroup K) ⊓ Z) ⊓ W := by
    apply le_antisymm
    · exact le_inf (le_inf inf_le_left hPZ) inf_le_right
    · exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
  change P.Normal
  rw [he]
  infer_instance

/-- E.1.10(3): if `KbarX/O₂(KbarX)` is a `p`-group for an odd prime `p`,
then `K = O₂,p,₂(K)`. The conclusion uses successive intrinsic cores. -/
theorem IsMinimalSupplement.oddSeries (T : Sylow 2 G)
    {X Y K : Subgroup G} [X.Normal] [Y.Normal]
    (h : IsMinimalSupplement (T : Subgroup G) X Y K) (hYX : Y ≤ X)
    {p : ℕ} [Fact p.Prime] (hpne : p ≠ 2)
    (hp : IsPGroup p (((K ⊓ X).map (QuotientGroup.mk' Y)) ⧸
      pCore 2 ((K ⊓ X).map (QuotientGroup.mk' Y)))) :
    IsPGroup 2 ((K ⧸ pCore 2 K) ⧸ pCore p (K ⧸ pCore 2 K)) := by
  obtain ⟨his, hip⟩ := image_solvable_and_twoPrime T h hYX hp
  have hKpi := h.twoPrime_of_image T his hip
  let S : Sylow 2 K := T.subtype h.1.1
  let W := X.subgroupOf K
  have hn : ((S : Subgroup K) ⊓ W).Normal := h.normal_sylow_inf_X T hYX hpne.symm hp
  have hPcore : (S : Subgroup K) ⊓ W ≤ pCore 2 K :=
    le_sSup ⟨hn, S.isPGroup'.to_le inf_le_left⟩
  let q₂ := QuotientGroup.mk' (pCore 2 K)
  obtain ⟨R, hR⟩ := S.exists_subgroupOf_eq_of_normal W
  have hRle : (R : Subgroup W) ≤ (pCore 2 K).subgroupOf W := by
    intro w hw
    rw [hR] at hw
    exact hPcore ⟨hw, w.property⟩
  have hd : Nat.card (W.map q₂) ∣ R.index := by
    rw [← relIndex_ker W q₂, QuotientGroup.ker_mk']
    exact index_dvd_of_le hRle
  have hodd : ¬ 2 ∣ Nat.card (W.map q₂) := fun hh => R.not_dvd_index (hh.trans hd)
  have hWp : IsPGroup p (W.map q₂) := pGroup_of_twoPrime_odd
    ((hKpi.quotient (pCore 2 K)).of_injective
      (W.map q₂).subtype (W.map q₂).subtype_injective) hodd
  have : (W.map q₂).Normal := Subgroup.Normal.map inferInstance q₂
    (QuotientGroup.mk'_surjective _)
  have hWcore : W.map q₂ ≤ pCore p (K ⧸ pCore 2 K) := le_sSup ⟨inferInstance, hWp⟩
  let q := (QuotientGroup.mk' (pCore p (K ⧸ pCore 2 K))).comp q₂
  have hWkill : W.map q = ⊥ := by
    change W.map ((QuotientGroup.mk' _).comp q₂) = ⊥
    rw [← Subgroup.map_map]
    apply le_bot_iff.mp
    apply Subgroup.map_le_iff_le_comap.mpr
    simpa only [MonoidHom.comap_bot, QuotientGroup.ker_mk'] using hWcore
  have hWS : W ⊔ (S : Subgroup K) = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    simp only [Subgroup.map_sup, W, S, Sylow.coe_subtype, subgroupOf_map_subtype,
      inf_eq_left.mpr h.1.1]
    rw [inf_comm X K, ← h.eq_inf_sup]
    rw [← MonoidHom.range_eq_map, K.range_subtype]
  have hq : Function.Surjective q := (QuotientGroup.mk'_surjective _).comp
    (QuotientGroup.mk'_surjective _)
  have hStop : (S : Subgroup K).map q = ⊤ := by
    have he := congrArg (Subgroup.map q) hWS
    rwa [Subgroup.map_sup, hWkill, bot_sup_eq, map_top_of_surjective q hq] at he
  have h2 := S.isPGroup'.map q
  rw [hStop] at h2
  exact h2.of_equiv Subgroup.topEquiv

end CFSG.Quasithin.ChapterE

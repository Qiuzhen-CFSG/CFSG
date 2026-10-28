module

public import CFSG.Quasithin.Chapter2.Section05.A6ShadowConstruction.Initial
public import Theory.GroupTheory.SpecificGroups.CyclicInvertedDihedral

/-!
# Algebra for the terminal A₆ normalizer calculation

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed
pp.569–570, following Lemma 2.5.27.

The cyclic-core reduction makes each conjugate reflection invert an actual
cyclic four-group. This proves its dihedral extension and separates that
extension from `K`. It also separates `Eˣ` from `K`, so that `K ∩ EEˣ = E`.
Normality of `K` in `H` then gives one inclusion of the normalizer equality.

The other inclusion follows from generation of `N_H(E)` once the conjugate
reflection centralizes `N_K(E)`. The final order computation uses the genuine
Sylow assertion in the incoming setup. Choosing `E`, proving its stability
under `x²`, and computing the action normalizer remain separate obligations;
none of these lemmas assumes that the source theorem has been established.
-/

namespace CFSG.Quasithin.Chapter2.A6ShadowConstruction
namespace NormalizerCalculation

open Subgroup
open scoped Pointwise
variable {G : Type*} [Group G]

/-- The centralizer core meets the actual A₆ subgroup trivially. -/
public theorem core_disjoint_k (d : Setup G) : Disjoint d.core d.K := by
  apply disjoint_def.mpr
  intro g hgC hgK
  have hgZ : (⟨g, hgK⟩ : d.K) ∈ center d.K := by
    apply mem_center_iff.mpr
    intro k
    exact Subtype.ext (hgC.2 k k.property)
  have hp := (centerCongr d.modelK ⟨⟨g, hgK⟩, hgZ⟩).property
  change d.modelK ⟨g, hgK⟩ ∈ center (alternatingGroup (Fin 6)) at hp
  rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at hp
  have hg := d.modelK.injective (hp.trans d.modelK.map_one.symm)
  exact congrArg Subtype.val hg

/-- The cyclic four-core contains an element distinct from its inverse. -/
public theorem core_not_exponent_two (d : Setup G) (r : CoreReduction d) :
    ∃ v ∈ d.core, v ≠ v⁻¹ := by
  obtain ⟨f⟩ := r.cyclic
  let a : Multiplicative (ZMod 4) := Multiplicative.ofAdd 1
  refine ⟨f.symm a, (f.symm a).property, ?_⟩
  intro he
  have h : f.symm a = (f.symm a)⁻¹ := Subtype.ext he
  have hh : a = a⁻¹ := by simpa only [map_inv, f.apply_symm_apply] using congrArg f h
  exact (by decide : a ≠ a⁻¹) hh

/-- A conjugate reflection acts nontrivially on the cyclic core. -/
public theorem conjugate_not_centralizer (d : Setup G) (r : CoreReduction d)
    (E : Subgroup G) [IsKleinFour E] (hE : E ≤ d.sk)
    {e : G} (he : e ∈ E) (heout : e ∉ zpowers d.zK) :
    d.x⁻¹ * e * d.x ∉ centralizer (d.core : Set G) := by
  intro hc
  obtain ⟨v, hv, hvne⟩ := core_not_exponent_two d r
  have hi := r.inverts E hE inferInstance e he heout v hv
  apply hvne
  calc
    v = (d.x⁻¹ * e * d.x)⁻¹ * v * (d.x⁻¹ * e * d.x) := by
      rw [mul_assoc, hc v hv]
      group
    _ = v⁻¹ := hi

/-- Every four-group conjugate is disjoint from the actual `K`. -/
public theorem conjugate_disjoint_k (d : Setup G) (r : CoreReduction d)
    (E : Subgroup G) [IsKleinFour E] (hE : E ≤ d.sk) :
    Disjoint (conjugate d.x E) d.K := by
  apply disjoint_def.mpr
  rintro g ⟨e, he, rfl⟩ hgK
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv] at hgK ⊢
  by_cases heZ : e ∈ zpowers d.zK
  · have hzmap : conjugate d.x (zpowers d.zK) = zpowers d.t := by
      unfold conjugate
      rw [MonoidHom.map_zpowers]
      congr 1
      simpa using d.zK_conjugate
    have hgC : d.x⁻¹ * e * d.x ∈ d.core := by
      apply (zpowers_le.mpr d.t_mem : zpowers d.t ≤ d.core)
      rw [← hzmap]
      exact ⟨e, heZ, by simp⟩
    exact disjoint_def.mp (core_disjoint_k d) hgC hgK
  · exfalso
    apply conjugate_not_centralizer d r E hE he heZ
    intro v hv
    exact (hv.2 _ hgK).symm

/-- The original four-group is recovered by intersecting its product with `K`. -/
public theorem product_inf_k [Finite G] (d : Setup G) (r : CoreReduction d)
    (E : Subgroup G) [IsKleinFour E] (hE : E ≤ d.sk) :
    (E ⊔ conjugate d.x E) ⊓ d.K = E := by
  have hcomm : E ≤ centralizer (conjugate d.x E : Set G) := by
    intro a ha b hb
    exact d.sk_centralizes_conjugate (hE ha) b (map_mono hE hb)
  obtain ⟨m, hm⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    E (conjugate d.x E) (d.disjoint_sk_conjugate.mono hE (map_mono hE)) hcomm
  apply le_antisymm
  · rintro g ⟨hgA, hgK⟩
    obtain ⟨⟨a, b⟩, hab⟩ := m.surjective ⟨g, hgA⟩
    have hab' : (a : G) * b = g := (hm a b).symm.trans (congrArg Subtype.val hab)
    have hbK : (b : G) ∈ d.K := by
      have hb : (b : G) = (a : G)⁻¹ * g := by rw [← hab']; group
      rw [hb]
      exact d.K.mul_mem (d.K.inv_mem (hE a.property).2) hgK
    have hb1 := disjoint_def.mp (conjugate_disjoint_k d r E hE) b.property hbK
    rw [hb1, mul_one] at hab'
    exact hab' ▸ a.property
  · exact le_inf le_sup_left (hE.trans inf_le_right)

/-- The conjugate reflection and the cyclic core generate an actual dihedral eight-group. -/
public theorem conjugate_dihedral [Finite G] (d : Setup G) (r : CoreReduction d)
    (E : Subgroup G) [IsKleinFour E] (hE : E ≤ d.sk)
    {e : G} (he : e ∈ E) (heout : e ∉ zpowers d.zK) :
    Nonempty ((zpowers (d.x⁻¹ * e * d.x) ⊔ d.core : Subgroup G) ≃*
      DihedralGroup 4) := by
  obtain ⟨f⟩ := r.cyclic
  let : IsCyclic d.core := isCyclic_of_injective f.toMonoidHom f.injective
  have hcard : Nat.card d.core = 4 := by
    rw [Nat.card_congr f.toEquiv]
    simp
  have he2 : e ^ 2 = 1 := by
    simpa only [pow_two, coe_mul, coe_one] using congrArg Subtype.val (IsKleinFour.mul_self (⟨e, he⟩ : E))
  have hex2 : (d.x⁻¹ * e * d.x) ^ 2 = 1 := by
    have hh : ((MulAut.conj d.x⁻¹) e) ^ 2 = 1 := by rw [← map_pow, he2, map_one]
    simpa using hh
  have hexC : d.x⁻¹ * e * d.x ∉ d.core := by
    intro hc
    apply conjugate_not_centralizer d r E hE he heout
    intro v hv
    have hh : (⟨v, hv⟩ : d.core) * ⟨_, hc⟩ = ⟨_, hc⟩ * (⟨v, hv⟩ : d.core) := by
      apply f.injective
      simp only [map_mul]
      exact mul_comm _ _
    exact congrArg Subtype.val hh
  have hexinv : (d.x⁻¹ * e * d.x)⁻¹ = d.x⁻¹ * e * d.x :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hex2)
  have hi : ∀ v ∈ d.core,
      (d.x⁻¹ * e * d.x) * v * (d.x⁻¹ * e * d.x)⁻¹ = v⁻¹ := by
    intro v hv
    simpa only [hexinv] using r.inverts E hE inferInstance e he heout v hv
  have hh := nonempty_mulEquiv_dihedralGroup_of_cyclic_inverted
    d.core (d.x⁻¹ * e * d.x) inferInstance hex2 hexC hi
  rwa [hcard, sup_comm] at hh

/-- Relative normality of `K` gives the first normalizer inclusion. -/
public theorem normalizer_le [Finite G] (d : Setup G) (r : CoreReduction d)
    (E : Subgroup G) [IsKleinFour E] (hE : E ≤ d.sk) :
    d.H ⊓ normalizer ((E ⊔ conjugate d.x E : Subgroup G) : Set G) ≤
      d.H ⊓ normalizer (E : Set G) := by
  have hKH : d.K ≤ d.H := by rw [d.generated]; exact le_sup_left
  have hHN := (normal_subgroupOf_iff_le_normalizer hKH).mp d.normalK
  intro g hg
  refine ⟨hg.1, ?_⟩
  rw [← product_inf_k d r E hE]
  exact inf_normalizer_le_normalizer_inf ⟨hg.2, hHN hg.1⟩

/-- The action kernel makes the core normal inside `H`. -/
public theorem core_normalized (d : Setup G) :
    d.H ≤ normalizer (d.core : Set G) := by
  have hCH : d.core ≤ d.H := by
    rw [d.generated]
    exact inf_le_left.trans le_sup_right
  have hn : (d.core.subgroupOf d.H).Normal := by
    change ((d.S ⊓ centralizer (d.K : Set G)).subgroupOf d.H).Normal
    rw [← d.action_kernel]
    infer_instance
  exact (normal_subgroupOf_iff_le_normalizer hCH).mp hn

/-- Conjugating a subgroup of `S` by the specified `x` stays inside `S`. -/
public theorem conjugate_le_s (d : Setup G) {E : Subgroup G} (hE : E ≤ d.S) :
    conjugate d.x E ≤ d.S := by
  have hS : conjugate d.x d.S = d.S :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (d.S : Set G)).inv_mem d.x_normalizes)
  exact hS ▸ map_mono hE

private theorem mem_zpowers_two [Finite G] {s y : G}
    (hs : s ^ 2 = 1) (hy : y ∈ zpowers s) : y = 1 ∨ y = s := by
  classical
  by_cases hs1 : s = 1
  · simpa [hs1] using hy
  have hord : orderOf s = 2 := orderOf_eq_prime hs hs1
  rw [mem_zpowers_iff_mem_range_orderOf, hord] at hy
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hy
  have hnlt : n < 2 := Finset.mem_range.mp hn
  interval_cases n <;> simp

/-- The entire dihedral factor is disjoint from `K`, hence from `N_K(E)`. -/
public theorem factors_disjoint [Finite G] (d : Setup G) (r : CoreReduction d)
    (E : Subgroup G) [IsKleinFour E] (hE : E ≤ d.sk)
    {e : G} (he : e ∈ E) (heout : e ∉ zpowers d.zK) :
    Disjoint (zpowers (d.x⁻¹ * e * d.x) ⊔ d.core) d.K := by
  let s := d.x⁻¹ * e * d.x
  have hsS : s ∈ d.S := conjugate_le_s d (hE.trans inf_le_left)
    (show s ∈ conjugate d.x E from ⟨e, he, by simp [s]⟩)
  have hSH : d.S ≤ d.H := by rw [d.generated]; exact le_sup_right
  have hsN : zpowers s ≤ normalizer (d.core : Set G) :=
    zpowers_le.mpr (core_normalized d (hSH hsS))
  have hs2 : s ^ 2 = 1 := by
    have he2 : e ^ 2 = 1 := by
      simpa only [pow_two, coe_mul, coe_one] using
        congrArg Subtype.val (IsKleinFour.mul_self (⟨e, he⟩ : E))
    have hh : ((MulAut.conj d.x⁻¹) e) ^ 2 = 1 := by rw [← map_pow, he2, map_one]
    simpa [s] using hh
  have hccomm : d.core ≤ centralizer (d.core : Set G) := by
    obtain ⟨f⟩ := r.cyclic
    intro u hu v hv
    have hh : (⟨v, hv⟩ : d.core) * ⟨u, hu⟩ = ⟨u, hu⟩ * (⟨v, hv⟩ : d.core) := by
      apply f.injective
      simp only [map_mul]
      exact mul_comm _ _
    exact congrArg Subtype.val hh
  apply disjoint_def.mpr
  intro g hg hgK
  have hgprod : g ∈ (d.core : Set G) * (zpowers s : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left d.core (zpowers s) hsN, sup_comm]
    exact hg
  obtain ⟨v, hv, y, hy, rfl⟩ := hgprod
  rcases mem_zpowers_two hs2 hy with rfl | rfl
  · simpa only [mul_one] using
      disjoint_def.mp (core_disjoint_k d) hv (by simpa using hgK)
  · exfalso
    apply conjugate_not_centralizer d r E hE he heout
    have hvs : v * s ∈ centralizer (d.core : Set G) :=
      fun w hw => (hw.2 _ hgK).symm
    have hs : s = v⁻¹ * (v * s) := by group
    change s ∈ centralizer (d.core : Set G)
    rw [hs]
    exact (centralizer (d.core : Set G)).mul_mem
      ((centralizer (d.core : Set G)).inv_mem (hccomm hv)) hvs

/-- All squares in the cyclic four-core lie in the distinguished involution line. -/
public theorem core_square (d : Setup G) (r : CoreReduction d)
    {v : G} (hv : v ∈ d.core) : v ^ 2 ∈ zpowers d.t := by
  obtain ⟨f⟩ := r.cyclic
  let tC : d.core := ⟨d.t, d.t_mem⟩
  have htne : tC ≠ 1 := fun h => d.t_ne_one (congrArg Subtype.val h)
  have ht2 : tC ^ 2 = 1 := Subtype.ext d.t_square
  have hftne : f tC ≠ 1 := fun h => htne (f.injective (h.trans f.map_one.symm))
  have hft2 : (f tC) ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  have htmodel : f tC = Multiplicative.ofAdd (2 : ZMod 4) :=
    (by decide : ∀ a : Multiplicative (ZMod 4), a ≠ 1 → a ^ 2 = 1 →
      a = Multiplicative.ofAdd 2) (f tC) hftne hft2
  have hcases : (f (⟨v, hv⟩ : d.core)) ^ 2 = 1 ∨
      (f (⟨v, hv⟩ : d.core)) ^ 2 = f tC := by
    rw [htmodel]
    exact (by decide : ∀ a : Multiplicative (ZMod 4),
      a ^ 2 = 1 ∨ a ^ 2 = Multiplicative.ofAdd 2) _
  rcases hcases with h | h
  · have h1 : (⟨v, hv⟩ : d.core) ^ 2 = 1 := f.injective (by simpa only [map_pow, map_one] using h)
    rw [show v ^ 2 = 1 from congrArg Subtype.val h1]
    exact (zpowers d.t).one_mem
  · have ht : (⟨v, hv⟩ : d.core) ^ 2 = tC := f.injective (by simpa only [map_pow, map_one] using h)
    rw [show v ^ 2 = d.t from congrArg Subtype.val ht]
    exact mem_zpowers d.t

/-- The central involution and any element outside its line generate the four-group. -/
public theorem four_generators (d : Setup G) (E : Subgroup G) [IsKleinFour E]
    (hz : d.zK ∈ E) {e : G} (he : e ∈ E) (heout : e ∉ zpowers d.zK) :
    E = zpowers d.zK ⊔ zpowers e := by
  have hz1 : d.zK ≠ 1 := by
    intro h
    apply d.t_ne_one
    rw [← d.zK_conjugate, h]
    simp
  have he1 : e ≠ 1 := fun h => heout (h ▸ (zpowers d.zK).one_mem)
  have hez : e ≠ d.zK := fun h => heout (h ▸ mem_zpowers d.zK)
  apply le_antisymm
  · intro g hg
    by_cases hg1 : g = 1
    · exact hg1 ▸ (zpowers d.zK ⊔ zpowers e).one_mem
    by_cases hgz : g = d.zK
    · rw [hgz]
      exact mem_sup_left (mem_zpowers d.zK)
    by_cases hge : g = e
    · rw [hge]
      exact mem_sup_right (mem_zpowers e)
    have heq : (⟨g, hg⟩ : E) = (⟨d.zK, hz⟩ : E) * ⟨e, he⟩ :=
      IsKleinFour.eq_mul_of_ne_all
        (fun h => hz1 (congrArg Subtype.val h))
        (fun h => he1 (congrArg Subtype.val h))
        (fun h => hez (congrArg Subtype.val h).symm)
        (fun h => hg1 (congrArg Subtype.val h))
        (fun h => hgz (congrArg Subtype.val h))
        (fun h => hge (congrArg Subtype.val h))
    have hgze : g = d.zK * e := congrArg Subtype.val heq
    rw [hgze]
    exact (zpowers d.zK ⊔ zpowers e).mul_mem
      (mem_sup_left (mem_zpowers d.zK)) (mem_sup_right (mem_zpowers e))
  · exact sup_le (zpowers_le.mpr hz) (zpowers_le.mpr he)

/-- The conjugate four-group is generated by `t` and the conjugate reflection. -/
public theorem conjugate_generators (d : Setup G) (E : Subgroup G) [IsKleinFour E]
    (hz : d.zK ∈ E) {e : G} (he : e ∈ E) (heout : e ∉ zpowers d.zK) :
    conjugate d.x E = zpowers d.t ⊔ zpowers (d.x⁻¹ * e * d.x) := by
  unfold conjugate
  rw [four_generators d E hz he heout, Subgroup.map_sup, MonoidHom.map_zpowers,
    MonoidHom.map_zpowers]
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv,
    d.zK_conjugate]

/-- Inversion and the square calculation make the core normalize `EEˣ`. -/
public theorem core_normalizes_product (d : Setup G) (r : CoreReduction d)
    (E : Subgroup G) [IsKleinFour E] (hE : E ≤ d.sk)
    (hz : d.zK ∈ E) {e : G} (he : e ∈ E) (heout : e ∉ zpowers d.zK) :
    d.core ≤ normalizer ((E ⊔ conjugate d.x E : Subgroup G) : Set G) := by
  let F := conjugate d.x E
  have htF : zpowers d.t ≤ F := by
    rw [show F = zpowers d.t ⊔ zpowers (d.x⁻¹ * e * d.x) from
      conjugate_generators d E hz he heout]
    exact le_sup_left
  have heF : d.x⁻¹ * e * d.x ∈ F := ⟨e, he, by simp⟩
  have hccomm : d.core ≤ centralizer (d.core : Set G) := by
    obtain ⟨f⟩ := r.cyclic
    intro u hu v hv
    have hh : (⟨v, hv⟩ : d.core) * ⟨u, hu⟩ = ⟨u, hu⟩ * (⟨v, hv⟩ : d.core) := by
      apply f.injective
      simp only [map_mul]
      exact mul_comm _ _
    exact congrArg Subtype.val hh
  have hfwd : ∀ v ∈ d.core, F.map (MulAut.conj v).toMonoidHom ≤ F := by
    intro v hv
    dsimp only [F]
    rw [conjugate_generators d E hz he heout, Subgroup.map_sup,
      MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    apply sup_le
    · apply zpowers_le.mpr
      have htcomm := hccomm hv d.t d.t_mem
      have hconj : (MulAut.conj v) d.t = d.t := by
        simp only [MulAut.conj_apply]
        rw [← htcomm]
        group
      rw [show (MulAut.conj v).toMonoidHom d.t = d.t from hconj]
      exact mem_sup_left (mem_zpowers d.t)
    · apply zpowers_le.mpr
      have hi := r.inverts E hE inferInstance e he heout v hv
      have hswitch : (d.x⁻¹ * e * d.x) * v⁻¹ = v * (d.x⁻¹ * e * d.x) := by
        rw [← hi]
        group
      have hconj : (MulAut.conj v) (d.x⁻¹ * e * d.x) =
          v ^ 2 * (d.x⁻¹ * e * d.x) := by
        simp only [MulAut.conj_apply, pow_two]
        rw [mul_assoc v, hswitch]
        group
      change (MulAut.conj v) (d.x⁻¹ * e * d.x) ∈ _
      rw [hconj]
      exact (zpowers d.t ⊔ zpowers (d.x⁻¹ * e * d.x)).mul_mem
        (mem_sup_left (core_square d r hv)) (mem_sup_right (mem_zpowers _))
  intro v hv
  have hvF : v ∈ normalizer (F : Set G) := by
    apply mem_normalizer_iff.mpr
    intro a
    constructor
    · intro ha
      exact hfwd v hv (mem_map_of_mem (MulAut.conj v).toMonoidHom ha)
    · intro ha
      have hh := hfwd v⁻¹ (d.core.inv_mem hv)
        (mem_map_of_mem (MulAut.conj v⁻¹).toMonoidHom ha)
      simpa [MulAut.conj_apply, mul_assoc] using hh
  apply normalizer_inf_normalizer_le_normalizer_sup E F
  refine ⟨centralizer_le_normalizer _ ?_, hvF⟩
  intro a ha
  exact hv.2 a (hE ha).2

/-- Centralizing `N_K(E)` by the reflection extends to the whole dihedral factor. -/
public theorem factors_commute (d : Setup G) (E : Subgroup G) {e : G}
    (hc : d.x⁻¹ * e * d.x ∈
      centralizer ((d.K ⊓ normalizer (E : Set G) : Subgroup G) : Set G)) :
    (zpowers (d.x⁻¹ * e * d.x) ⊔ d.core) ≤
      centralizer ((d.K ⊓ normalizer (E : Set G) : Subgroup G) : Set G) := by
  refine sup_le (zpowers_le.mpr hc) ?_
  intro v hv k hk
  exact hv.2 k hk.1

/-- The missing reflection-centralizer identity makes `N_K(E)` normalize `EEˣ`. -/
public theorem k_normalizer_normalizes_product (d : Setup G)
    (E : Subgroup G) [IsKleinFour E]
    (hz : d.zK ∈ E) {e : G} (he : e ∈ E) (heout : e ∉ zpowers d.zK)
    (hc : d.x⁻¹ * e * d.x ∈
      centralizer ((d.K ⊓ normalizer (E : Set G) : Subgroup G) : Set G)) :
    d.K ⊓ normalizer (E : Set G) ≤
      normalizer ((E ⊔ conjugate d.x E : Subgroup G) : Set G) := by
  have hFC : conjugate d.x E ≤
      centralizer ((d.K ⊓ normalizer (E : Set G) : Subgroup G) : Set G) := by
    rw [conjugate_generators d E hz he heout]
    refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr hc)
    intro k hk
    exact d.t_mem.2 k hk.1
  intro k hk
  apply normalizer_inf_normalizer_le_normalizer_sup E (conjugate d.x E)
  refine ⟨hk.2, centralizer_le_normalizer _ ?_⟩
  intro v hv
  exact (hFC hv k hk).symm

/-- The genuine Sylow assertion converts the normalizer model into the order 64. -/
public theorem card_base_of_normalizer_model [Finite G] (d : Setup G)
    (E : Subgroup G) [IsKleinFour E] (hE : E ≤ d.sk)
    (hmodel : Nonempty ((d.H ⊓ normalizer (E : Set G) : Subgroup G) ≃*
      DihedralGroup 4 × Equiv.Perm (Fin 4))) :
    Nat.card (d.S ⊓ normalizer (E : Set G) : Subgroup G) = 64 := by
  obtain ⟨f⟩ := hmodel
  have hcard : Nat.card (d.H ⊓ normalizer (E : Set G) : Subgroup G) = 192 := by
    rw [Nat.card_congr f.toEquiv, Nat.card_prod, DihedralGroup.nat_card]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  obtain ⟨P, hP⟩ := d.normalizerSylow E hE inferInstance
  rw [← hP, card_map_of_injective (d.H ⊓ normalizer (E : Set G)).subtype_injective,
    P.card_eq_multiplicity, hcard]
  rw [show 192 = 2 ^ 6 * 3 by decide,
    Nat.factorization_mul_apply_of_coprime (by decide), Nat.factorization_pow,
    Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Nat.prime_two.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by decide)]
  norm_num

end NormalizerCalculation

end CFSG.Quasithin.Chapter2.A6ShadowConstruction

module

public import Glauberman.SuzukiCharacterization.NormalizerBasics
public import Glauberman.SuzukiCharacterization.CentralizerReduction
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup
public import FeitThompson.BGsection3.lemma_3_1
public import Mathlib.GroupTheory.SchurZassenhaus

/-!
# The Frobenius quotient of the Sylow normalizer

Write D = N_G(P), K = O_{2'}(D), and S for P viewed in D. For nonidentity
x in S, the normal odd complement of C_D(x) centralizes C_S(x), hence Z(S).
The centralizer of Z(S) is normal in D and has a normal odd complement,
so its odd core lies in K. Consequently C_D(x) = C_S(x)K.

The quotient map is injective on S. Thus commutation with its image modulo
K lifts to actual commutation, proving the Frobenius centralizer property.
The previously established inequality D ≠ SK makes the kernel proper;
Schur–Zassenhaus supplies a complement.

Finally, normal subgroups are comparable with a Frobenius kernel. A normal
subgroup with two-group quotient supplements a Sylow two-subgroup, so it
must contain the kernel. Applied in D/K, this proves P ≤ M whenever M is
normal in G and G/M is a two-group.

Source: Glauberman, *A Characterization of the Suzuki Groups* (1968),
Lemma 2.2, Lemma 2.3(ii), and Proposition 2.1(i)–(ii), pp. 79–80, saved at
`refs/original/n-group-global/odd-core-rank-two-source/glauberman-suzuki-1968-euclid-wayback.pdf`.
-/

open Subgroup
namespace Glauberman.SuzukiCharacterization
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem coprime_le_of_pgroup_quotient (N L : Subgroup G) [N.Normal]
    (hquot : IsPGroup 2 (G ⧸ N)) (hL : Nat.Coprime 2 (Nat.card L)) : L ≤ N := by
  intro x hx
  apply (QuotientGroup.eq_one_iff (N := N) x).mp
  apply orderOf_eq_one_iff.mp
  obtain ⟨k, hk⟩ := hquot.exists_orderOf_eq_pow (QuotientGroup.mk' N x)
  apply Nat.eq_one_of_dvd_coprimes (hL.pow_left k)
  · change orderOf (QuotientGroup.mk' N x) ∣ 2 ^ k
    rw [hk]
  · exact (orderOf_map_dvd (QuotientGroup.mk' N) x).trans
      (by simpa using orderOf_dvd_natCard (⟨x, hx⟩ : L))

omit [Finite G] in
private theorem normal_sylow_restrict (S : Sylow 2 G) [(S : Subgroup G).Normal]
    (C : Subgroup G) : ∃ T : Sylow 2 C, (T : Subgroup C) = (S : Subgroup G).subgroupOf C := by
  let T : Sylow 2 C := Sylow.nonempty.some
  obtain ⟨Q, hQ⟩ := T.exists_comap_subtype_eq
  have hSQ : (S : Subgroup G) ≤ (Q : Subgroup G) := S.isPGroup'.le_sylow_of_normal Q
  have he : Q = S := Sylow.ext (S.is_maximal' Q.isPGroup' hSQ)
  exact ⟨T, by rw [he] at hQ; exact hQ.symm⟩

private theorem normal_sylow_centralizer_le (S : Sylow 2 G)
    [(S : Subgroup G).Normal] (hS : (S : Subgroup G) ≠ ⊥)
    (hcomp : ∀ x ∈ (S : Subgroup G), x ≠ 1 →
      HasNormalPComplement 2 (centralizer ({x} : Set G)))
    (x : G) (hx : x ∈ (S : Subgroup G)) (hne : x ≠ 1) :
    centralizer ({x} : Set G) ≤ (S : Subgroup G) ⊔ pPrimeCore 2 G := by
  let Z := (center S).map (S : Subgroup G).subtype
  let B := centralizer (Z : Set G)
  have : Z.Normal := inferInstance
  have : B.Normal := normal_centralizer
  have : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot _).mpr hS
  have : Nontrivial (center S) := S.isPGroup'.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : center S)
  have hzG : ((z : S) : G) ≠ 1 := fun he => hz (Subtype.ext (Subtype.ext he))
  have hBcomp : HasNormalPComplement 2 B :=
    hasNormalPComplement_of_le 2
      (show B ≤ centralizer ({((z : S) : G)} : Set G) from
        fun b hb => mem_centralizer_singleton_iff.mpr
          (mem_centralizer_iff.mp hb _ (mem_map_of_mem _ z.property)).symm)
      (hcomp _ (z : S).property hzG)
  let C := centralizer ({x} : Set G)
  let L := (pPrimeCore 2 C).map C.subtype
  obtain ⟨T, hT⟩ := normal_sylow_restrict S C
  have : (T : Subgroup C).Normal := hT ▸ inferInstance
  have hZC : Z ≤ C := by
    rintro a ⟨a, ha, rfl⟩
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp ha ⟨x, hx⟩)).symm
  have hLB : L ≤ B := by
    rintro a ⟨a, ha, rfl⟩
    apply mem_centralizer_iff.mpr
    rintro b ⟨b, hb, rfl⟩
    have hbT : (⟨(b : G), hZC (mem_map_of_mem _ hb)⟩ : C) ∈ (T : Subgroup C) := by
      rw [hT]
      exact b.property
    exact congrArg Subtype.val (mem_centralizer_iff.mp
      (T.pPrimeCore_le_centralizer_of_normal ha) _ hbT)
  have hLcore : L ≤ pPrimeCore 2 G := by
    have hquot := isPGroup_quotient_pPrimeCore_of_hasNormalPComplement 2 B hBcomp
    have hodd : Nat.Coprime 2 (Nat.card (L.subgroupOf B)) := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hLB).toEquiv,
        card_map_of_injective C.subtype_injective]
      exact pPrimeCore_coprime_card
    have hl := coprime_le_of_pgroup_quotient (pPrimeCore 2 B) (L.subgroupOf B) hquot hodd
    intro a ha
    apply pPrimeCore_map_subtype_le_pPrimeCore_of_normal 2 B
    exact mem_map_of_mem B.subtype (hl (show (⟨a, hLB ha⟩ : B) ∈ L.subgroupOf B from ha))
  have hgen : (T : Subgroup C) ⊔ pPrimeCore 2 C = ⊤ :=
    T.sup_eq_top_of_quotient_isPGroup _
      (isPGroup_quotient_pPrimeCore_of_hasNormalPComplement 2 C (hcomp x hx hne))
  intro c hc
  have hh : (⟨c, hc⟩ : C) ∈ (T : Subgroup C) ⊔ pPrimeCore 2 C := by rw [hgen]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_normal_right.mp hh
  have haS : (a : G) ∈ (S : Subgroup G) := by
    change a ∈ (S : Subgroup G).subgroupOf C
    rwa [← hT]
  have habG : (a : G) * (b : G) = c := congrArg Subtype.val hab
  rw [← habG]
  exact ((S : Subgroup G) ⊔ pPrimeCore 2 G).mul_mem
    ((show (S : Subgroup G) ≤ (S : Subgroup G) ⊔ pPrimeCore 2 G from le_sup_left) haS)
    ((show pPrimeCore 2 G ≤ (S : Subgroup G) ⊔ pPrimeCore 2 G from le_sup_right)
      (hLcore (mem_map_of_mem C.subtype hb)))

omit [Finite G] in
private theorem normalizer_sylow_ne_bot (P : Sylow 2 G) (h : Hypotheses P) :
    ((P.subtype (P : Subgroup G).le_normalizer) :
      Subgroup (normalizer (P : Set G))) ≠ ⊥ := by
  intro he
  have hp : (P : Subgroup G) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hxS : (⟨x, (P : Subgroup G).le_normalizer hx⟩ : normalizer (P : Set G)) ∈
        (P.subtype (P : Subgroup G).le_normalizer : Subgroup _) := hx
    rw [he, mem_bot] at hxS
    exact mem_bot.mpr (congrArg Subtype.val hxS)
  exact h.not_normal (hp ▸ normal_bot)

/-- Lemma 2.2: the centralizer in the Sylow normalizer lies in PK. -/
public theorem Hypotheses.normalizer_centralizer_le (P : Sylow 2 G) (h : Hypotheses P)
    (x : normalizer (P : Set G)) (hx : (x : G) ∈ (P : Subgroup G)) (hne : x ≠ 1) :
    centralizer ({x} : Set (normalizer (P : Set G))) ≤ normalizerSylowCore P := by
  let D := normalizer (P : Set G)
  let S := P.subtype (P : Subgroup G).le_normalizer
  have : (S : Subgroup D).Normal := normal_in_normalizer
  apply normal_sylow_centralizer_le S (normalizer_sylow_ne_bot P h) _ x hx hne
  intro y hy hny
  apply hasNormalPComplement_of_map_subtype 2 D (centralizer ({y} : Set D))
  apply hasNormalPComplement_of_le 2 (L := centralizer ({(y : G)} : Set G))
  · rintro a ⟨a, ha, rfl⟩
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp ha))
  · exact h.centralizer_hasNormalPComplement P y hy
      (fun he => hny (Subtype.ext he))

/-- The full centralizer factorization in Lemma 2.2. -/
public theorem Hypotheses.normalizer_centralizer_eq (P : Sylow 2 G) (h : Hypotheses P)
    (x : normalizer (P : Set G)) (hx : (x : G) ∈ (P : Subgroup G)) (hne : x ≠ 1) :
    centralizer ({x} : Set (normalizer (P : Set G))) =
      ((P : Subgroup G).subgroupOf (normalizer (P : Set G)) ⊓
        centralizer ({x} : Set (normalizer (P : Set G)))) ⊔
          pPrimeCore 2 (normalizer (P : Set G)) := by
  let D := normalizer (P : Set G)
  let S := P.subtype (P : Subgroup G).le_normalizer
  let C := centralizer ({x} : Set D)
  have : (S : Subgroup D).Normal := normal_in_normalizer
  have hKC : pPrimeCore 2 D ≤ C := by
    intro k hk
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp (S.pPrimeCore_le_centralizer_of_normal hk) x hx).symm
  apply le_antisymm
  · intro c hc
    obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_normal_right.mp
      (h.normalizer_centralizer_le P x hx hne hc)
    have haC : a ∈ C := by
      have hh := C.mul_mem hc (C.inv_mem (hKC hb))
      simpa only [← hab, mul_assoc, mul_inv_cancel, mul_one] using hh
    rw [← hab]
    exact mul_mem (mem_sup_left ⟨ha, haC⟩) (mem_sup_right hb)
  · exact sup_le inf_le_right hKC

/-- The image of P in its normalizer modulo the odd core. -/
@[expose] public noncomputable def normalizerFrobeniusKernel (P : Sylow 2 G) :
    Subgroup ((normalizer (P : Set G)) ⧸ pPrimeCore 2 (normalizer (P : Set G))) :=
  ((P.subtype (P : Subgroup G).le_normalizer) : Subgroup _).map
    (QuotientGroup.mk' (pPrimeCore 2 (normalizer (P : Set G))))

omit [Finite G] in
/-- The kernel in Proposition 2.1(i) is normal. -/
public theorem normalizerFrobeniusKernel_normal (P : Sylow 2 G) :
    (normalizerFrobeniusKernel P).Normal := by
  have : ((P.subtype (P : Subgroup G).le_normalizer) :
      Subgroup (normalizer (P : Set G))).Normal := normal_in_normalizer
  exact Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)

/-- The kernel in Proposition 2.1(i) is nontrivial. -/
public theorem Hypotheses.normalizerFrobeniusKernel_ne_bot (P : Sylow 2 G) (h : Hypotheses P) :
    normalizerFrobeniusKernel P ≠ ⊥ := by
  let D := normalizer (P : Set G)
  let S := P.subtype (P : Subgroup G).le_normalizer
  let q := QuotientGroup.mk' (pPrimeCore 2 D)
  have hi : Function.Injective (q.comp (S : Subgroup D).subtype) :=
    injective_comp_subtype_of_coprime_ker q
      (by simpa only [q, QuotientGroup.ker_mk'] using (pPrimeCore_coprime_card (p := 2) (G := D)))
      _ S.isPGroup'
  intro he
  apply normalizer_sylow_ne_bot P h
  apply eq_bot_iff.mpr
  intro x hx
  have hxq : q x = 1 := by
    have hm : q x ∈ normalizerFrobeniusKernel P := mem_map_of_mem q hx
    rwa [he, mem_bot] at hm
  exact mem_bot.mpr (congrArg Subtype.val (hi (show q.comp (S : Subgroup D).subtype ⟨x, hx⟩ =
    q.comp (S : Subgroup D).subtype 1 from hxq.trans (map_one _).symm)))

/-- The kernel in Proposition 2.1(i) is proper. -/
public theorem Hypotheses.normalizerFrobeniusKernel_ne_top (P : Sylow 2 G) (h : Hypotheses P) :
    normalizerFrobeniusKernel P ≠ ⊤ := by
  intro he
  have hh := congrArg (Subgroup.comap
    (QuotientGroup.mk' (pPrimeCore 2 (normalizer (P : Set G))))) he
  rw [normalizerFrobeniusKernel, QuotientGroup.comap_map_mk', comap_top] at hh
  apply h.normalizerSylowCore_ne_top P
  rw [sup_comm] at hh
  exact hh

/-- Nonidentity kernel elements have their full centralizer in the kernel. -/
public theorem Hypotheses.normalizerFrobeniusKernel_centralizer_le (P : Sylow 2 G) (h : Hypotheses P)
    (y : (normalizer (P : Set G)) ⧸ pPrimeCore 2 (normalizer (P : Set G)))
    (hy : y ∈ normalizerFrobeniusKernel P) (hne : y ≠ 1) :
    centralizer ({y} : Set _) ≤ normalizerFrobeniusKernel P := by
  let D := normalizer (P : Set G)
  let S := P.subtype (P : Subgroup G).le_normalizer
  let q := QuotientGroup.mk' (pPrimeCore 2 D)
  have hSn : (S : Subgroup D).Normal := normal_in_normalizer
  have hi : Function.Injective (q.comp (S : Subgroup D).subtype) :=
    injective_comp_subtype_of_coprime_ker q
      (by simpa only [q, QuotientGroup.ker_mk'] using (pPrimeCore_coprime_card (p := 2) (G := D)))
      _ S.isPGroup'
  obtain ⟨x, hx, rfl⟩ := hy
  intro a ha
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 D) a
  have hc : q n * q x = q x * q n := mem_centralizer_singleton_iff.mp ha
  have hnx : n * x * n⁻¹ = x := by
    have he := hi (a₁ := ⟨n * x * n⁻¹, hSn.conj_mem x hx n⟩) (a₂ := ⟨x, hx⟩) (by
      change q (n * x * n⁻¹) = q x
      rw [map_mul, map_mul, map_inv, hc]
      simp)
    exact congrArg Subtype.val he
  have hn := h.normalizer_centralizer_le P x hx
    (fun he => hne (by simp only [he, map_one]))
    (mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hnx))
  change q n ∈ normalizerFrobeniusKernel P
  change n ∈ (normalizerFrobeniusKernel P).comap q
  rw [normalizerFrobeniusKernel, QuotientGroup.comap_map_mk']
  rw [sup_comm]
  exact hn

omit [Finite G] in
/-- The Frobenius kernel remains a two-group. -/
public theorem normalizerFrobeniusKernel_isPGroup (P : Sylow 2 G) :
    IsPGroup 2 (normalizerFrobeniusKernel P) :=
  (P.subtype (P : Subgroup G).le_normalizer).isPGroup'.map _

/-- Proposition 2.1(i), including a complement for the character construction. -/
public theorem Hypotheses.normalizer_frobenius (P : Sylow 2 G) (h : Hypotheses P) :
    ∃ R, IsFrobeniusGroupWithKernelComplement (normalizerFrobeniusKernel P) R := by
  let D := normalizer (P : Set G)
  let K := pPrimeCore 2 D
  let T := (P.subtype (P : Subgroup G).le_normalizer).mapSurjective
    (QuotientGroup.mk'_surjective K)
  have : (normalizerFrobeniusKernel P).Normal := normalizerFrobeniusKernel_normal P
  have hcop : Nat.Coprime (Nat.card (normalizerFrobeniusKernel P))
      (normalizerFrobeniusKernel P).index := T.card_coprime_index
  obtain ⟨R, hR⟩ := exists_right_complement'_of_coprime hcop
  have hRne : R ≠ ⊥ := by
    intro he
    have hh := hR.sup_eq_top
    rw [he, sup_bot_eq] at hh
    exact h.normalizerFrobeniusKernel_ne_top P hh
  refine ⟨R, (lemma_3_1 _ R (h.normalizerFrobeniusKernel_ne_bot P) hRne
    (normalizerFrobeniusKernel_normal P) hR).mpr ?_⟩
  intro r hr
  apply eq_bot_iff.mpr
  rintro x ⟨hx, hc⟩
  apply mem_bot.mpr
  by_contra hxne
  have hrK := h.normalizerFrobeniusKernel_centralizer_le P x hx hxne
    (mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hc).symm)
  exact hr (Subtype.ext (Subgroup.disjoint_def.mp hR.disjoint hrK r.property))

/-- Proposition 2.1(ii)'s quotient consequence: every normal subgroup with
two-group quotient contains the given Sylow two-subgroup. -/
public theorem Hypotheses.sylow_le_of_quotient_isPGroup (P : Sylow 2 G) (h : Hypotheses P)
    (M : Subgroup G) [M.Normal] (hquot : IsPGroup 2 (G ⧸ M)) : (P : Subgroup G) ≤ M := by
  let D := normalizer (P : Set G)
  let K := pPrimeCore 2 D
  let q := QuotientGroup.mk' K
  let f₀ : D →* G ⧸ M := (QuotientGroup.mk' M).comp D.subtype
  have hodd : Nat.Coprime 2 (Nat.card (normalizerOddCore P)) := by
    rw [normalizerOddCore, card_map_of_injective D.subtype_injective]
    exact pPrimeCore_coprime_card
  have hKM : normalizerOddCore P ≤ M :=
    coprime_le_of_pgroup_quotient M _ hquot hodd
  have hKker : K ≤ f₀.ker := by
    intro k hk
    change QuotientGroup.mk' M (k : G) = 1
    exact (QuotientGroup.eq_one_iff (N := M) _).mpr (hKM (mem_map_of_mem D.subtype hk))
  let f : D ⧸ K →* G ⧸ M := QuotientGroup.lift K f₀ hKker
  let T := (P.subtype (P : Subgroup G).le_normalizer).mapSurjective
    (QuotientGroup.mk'_surjective K)
  have : (T : Subgroup (D ⧸ K)).Normal := normalizerFrobeniusKernel_normal P
  have hTker : (T : Subgroup (D ⧸ K)) ≤ f.ker :=
    T.le_normal_of_quotient_isPGroup_of_centralizer_le
      (h.normalizerFrobeniusKernel_ne_top P)
      (h.normalizerFrobeniusKernel_centralizer_le P) f.ker
      ((hquot.to_subgroup f.range).of_equiv (QuotientGroup.quotientKerEquivRange f).symm)
  intro x hx
  have hxT : q ⟨x, (P : Subgroup G).le_normalizer hx⟩ ∈ (T : Subgroup (D ⧸ K)) :=
    mem_map_of_mem q hx
  exact (QuotientGroup.eq_one_iff (N := M) x).mp (hTker hxT)

end Glauberman.SuzukiCharacterization

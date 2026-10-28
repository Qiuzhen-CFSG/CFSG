module

public import CFSG.Quasithin.ChapterI.Section06To08.Basic
public import BenderSuzuki.SE.StrongEmbeddingIntersections
public import BenderSuzuki.SE.StrongEmbeddingFusion
public import Theory.ElementaryAbelian.Basic
public import Mathlib.Data.List.TFAE

/-!
# Strong embedding and unique fixed cosets (I.8.1 and I.8.5)

The coset stabilizer formula turns uniqueness of fixed points into a transporter
bound. Applied to involutions, this identifies the fixed-point and odd-intersection
criteria with the existing strong-embedding predicate. The Sylow-centralizer
criterion follows by using a central involution to force every 2-subgroup meeting
an involution of `M` into `M`, and then applying Sylow conjugacy. Applied to a normal
2-subgroup, it gives the elementary reductions used in I.8.5. Sylow containment
follows from the normalizer condition in a finite 2-group.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, printed pp. 428--430, Lemmas I.8.1 and I.8.5.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterI.Section06To08

open BenderSuzuki PFAppendixIII PFchapter1section1

universe u
variable {G : Type u} [Group G]

/-- The base coset is fixed precisely by elements of its stabilizer. -/
theorem fixes_baseCoset_iff (M : Subgroup G) (x : G) :
    x • (QuotientGroup.mk 1 : G ⧸ M) = QuotientGroup.mk 1 ↔ x ∈ M := by
  rw [← MulAction.mem_stabilizer_iff, baseCoset_stabilizer]

/-- A unique fixed coset forces every transporter back into its stabilizer to
lie in that stabilizer. -/
theorem mem_of_unique_fixed_coset {M : Subgroup G} {x g : G}
    (hxM : x ∈ M) (hunique : ∃! q : G ⧸ M, x • q = q)
    (hconj : g * x * g⁻¹ ∈ M) : g ∈ M := by
  have hbase := (fixes_baseCoset_iff M x).mpr hxM
  have hgfix : x • (QuotientGroup.mk g⁻¹ : G ⧸ M) = QuotientGroup.mk g⁻¹ := by
    rw [fixed_coset_iff_mem_rightConjugate]
    simp only [inv_inv]
    rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨g * x * g⁻¹, hconj, ?_⟩
    simp [mul_assoc]
  have heq := hunique.unique hbase hgfix
  have hginv : g⁻¹ ∈ M := by
    simpa using (QuotientGroup.eq.mp heq)
  exact M.inv_mem_iff.mp hginv

/-- The transporter formulation yields centralizer containment. -/
theorem centralizer_le_of_unique_fixed_coset {M : Subgroup G} {x : G}
    (hxM : x ∈ M) (hunique : ∃! q : G ⧸ M, x • q = q) :
    Subgroup.centralizer ({x} : Set G) ≤ M := by
  intro g hg
  apply mem_of_unique_fixed_coset hxM hunique
  have hc := Subgroup.mem_centralizer_singleton_iff.mp hg
  simpa only [hc, mul_assoc, mul_inv_cancel, mul_one] using hxM

/-- Cauchy's theorem, in the ambient-element form used by strong embedding. -/
theorem exists_involution_of_card_even [Finite G] {M : Subgroup G}
    (hEven : Even (Nat.card M)) : ∃ x : G, x ∈ M ∧ IsInvolution x := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := M) 2
    (even_iff_two_dvd.mp hEven)
  have horder : orderOf (x : G) = 2 := (Subgroup.orderOf_coe x).trans hx
  have h := orderOf_eq_prime_iff.mp horder
  exact ⟨x, x.property, h.2, h.1⟩

/-- I.8.1(2), with a bridge to the existing strong-embedding predicate. -/
theorem stronglyEmbedded_iff_odd_intersections [Finite G] {M : Subgroup G}
    (hproper : M ≠ ⊤) (hEven : Even (Nat.card M)) :
    BenderSuzuki.IsStronglyEmbedded M ↔
      ∀ g : G, g ∉ M → Odd (Nat.card (M ⊓ rightConjugate M g : Subgroup G)) := by
  constructor
  · exact fun h _ hg => h.inf_rightConjugate_card_odd hg
  · intro h
    refine ⟨hproper, exists_involution_of_card_even hEven, ?_⟩
    intro g hg x hxM hxg hx
    let y : (M ⊓ rightConjugate M g : Subgroup G) := ⟨x, hxM, hxg⟩
    have hy : IsInvolution y := IsInvolution.subtype (M := M ⊓ rightConjugate M g) hx y.property
    have hord : orderOf y = 2 := orderOf_eq_prime hy.sq_eq_one hy.ne_one
    have hdvd : 2 ∣ Nat.card (M ⊓ rightConjugate M g : Subgroup G) :=
      hord ▸ orderOf_dvd_natCard y
    exact (Nat.not_even_iff_odd.mpr (h g hg)) (even_iff_two_dvd.mpr hdvd)

/-- I.8.1(4), using the canonical action on cosets. Inverting representatives
identifies this with the source's right-coset action. -/
theorem stronglyEmbedded_iff_unique_fixed_cosets [Finite G] {M : Subgroup G}
    (hproper : M ≠ ⊤) (hEven : Even (Nat.card M)) :
    BenderSuzuki.IsStronglyEmbedded M ↔
      ∀ x : G, IsInvolution x → ∃! q : G ⧸ M, x • q = q := by
  constructor
  · exact fun h _ hx => h.involution_fixed_coset_unique hx
  · intro h
    refine ⟨hproper, exists_involution_of_card_even hEven, ?_⟩
    intro g hg x hxM hxg hx
    apply hg
    apply mem_of_unique_fixed_coset hxM (h x hx)
    have hc := rightConjugateElem_mem_of_mem_rightConjugate (g := g⁻¹)
      (by simpa using hxg)
    simpa [rightConjugateElem] using hc

/-- Strong embedding bounds the normalizer of every nontrivial 2-subgroup
of the strongly embedded subgroup. -/
theorem normalizer_le_of_stronglyEmbedded [Finite G] {M Q : Subgroup G}
    (hM : BenderSuzuki.IsStronglyEmbedded M) (hQ : IsPGroup 2 Q)
    (hne : Q ≠ ⊥) (hQM : Q ≤ M) : Subgroup.normalizer (Q : Set G) ≤ M := by
  let : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hne
  obtain ⟨n, hn, hcard⟩ := hQ.nontrivial_iff_card.mp inferInstance
  have heven : Even (Nat.card Q) := by
    apply even_iff_two_dvd.mpr
    rw [hcard]
    exact dvd_pow_self 2 hn.ne'
  obtain ⟨x, hxQ, hx⟩ := exists_involution_of_card_even heven
  intro g hg
  apply mem_of_unique_fixed_coset (hQM hxQ) (hM.involution_fixed_coset_unique hx)
  exact hQM ((Subgroup.mem_normalizer_iff.mp hg x).mp hxQ)

/-! ## The elementary unique-fixed-point reductions of I.8.5 -/

/-- Unique fixed cosets force every conjugator taking a nonidentity element
of `V` into `M` to belong to `M`. -/
theorem unique_fixed_cosets_transporter {V M : Subgroup G} (hVM : V ≤ M)
    (hfix : ∀ v : G, v ∈ V → v ≠ 1 → ∃! q : G ⧸ M, v • q = q)
    {v g : G} (hv : v ∈ V) (hne : v ≠ 1) (hconj : g * v * g⁻¹ ∈ M) :
    g ∈ M :=
  mem_of_unique_fixed_coset (hVM hv) (hfix v hv hne) hconj

/-- In particular, every subgroup of `M` containing `V ≠ 1` has its ambient
normalizer contained in `M`. -/
theorem normalizer_le_of_unique_fixed_cosets {V M A : Subgroup G}
    (hVM : V ≤ M) (hVne : V ≠ ⊥)
    (hfix : ∀ v : G, v ∈ V → v ≠ 1 → ∃! q : G ⧸ M, v • q = q)
    (hVA : V ≤ A) (hAM : A ≤ M) : Subgroup.normalizer (A : Set G) ≤ M := by
  obtain ⟨⟨v, hv⟩, hvne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hVne
  intro g hg
  exact unique_fixed_cosets_transporter hVM hfix hv
    (fun h => hvne (Subtype.ext h))
    (hAM ((Subgroup.mem_normalizer_iff.mp hg v).mp (hVA hv)))

/-- A nontrivial normal subgroup with the unique-fixed-point property has
normalizer exactly `M`. Normality is expressed as `M ≤ N_G(V)`. -/
theorem normalizer_eq_of_unique_fixed_cosets {V M : Subgroup G}
    (hVM : V ≤ M) (hVne : V ≠ ⊥) (hnormal : M ≤ Subgroup.normalizer (V : Set G))
    (hfix : ∀ v : G, v ∈ V → v ≠ 1 → ∃! q : G ⧸ M, v • q = q) :
    Subgroup.normalizer (V : Set G) = M :=
  le_antisymm (normalizer_le_of_unique_fixed_cosets hVM hVne hfix le_rfl hVM) hnormal

/-- The TI reduction of I.8.5. It does not need commutativity or exponent two. -/
theorem isTISubgroup_of_unique_fixed_cosets {V M : Subgroup G}
    (hVM : V ≤ M) (hnormal : M ≤ Subgroup.normalizer (V : Set G))
    (hfix : ∀ v : G, v ∈ V → v ≠ 1 → ∃! q : G ⧸ M, v • q = q) :
    IsTISubgroup V := by
  rw [isTISubgroup_iff]
  intro g hg v hv hconj
  by_contra hne
  exact hg (hnormal (unique_fixed_cosets_transporter hVM hfix hv hne (hVM hconj)))

/-- Fusion into `M` preserves `V`: the strong-closure assertion before
choosing a Sylow subgroup. -/
theorem conj_mem_of_unique_fixed_cosets {V M : Subgroup G}
    (hVM : V ≤ M) (hnormal : M ≤ Subgroup.normalizer (V : Set G))
    (hfix : ∀ v : G, v ∈ V → v ≠ 1 → ∃! q : G ⧸ M, v • q = q)
    {v g : G} (hv : v ∈ V) (hconj : g * v * g⁻¹ ∈ M) : g * v * g⁻¹ ∈ V := by
  by_cases hne : v = 1
  · simp [hne]
  · exact (Subgroup.mem_normalizer_iff.mp
      (hnormal (unique_fixed_cosets_transporter hVM hfix hv hne hconj)) v).mp hv

/-- A Sylow subgroup of `M` is ambient Sylow if its ambient normalizer lies in
`M`. The proof uses the normalizer condition inside an ambient Sylow subgroup. -/
theorem sylow_map_eq_of_normalizer_le [Finite G] (M : Subgroup G) (T : Sylow 2 M)
    (hnorm : Subgroup.normalizer
      (((T : Subgroup M).map M.subtype : Subgroup G) : Set G) ≤ M) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = (T : Subgroup M).map M.subtype := by
  let A : Subgroup G := (T : Subgroup M).map M.subtype
  obtain ⟨S, hST⟩ := T.exists_comap_subtype_eq
  have hAS : A ≤ (S : Subgroup G) := by
    rintro x ⟨t, ht, rfl⟩
    rw [← hST] at ht
    exact ht
  have hSA : (S : Subgroup G) ≤ A := by
    by_contra hnot
    have hproper : A.subgroupOf (S : Subgroup G) < ⊤ := by
      rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
      exact hnot
    let : Group.IsNilpotent S := S.isPGroup'.isNilpotent
    obtain ⟨q, hqN, hqnot⟩ := SetLike.exists_of_lt
      (Group.normalizerCondition_of_isNilpotent _ hproper)
    have hqNA : (q : G) ∈ Subgroup.normalizer (A : Set G) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hAS] at hqN
      exact hqN
    have hqM : (q : G) ∈ M := hnorm hqNA
    have hqT : (⟨(q : G), hqM⟩ : M) ∈ (T : Subgroup M) := by
      rw [← hST]
      exact q.property
    exact hqnot ⟨⟨(q : G), hqM⟩, hqT, rfl⟩
  exact ⟨S, le_antisymm hSA hAS⟩

/-- A normal 2-subgroup of `M` lies in the ambient image of every Sylow
2-subgroup of `M`. -/
theorem le_sylow_map_of_normal [Finite G] {V M : Subgroup G} (hVM : V ≤ M)
    (hnormal : M ≤ Subgroup.normalizer (V : Set G)) (hVtwo : IsPGroup 2 V)
    (T : Sylow 2 M) : V ≤ (T : Subgroup M).map M.subtype := by
  let : (V.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVM).mpr hnormal
  have hp : IsPGroup 2 (V.subgroupOf M) :=
    hVtwo.of_equiv (Subgroup.subgroupOfEquivOfLe hVM).symm
  intro v hv
  exact ⟨⟨v, hVM hv⟩, hp.le_sylow_of_normal T hv, rfl⟩

/-- The needed Sylow containment in I.8.5: every Sylow 2-subgroup of `M`
is itself an ambient Sylow subgroup. -/
theorem sylow_map_eq_of_unique_fixed_cosets [Finite G] {V M : Subgroup G}
    (hVM : V ≤ M) (hVne : V ≠ ⊥) (hnormal : M ≤ Subgroup.normalizer (V : Set G))
    (hVtwo : IsPGroup 2 V)
    (hfix : ∀ v : G, v ∈ V → v ≠ 1 → ∃! q : G ⧸ M, v • q = q)
    (T : Sylow 2 M) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = (T : Subgroup M).map M.subtype := by
  apply sylow_map_eq_of_normalizer_le
  exact normalizer_le_of_unique_fixed_cosets hVM hVne hfix
    (le_sylow_map_of_normal hVM hnormal hVtwo T) (Subgroup.map_subtype_le _)

/-- The strong-closure reduction of I.8.5, including a Sylow subgroup witness.
The last clause states strong closure pointwise to avoid choosing a fusion API. -/
theorem exists_sylow_strongly_closed_of_unique_fixed_cosets [Finite G] {V M : Subgroup G}
    (hVM : V ≤ M) (hVne : V ≠ ⊥) (hnormal : M ≤ Subgroup.normalizer (V : Set G))
    (hVtwo : IsPGroup 2 V)
    (hfix : ∀ v : G, v ∈ V → v ≠ 1 → ∃! q : G ⧸ M, v • q = q)
    (T : Sylow 2 M) :
    ∃ S : Sylow 2 G,
      (S : Subgroup G) = (T : Subgroup M).map M.subtype ∧
      V ≤ (S : Subgroup G) ∧ (S : Subgroup G) ≤ M ∧
      ∀ v : G, v ∈ V → ∀ g : G, g * v * g⁻¹ ∈ (S : Subgroup G) →
        g * v * g⁻¹ ∈ V := by
  obtain ⟨S, hS⟩ := sylow_map_eq_of_unique_fixed_cosets hVM hVne hnormal hVtwo hfix T
  have hSM : (S : Subgroup G) ≤ M := hS ▸ Subgroup.map_subtype_le _
  refine ⟨S, hS, hS ▸ le_sylow_map_of_normal hVM hnormal hVtwo T, hSM, ?_⟩
  intro v hv g hg
  exact conj_mem_of_unique_fixed_cosets hVM hnormal hfix hv (hSM hg)

/-- Properness of `M` ensures the TI subgroup in I.8.5 is not normal in `G`. -/
theorem not_normal_of_unique_fixed_cosets {V M : Subgroup G}
    (hVM : V ≤ M) (hVne : V ≠ ⊥) (hproper : M ≠ ⊤)
    (hnormal : M ≤ Subgroup.normalizer (V : Set G))
    (hfix : ∀ v : G, v ∈ V → v ≠ 1 → ∃! q : G ⧸ M, v • q = q) :
    ¬ V.Normal := by
  intro hV
  apply hproper
  rw [← normalizer_eq_of_unique_fixed_cosets hVM hVne hnormal hfix]
  exact Subgroup.normalizer_eq_top_iff.mpr hV

/-! ## The Sylow-centralizer criterion of I.8.1 -/

private theorem exists_conj_in_sylow [Finite G] (M : Subgroup G) (T : Sylow 2 M)
    {x : G} (hxM : x ∈ M) (hx : IsInvolution x) :
    ∃ m : M, (m : G) * x * (m : G)⁻¹ ∈ (T : Subgroup M).map M.subtype := by
  let xm : M := ⟨x, hxM⟩
  have hxm : IsInvolution xm := IsInvolution.subtype hx hxM
  obtain ⟨P, hP⟩ := (isPGroup_zpowers_of_involution hxm).exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M P T
  refine ⟨m, ⟨m * xm * m⁻¹, ?_, rfl⟩⟩
  rw [← hm]
  exact Subgroup.mem_map_of_mem (MulAut.conj m).toMonoidHom
    (hP (Subgroup.mem_zpowers xm))

private theorem centralizers_in_sylow_extend [Finite G] (M : Subgroup G) (T : Sylow 2 M)
    (hc : ∀ i : G, i ∈ (T : Subgroup M).map M.subtype → IsInvolution i →
      Subgroup.centralizer ({i} : Set G) ≤ M) :
    ∀ i : G, i ∈ M → IsInvolution i → Subgroup.centralizer ({i} : Set G) ≤ M := by
  intro x hxM hx g hg
  obtain ⟨m, hm⟩ := exists_conj_in_sylow M T hxM hx
  have hi : IsInvolution ((m : G) * x * (m : G)⁻¹) := by
    simpa [rightConjugateElem] using
      (isInvolution_rightConjugateElem (g := (m : G)⁻¹) hx)
  have hcg : (m : G) * g * (m : G)⁻¹ ∈
      Subgroup.centralizer ({(m : G) * x * (m : G)⁻¹} : Set G) := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hg
    simpa [mul_assoc] using congrArg (fun a : G => (m : G) * a * (m : G)⁻¹) hcomm
  have hmg := hc _ hm hi hcg
  have := M.mul_mem (M.mul_mem (M.inv_mem m.property) hmg) m.property
  simpa [mul_assoc] using this

private theorem twoSubgroup_le_of_centralizers [Finite G] {M P : Subgroup G}
    (hc : ∀ i : G, i ∈ M → IsInvolution i → Subgroup.centralizer ({i} : Set G) ≤ M)
    (hP : IsPGroup 2 P) {x : G} (hxP : x ∈ P) (hxM : x ∈ M) (hx : IsInvolution x) :
    P ≤ M := by
  have hPne : P ≠ ⊥ := by
    intro h
    exact hx.ne_one (by simpa [h] using hxP)
  let : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hPne
  let : Nontrivial (Subgroup.center P) := hP.center_nontrivial
  have hZp := hP.to_subgroup (Subgroup.center P)
  obtain ⟨n, hn, hcard⟩ := hZp.nontrivial_iff_card.mp inferInstance
  have heven : Even (Nat.card (Subgroup.center P)) := by
    apply even_iff_two_dvd.mpr
    rw [hcard]
    exact dvd_pow_self 2 hn.ne'
  obtain ⟨z, hzZ, hz⟩ := exists_involution_of_card_even heven
  have hzG : IsInvolution (z : G) := IsInvolution.map_of_injective hz P.subtype Subtype.val_injective
  have hzM : (z : G) ∈ M := by
    apply hc x hxM hx
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hzZ ⟨x, hxP⟩)).symm
  intro y hy
  apply hc (z : G) hzM hzG
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzZ ⟨y, hy⟩)

/-- The substantive implication I.8.1(3) ⇒ strong embedding. The centralizer
hypothesis propagates from the chosen Sylow subgroup to all involutions of `M`;
central involutions then force every 2-subgroup meeting those involutions into `M`. -/
theorem stronglyEmbedded_of_sylow_normalizer_and_centralizers [Finite G]
    (M : Subgroup G) (T : Sylow 2 M) (hproper : M ≠ ⊤) (hEven : Even (Nat.card M))
    (hnorm : Subgroup.normalizer
      (((T : Subgroup M).map M.subtype : Subgroup G) : Set G) ≤ M)
    (hc : ∀ i : G, i ∈ (T : Subgroup M).map M.subtype → IsInvolution i →
      Subgroup.centralizer ({i} : Set G) ≤ M) :
    BenderSuzuki.IsStronglyEmbedded M := by
  obtain ⟨S, hS⟩ := sylow_map_eq_of_normalizer_le M T hnorm
  have hSM : (S : Subgroup G) ≤ M := hS ▸ Subgroup.map_subtype_le _
  have hcM := centralizers_in_sylow_extend M T hc
  refine ⟨hproper, exists_involution_of_card_even hEven, ?_⟩
  intro g hg x hxM hxg hx
  have hyM : g * x * g⁻¹ ∈ M := by
    have := rightConjugateElem_mem_of_mem_rightConjugate (g := g⁻¹)
      (by simpa using hxg)
    simpa [rightConjugateElem] using this
  have hy : IsInvolution (g * x * g⁻¹) := by
    simpa [rightConjugateElem] using (isInvolution_rightConjugateElem (g := g⁻¹) hx)
  obtain ⟨m, hm⟩ := exists_conj_in_sylow M T hyM hy
  let k : G := (m : G) * g
  have hxS : k * x * k⁻¹ ∈ (S : Subgroup G) := by
    rw [hS]
    simpa [k, mul_assoc] using hm
  let P : Sylow 2 G := k⁻¹ • S
  have hxP : x ∈ (P : Subgroup G) := by
    change x ∈ (S : Subgroup G).map (MulAut.conj k⁻¹).toMonoidHom
    refine ⟨k * x * k⁻¹, hxS, ?_⟩
    simp [mul_assoc]
  have hPM : (P : Subgroup G) ≤ M := twoSubgroup_le_of_centralizers hcM P.isPGroup' hxP hxM hx
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq M (P.subtype hPM) (S.subtype hSM)
  rw [Sylow.smul_subtype] at hn
  have hn' : (n : G) • P = S := Sylow.subtype_injective hn
  have hnN : (n : G) * k⁻¹ ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) := by
    apply Sylow.smul_eq_iff_mem_normalizer.mp
    simpa only [P, mul_smul] using hn'
  have hnM : (n : G) * k⁻¹ ∈ M := hnorm (hS ▸ hnN)
  have hkM : k ∈ M := by
    have := M.mul_mem (M.inv_mem hnM) n.property
    simpa [mul_assoc] using this
  apply hg
  have := M.mul_mem (M.inv_mem m.property) hkM
  simpa [k] using this

private theorem sylow_map_ne_bot_of_even [Finite G] (M : Subgroup G) (T : Sylow 2 M)
    (hEven : Even (Nat.card M)) : (T : Subgroup M).map M.subtype ≠ ⊥ := by
  intro hbot
  have hTbot : (T : Subgroup M) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ Subtype.val_injective).mp hbot
  apply T.not_dvd_index
  simpa [hTbot] using even_iff_two_dvd.mp hEven

/-- I.8.1(3) is equivalent to the existing strong-embedding predicate. -/
theorem stronglyEmbedded_iff_sylow_normalizer_and_centralizers [Finite G]
    (M : Subgroup G) (T : Sylow 2 M) (hproper : M ≠ ⊤) (hEven : Even (Nat.card M)) :
    BenderSuzuki.IsStronglyEmbedded M ↔
      Subgroup.normalizer (((T : Subgroup M).map M.subtype : Subgroup G) : Set G) ≤ M ∧
      ∀ i : G, i ∈ (T : Subgroup M).map M.subtype → IsInvolution i →
        Subgroup.centralizer ({i} : Set G) ≤ M := by
  constructor
  · intro hM
    refine ⟨normalizer_le_of_stronglyEmbedded hM (T.isPGroup'.map M.subtype)
      (sylow_map_ne_bot_of_even M T hEven) (Subgroup.map_subtype_le _), ?_⟩
    exact fun _ hi hiI => hM.centralizer_le (Subgroup.map_subtype_le _ hi) hiI
  · rintro ⟨hn, hc⟩
    exact stronglyEmbedded_of_sylow_normalizer_and_centralizers M T hproper hEven hn hc

/-- The source definition, using normalizers of nontrivial subgroups of a
Sylow subgroup of `M`, agrees with the existing strong-embedding predicate. -/
theorem stronglyEmbedded_iff_normalizers [Finite G]
    (M : Subgroup G) (T : Sylow 2 M) (hproper : M ≠ ⊤) (hEven : Even (Nat.card M)) :
    BenderSuzuki.IsStronglyEmbedded M ↔
      ∀ Q : Subgroup G, Q ≠ ⊥ → Q ≤ (T : Subgroup M).map M.subtype →
        Subgroup.normalizer (Q : Set G) ≤ M := by
  constructor
  · intro hM Q hQne hQT
    exact normalizer_le_of_stronglyEmbedded hM
      ((T.isPGroup'.map M.subtype).to_le hQT) hQne
      (hQT.trans (Subgroup.map_subtype_le _))
  · intro hn
    apply stronglyEmbedded_of_sylow_normalizer_and_centralizers M T hproper hEven
    · exact hn _ (sylow_map_ne_bot_of_even M T hEven) le_rfl
    · intro i hi hiI
      have hzne : Subgroup.zpowers i ≠ ⊥ := by
        simpa [Subgroup.zpowers_eq_bot] using hiI.ne_one
      calc
        Subgroup.centralizer ({i} : Set G) =
            Subgroup.centralizer ((Subgroup.zpowers i : Subgroup G) : Set G) := by
          rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
        _ ≤ Subgroup.normalizer ((Subgroup.zpowers i : Subgroup G) : Set G) :=
          Subgroup.centralizer_le_normalizer _
        _ ≤ M := hn _ hzne (Subgroup.zpowers_le.mpr hi)

/-- Lemma I.8.1: the four formulations in the source are equivalent. The
preceding equivalences separately identify each with `BenderSuzuki.IsStronglyEmbedded`. -/
theorem lemma_I_8_1 [Finite G]
    (M : Subgroup G) (T : Sylow 2 M) (hproper : M ≠ ⊤) (hEven : Even (Nat.card M)) :
    List.TFAE [
      (∀ Q : Subgroup G, Q ≠ ⊥ → Q ≤ (T : Subgroup M).map M.subtype →
        Subgroup.normalizer (Q : Set G) ≤ M),
      (∀ g : G, g ∉ M → Odd (Nat.card (M ⊓ rightConjugate M g : Subgroup G))),
      (Subgroup.normalizer (((T : Subgroup M).map M.subtype : Subgroup G) : Set G) ≤ M ∧
        ∀ i : G, i ∈ (T : Subgroup M).map M.subtype → IsInvolution i →
          Subgroup.centralizer ({i} : Set G) ≤ M),
      (∀ x : G, IsInvolution x → ∃! q : G ⧸ M, x • q = q)] := by
  have h1 := stronglyEmbedded_iff_normalizers M T hproper hEven
  have h2 := stronglyEmbedded_iff_odd_intersections hproper hEven
  have h3 := stronglyEmbedded_iff_sylow_normalizer_and_centralizers M T hproper hEven
  have h4 := stronglyEmbedded_iff_unique_fixed_cosets hproper hEven
  simp only [List.tfae_cons_cons, List.tfae_singleton, and_true]
  exact ⟨h1.symm.trans h2, h2.symm.trans h3, h3.symm.trans h4⟩

/-- The elementary reductions used to apply I.8.3 in the proof of I.8.5.
This statement uses the source hypotheses, with normality inside `M`, and
supplies the TI, nonnormality, centralizer and ambient Sylow/strong-closure data. -/
theorem lemma_I_8_5_reductions [Finite G] (V M : Subgroup G)
    [IsElementaryAbelian 2 V] [(V.subgroupOf M).Normal]
    (hVM : V ≤ M) (hVne : V ≠ ⊥) (hproper : M ≠ ⊤)
    (hfix : ∀ v : G, v ∈ V → v ≠ 1 → ∃! q : G ⧸ M, v • q = q)
    (T : Sylow 2 M) :
    Subgroup.normalizer (V : Set G) = M ∧ IsTISubgroup V ∧ ¬ V.Normal ∧
      (∀ v : G, v ∈ V → v ≠ 1 → Subgroup.centralizer ({v} : Set G) ≤ M) ∧
      ∃ S : Sylow 2 G,
        (S : Subgroup G) = (T : Subgroup M).map M.subtype ∧
        V ≤ (S : Subgroup G) ∧ (S : Subgroup G) ≤ M ∧
        ∀ v : G, v ∈ V → ∀ g : G, g * v * g⁻¹ ∈ (S : Subgroup G) →
          g * v * g⁻¹ ∈ V := by
  have hn : M ≤ Subgroup.normalizer (V : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVM).mp inferInstance
  exact ⟨normalizer_eq_of_unique_fixed_cosets hVM hVne hn hfix,
    isTISubgroup_of_unique_fixed_cosets hVM hn hfix,
    not_normal_of_unique_fixed_cosets hVM hVne hproper hn hfix,
    fun v hv hne => centralizer_le_of_unique_fixed_coset (hVM hv) (hfix v hv hne),
    exists_sylow_strongly_closed_of_unique_fixed_cosets hVM hVne hn
      (IsElementaryAbelian.isPGroup 2 V) hfix T⟩

end CFSG.Quasithin.ChapterI.Section06To08

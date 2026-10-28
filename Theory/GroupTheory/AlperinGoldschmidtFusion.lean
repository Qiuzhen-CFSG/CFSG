module

public import Theory.GroupTheory.RelativeRadicalFusion
public import Theory.GroupTheory.CentricRadicalCoreComparison
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.SetStrongClosure

/-!
# The literal Alperin–Goldschmidt element-fusion family

The family consists of nontrivial D in a fixed Sylow p-subgroup T, with
N_T(D) Sylow in N_G(D), C_G(D) inside O_{p',p}(N_G(D)), and that iterated
core the internal direct product O_{p'}(N_G(D)) D. The Sylow condition is
an actual ambient-image equality. Commutativity, disjointness, and product
equality are all recorded, and the iterated core uses the genuine quotient.

Relative radical fusion and the normalizer-core comparison prove that this
family controls element fusion. The relation theorem gives an actual chain
of family-normalizer steps. Containing these normalizers therefore makes
every relatively normal p-subgroup of M strongly closed in T. Every family
member also contains the Sylow center, as needed in the next source lemma.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Definition 2.2.1, Proposition 2.2.2(1), and the
first step of Lemma 2.2.3, pp. 518–520. The source specializes p to 2.
-/

@[expose] public section

open Subgroup BenderSuzuki.External
namespace AlperinGoldschmidt
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

def normalizerPrimeCore (p : ℕ) (D : Subgroup G) : Subgroup G :=
  (primeCorePreimage p (normalizer (D : Set G))).map (normalizer (D : Set G)).subtype

def normalizerPrimeComplementCore (p : ℕ) (D : Subgroup G) : Subgroup G :=
  (pPrimeCore p (normalizer (D : Set G))).map (normalizer (D : Set G)).subtype

structure Family (T : Sylow p G) (D : Subgroup G) : Prop where
  ne_bot : D ≠ ⊥
  le_sylow : D ≤ (T : Subgroup G)
  sylow_normalizer : ∃ P : Sylow p (normalizer (D : Set G)),
    (P : Subgroup (normalizer (D : Set G))).map (normalizer (D : Set G)).subtype =
      (T : Subgroup G) ⊓ normalizer (D : Set G)
  centralizer_le : centralizer (D : Set G) ≤ normalizerPrimeCore p D
  core_eq : normalizerPrimeCore p D = normalizerPrimeComplementCore p D ⊔ D
  disjoint : Disjoint (normalizerPrimeComplementCore p D) D
  commute : ∀ o ∈ normalizerPrimeComplementCore p D, ∀ d ∈ D, Commute o d

theorem family_of_relative_radical (T : Sylow p G) (D : Subgroup G)
    (hne : D ≠ ⊥) (hext : HuppertExtremal T D)
    (hcent : (T : Subgroup G) ⊓ centralizer (D : Set G) ≤ D)
    (hrad : pCore p D.normalizerMonoidHom.range ≤
      (D.subgroupOf (normalizer (D : Set G))).map D.normalizerMonoidHom.rangeRestrict) :
    Family T D := by
  let N := normalizer (D : Set G)
  let D₀ := D.subgroupOf N
  let f := D.normalizerMonoidHom.rangeRestrict
  obtain ⟨P, hP⟩ := hext.exists_sylow_normalizer
  have hD : IsPGroup p D := T.isPGroup'.of_injective (inclusion hext.1) (inclusion_injective _)
  have hD₀ : IsPGroup p D₀ := hD.comap_subtype
  have hker : f.ker = centralizer (D₀ : Set N) := by
    rw [MonoidHom.ker_rangeRestrict, normalizerMonoidHom_ker]
    ext n
    constructor
    · intro hn
      rw [mem_centralizer_iff]
      intro d hd
      exact Subtype.ext (mem_centralizer_iff.mp hn d hd)
    · intro hn
      change (n : G) ∈ centralizer (D : Set G)
      rw [mem_centralizer_iff]
      intro d hd
      exact congrArg Subtype.val (mem_centralizer_iff.mp hn ⟨d, D.le_normalizer hd⟩ hd)
  have hcent₀ : (P : Subgroup N) ⊓ centralizer (D₀ : Set N) ≤ D₀ := by
    intro n hn
    have hnT : (n : G) ∈ (T : Subgroup G) := by
      have hh : (n : G) ∈ (P : Subgroup N).map N.subtype := ⟨n, hn.1, rfl⟩
      rw [hP] at hh
      exact hh.1
    have hnC : (n : G) ∈ centralizer (D : Set G) := by
      rw [mem_centralizer_iff]
      intro d hd
      exact congrArg Subtype.val (mem_centralizer_iff.mp hn.2 ⟨d, D.le_normalizer hd⟩ hd)
    exact hcent ⟨hnT, hnC⟩
  obtain ⟨hc, heq, hdisj, hcomm⟩ := primeCore_product P D₀ hD₀ hcent₀ f
    D.normalizerMonoidHom.rangeRestrict_surjective hker hrad
  have hmap : D₀.map N.subtype = D := map_subgroupOf_eq_of_le D.le_normalizer
  refine ⟨hne, hext.1, ⟨P, hP⟩, ?_, ?_, ?_, ?_⟩
  · intro c hcD
    let cN : N := ⟨c, centralizer_le_normalizer _ hcD⟩
    have hcN : cN ∈ centralizer (D₀ : Set N) := by
      rw [mem_centralizer_iff]
      intro d hd
      exact Subtype.ext (mem_centralizer_iff.mp hcD d hd)
    exact ⟨cN, hc hcN, rfl⟩
  · change (primeCorePreimage p N).map N.subtype = _
    rw [heq, Subgroup.map_sup, hmap]
    rfl
  · have hcO : Nat.Coprime p (Nat.card (normalizerPrimeComplementCore p D)) :=
      (pPrimeCore_coprime_card (p := p) (G := N)).of_dvd_right (card_map_dvd _ N.subtype)
    obtain ⟨n, hn⟩ := hD.exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hn]
    exact hcO.symm.pow_right n
  · intro o ho d hd
    obtain ⟨a, ha, rfl⟩ := ho
    exact congrArg Subtype.val (hcomm a ha ⟨d, D.le_normalizer hd⟩ hd).eq

omit [Finite G] [Fact p.Prime] in
theorem Family.mem_core_iff_product {T : Sylow p G} {D : Subgroup G} (h : Family T D)
    (g : G) : g ∈ normalizerPrimeCore p D ↔
      ∃ o ∈ normalizerPrimeComplementCore p D, ∃ d ∈ D, o * d = g := by
  have hn : D ≤ normalizer (normalizerPrimeComplementCore p D : Set G) := by
    apply le_trans _ (centralizer_le_normalizer _)
    intro d hd
    rw [mem_centralizer_iff]
    intro o ho
    exact (h.commute o ho d hd).eq
  rw [h.core_eq, ← SetLike.mem_coe,
    coe_mul_of_right_le_normalizer_left _ _ hn]
  rfl

/-- Every literal family member is centric in the fixed Sylow subgroup. -/
theorem Family.sylow_centralizer_le {T : Sylow p G} {D : Subgroup G} (h : Family T D) :
    (T : Subgroup G) ⊓ centralizer (D : Set G) ≤ D := by
  have hcO : Nat.Coprime p (Nat.card (normalizerPrimeComplementCore p D)) :=
    (pPrimeCore_coprime_card (p := p) (G := normalizer (D : Set G))).of_dvd_right
      (card_map_dvd _ (normalizer (D : Set G)).subtype)
  obtain ⟨n, hn⟩ := T.isPGroup'.exists_card_eq
  have hd : Disjoint (normalizerPrimeComplementCore p D) (T : Subgroup G) := by
    apply disjoint_of_coprime_natCard
    rw [hn]
    exact hcO.symm.pow_right n
  intro x hx
  obtain ⟨o, ho, d, hdD, he⟩ := (h.mem_core_iff_product x).mp (h.centralizer_le hx.2)
  have hoT : o ∈ (T : Subgroup G) := by
    have hh := (T : Subgroup G).mul_mem hx.1 ((T : Subgroup G).inv_mem (h.le_sylow hdD))
    simpa only [← he, mul_inv_cancel_right] using hh
  have ho1 := disjoint_def.mp hd ho hoT
  have heq : d = x := by simpa only [ho1, one_mul] using he
  exact heq ▸ hdD

/-- In particular a source-family member contains the ambient Sylow center. -/
theorem Family.center_le {T : Sylow p G} {D : Subgroup G} (h : Family T D) :
    (center T).map (T : Subgroup G).subtype ≤ D := by
  rintro x ⟨z, hz, rfl⟩
  apply h.sylow_centralizer_le
  refine ⟨z.property, ?_⟩
  change (z : G) ∈ centralizer (D : Set G)
  rw [mem_centralizer_iff]
  intro d hd
  exact congrArg Subtype.val (mem_center_iff.mp hz ⟨d, h.le_sylow hd⟩)

theorem fusion_relation (T : Sylow p G) (R : T → T → Prop)
    (hrefl : ∀ x, R x x)
    (htrans : ∀ {x y z}, R x y → R y z → R x z)
    (hlocal : ∀ D : Subgroup G, Family T D → ∀ g ∈ normalizer (D : Set G),
      ∀ x y : T, (x : G) ∈ D → g⁻¹ * (x : G) * g = (y : G) → R x y)
    {x y : T} (hxy : IsConj (x : G) (y : G)) : R x y := by
  apply T.relative_radical_fusion_relation R hrefl htrans ?_ hxy
  intro D hDT hext hcent hrad g hg x y hx hxy
  by_cases hne : D = ⊥
  · have hx1 : (x : G) = 1 := by simpa only [hne, mem_bot] using hx
    have hy1 : (y : G) = 1 := by simpa only [hx1, mul_one, inv_mul_cancel] using hxy.symm
    have he : x = y := Subtype.ext (hx1.trans hy1.symm)
    rw [he]
    exact hrefl y
  · exact hlocal D (family_of_relative_radical T D hne ⟨hDT, hext⟩ hcent hrad)
      g hg x y hx hxy

def ElementStep (T : Sylow p G) (x y : T) : Prop :=
  ∃ D : Subgroup G, Family T D ∧ (x : G) ∈ D ∧ (y : G) ∈ D ∧
    ∃ g ∈ normalizer (D : Set G), g⁻¹ * (x : G) * g = (y : G)

theorem element_fusion (T : Sylow p G) {x y : T} (hxy : IsConj (x : G) (y : G)) :
    Relation.ReflTransGen (ElementStep T) x y := by
  apply fusion_relation T (Relation.ReflTransGen (ElementStep T))
    (fun _ => .refl) (fun h₁ h₂ => h₁.trans h₂) ?_ hxy
  intro D hD g hg x y hx he
  have hy : (y : G) ∈ D := by
    have hh := (mem_normalizer_iff.mp ((normalizer (D : Set G)).inv_mem hg) (x : G)).mp hx
    simpa only [inv_inv, he] using hh
  exact Relation.ReflTransGen.single ⟨D, hD, hx, hy, g, hg, he⟩

theorem normal_p_subgroup_strongly_closed (T : Sylow p G) {M U : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M)
    (hfamily : ∀ D : Subgroup G, Family T D → normalizer (D : Set G) ≤ M)
    (hUM : U ≤ M) (hMU : M ≤ normalizer (U : Set G)) (hUp : IsPGroup p U) :
    Theory.GroupTheory.IsStronglyClosedSet (U : Set G) (T : Subgroup G) ⊤ := by
  have hUT : U ≤ (T : Subgroup G) := by
    have hh := (le_pCoreIn_of_normalizes hUp hUM hMU).trans
      (pCoreIn_le_sylow M (T.subtype hTM))
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTM] using hh
  refine ⟨hUT, ?_⟩
  intro u hu g _ hconj
  have hf := fusion_relation T (fun x y => (x : G) ∈ U → (y : G) ∈ U)
    (fun _ h => h) (fun h₁ h₂ h => h₂ (h₁ h)) (by
      intro D hD a ha x y _ hxy hx
      have hh := (mem_normalizer_iff.mp (hMU (hfamily D hD
        ((normalizer (D : Set G)).inv_mem ha))) (x : G)).mp hx
      simpa only [inv_inv, hxy] using hh)
    (x := ⟨u, hUT hu⟩) (y := ⟨g⁻¹ * u * g, hconj⟩)
    (isConj_iff.mpr ⟨g⁻¹, by simp only [inv_inv]⟩)
  exact hf hu

/-- The source's subgroup-intersection formulation of strong closure. -/
theorem normal_p_subgroup_conjugate_intersection_le (T : Sylow p G) {M U : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M)
    (hfamily : ∀ D : Subgroup G, Family T D → normalizer (D : Set G) ≤ M)
    (hUM : U ≤ M) (hMU : M ≤ normalizer (U : Set G)) (hUp : IsPGroup p U)
    (g : G) :
    BenderSuzuki.PFchapter1section1.rightConjugate U g ⊓ (T : Subgroup G) ≤ U := by
  have hc := normal_p_subgroup_strongly_closed T hTM hfamily hUM hMU hUp
  rintro x ⟨⟨u, hu, rfl⟩, hxT⟩
  change g⁻¹ * u * (g⁻¹)⁻¹ ∈ (T : Subgroup G) at hxT
  change g⁻¹ * u * (g⁻¹)⁻¹ ∈ U
  simp only [inv_inv] at hxT ⊢
  exact hc.2 u hu g (mem_top _) hxT

end AlperinGoldschmidt

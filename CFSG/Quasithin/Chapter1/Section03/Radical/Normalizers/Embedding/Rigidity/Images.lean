module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.Rigidity.Structure
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.Rigidity.Omega

/-!
# The image of X in a component's solvable radical

The full A.3.6 common clauses place the two-perfect image of X in the
odd Fitting subgroup. Its two-core is trivial, so the restricted quotient
map identifies it with X/O₂(X). Nilpotence then puts it in the p-core.
The prime p > 3 excludes the quasisimple alternatives of A.3.6.

To identify the image with Ω₁(O_p), use the actual conjugation action of T.
The center of O_p is characteristic; its inverse image in X/O₂(X) is
T-invariant. If X/O₂(X) is elementary, Xi irreducibility gives the required
central intersection dichotomy. The omega recognition lemma now applies.
No implication from radical containment to normality is an input.

Source: Aschbacher–Smith, A.3.6, pp.43–45; proof of 1.3.8, p.513.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.Rigidity
open Section02 LocalModels
variable {G : Type*} [Group G] [Finite G]

private theorem elementary_quotient_dichotomy {T X : Subgroup G} (hX : XiMember T X)
    {p : ℕ} [Fact p.Prime] (he : IsElementaryAbelian p (XiQuotient X))
    (B : Subgroup (XiQuotient X))
    (hi : ∀ (t : T) (x : X), QuotientGroup.mk' (pCore 2 X) x ∈ B →
      QuotientGroup.mk' (pCore 2 X)
        ⟨(t : G) * x * (t : G)⁻¹,
          (mem_normalizer_iff.mp (hX.invariant t.property) x).mp x.property⟩ ∈ B) :
    B = ⊥ ∨ B = ⊤ := by
  let := he
  let : Fact (IsPGroup p (XiQuotient X)) := ⟨he.isPGroup⟩
  have hf : frattini (XiQuotient X) = ⊥ :=
    frattini_eq_bot_of_isElementaryAbelian (p := p)
  let q := QuotientGroup.mk' (frattini (XiQuotient X))
  have hinv : ∀ t : T, ∀ a ∈ B.map q,
      xiFrattiniAction T X hX.invariant t a ∈ B.map q := by
    rintro t a ⟨b, hb, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) b
    refine ⟨_, hi t x hb, ?_⟩
    simp only [q, xiFrattiniAction, MonoidHom.comp_apply, quotientAut_apply_mk]
    rfl
  rcases hX.irreducible _ hinv with hb | ht
  · left
    have h := congrArg (comap q) hb
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk', MonoidHom.comap_bot,
      hf, sup_bot_eq] using h
  · right
    have h := congrArg (comap q) ht
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top,
      hf, sup_bot_eq] using h



private theorem image_eq_omega_of_core {A : Type*} [Group A] [Finite A]
    {p : ℕ} [Fact p.Prime] {T X K : Subgroup G}
    (hX : XiMember T X) (hq : XiOddQuotient p (XiQuotient X))
    (hXK : X ≤ K) (hTK : T ≤ normalizer (K : Set G))
    (e : XiQuotient K ≃* A)
    (hk : IsPGroup 2 ((e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))).comp
      (inclusion hXK)).ker)
    (hcore : ((e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))).comp
      (inclusion hXK)).range ≤ pCore p A)
    (hbot : pCore 2 (((e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))).comp
      (inclusion hXK)).range) = ⊥)
    (hs : (IsElementaryAbelian p (pCore p A) ∧ Nat.card (pCore p A) = p ^ 2) ∨
      OddExtraspecialThree p (pCore p A) ∨ HomocyclicTwo p (pCore p A)) :
    ((e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))).comp
      (inclusion hXK)).range =
      (omega (pCore p A) (p := p) 1).map (pCore p A).subtype := by
  let f := (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))).comp (inclusion hXK)
  let a := quotientImageEquiv f hk hbot
  let g := (inclusion hcore).comp a.toMonoidHom
  have hgi : Function.Injective g := (inclusion_injective hcore).comp a.injective
  have hcenter : IsElementaryAbelian p (XiQuotient X) →
      (center (pCore p A)).comap g = ⊥ ∨ (center (pCore p A)).comap g = ⊤ := by
    intro hel
    apply elementary_quotient_dichotomy hX hel
    intro t x hx
    let D := (center (pCore p A)).map (pCore p A).subtype
    have hD : D.Characteristic := characteristic_of_characteristic_of_characteristic
    let _ := conjMulDistribMulActionOfLeNormalizer T K hTK
    let aut : A ≃* A := e.symm.trans
      ((quotientAut (pCore 2 K)) (MulDistribMulAction.toMulAut T K t)) |>.trans e
    have hDx : f x ∈ D := by
      refine ⟨g (QuotientGroup.mk' (pCore 2 X) x), hx, ?_⟩
      exact quotientImageEquiv_apply_mk f hk hbot x
    have hDa := characteristic_iff_le_comap.mp hD aut hDx
    let z : X := ⟨(t : G) * x * (t : G)⁻¹,
      (mem_normalizer_iff.mp (hX.invariant t.property) x).mp x.property⟩
    have haz : aut (f x) = f z := by
      simp only [aut, f, MulEquiv.trans_apply, MonoidHom.comp_apply,
        MulEquiv.coe_toMonoidHom, e.symm_apply_apply, quotientAut_apply_mk]
      rfl
    change aut (f x) ∈ D at hDa
    rw [haz] at hDa
    obtain ⟨d, hd, hde⟩ := hDa
    have heq : g (QuotientGroup.mk' (pCore 2 X) z) = d := by
      apply Subtype.ext
      exact (quotientImageEquiv_apply_mk f hk hbot z).trans hde.symm
    change g (QuotientGroup.mk' (pCore 2 X) z) ∈ center (pCore p A)
    rw [heq]
    exact hd
  have he := range_eq_omega_of_center_dichotomy hq hs g hgi hcenter
  have hm := congrArg (map (pCore p A).subtype) he
  have hr : g.range.map (pCore p A).subtype = f.range := by
    rw [← MonoidHom.range_comp]
    have hh : (pCore p A).subtype.comp g = f.range.subtype.comp a.toMonoidHom := rfl
    have har : a.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr a.surjective
    rw [hh, MonoidHom.range_comp, har, ← MonoidHom.range_eq_map, range_subtype]
  exact hr.symm.trans hm



private theorem nonquasisimple_of_large_fitting_prime {A : Type*} [Group A] [Finite A]
    (hc : A36Common A) {p : ℕ} (hp3 : 3 < p)
    (hd : p ∣ Nat.card (fittingSubgroup A)) : ¬ IsQuasisimple A := by
  intro hA
  let := hA
  rcases hc.2.2.1 with h | h
  · have htop : (⊤ : Subgroup A) ≤ generalizedFitting A :=
      component_le_generalizedFitting A ⊤
        ⟨(inferInstance : (⊤ : Subgroup A).Normal).isSubnormal,
          IsQuasisimple.of_mulEquiv topEquiv.symm⟩
    have hfit : fittingSubgroup A = ⊤ := top_unique (h.1.symm ▸ htop)
    let : Group.IsNilpotent A := Group.nilpotent_of_mulEquiv
      ((MulEquiv.subgroupCongr hfit).trans topEquiv)
    let : IsSimpleGroup (A ⧸ center A) := IsQuasisimple.simple
    let : Nontrivial A := Function.Surjective.nontrivial
      (QuotientGroup.mk'_surjective (center A))
    exact Group.IsPerfect.not_isSolvable A inferInstance
  · rcases h.2.2 with he | he <;> rw [he] at hd
    · have := Nat.le_of_dvd (by decide : 0 < 1) hd
      omega
    · have := Nat.le_of_dvd (by decide : 0 < 3) hd
      omega

/-- The full A.3.6 structure and actual Xi action determine the omega image. -/
theorem radical_image_eq_omega {E : Type*} [Group E] [Finite E] {A : Subgroup E}
    {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) {T X K : Subgroup G}
    (hX : XiMember T X) (hq : XiOddQuotient p (XiQuotient X))
    (hXK : X ≤ K) (hTK : T ≤ normalizer (K : Set G))
    (e : XiQuotient K ≃* A) (hc : A36Conclusion A)
    (hR : X ≤ (solvableRadical K).map K.subtype) :
    ((e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))).comp
      (inclusion hXK)).range =
      (omega (pCore p A) (p := p) 1).map (pCore p A).subtype := by
  let f := (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))).comp (inclusion hXK)
  have hk : IsPGroup 2 f.ker := by
    have he : f.ker = (pCore 2 K).comap (inclusion hXK) := by
      ext x
      change e (QuotientGroup.mk' (pCore 2 K) (inclusion hXK x)) = 1 ↔ _
      rw [e.map_eq_one_iff]
      exact QuotientGroup.eq_one_iff (inclusion hXK x)
    rw [he]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hXK)
  have hr : f.range ≤ solvableRadical A := by
    rintro _ ⟨x, rfl⟩
    have hx : inclusion hXK x ∈ solvableRadical K := by
      obtain ⟨y, hy, hey⟩ := hR x.property
      exact (show y = inclusion hXK x from Subtype.ext hey) ▸ hy
    exact map_solvableRadical_le_of_surjective
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))
      (e.surjective.comp (QuotientGroup.mk'_surjective _)) (mem_map_of_mem _ hx)
  have hf := twoPerfect_le_fitting hc.2
    (hX.perfect.of_surjective f.rangeRestrict f.rangeRestrict_surjective) hr
  have hb := twoCore_eq_bot_of_le_fitting hc.2 hf
  have hqi := hq.of_mulEquiv (quotientImageEquiv f hk hb)
  have hcore := pSubgroup_le_core hqi.isPGroup hf
  have hd : p ∣ Nat.card (fittingSubgroup A) := by
    apply (dvd_trans · (card_dvd_of_le hf))
    rcases hqi with h | h
    · rw [h.2]
      exact dvd_pow_self p (by decide)
    · rw [h.2.1]
      exact dvd_pow_self p (by decide)
  have hn := RadicalStructure.nonsimple_radical hc
    (nonquasisimple_of_large_fitting_prime hc.2 hp3 hd)
  exact image_eq_omega_of_core hX hq hXK hTK e hk hcore hb
    (RadicalStructure.radical_core hn hd).2.2

end CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.Rigidity

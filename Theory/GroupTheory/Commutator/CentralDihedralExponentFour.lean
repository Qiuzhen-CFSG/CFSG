module

public import Theory.GroupTheory.Commutator.CentralSylowTransfer
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic

/-!
# Splitting the derived part of an exponent-four dihedral cover

For a central extension of D8 whose kernel has exponent two, an exponent-four
cover has trivial intersection between its kernel and derived subgroup.
Lifting a rotation r and reflection s gives a central element
`a = s * r * s⁻¹ * r` in the kernel. The commutator is `a * (r ^ 2)⁻¹`,
so it squares to one. Its nontrivial image in D8 shows that its cyclic
subgroup misses the kernel. The dihedral lifting calculation places the
whole derived subgroup in that cyclic subgroup.

Central Sylow transfer then gives the same disjointness for a finite central
extension with kernel of order two and an exponent-four Sylow subgroup whose
image is D8. Perfectness of the quotient is unnecessary for disjointness;
it is used separately to make the restricted derived map surjective.

This is the splitting step in Held, "A Characterization of some multiply
transitive permutation groups, I", Illinois J. Math. 13 (1969), 224--240,
Lemma 4.2, p.234, DOI 10.1215/ijm/1256053756. The private dihedral-lift
calculation below follows `CentralDihedral.lean`, preserving that module's
existing visibility and dependency boundary.
-/

open scoped commutatorElement
open Subgroup

namespace CentralExtension

private theorem commutator_conj_relations
    {G : Type*} [Group G] (r s : G)
    (hs : s ^ 2 ∈ center G)
    (hr : s * r * s⁻¹ * r ∈ center G) :
    Commute r ⁅s, r⁆ ∧ s * ⁅s, r⁆ * s⁻¹ = ⁅s, r⁆⁻¹ := by
  let a := s * r * s⁻¹ * r
  have hform : s * r * s⁻¹ = a * r⁻¹ := by dsimp [a]; group
  have hacomm : Commute a r := (mem_center_iff.mp hr r).symm
  have htcomm : Commute (s * r * s⁻¹) r := by
    rw [hform]
    exact hacomm.mul_left (Commute.refl r).inv_left
  have hrc : Commute r ⁅s, r⁆ := by
    change r * (s * r * s⁻¹ * r⁻¹) = (s * r * s⁻¹ * r⁻¹) * r
    calc
      r * (s * r * s⁻¹ * r⁻¹) = (r * (s * r * s⁻¹)) * r⁻¹ := by group
      _ = ((s * r * s⁻¹) * r) * r⁻¹ := by rw [htcomm.eq]
      _ = (s * r * s⁻¹ * r⁻¹) * r := by group
  have hsconj : s * (s * r * s⁻¹) * s⁻¹ = r := by
    calc
      s * (s * r * s⁻¹) * s⁻¹ = s ^ 2 * r * (s ^ 2)⁻¹ := by
        simp only [pow_two]; group
      _ = r := by rw [← (mem_center_iff.mp hs r)]; group
  refine ⟨hrc, ?_⟩
  calc
    s * ⁅s, r⁆ * s⁻¹ =
        (s * (s * r * s⁻¹) * s⁻¹) * (s * r * s⁻¹)⁻¹ := by
          simp only [commutatorElement_def]; group
    _ = r * (s * r * s⁻¹)⁻¹ := by rw [hsconj]
    _ = ⁅s, r⁆⁻¹ := by simp only [commutatorElement_def]; group

private theorem eq_top_of_dihedral_lifts
    {G : Type*} [Group G] {n : ℕ} [NeZero n]
    (f : G →* DihedralGroup n) (r s : G)
    (hr : f r = DihedralGroup.r 1) (hs : f s = DihedralGroup.sr 0)
    (H : Subgroup G) (hker : f.ker ≤ H) (hrH : r ∈ H) (hsH : s ∈ H) :
    H = ⊤ := by
  apply top_unique
  intro g _
  have lift_mem (d : G) (hd : d ∈ H) (hfd : f d = f g) : g ∈ H := by
    have hk : g * d⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hfd, mul_inv_cancel]
    simpa using H.mul_mem (hker hk) hd
  cases hfg : f g with
  | r i =>
      apply lift_mem (r ^ i.val) (H.pow_mem hrH i.val)
      simp [map_pow, hr, hfg]
  | sr i =>
      apply lift_mem (s * r ^ i.val) (H.mul_mem hsH (H.pow_mem hrH i.val))
      simp [map_pow, hr, hs, hfg]

private theorem derived_le_lift_commutator
    {G : Type*} [Group G] {n : ℕ} [NeZero n]
    (f : G →* DihedralGroup n) (hker : f.ker ≤ center G)
    (r s : G) (hr : f r = DihedralGroup.r 1) (hs : f s = DihedralGroup.sr 0) :
    _root_.commutator G ≤ zpowers ⁅s, r⁆ ∧
      s * ⁅s, r⁆ * s⁻¹ = ⁅s, r⁆⁻¹ := by
  have hs2 : s ^ 2 ∈ center G := by
    apply hker
    simp [MonoidHom.mem_ker, hs, pow_two]
  have hsr : s * r * s⁻¹ * r ∈ center G := by
    apply hker
    simp [MonoidHom.mem_ker, hr, hs, map_mul, map_inv]
  obtain ⟨hrc, hsc⟩ := commutator_conj_relations r s hs2 hsr
  let C : Subgroup G := zpowers ⁅s, r⁆
  have hnorm : C.Normal := by
    apply normalizer_eq_top_iff.mp
    apply eq_top_of_dihedral_lifts f r s hr hs
    · intro k hk
      rw [mem_normalizer_iff_map_conj_eq]
      dsimp [C]
      rw [MonoidHom.map_zpowers]
      congr 1
      change k * ⁅s, r⁆ * k⁻¹ = ⁅s, r⁆
      rw [← mem_center_iff.mp (hker hk) ⁅s, r⁆]
      group
    · rw [mem_normalizer_iff_map_conj_eq]
      dsimp [C]
      rw [MonoidHom.map_zpowers]
      congr 1
      change r * ⁅s, r⁆ * r⁻¹ = ⁅s, r⁆
      rw [hrc.eq]
      group
    · rw [mem_normalizer_iff_map_conj_eq]
      dsimp [C]
      rw [MonoidHom.map_zpowers]
      change zpowers (s * ⁅s, r⁆ * s⁻¹) = zpowers ⁅s, r⁆
      rw [hsc, zpowers_inv]
  let : C.Normal := hnorm
  let q : G →* G ⧸ C := QuotientGroup.mk' C
  have hqcomm : Commute (q s) (q r) := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr (mem_zpowers ⁅s, r⁆)
  have hqker (k : G) (hk : k ∈ f.ker) : q k ∈ center (G ⧸ C) := by
    rw [mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective C y
    simpa only [map_mul] using congrArg q (mem_center_iff.mp (hker hk) x)
  have hqcentral (a : G) (har : Commute (q a) (q r))
      (has : Commute (q a) (q s)) : q a ∈ center (G ⧸ C) := by
    have hH : (centralizer ({q a} : Set (G ⧸ C))).comap q = ⊤ := by
      apply eq_top_of_dihedral_lifts f r s hr hs
      · intro k hk
        exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp (hqker k hk) (q a)).symm
      · exact mem_centralizer_singleton_iff.mpr har.eq.symm
      · exact mem_centralizer_singleton_iff.mpr has.eq.symm
    rw [mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective C y
    have hx : q x ∈ centralizer ({q a} : Set (G ⧸ C)) := by
      change x ∈ (centralizer ({q a} : Set (G ⧸ C))).comap q
      rw [hH]; trivial
    exact mem_centralizer_singleton_iff.mp hx
  have hqr := hqcentral r (Commute.refl _) hqcomm.symm
  have hqs := hqcentral s hqcomm (Commute.refl _)
  have htop : (center (G ⧸ C)).comap q = ⊤ :=
    eq_top_of_dihedral_lifts f r s hr hs _ hqker hqr hqs
  have habel : IsMulCommutative (G ⧸ C) := by
    apply center_eq_top_iff.mp
    apply top_unique
    intro y _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective C y
    change x ∈ (center (G ⧸ C)).comap q
    rw [htop]; trivial
  exact ⟨Normal.quotient_commutative_iff_commutator_le.mp habel, hsc⟩


/-- A central exponent-two kernel misses the derived subgroup of an
exponent-four cover of the dihedral group of order eight. -/
public theorem ker_inf_commutator_eq_bot_of_dihedral_four
    {G : Type*} [Group G]
    (f : G →* DihedralGroup 4) (hf : Function.Surjective f)
    (hker : f.ker ≤ center G)
    (hker2 : ∀ x ∈ f.ker, x ^ 2 = 1)
    (hfour : ∀ x : G, x ^ 4 = 1) :
    f.ker ⊓ _root_.commutator G = ⊥ := by
  classical
  obtain ⟨r, hr⟩ := hf (DihedralGroup.r 1)
  obtain ⟨s, hs⟩ := hf (DihedralGroup.sr 0)
  have hd := (derived_le_lift_commutator f hker r s hr hs).1
  let a := s * r * s⁻¹ * r
  have ha : a ∈ f.ker := by
    simp [a, MonoidHom.mem_ker, hr, hs]
  have hacomm : Commute a ((r ^ 2)⁻¹) :=
    (mem_center_iff.mp (hker ha) _).symm
  have hcform : ⁅s, r⁆ = a * (r ^ 2)⁻¹ := by
    dsimp [a]
    simp only [commutatorElement_def, pow_two]
    group
  have hc2 : ⁅s, r⁆ ^ 2 = 1 := by
    rw [hcform, hacomm.mul_pow, hker2 a ha, one_mul, inv_pow, ← pow_mul]
    simp [hfour r]
  have hcimage : f ⁅s, r⁆ = DihedralGroup.r 2 := by
    norm_num [commutatorElement_def, hr, hs]
    decide
  have hcne : ⁅s, r⁆ ≠ 1 := by
    intro h
    have hh : (DihedralGroup.r 2 : DihedralGroup 4) = 1 := by
      rw [← hcimage, h, map_one]
    have : (DihedralGroup.r 2 : DihedralGroup 4) ≠ 1 := by decide
    exact this hh
  have horder : orderOf ⁅s, r⁆ = 2 := orderOf_eq_prime hc2 hcne
  apply eq_bot_iff.mpr
  intro x hx
  have hcx : x ∈ zpowers ⁅s, r⁆ := hd hx.2
  have hfin : IsOfFinOrder ⁅s, r⁆ :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, hc2⟩
  have hcases : x = 1 ∨ x = ⁅s, r⁆ := by
    obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp
      (hfin.mem_zpowers_iff_mem_range_orderOf.mp hcx)
    have hi' : i < 2 := horder ▸ Finset.mem_range.mp hi
    interval_cases i <;> simp_all
  rcases hcases with rfl | rfl
  · exact one_mem _
  · have hxmap : f ⁅s, r⁆ = 1 := hx.1
    rw [hcimage] at hxmap
    exact False.elim ((by decide : (DihedralGroup.r 2 : DihedralGroup 4) ≠ 1) hxmap)

/-- In a finite central double cover, an exponent-four Sylow two-subgroup
with dihedral image of order eight forces the kernel to miss the derived subgroup. -/
public theorem ker_inf_commutator_eq_bot_of_dihedral_four_sylow
    {E B : Type*} [Group E] [Finite E] [Group B] [Finite B]
    (f : E →* B) (hf : Function.Surjective f)
    (hcentral : f.ker ≤ center E) (hcard : Nat.card f.ker = 2)
    (S : Sylow 2 E)
    (e : Sylow.mapSurjective hf S ≃* DihedralGroup 4)
    (hfour : ∀ x : S, x ^ 4 = 1) :
    f.ker ⊓ _root_.commutator E = ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hkernel : IsPGroup 2 f.ker := IsPGroup.of_card (n := 1) (by simpa using hcard)
  have hker2 (x : E) (hx : x ∈ f.ker) : x ^ 2 = 1 := by
    have h := pow_card_eq_one' (x := (⟨x, hx⟩ : f.ker))
    rw [hcard] at h
    exact congrArg Subtype.val h
  let T : Sylow 2 B := Sylow.mapSurjective hf S
  let q : S →* T := f.subgroupMap (S : Subgroup E)
  have hq : Function.Surjective q := f.subgroupMap_surjective (S : Subgroup E)
  let g : S →* DihedralGroup 4 := e.toMonoidHom.comp q
  have hg : Function.Surjective g := e.surjective.comp hq
  have hgker (x : S) (hx : x ∈ g.ker) : (x : E) ∈ f.ker := by
    have hqx : q x = 1 := by
      apply e.injective
      change e (q x) = 1 at hx
      exact hx.trans e.map_one.symm
    exact congrArg Subtype.val hqx
  have hgcenter : g.ker ≤ center S := by
    intro x hx
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_center_iff.mp (hcentral (hgker x hx)) (y : E))
  have hg2 (x : S) (hx : x ∈ g.ker) : x ^ 2 = 1 :=
    Subtype.ext (hker2 x (hgker x hx))
  have hlocal := ker_inf_commutator_eq_bot_of_dihedral_four g hg hgcenter hg2 hfour
  have hkerS : f.ker ≤ (S : Subgroup E) := hkernel.le_sylow_of_normal S
  apply eq_bot_iff.mpr
  intro x hx
  have hder : x ∈ ⁅(S : Subgroup E), (S : Subgroup E)⁆ :=
    center_inf_commutator_inf_sylow_le_commutator S
      ⟨⟨hcentral hx.1, hx.2⟩, hkerS hx.1⟩
  rw [← map_subtype_commutator] at hder
  obtain ⟨y, hy, hyx⟩ := hder
  change (y : E) = x at hyx
  have hyker : y ∈ g.ker := by
    have hqy : q y = 1 := Subtype.ext (by
      change f (y : E) = 1
      rw [hyx]
      exact hx.1)
    change e (q y) = 1
    rw [hqy, map_one]
  have hyone : y = 1 := by
    have hmem : y ∈ g.ker ⊓ _root_.commutator S := ⟨hyker, hy⟩
    rwa [hlocal, mem_bot] at hmem
  exact hyx.symm.trans (congrArg Subtype.val hyone)

end CentralExtension

module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer.Component
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer.Products
public import Theory.GroupTheory.DihedralGeneratedFactor
public import Theory.GroupTheory.MarkedInternalProduct

/-!
# Marked product assembly from a normalizer bound and a centralizing inverter

An involution inverting the order-five subgroup generates its actual
D₁₀ extension. If it centralizes the intrinsic A₅ component, these two
subgroups commute and have trivial intersection, since A₅ is centerless.
Their product has order 600, so an upper bound of 600 on the full
normalizer makes it the whole normalizer. The internal-product equivalence
retains both prescribed coordinate-factor equations.

The geometric centralization and normalizer bound remain explicit here;
this module does not claim to construct them from the selected geometry.

Source: Aschbacher, *Sporadic Groups* (1994), 47.2(2), printed p.261.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer.LocalProduct
variable {G : Type*} [Group G] [Finite G]
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Inversion preserves the literal subgroup, hence belongs to its normalizer. -/
theorem mem_normalizer_of_inverts (E : Subgroup G) (j : G)
    (hinv : ∀ x ∈ E, j * x * j⁻¹ = x⁻¹) : j ∈ normalizer (E : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq]
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x, hx, rfl⟩
    change j * x * j⁻¹ ∈ E
    rw [hinv x hx]
    exact E.inv_mem hx
  · rw [card_map_of_injective (MulAut.conj j).injective]

omit [Finite G] in
private theorem dihedral_factor (E : Subgroup G) (hE : Nat.card E = 5)
    (j : G) (hj : orderOf j = 2)
    (hinv : ∀ x ∈ E, j * x * j⁻¹ = x⁻¹) :
    Nonempty ((E ⊔ zpowers j : Subgroup G) ≃* DihedralGroup 5) := by
  let : IsCyclic E := isCyclic_of_prime_card hE
  obtain ⟨c, hc⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic E)
  have hgen : zpowers (c : G) = E := by
    have hh := congrArg (Subgroup.map E.subtype) hc
    simpa only [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, range_subtype, Subgroup.subtype_apply] using hh
  have hc5 : orderOf (c : G) = 5 := by rw [← Nat.card_zpowers, hgen, hE]
  have hout : j ∉ zpowers (c : G) := by
    rw [hgen]
    intro hjE
    have hh := E.orderOf_dvd_natCard hjE
    rw [hj, hE] at hh
    norm_num at hh
  have h := (DihedralGroup.sup_zpowers_equiv_of_inversion (by decide : 0 < 5)
    (c : G) j hc5 (hj ▸ pow_orderOf_eq_one j) hout (hinv c c.property)).2
  rwa [hgen] at h

omit [Finite G] in
private theorem disjoint_of_centralizes_a5 (A L : Subgroup G)
    (eL : L ≃* alternatingGroup (Fin 5)) (hc : A ≤ centralizer (L : Set G)) :
    Disjoint A L := by
  rw [disjoint_def]
  intro x hxA hxL
  have hz : (⟨x, hxL⟩ : L) ∈ center L := by
    rw [mem_center_iff]
    intro y
    apply Subtype.ext
    exact hc hxA y y.property
  have hz' : eL ⟨x, hxL⟩ ∈ center (alternatingGroup (Fin 5)) := by
    rw [mem_center_iff]
    intro y
    obtain ⟨u, rfl⟩ := eL.surjective y
    simpa only [map_mul] using congrArg eL (mem_center_iff.mp hz u)
  rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at hz'
  exact congrArg Subtype.val (eL.map_eq_one_iff.mp hz')

omit [Finite G] in
private theorem marked_factors {H A B : Subgroup G}
    (e : H ≃* A × B)
    (hA : (A.subgroupOf H).map e.toMonoidHom = (⊤ : Subgroup A).prod ⊥)
    (hB : (B.subgroupOf H).map e.toMonoidHom = (⊥ : Subgroup A).prod ⊤)
    (hAH : A ≤ H) (hBH : B ≤ H)
    {U V : Type*} [Group U] [Group V] (a : A ≃* U) (b : B ≃* V) :
    let d := e.trans (a.prodCongr b)
    ((⊤ : Subgroup U).prod (⊥ : Subgroup V)).map
      (H.subtype.comp d.symm.toMonoidHom) = A ∧
    ((⊥ : Subgroup U).prod (⊤ : Subgroup V)).map
      (H.subtype.comp d.symm.toMonoidHom) = B := by
  dsimp only
  have hleft : ((⊤ : Subgroup U).prod (⊥ : Subgroup V)).map
      (a.prodCongr b).symm.toMonoidHom = (⊤ : Subgroup A).prod ⊥ := by
    rw [map_equiv_eq_comap_symm']
    ext x
    change (True ∧ b x.2 = 1) ↔ (True ∧ x.2 = 1)
    simp
  have hright : ((⊥ : Subgroup U).prod (⊤ : Subgroup V)).map
      (a.prodCongr b).symm.toMonoidHom = (⊥ : Subgroup A).prod ⊤ := by
    rw [map_equiv_eq_comap_symm']
    ext x
    change (a x.1 = 1 ∧ True) ↔ (x.1 = 1 ∧ True)
    simp
  constructor
  · change ((⊤ : Subgroup U).prod (⊥ : Subgroup V)).map (H.subtype.comp (e.symm.toMonoidHom.comp (a.prodCongr b).symm.toMonoidHom)) = A
    rw [← map_map, ← map_map, hleft, ← hA, map_map, map_map]
    have hh : H.subtype.comp (e.symm.toMonoidHom.comp e.toMonoidHom) = H.subtype := by
      ext x
      simp
    change (A.subgroupOf H).map (H.subtype.comp (e.symm.toMonoidHom.comp e.toMonoidHom)) = A
    rw [hh]
    exact map_subgroupOf_eq_of_le hAH
  · change ((⊥ : Subgroup U).prod (⊤ : Subgroup V)).map (H.subtype.comp (e.symm.toMonoidHom.comp (a.prodCongr b).symm.toMonoidHom)) = B
    rw [← map_map, ← map_map, hright, ← hB, map_map, map_map]
    have hh : H.subtype.comp (e.symm.toMonoidHom.comp e.toMonoidHom) = H.subtype := by
      ext x
      simp
    change (B.subgroupOf H).map (H.subtype.comp (e.symm.toMonoidHom.comp e.toMonoidHom)) = B
    rw [hh]
    exact map_subgroupOf_eq_of_le hBH

/-- Once the geometric action and normalizer bound are known, the inverter
and the intrinsic component give both marked factors in the literal normalizer. -/
theorem productData_of_inverter_and_bound (D : Seed G) (E : Subgroup G)
    (hE : Nat.card E = 5) (e : Quotient E ≃* alternatingGroup (Fin 5))
    (hN : Nat.card (normalizer (E : Set G)) ≤ 600)
    (j : G) (hj : orderOf j = 2) (hconj : IsConj D.z j)
    (hinv : ∀ x ∈ E, j * x * j⁻¹ = x⁻¹)
    (hcomm : j ∈ centralizer (fiveComponent E : Set G)) :
    Nonempty (ProductData D E) := by
  let A := E ⊔ zpowers j
  let L := fiveComponent E
  obtain ⟨eA⟩ := dihedral_factor E hE j hj hinv
  obtain ⟨eL⟩ := fiveComponent_equiv E hE e
  have hLC : L ≤ centralizer (E : Set G) := map_subtype_le _
  have hAC : A ≤ centralizer (L : Set G) :=
    sup_le (le_centralizer_iff.mpr hLC) (zpowers_le.mpr hcomm)
  have hdis : Disjoint A L := disjoint_of_centralizes_a5 A L eL hAC
  have hAN : A ≤ normalizer (E : Set G) :=
    sup_le E.le_normalizer (zpowers_le.mpr (mem_normalizer_of_inverts E j hinv))
  have hLN : L ≤ normalizer (E : Set G) :=
    hLC.trans (centralizer_le_normalizer (E : Set G))
  have hsup : A ⊔ L = normalizer (E : Set G) := by
    apply eq_of_le_of_card_ge (sup_le hAN hLN)
    obtain ⟨d, _, _⟩ := Theory.GroupTheory.exists_marked_internalProductEquiv
      (A ⊔ L) A L rfl hdis hAC
    rw [Nat.card_congr d.toEquiv, Nat.card_prod,
      Nat.card_congr eA.toEquiv, Nat.card_congr eL.toEquiv,
      DihedralGroup.nat_card, InvolutionGeometry.card_A5]
    exact hN
  obtain ⟨d, hdA, hdL⟩ := Theory.GroupTheory.exists_marked_internalProductEquiv
    (normalizer (E : Set G)) A L hsup hdis hAC
  obtain ⟨hmarkA, hmarkL⟩ := marked_factors d hdA hdL hAN hLN eA eL
  exact ⟨{
    equiv := d.trans (eA.prodCongr eL)
    component_factor := hmarkL
    inverter := j
    inverter_conj := hconj
    inverts := hinv
    dihedral_factor := hmarkA }⟩
end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer.LocalProduct

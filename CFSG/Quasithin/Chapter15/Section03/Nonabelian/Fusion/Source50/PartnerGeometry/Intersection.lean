module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.Power
public import Theory.GroupTheory.AlmostSpecialIntersection
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.ElementaryAbelian.Extraspecial

/-!
# The elementary rank-one intersection in source 15.3.56

The original F=U∩Hʸ and X=Fʸ have intersection U∩Uʸ. The point plane
V₀=Z∨Zʸ is y-invariant and lies in U, while U centralizes Z. These facts
identify the two descriptions of E. Disjoint conjugate Frattini bounds
make E elementary. Its commutators with J=⟨U,Uʸ⟩ lie in V₀, so E is
normal in J and lies in its two-core.

Source: Aschbacher–Smith, 15.3.56(3), printed p.1147; the repeated
intersection argument from G.2.3 is used without imposing T-normality
on the individual tensor factor Y₁.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
open Recognition
variable {G : Type*} [Group G] (Z ZS : Subgroup G)

/-- Right conjugation transports the literal ambient centralizer. -/
theorem rightConjugate_centralizer (A : Subgroup G) (y : G) :
    rightConjugate (centralizer (A : Set G)) y =
      centralizer (rightConjugate A y : Set G) := by
  let e := MulAut.conj y⁻¹
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro a ha
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hx (e a) (mem_map_of_mem _ ha)

private theorem conjugate_inf (A B : Subgroup G) (y : G) :
    rightConjugate (A ⊓ B) y = rightConjugate A y ⊓ rightConjugate B y :=
  map_inf _ _ _ (MulAut.conj y⁻¹).injective

/-- The source's F∩Fʸ equals the literal intersection of the two U conjugates.
Only the natural point-plane marking is used. -/
theorem intersectionE_eq (V₀ : Subgroup G) (y : G)
    (hZS : ZS ≤ centralizerH Z)
    (hplane : V₀ = Z ⊔ rightConjugate Z y)
    (hy : y ∈ normalizer (V₀ : Set G)) :
    intersectionE Z ZS y = closureU Z ZS ⊓ rightConjugate (closureU Z ZS) y := by
  have hU : closureU Z ZS ≤ centralizerH Z := closureU_le_H hZS
  have hUy : rightConjugate (closureU Z ZS) y ≤
      centralizer (rightConjugate Z y : Set G) := by
    rw [← rightConjugate_centralizer]
    exact map_mono hU
  have hplaneY : rightConjugate V₀ y = V₀ :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (V₀ : Set G)).inv_mem hy)
  have hZyy : rightConjugate (rightConjugate Z y) y ≤ V₀ := by
    rw [← hplaneY]
    apply map_mono
    rw [hplane]
    exact le_sup_right
  have hX : partnerX Z ZS y = rightConjugate (closureU Z ZS) y ⊓
      centralizer (rightConjugate (rightConjugate Z y) y : Set G) := by
    rw [partnerX, intersectionF, conjugate_inf, rightConjugate_centralizer, rightConjugate_centralizer]
  have hF : intersectionF Z ZS y = closureU Z ZS ⊓
      centralizer (rightConjugate Z y : Set G) := by
    rw [intersectionF, rightConjugate_centralizer]
  rw [intersectionE, hX, hF]
  apply le_antisymm
  · exact fun _ hx => ⟨hx.1.1, hx.2.1⟩
  · intro x hx
    have hxplane : x ∈ centralizer (V₀ : Set G) := by
      have hcZ : Z ≤ centralizer ({x} : Set G) := fun z hz =>
        mem_centralizer_singleton_iff.mpr (hU hx.1 z hz)
      have hcZy : rightConjugate Z y ≤ centralizer ({x} : Set G) := fun z hz =>
        mem_centralizer_singleton_iff.mpr (hUy hx.2 z hz)
      intro z hz
      have hv : V₀ ≤ centralizer ({x} : Set G) := by
        rw [hplane]
        exact sup_le hcZ hcZy
      exact mem_centralizer_singleton_iff.mp (hv hz)
    exact ⟨⟨hx.1, hUy hx.2⟩, ⟨hx.2, centralizer_le hZyy hxplane⟩⟩

/-- The actual point plane lies in E, and the intersection supplies the
normal elementary first layer of the rank-one pair. -/
theorem rank_one_intersection_layer [Finite G]
    (V₀ : Subgroup G) (y : G)
    (hZS : ZS ≤ centralizerH Z)
    (hp : IsPGroup 2 (closureU Z ZS))
    (hf : (frattini (closureU Z ZS)).map (closureU Z ZS).subtype ≤ Z)
    (hplane : V₀ = Z ⊔ rightConjugate Z y)
    (hVU : V₀ ≤ closureU Z ZS)
    (hy : y ∈ normalizer (V₀ : Set G))
    (hdis : Disjoint Z (rightConjugate Z y)) :
    V₀ ≤ intersectionE Z ZS y ∧
      intersectionE Z ZS y ≤ pairP Z ZS y ∧
      pairI Z ZS y ≤ normalizer (intersectionE Z ZS y : Set G) ∧
      ⁅intersectionE Z ZS y, pairI Z ZS y⁆ ≤ V₀ ∧
      IsElementaryAbelian 2 (intersectionE Z ZS y) := by
  have hZV : Z ≤ V₀ := by
    rw [hplane]
    exact le_sup_left
  have hVg : rightConjugate V₀ y = V₀ :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (V₀ : Set G)).inv_mem hy)
  have hVU' : V₀ ≤ rightConjugate (closureU Z ZS) y := by
    rw [← hVg]
    exact map_mono hVU
  have hEeq := intersectionE_eq Z ZS V₀ y hZS hplane hy
  have hVE : V₀ ≤ intersectionE Z ZS y := by
    rw [hEeq]
    exact le_inf hVU hVU'
  have hderived : ⁅closureU Z ZS, closureU Z ZS⁆ ≤ V₀ :=
    (derived_le_of_frattini_image_le hp hf).trans hZV
  have hderivedY : ⁅rightConjugate (closureU Z ZS) y,
      rightConjugate (closureU Z ZS) y⁆ ≤ V₀ := by
    have hh := map_mono (f := (MulAut.conj y⁻¹).toMonoidHom) hderived
    rwa [map_commutator, show V₀.map (MulAut.conj y⁻¹).toMonoidHom = V₀ from hVg] at hh
  have hIV : pairI Z ZS y ≤ normalizer (V₀ : Set G) := by
    apply sup_le
    · exact le_normalizer_iff_commutator_le_right.mpr
        ((commutator_mono le_rfl hVU).trans hderived)
    · exact le_normalizer_iff_commutator_le_right.mpr
        ((commutator_mono le_rfl hVU').trans hderivedY)
  have hcomm : ⁅intersectionE Z ZS y, pairI Z ZS y⁆ ≤ V₀ := by
    rw [hEeq]
    exact intersection_commutator_sup_le hderived hderivedY hIV
  have hnorm : pairI Z ZS y ≤ normalizer (intersectionE Z ZS y : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hcomm.trans hVE)
  have hEI : intersectionE Z ZS y ≤ pairI Z ZS y := by
    rw [hEeq]
    exact inf_le_left.trans le_sup_left
  have helem : IsElementaryAbelian 2 (intersectionE Z ZS y) := by
    rw [hEeq]
    exact conjugate_intersection_elementary hp hf y⁻¹ hdis
  let := helem
  exact ⟨hVE, le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 _) hEI hnorm,
    hnorm, hcomm, helem⟩

private theorem extraspecial_centralizer_index_two
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 2 P]
    (u : P) (hu : u ∉ center P) : (centralizer ({u} : Set P)).index = 2 := by
  have hc (x : P) : ⁅u,x⁆ ∈ center P := by
    let := IsExtraspecial.quotient_elementary_abelian 2 P
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (center P) ⁅u,x⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  let f : P →* center P := {
    toFun x := ⟨⁅u,x⁆, hc x⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' x y := by
      apply Subtype.ext
      change ⁅u,x*y⁆ = ⁅u,x⁆ * ⁅u,y⁆
      rw [commutatorElement_mul_right_eq_mul_conj, mul_assoc ⁅u,x⁆ x ⁅u,y⁆,
        mem_center_iff.mp (hc y) x]
      simp only [← mul_assoc, mul_inv_cancel_right] }
  have hk : f.ker = centralizer ({u} : Set P) := by
    ext x
    change (⟨⁅u,x⁆, hc x⟩ : center P) = 1 ↔ _
    rw [Subtype.ext_iff, coe_one, commutatorElement_eq_one_iff_mul_comm,
      mem_centralizer_singleton_iff]
    exact eq_comm
  have hi : (centralizer ({u} : Set P)).index ≤ 2 := by
    rw [← hk, index_ker, ← IsExtraspecial.center_order_p 2 P]
    exact Nat.card_le_card_of_injective _ f.range.subtype_injective
  have hn : (centralizer ({u} : Set P)).index ≠ 1 := by
    intro he
    apply hu
    apply mem_center_iff.mpr
    intro x
    exact mem_centralizer_singleton_iff.mp ((index_eq_one.mp he).symm ▸ mem_top x)
  have hp := (centralizer ({u} : Set P)).index_ne_zero_of_finite
  omega

/-- The noncentral conjugate point makes the literal F=U∩Hʸ an index-two
subgroup of U, as required by the rank-one core argument. -/
theorem intersectionF_index [Finite G] [IsExtraspecial 2 (closureU Z ZS)]
    (y : G) (hcenter : center (closureU Z ZS) = Z.subgroupOf (closureU Z ZS))
    (hZcard : Nat.card Z = 2)
    (hZy : rightConjugate Z y ≤ closureU Z ZS)
    (hdis : Disjoint Z (rightConjugate Z y)) :
    (intersectionF Z ZS y).relIndex (closureU Z ZS) = 2 := by
  have hycard : Nat.card (rightConjugate Z y) = 2 :=
    (card_map_of_injective (MulAut.conj y⁻¹).injective).trans hZcard
  obtain ⟨a, ha, hall⟩ := (Nat.card_eq_two_iff' (1 : rightConjugate Z y)).mp hycard
  let u : closureU Z ZS := ⟨a, hZy a.property⟩
  have hu : u ∉ center (closureU Z ZS) := by
    rw [hcenter]
    intro huZ
    have he : (a : G) = 1 := disjoint_def.mp hdis huZ a.property
    exact ha (Subtype.ext he)
  have hF : (intersectionF Z ZS y).subgroupOf (closureU Z ZS) =
      centralizer ({u} : Set (closureU Z ZS)) := by
    ext x
    change ((x : G) ∈ closureU Z ZS ∧
      (x : G) ∈ rightConjugate (centralizerH Z) y) ↔ _
    rw [rightConjugate_centralizer, mem_centralizer_singleton_iff]
    constructor
    · intro hx
      exact Subtype.ext (hx.2 a a.property).symm
    · intro hx
      refine ⟨x.property, ?_⟩
      intro b hb
      by_cases hb1 : b = 1
      · simp [hb1]
      have he : (⟨b, hb⟩ : rightConjugate Z y) = a := hall _ (fun h => hb1 (congrArg Subtype.val h))
      have he' : b = (a : G) := congrArg Subtype.val he
      rw [he']
      exact (congrArg Subtype.val hx).symm
  change ((intersectionF Z ZS y).subgroupOf (closureU Z ZS)).index = 2
  rw [hF]
  exact extraspecial_centralizer_index_two u hu

/-- The actual E-image is totally singular for the previously constructed
power form, not an unrelated abstract orthogonal structure. -/
theorem intersectionE_totally_singular
    [(Z.subgroupOf (closureU Z ZS)).Normal]
    [IsElementaryAbelian 2 (VectorQuotient Z ZS)]
    (y : G) (q : QuadraticForm (ZMod 2) (Space Z ZS))
    (hpower : ∀ x : closureU Z ZS,
      q (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) x)) = 0 ↔
        x ^ 2 = 1)
    (hE : IsElementaryAbelian 2 (intersectionE Z ZS y)) :
    ∀ w ∈ Recognition.vectorImage Z ZS (intersectionE Z ZS y),
      q (Additive.ofMul w) = 0 := by
  let := hE
  rintro w ⟨u, hu, rfl⟩
  apply (hpower u).mpr
  have he := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 (intersectionE Z ZS y))
    (⟨u, hu⟩ : intersectionE Z ZS y)
  apply Subtype.ext
  exact congrArg (fun e : intersectionE Z ZS y => (e : G)) he

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry

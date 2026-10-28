module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.AbelianNormalizer
public import Theory.SpecificGroups.GL2.FiveWreathSylow
public import Mathlib.GroupTheory.IndexNormal

/-!
# The reflection carried by the marked cyclic-four wreath complement

The cyclic-four wreath product has a unique central involution. Hence two
distinct marked involutions z,u in an abelian subgroup I of order16 force u
noncentral. Its centralizer, containing I and properly contained in the group
of order32, is exactly I. The normal index-two subgroup I has four elements
whose square is one, so every outside element fixes z and interchanges u,zu.
The finite checks inspect elements of C₄ wr C₂ and C₄², not subgroup lattices.
Source: Aschbacher--Smith, paragraph preceding J.4.8, printed p.443.
-/

public section
noncomputable section
namespace Tits.ExceptionalParabolics.FullRee.LongRootPaths.WreathReflection
open Subgroup
abbrev C2 := Multiplicative (ZMod 2)
abbrev C4 := Multiplicative (ZMod 4)
abbrev W := RegularWreathProduct C4 C2
abbrev A4 := C4 × C4

private instance : Fintype W := Fintype.ofEquiv ((C2 → C4) × C2)
  (RegularWreathProduct.equivProd C4 C2).symm
private instance : DecidableEq W := (RegularWreathProduct.equivProd C4 C2).injective.decidableEq

private def centralTwo : W := ⟨fun _ => Multiplicative.ofAdd 2, 1⟩

private theorem central_two_cases (x : W) (hc : ∀ y, y*x=x*y) (h2 : x^2=1) :
    x=1 ∨ x=centralTwo := by
  have h : ∀ a : W, (∀ b : W, b*a=a*b) → a^2=1 → a=1 ∨ a=centralTwo := by
    decide +kernel
  exact h x hc h2

set_option maxRecDepth 10000 in
set_option synthInstance.maxSize 1024 in
private theorem square_cases (u z x : A4)
    (hu2 : u^2=1) (hu1 : u≠1) (hz2 : z^2=1) (hz1 : z≠1) (hne : u≠z)
    (hx2 : x^2=1) : x=1 ∨ x=u ∨ x=z ∨ x=z*u := by
  have h : ∀ u z x : A4, u^2=1 → u≠1 → z^2=1 → z≠1 → u≠z →
      x^2=1 → x=1 ∨ x=u ∨ x=z ∨ x=z*u := by decide +kernel
  exact h u z x hu2 hu1 hz2 hz1 hne hx2

/-- The marked abelian subgroup is precisely the involution centralizer,
and every outside element induces the source transvection with center z. -/
theorem centralizer_and_reflection {R : Type*} [Group R] [Finite R]
    (e : R ≃* W) (I : Subgroup R) (eI : I ≃* A4)
    (z u : R) (hzI : z∈I) (huI : u∈I)
    (hzC : z∈center R) (hz2 : z^2=1) (hz1 : z≠1)
    (hu2 : u^2=1) (hu1 : u≠1) (huz : u≠z) :
    centralizer ({u} : Set R)=I ∧ ∀ r∉I, r*u*r⁻¹=z*u := by
  have hcardR : Nat.card R=32 :=
    (Nat.card_congr e.toEquiv).trans Matrix.GeneralLinearGroup.FiveWreathSylow.wreath_card
  have hcardI : Nat.card I=16 := (Nat.card_congr eI.toEquiv).trans (by
    change Nat.card (ZMod 4 × ZMod 4)=16
    norm_num [Nat.card_prod])
  have hcomm (a b : I) : a*b=b*a := by
    apply eI.injective
    simp only [map_mul, mul_comm]
  have hIC : I ≤ centralizer ({u} : Set R) := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hcomm ⟨x,hx⟩ ⟨u,huI⟩)
  have hunon : u∉center R := by
    intro huc
    have hc (x : R) (hxc : x∈center R) : ∀ y : W, y*e x=e x*y := by
      intro y
      obtain ⟨a,rfl⟩ := e.surjective y
      simpa only [map_mul] using congrArg e (mem_center_iff.mp hxc a)
    have he2 (x:R) (hx:x^2=1) : (e x)^2=1 := by rw [← map_pow,hx,map_one]
    have he1 (x:R) (hx:x≠1) : e x≠1 := by
      intro h
      exact hx (e.injective (h.trans (map_one e).symm))
    have huz' := central_two_cases (e u) (hc u huc) (he2 u hu2)
    have hzz' := central_two_cases (e z) (hc z hzC) (he2 z hz2)
    exact huz (e.injective ((huz'.resolve_left (he1 u hu1)).trans
      (hzz'.resolve_left (he1 z hz1)).symm))
  have hne : centralizer ({u} : Set R)≠⊤ := by
    intro htop
    apply hunon
    apply mem_center_iff.mpr
    intro r
    exact mem_centralizer_singleton_iff.mp (htop ▸ mem_top r)
  have hcardC : Nat.card (centralizer ({u} : Set R))=16 := by
    have h16 : 16 ∣ Nat.card (centralizer ({u} : Set R)) := hcardI ▸ card_dvd_of_le hIC
    have h32 : Nat.card (centralizer ({u} : Set R)) ∣ 32 :=
      hcardR ▸ (centralizer ({u} : Set R)).card_subgroup_dvd_card
    have hlt : Nat.card (centralizer ({u} : Set R)) < 32 := by
      have hle : Nat.card (centralizer ({u} : Set R)) ≤ 32 := hcardR ▸ card_le_card_group _
      have heq : Nat.card (centralizer ({u} : Set R))≠32 := by
        intro he
        exact hne (eq_top_of_card_eq _ (he.trans hcardR.symm))
      omega
    have hlow := Nat.le_of_dvd (Nat.card_pos : 0<Nat.card (centralizer ({u} : Set R))) h16
    obtain ⟨k,hk⟩ := h16
    have hk0 : 0<k := by omega
    have hk2 : k<2 := by omega
    have hk1 : k=1 := by omega
    simpa only [hk1,mul_one] using hk
  have hCI : centralizer ({u} : Set R)=I :=
    (eq_of_le_of_card_ge hIC (by rw [hcardC,hcardI])).symm
  refine ⟨hCI,?_⟩
  have hindex : I.index=2 := by
    have h := I.card_mul_index
    rw [hcardI,hcardR] at h
    omega
  let : I.Normal := I.normal_of_index_eq_two hindex
  intro r hr
  let v := r*u*r⁻¹
  have hvI : v∈I := Subgroup.Normal.conj_mem inferInstance u huI r
  have hv2 : v^2=1 := by
    have h := congrArg (MulAut.conj r) hu2
    simpa only [map_pow,map_one,MulAut.conj_apply] using h
  have hE2 (a : R) (ha:a∈I) (h2:a^2=1) : (eI ⟨a,ha⟩)^2=1 := by
    rw [← map_pow,show (⟨a,ha⟩:I)^2=1 from Subtype.ext h2,map_one]
  have hE1 (a : R) (ha:a∈I) (h1:a≠1) : eI ⟨a,ha⟩≠1 := by
    intro h
    exact h1 (congrArg Subtype.val (eI.injective (h.trans (map_one eI).symm)))
  have hs := square_cases (eI ⟨u,huI⟩) (eI ⟨z,hzI⟩) (eI ⟨v,hvI⟩)
    (hE2 u huI hu2) (hE1 u huI hu1) (hE2 z hzI hz2) (hE1 z hzI hz1)
    (fun h => huz (congrArg Subtype.val (eI.injective h))) (hE2 v hvI hv2)
  have hsv : v=1 ∨ v=u ∨ v=z ∨ v=z*u := by
    rcases hs with h|h|h|h
    · exact Or.inl (congrArg Subtype.val (eI.injective (h.trans (map_one eI).symm)))
    · exact Or.inr (Or.inl (congrArg Subtype.val (eI.injective h)))
    · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val (eI.injective h))))
    · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val
        (eI.injective (h.trans (map_mul eI _ _).symm)))))
  rcases hsv with hv|hv|hv|hv
  · exact (hu1 ((MulAut.conj r).injective (hv.trans (map_one (MulAut.conj r)).symm))).elim
  · have hc : r∈centralizer ({u}:Set R) :=
      mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hv)
    exact (hr (hCI ▸ hc)).elim
  · have hzfix : r*z*r⁻¹=z := mul_inv_eq_of_eq_mul (mem_center_iff.mp hzC r)
    exact (huz ((MulAut.conj r).injective (hv.trans hzfix.symm))).elim
  · exact hv

end Tits.ExceptionalParabolics.FullRee.LongRootPaths.WreathReflection

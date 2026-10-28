module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PureNonseedIncidence
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.NonseedExteriorTransitivity

/-!
# The opposite extension of a pure nonseed eight is not pure

At a point of the common eight outside its marked line, a pure sixteen
meets the actual point core in an eight. If both opposite extensions were
pure, an exterior element from each such intersection would have product
in the intersection of the two original point cores, with square equal
to the marked involution. That core intersection is an elementary seed.
This distinguishes the two extensions using the actual original cores.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

omit [Finite G] in
private theorem outside_pair_mem (E A : Subgroup G) (hEA : E ≤ A)
    (hE : Nat.card E = 8) (hA : Nat.card A = 16)
    (a b : G) (ha : a ∈ A) (hb : b ∈ A) (haE : a ∉ E) (hbE : b ∉ E) :
    a*b ∈ E := by
  have hi : (E.subgroupOf A).index=2 := by
    have hh := (E.subgroupOf A).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hEA).toEquiv,hE,hA] at hh
    omega
  exact (mul_mem_iff_of_index_two hi (a:= (⟨a,ha⟩ : A)) (b:= (⟨b,hb⟩ : A))).mpr
    (iff_of_false haE hbE)

private theorem exists_exterior_in_core
    (E A R : Subgroup G) (_hEA : E ≤ A)
    (hAR : Nat.card (A ⊓ R : Subgroup G)=8)
    (hER : Nat.card (E ⊓ R : Subgroup G)=4) :
    ∃ a, a ∈ A ∧ a ∈ R ∧ a ∉ E := by
  by_contra! hh
  have hle : A ⊓ R ≤ E ⊓ R := fun a ha => ⟨hh a ha.1 ha.2,ha.2⟩
  have hc := card_le_of_le hle
  rw [hAR,hER] at hc
  omega

/-- Two opposite extensions through an actual nonseed eight cannot both
be pure in the original marked involution class. The central-four and
reflection generators are retained explicitly. -/
theorem TypeAt.opposite_nonseed_extensions_not_both_pure (h : TypeAt z V)
    (E : pointCoreEights z) (hEn : E.val ∉ pointCoreSeedOrbit z V)
    (A B : Subgroup G) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hA : Nat.card A=16) (hB : Nat.card B=16) (hEA : E.val ≤ A) (hEB : E.val ≤ B)
    (c b : G) (hc2 : c^2=z)
    (hcZ : c ∈ (center ((involutionCentralizer z).pCoreIn 2)).map
      ((involutionCentralizer z).pCoreIn 2).subtype)
    (hbA : b ∈ A) (hbE : b ∉ E.val) (hcbB : c*b ∈ B) (hcbE : c*b ∉ E.val)
    (hbc : b*c*b⁻¹=c⁻¹)
    (hpureA : ∀ a ∈ A, a≠1 → IsConj a z) :
    ¬ (∀ a ∈ B, a≠1 → IsConj a z) := by
  intro hpureB
  let Q := (involutionCentralizer z).pCoreIn 2
  let : IsElementaryAbelian 2 E.val := E.property.2.2.1
  have hnot : ¬ E.val ≤ zpowers z := by
    intro he
    have hh := card_le_of_le he
    rw [E.property.2.2.2,Nat.card_zpowers,h.involution] at hh
    omega
  obtain ⟨x,hxE,hxz⟩ := SetLike.not_le_iff_exists.mp hnot
  have hx1 : x≠1 := fun he => hxz (he ▸ (zpowers z).one_mem)
  have hxne : x≠z := fun he => hxz (he ▸ mem_zpowers z)
  have hx2 : orderOf x=2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian x hxE) hx1
  let R := (involutionCentralizer x).pCoreIn 2
  have hER : Nat.card (E.val ⊓ R : Subgroup G)=4 :=
    h.nonseed_eight_point_core_intersection_card E hEn x hxE hxz
  have hAR := h.pure_nonseed_extension_point_core_eights E hEn A hA hEA hpureA x (hEA hxE) hx1
  have hBR := h.pure_nonseed_extension_point_core_eights E hEn B hB hEB hpureB x (hEB hxE) hx1
  obtain ⟨a,haA,haR,haE⟩ := exists_exterior_in_core E.val A R hEA hAR hER
  obtain ⟨d,hdB,hdR,hdE⟩ := exists_exterior_in_core E.val B R hEB hBR hER
  have habE : a*b ∈ E.val := outside_pair_mem E.val A hEA E.property.2.2.2 hA a b haA hbA haE hbE
  have hdcE : d*(c*b) ∈ E.val := outside_pair_mem E.val B hEB E.property.2.2.2 hB d (c*b) hdB hcbB hdE hcbE
  let e := a*b
  let f := d*(c*b)
  have hb2 : b^2=1 := elemPow_eq_one_of_isElementaryAbelian b hbA
  have hcb2 : (c*b)^2=1 := elemPow_eq_one_of_isElementaryAbelian (c*b) hcbB
  have haeq : a=e*b := by dsimp [e]; simp only [mul_assoc,←pow_two,hb2,mul_one]
  have hdeq : d=f*(c*b) := by dsimp [f]; simp only [mul_assoc,←pow_two,hcb2,mul_one]
  have hcQ : c∈Q := by obtain ⟨q,_,rfl⟩ := hcZ; exact q.property
  have hce (y:G) (hy:y∈E.val) : Commute c y := by
    obtain ⟨q,hq,he⟩ := hcZ
    rw [←he]
    exact (congrArg Subtype.val (mem_center_iff.mp hq ⟨y,E.property.1 hy⟩)).symm
  have hbf : Commute b f := setLike_mul_comm hbA (hEA hdcE)
  have hbcb : b*c*b=c⁻¹ := by
    have hbI : b⁻¹=b := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hb2)
    simpa only [hbI] using hbc
  have had : a*d=(e*f)*c⁻¹ := by
    rw [haeq,hdeq]
    calc
      (e*b)*(f*(c*b)) = e*(b*f)*(c*b) := by group
      _ = e*(f*b)*(c*b) := by rw [hbf.eq]
      _ = (e*f)*(b*c*b) := by group
      _ = (e*f)*c⁻¹ := by rw [hbcb]
  have hefE : e*f∈E.val := E.val.mul_mem habE hdcE
  have hadQ : a*d∈Q := by rw [had]; exact Q.mul_mem (E.property.1 hefE) (Q.inv_mem hcQ)
  have hadR : a*d∈R := R.mul_mem haR hdR
  have hsquare : (a*d)^2=z := by
    rw [had,((hce (e*f) hefE).symm.inv_right).mul_pow,
      elemPow_eq_one_of_isElementaryAbelian (e*f) hefE,one_mul,inv_pow,hc2]
    exact inv_eq_of_mul_eq_one_right (by simpa only [pow_two,h.involution] using pow_orderOf_eq_one z)
  obtain ⟨g,hg⟩ := h.point_core_intersection_seed x (E.property.1 hxE) hx2 hxne
  have hadS : a*d∈V.map (MulAut.conj (g:G)).toMonoidHom := hg ▸ ⟨hadQ,hadR⟩
  let : IsElementaryAbelian 2 V := h.elementary
  let : IsElementaryAbelian 2 (V.map (MulAut.conj (g:G)).toMonoidHom) := IsElementaryAbelian.map _
  have hone := elemPow_eq_one_of_isElementaryAbelian (p:=2) (a*d) hadS
  rw [hsquare] at hone
  have hz1 : z≠1 := by
    intro he
    have hi := h.involution
    rw [he,orderOf_one] at hi
    omega
  exact hz1 hone

end CFSG.Quasithin.HigmanSims

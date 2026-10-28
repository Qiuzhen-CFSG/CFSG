module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadCubic
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.MixedProduct
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CubicCentralizer.InvertedCubicCommutator

/-!
# The original hexad cubic and mixed reflection cross-relation

The same original endpoint reflection inverts the constructed second cubic
and the mixed product of its paired reflections. Its transposition action
on the actual cubic-centralizer quotient forces their commutator to have
square one. The marked centralizer splitting lifts that relation to G.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- The literal hexad overgroup contains a second inverted cubic satisfying
the cross-relation with the same actual mixed reflection product. -/
theorem TypeAt.exists_hexad_cubic_cross_relation (h : TypeAt z V)
    (W A B : Subgroup G) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hWV : W ≤ V) (hW4 : Nat.card W = 4)
    (hA16 : Nat.card A = 16) (hB16 : Nat.card B = 16)
    (hAP : A ⊓ (normalizer (V : Set G)).pCoreIn 2 = W)
    (hBP : B ⊓ (normalizer (V : Set G)).pCoreIn 2 = W)
    (hC : A ⊔ B ≤ centralizer (W : Set G))
    (hBA : B ≤ normalizer (A : Set G))
    (d : NaturalEndpointData A) (hBd : B ≤ d.carrier)
    (h64 : Nat.card (A ⊔ B : Subgroup G) = 64)
    (hpureB : ∀ b ∈ B, b ≠ 1 → IsConj b z)
    (hpointsB : ∀ b ∈ B, b ≠ 1 →
      Nat.card (B ⊓ (involutionCentralizer b).pCoreIn 2 : Subgroup G) = 8)
    (u c t r : G) (huV : u ∈ V) (huW : u ∉ W)
    (hcP : c ∈ (normalizer (V : Set G)).pCoreIn 2)
    (hc2 : c ^ 2 = u) (hc4 : orderOf c = 4) (hct : Commute c t)
    (hB : B = A.map (MulAut.conj c).toMonoidHom)
    (ht3 : orderOf t = 3)
    (htW : t ∈ normalizer (W : Set G))
    (hJ192 : Nat.card ((A ⊔ B) ⊔ zpowers t : Subgroup G) = 192)
    (ht : t ∈ d.carrier) (hr : r ∈ d.carrier) (hrJ : r ∉ (A ⊔ B) ⊔ zpowers t)
    (hr2 : orderOf r = 2) (hinv : r * t * r⁻¹ = t⁻¹) :
    let ell := r * (c * r * c⁻¹)
    ∃ n : G, n∈d.hexad_overgroup ∧ Commute n t ∧ orderOf n=3 ∧
      n∉zpowers t ∧ r*n*r⁻¹=n⁻¹ ∧ orderOf ell=3 ∧ ⁅ell,n⁆^2=1 := by
  dsimp only
  obtain ⟨n,hnD,hnt,hn3,hnT,hrn⟩ :=
    d.exists_inverted_hexad_cubic t r ht ht3 hr hr2 hinv
  have hell3 := h.endpoint_conjugate_reflection_product_order W A B hWV hW4
    hA16 hB16 hAP hBP hC hBA d hBd h64 hpureB hpointsB u c t r huV huW
    hcP hc2 hc4 hct hB ht3 htW hJ192 ht hr hrJ hr2 hinv
  have hWA : W ≤ A := hAP ▸
    (show A ⊓ (normalizer (V : Set G)).pCoreIn 2 ≤ A from inf_le_left)
  have hWB : W ≤ B := hBP ▸
    (show B ⊓ (normalizer (V : Set G)).pCoreIn 2 ≤ B from inf_le_left)
  have hAC : A ≤ centralizer (W : Set G) := le_sup_left.trans hC
  have hu1 : u ≠ 1 := fun he => huW (he ▸ W.one_mem)
  have huT := h.at_seed_point u huV hu1
  have huP : u ∈ (normalizer (V : Set G)).pCoreIn 2 := hc2 ▸ pow_mem hcP 2
  have huN : u ∈ normalizer (A : Set G) :=
    (h.plane_radical_core_normalizer W A hWV hW4 hA16 hWA hAC hAP u huP).mpr
      (by rw [show u ^ 2 = 1 from huT.involution ▸ pow_orderOf_eq_one u]; exact W.one_mem)
  have hut : Commute u t := hc2 ▸ hct.pow_left 2
  have htU : t ∈ involutionCentralizer u := mem_centralizer_singleton_iff.mpr hut.symm.eq
  have hcW : c ^ 2 ∉ W := by rwa [hc2]
  have hrA : r ∉ A := fun he => hrJ (mem_sup_left (mem_sup_left he))
  obtain ⟨v,_,k,hvE,hv2,hvr,_,_,_,_,_,hk4,hk2,_,_,hkt,hrk⟩ :=
    h.endpoint_reflection_fixed_root W A B hWV hW4 hWA hWB hB16 hAC hAP hBP
      c hcP hcW hB hBA d hBd h64 hpureB hpointsB u t r
        huV huW huN hut ht ht3 hr hrA hr2 hinv
  let C := centralizer ({t} : Set G)
  let O := pPrimeCore 2 C
  let X := C ⧸ O
  let q := QuotientGroup.mk' O
  obtain ⟨φ⟩ := huT.cubic_centralizer_quotient_perm_five d t htU ht ht3 huN
  obtain ⟨hrC,a,ha,_,heval⟩ := huT.cubic_quotient_reflection_transposition d
    t r v k htU ht ht3 huN hr hr2 hinv hvE hv2 hvr hkt hk4 hk2 hrk φ
  let s := c*r*c⁻¹
  let ell := r*s
  have hci : c⁻¹*t*c=t := by
    rw [hct.inv_left.eq]
    group
  have hst : s*t*s⁻¹=t⁻¹ := by
    change (c*r*c⁻¹)*t*(c*r*c⁻¹)⁻¹=t⁻¹
    calc
      _ = c*(r*(c⁻¹*t*c)*r⁻¹)*c⁻¹ := by group
      _ = t⁻¹ := by rw [hci,hinv,hct.inv_right.eq]; group
  have hellt : ell*t*ell⁻¹=t := by
    change (r*s)*t*(r*s)⁻¹=t
    calc
      _ = r*(s*t*s⁻¹)*r⁻¹ := by group
      _ = (r*t*r⁻¹)⁻¹ := by rw [hst]; group
      _ = t := by rw [hinv,inv_inv]
  have hellC : ell∈C := mem_centralizer_singleton_iff.mpr
    (mul_inv_eq_iff_eq_mul.mp hellt)
  have hrSq : r^2=1 := hr2 ▸ pow_orderOf_eq_one r
  have hri : r⁻¹=r := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hrSq)
  have hsi : s⁻¹=s := by
    change (c*r*c⁻¹)⁻¹=c*r*c⁻¹
    simp only [mul_inv_rev,inv_inv,hri,mul_assoc]
  have hrell : r*ell*r⁻¹=ell⁻¹ := by
    change r*(r*s)*r⁻¹=(r*s)⁻¹
    rw [mul_inv_rev,hri,hsi]
    calc
      _ = (r*r)*s*r := by group
      _ = s*r := by rw [←pow_two,hrSq,one_mul]
  let ellC : C := ⟨ell,hellC⟩
  let nC : C := ⟨n,mem_centralizer_singleton_iff.mpr hnt.eq⟩
  have hellC3 : ellC^3=1 := Subtype.ext (hell3 ▸ pow_orderOf_eq_one (r*(c*r*c⁻¹)))
  have hnC3 : nC^3=1 := Subtype.ext (hn3 ▸ pow_orderOf_eq_one n)
  have hαell : C.normalizerMonoidHom ⟨r,hrC⟩ ellC=ellC⁻¹ := Subtype.ext hrell
  have hαn : C.normalizerMonoidHom ⟨r,hrC⟩ nC=nC⁻¹ := Subtype.ext hrn
  have hax : a*φ (q ellC)*a⁻¹=(φ (q ellC))⁻¹ := by
    rw [heval,hαell,map_inv,map_inv]
  have hay : a*φ (q nC)*a⁻¹=(φ (q nC))⁻¹ := by
    rw [heval,hαn,map_inv,map_inv]
  have hcross := huT.cubic_centralizer_inverted_cubics_commutator_square t htU ht3
    φ ellC nC hellC3 hnC3 a ha hax hay
  exact ⟨n,hnD,hnt,hn3,hnT,hrn,hell3,hcross⟩

end CFSG.Quasithin.HigmanSims

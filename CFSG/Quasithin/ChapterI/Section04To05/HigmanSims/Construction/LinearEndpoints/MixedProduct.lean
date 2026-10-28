module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.ReflectionFixedRoot
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CubicCentralizer.ReflectionActor
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CubicCentralizer.CubeLift
public import Theory.SpecificGroups.SymmetricFive.ReflectionCommutator

/-!
# The actual mixed endpoint reflection product has order three

The original paired local groups provide the inverted root selecting the
transposition actor on the full cubic quotient. The same original
reflection moves the square of the endpoint conjugator. The native
transposition displacement calculation gives order three in that literal
quotient; the proved splitting of the original cubic centralizer lifts
the cube relation, while its nontrivial quotient image gives exact order.
No root, actor, quotient model, or mixed-product hypothesis is an input.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- The same original endpoint reflection and its conjugate under the
actual cubic-centralizing cyclic-four element have product of order three. -/
theorem TypeAt.endpoint_conjugate_reflection_product_order (h : TypeAt z V)
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
    orderOf (r * (c * r * c⁻¹)) = 3 := by
  let J := (A ⊔ B) ⊔ zpowers t
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
  have hJ : J ≤ d.carrier ⊓ normalizer (W : Set G) :=
    le_inf (sup_le (sup_le d.kernel_le hBd) (zpowers_le.mpr ht))
      (sup_le (hC.trans (Subgroup.centralizer_le_normalizer _)) (zpowers_le.mpr htW))
  obtain ⟨v,_,k,hvE,hv2,hvr,_,_,_,_,_,hk4,hk2,_,_,hkt,hrk⟩ :=
    h.endpoint_reflection_fixed_root W A B hWV hW4 hWA hWB hB16 hAC hAP hBP
      c hcP hcW hB hBA d hBd h64 hpureB hpointsB u t r
        huV huW huN hut ht ht3 hr hrA hr2 hinv
  let C := centralizer ({t} : Set G)
  let O := pPrimeCore 2 C
  let X := C ⧸ O
  let q := QuotientGroup.mk' O
  obtain ⟨φ⟩ := huT.cubic_centralizer_quotient_perm_five d t htU ht ht3 huN
  obtain ⟨hrC,a,ha,hactor,_⟩ := huT.cubic_quotient_reflection_transposition d
    t r v k htU ht ht3 huN hr hr2 hinv hvE hv2 hvr hkt hk4 hk2 hrk φ
  let α := normalizerQuotientAction C O ⟨r,hrC⟩
  let aC := C.normalizerMonoidHom ⟨r,hrC⟩
  let cC : C := ⟨c,mem_centralizer_singleton_iff.mpr hct.eq⟩
  let uC : C := ⟨u,mem_centralizer_singleton_iff.mpr hut.eq⟩
  have hαq (y : C) : α (q y) = q (aC y) := quotientAut_apply_mk O aC y
  have hαφ (y : X) : φ (α y) = a * φ y * a⁻¹ := by
    have hh := DFunLike.congr_fun hactor (φ y)
    change φ (α (φ.symm (φ y))) = a * φ y * a⁻¹ at hh
    simpa only [φ.symm_apply_apply] using hh
  have hO : O.map C.subtype = zpowers t := huT.cubic_centralizer_oddCore t htU ht3
  have hk3 : Nat.card q.ker = 3 := by
    rw [QuotientGroup.ker_mk',←card_map_of_injective C.subtype_injective,hO,Nat.card_zpowers,ht3]
  have hker : IsPGroup 3 q.ker := IsPGroup.of_card (n := 1) (by simpa using hk3)
  have hcC4 : orderOf cC = 4 := (orderOf_coe cC).symm.trans hc4
  have hqc4 : orderOf (q cC) = 4 :=
    (q.orderOf_map_eq_of_coprime_of_isPGroup_ker hker cC (by rw [hcC4]; decide)).trans hcC4
  have hc5 : orderOf (φ (q cC)) = 4 := (φ.orderOf_eq _).trans hqc4
  have huq : φ (q uC) = (φ (q cC)) ^ 2 := by
    rw [←map_pow,←map_pow]
    exact congrArg (fun y : C => φ (q y)) (Subtype.ext hc2.symm)
  have hmove : α (q uC) ≠ q uC :=
    h.endpoint_reflection_moves_cubic_quotient W A hWV hW4 hAC hAP d J hJ hJ192
      u huV huW t htU ht3 r hr hrJ hrC uC rfl
  have hmove5 : a * (φ (q cC)) ^ 2 * a⁻¹ ≠ (φ (q cC)) ^ 2 := by
    intro he
    apply hmove
    apply φ.injective
    rw [hαφ,huq]
    exact he
  have hnative := Theory.SpecificGroups.SymmetricFive.transposition_four_displacement_order
    a (φ (q cC)) ha hc5 hmove5
  let x : C := aC cC * cC⁻¹
  have hxmap : φ (q x) = a * φ (q cC) * a⁻¹ * (φ (q cC))⁻¹ := by
    change φ (q (aC cC * cC⁻¹)) = _
    simp only [map_mul,map_inv]
    rw [←hαq,hαφ]
  have hxq3 : orderOf (q x) = 3 :=
    (φ.orderOf_eq _).symm.trans (hxmap ▸ hnative)
  have hx3 : x ^ 3 = 1 := huT.cubic_centralizer_cube_lift t htU ht3 x
    (hxq3 ▸ pow_orderOf_eq_one (q x))
  have hxne : x ≠ 1 := by
    intro he
    simp [he] at hxq3
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hxne
  have hG : orderOf (r * c * r⁻¹ * c⁻¹) = 3 := (orderOf_coe x).trans hxo
  have hrSq : r ^ 2 = 1 := hr2 ▸ pow_orderOf_eq_one r
  have hri : r⁻¹ = r := inv_eq_of_mul_eq_one_left
    (by simpa only [pow_two] using hrSq)
  simpa only [hri,mul_assoc] using hG

end CFSG.Quasithin.HigmanSims

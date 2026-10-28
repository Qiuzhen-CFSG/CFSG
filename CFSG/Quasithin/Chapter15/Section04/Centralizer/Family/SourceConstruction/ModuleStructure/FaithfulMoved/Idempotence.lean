module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ModuleStructure.FaithfulMoved
/-!
# Cubic displacement on the actual source module

The original cubic quotient makes conjugation by every member element cubic
on V(M). In a binary abelian group an automorphism a with a³=1 satisfies
δ(a(δ(v)))=δ(v), where δ(v)=v⁻¹a(v). Thus its displacement is already generated
by displacement on the moved subgroup. Applying the identity to every generator
of a subgroup L≤X gives [V(M),L]=[[V(M),X],L].

This identifies the actual residual-factor module with the corresponding moved
plane in the faithful binary calculation, rather than substituting an abstract
isomorphic module. Source: Aschbacher--Smith 15.4.12(6), printed pp.1160--1161,
combined manuscript of 1 March 2004.
-/

@[expose] public section

open Subgroup Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section04.FamilySource.ModuleStructure
private theorem binary_cubic_displacement {V : Type*} [Group V] [IsElementaryAbelian 2 V]
    (a : MulAut V) (ha : a ^ 3 = 1) (v : V) :
    (a (v⁻¹ * a v))⁻¹ * a (a (v⁻¹ * a v)) = v⁻¹ * a v := by
  have hinv (x : V) : x⁻¹ = x := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) x
  have ha3 (x : V) : a (a (a x)) = x := by
    have h := congrArg (fun b : MulAut V => b x) ha
    exact h
  simp only [map_mul, hinv, ha3]
  have hs : a (a v) * a (a v) = 1 := by
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) (a (a v))
  calc
    (a v * a (a v)) * (a (a v) * v) = (a (a v) * a (a v)) * (v * a v) := by ac_rfl
    _ = v * a v := by rw [hs,one_mul]
open BinaryNormalizer
variable {G : Type*} [Group G] [Finite G]

/-- Every original X-element induces a cubic automorphism on V(M). -/
theorem Input.localV_action_cube {K : GroupClass} {T : Sylow 2 G}
    {M X : Subgroup G} {s : ℕ} (h : Input K T M X s) (x : X) :
    moduleConjugation X (localV T M)
      (fun _x hx => localV_normalized (T : Subgroup G) M (h.member_le hx)) x ^ 3 = 1 := by
  let a := moduleConjugation X (localV T M)
    (fun _x hx => localV_normalized (T : Subgroup G) M (h.member_le hx))
  let : IsElementaryAbelian 3 (image M X) := h.image_structure.1
  have hp : memberProjection M X h.member_le (x ^ 3) = 1 := by
    rw [map_pow]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 3 (image M X)) _
  have hq : quotientMap M (inclusion h.member_le (x ^ 3)) = 1 := congrArg Subtype.val hp
  have hc : ((x ^ 3 : X) : G) ∈ M.pCoreIn 2 :=
    mem_map.mpr ⟨inclusion h.member_le (x ^ 3), (QuotientGroup.eq_one_iff _).mp hq, rfl⟩
  rw [←localV_centralizer T M h.sylow_le h.center_centralizer] at hc
  change a x ^ 3 = 1
  rw [←map_pow]
  ext v
  exact mul_inv_eq_iff_eq_mul.mpr (hc.2 v v.property).symm

/-- For any subgroup of the actual member, moving V(M) is the same as moving
[V(M),X]. This keeps the ambient commutator convention of the source factors. -/
theorem Input.moved_commutator_stable {K : GroupClass} {T : Sylow 2 G}
    {M X : Subgroup G} {s : ℕ} (h : Input K T M X s)
    (L : Subgroup G) (hLX : L ≤ X) :
    ⁅localV T M,L⁆ = ⁅movedModule T M X,L⁆ := by
  let V := localV T M
  let W := movedModule T M X
  let a := moduleConjugation X V
    (fun _x hx => localV_normalized (T : Subgroup G) M (h.member_le hx))
  let : IsElementaryAbelian 2 V := localV_elementary T M h.sylow_le
    (h.ambient.evenCharacteristic T M h.maximal h.sylow_le)
  have hnW := h.moved_normalized
  apply le_antisymm ?_ (commutator_mono h.moved_le le_rfl)
  apply commutator_le.mpr
  intro v hv x hx
  let xX : X := ⟨x,hLX hx⟩
  let vV : V := ⟨v⁻¹,V.inv_mem hv⟩
  let d : V := vV⁻¹ * a xX vV
  have hd : (d : G) ∈ W := by
    change (v⁻¹)⁻¹ * (x * v⁻¹ * x⁻¹) ∈ ⁅V,X⁆
    simpa only [commutatorElement_def,mul_assoc,inv_inv] using commutator_mem_commutator hv (hLX hx)
  have had : ((a xX) d : G) ∈ W :=
    (mem_normalizer_iff.mp (hnW (h.member_le (hLX hx))) (d : G)).mp hd
  have hmem := commutator_mem_commutator (W.inv_mem had) hx
  have he := congrArg Subtype.val (binary_cubic_displacement (a xX) (h.localV_action_cube xX) vV)
  change ((a xX d : V) : G)⁻¹ * (x * ((a xX d : V) : G) * x⁻¹) = (d : G) at he
  change ⁅v,x⁆ ∈ ⁅W,L⁆
  rw [commutatorElement_def]
  have hmem' : (d : G) ∈ ⁅W,L⁆ := by
    rw [←he]
    simpa only [commutatorElement_def,inv_inv,mul_assoc] using hmem
  change (v⁻¹)⁻¹ * (x * v⁻¹ * x⁻¹) ∈ ⁅W,L⁆ at hmem'
  simpa only [inv_inv,mul_assoc] using hmem'

end CFSG.Quasithin.Chapter15.Section04.FamilySource.ModuleStructure

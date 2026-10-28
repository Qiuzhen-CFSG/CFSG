module
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Mathlib.GroupTheory.Index
public import CFSG.Quasithin.Chapter5.Section03LinearSource.QuaternionCentralizer

/-!
# The binary flag in an exceptional root plane

An automorphism fixing an index-two subgroup of an elementary two-group
has square one. Repeatedly applying this to the flag of orders 2, 4, 8,
and 16 shows that its stabilizer has two-power action. Self-centralization
of the root plane then makes the full ambient flag stabilizer a two-group.

The same marked quaternion subgroup cuts the marked root plane in order
eight, supplying the third term of this flag. This derives the local
two-group premise in Aschbacher--Smith §5.3.7, printed p.661, from the
actual marking; no full-normalizer quotient identification is assumed.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter5.Section03LinearSource
variable {G : Type*} [Group G]

private theorem square_fixes_of_index_two (a : MulAut G) (P Q : Subgroup G)
    [IsElementaryAbelian 2 P] (_hQP : Q ≤ P) (hi : Q.relIndex P=2)
    (hP : ∀ x ∈ P, a x ∈ P) (hfix : ∀ x ∈ Q, a x=x) :
    ∀ x ∈ P, (a^2) x=x := by
  let : CommGroup P := IsMulCommutative.instCommGroup
  let D := Q.subgroupOf P
  let q := QuotientGroup.mk' D
  have hcard : Nat.card (P ⧸ D)=2 := hi
  obtain ⟨z,_,hz⟩ := (Nat.card_eq_two_iff' (1 : P ⧸ D)).mp hcard
  intro x hx
  let u : P := ⟨x,hx⟩
  let v : P := ⟨a x,hP x hx⟩
  have hq : q u=q v := by
    by_cases hxQ : x∈Q
    · have hvQ : a x∈Q := (hfix x hxQ).symm ▸ hxQ
      rw [show q u=1 from (QuotientGroup.eq_one_iff (N := D) _).mpr hxQ,
        show q v=1 from (QuotientGroup.eq_one_iff (N := D) _).mpr hvQ]
    · have hxu : q u≠1 := fun hh => hxQ ((QuotientGroup.eq_one_iff (N := D) _).mp hh)
      have hxv : q v≠1 := by
        intro hh
        have hav : a x∈Q := (QuotientGroup.eq_one_iff (N := D) _).mp hh
        have he : x=a x := a.injective (hfix (a x) hav).symm
        exact hxQ (he.symm ▸ hav)
      exact (hz _ hxu).trans (hz _ hxv).symm
  have hd : x⁻¹ * a x ∈ Q :=
    (QuotientGroup.eq (s := D) (a := u) (b := v)).mp hq
  have hh := hfix (x⁻¹*a x) hd
  rw [map_mul,map_inv] at hh
  have hx2 : x^2=1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx
  have ha2 : (a x)^2=1 := by rw [←map_pow,hx2,map_one]
  have hxi : x⁻¹=x := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hx2)
  have hcomm : a x*x=x*a x := congrArg Subtype.val (mul_comm v u)
  change a (a x)=x
  calc
    a (a x) = a x*((a x)⁻¹*a (a x)) := by simp
    _ = a x*(x⁻¹*a x) := congrArg (fun t => a x*t) hh
    _ = x := by rw [hxi,←mul_assoc,hcomm,mul_assoc,←pow_two,ha2,mul_one]

/-- The stabilizer of the full binary flag in a self-centralizing root
plane is a two-group. All four terms are literal ambient subgroups. -/
theorem four_flag_normalizer_isPGroup (C Z P V : Subgroup G)
    [IsElementaryAbelian 2 V]
    (hCZ : C ≤ Z) (hZP : Z ≤ P) (hPV : P ≤ V)
    (hC : Nat.card C=2) (hZ : Nat.card Z=4)
    (hP : Nat.card P=8) (hV : Nat.card V=16)
    (hself : centralizer (V : Set G) ≤ V) :
    IsPGroup 2 (normalizer (C : Set G) ⊓ normalizer (Z : Set G) ⊓
      normalizer (P : Set G) ⊓ normalizer (V : Set G) : Subgroup G) := by
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.of_injective
    (inclusion hPV) (inclusion_injective hPV)
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.of_injective
    (inclusion hZP) (inclusion_injective hZP)
  have hCZ2 : C.relIndex Z=2 := by
    have hh := (C.subgroupOf Z).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hCZ).toEquiv,hC,hZ] at hh
    change 2*C.relIndex Z=4 at hh
    omega
  have hZP2 : Z.relIndex P=2 := by
    have hh := (Z.subgroupOf P).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hZP).toEquiv,hZ,hP] at hh
    change 4*Z.relIndex P=8 at hh
    omega
  have hPV2 : P.relIndex V=2 := by
    have hh := (P.subgroupOf V).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hPV).toEquiv,hP,hV] at hh
    change 8*P.relIndex V=16 at hh
    omega
  intro g
  let a := MulAut.conj (g : G)
  have hfixC : ∀ x∈C, a x=x := by
    intro x hx
    exact mul_inv_eq_iff_eq_mul.mpr
      ((normalizer_le_centralizer_of_card_two C hC g.property.1.1.1 x hx).symm)
  have hfixZ : ∀ x∈Z, (a^2) x=x := square_fixes_of_index_two a Z C hCZ hCZ2
    (fun x hx => (g.property.1.1.2 x).mp hx) hfixC
  have hfixP : ∀ x∈P, (a^4) x=x := by
    have hh := square_fixes_of_index_two (a^2) P Z hZP hZP2
      (fun x hx => by
        rw [show a=MulAut.conj (g:G) from rfl,←map_pow]
        exact ((normalizer (P : Set G)).pow_mem g.property.1.2 2 x).mp hx) hfixZ
    simpa only [←pow_mul] using hh
  have hfixV : ∀ x∈V, (a^8) x=x := by
    have hh := square_fixes_of_index_two (a^4) V P hPV hPV2
      (fun x hx => by
        rw [show a=MulAut.conj (g:G) from rfl,←map_pow]
        exact ((normalizer (V : Set G)).pow_mem g.property.2 4 x).mp hx) hfixP
    simpa only [←pow_mul] using hh
  have hg8 : (g:G)^8 ∈ centralizer (V : Set G) := by
    intro x hx
    have hh := hfixV x hx
    change (MulAut.conj (g:G)^8) x=x at hh
    rw [←map_pow] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  refine ⟨4,Subtype.ext ?_⟩
  have hh : ((g:G)^8)^2=1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) _ (hself hg8)
  change (g:G)^(2^4)=1
  norm_num only [←pow_mul] at hh ⊢
  exact hh
/-- The same marked quaternion subgroup cuts the original first root plane
in the order-eight term of the binary flag. -/
theorem marked_flag_normalizer_isPGroup
    (c : Section03ExceptionalSylowModel.MarkedCopy G) (D : Subgroup G)
    (hz : D ≤ centralizer ({c.z} : Set G))
    (hZ : D ≤ normalizer (c.Z : Set G))
    (hQ : D ≤ normalizer (c.Q : Set G))
    (hV : D ≤ normalizer (c.V₁ : Set G))
    (hself : centralizer (c.V₁ : Set G) ≤ c.V₁) : IsPGroup 2 D := by
  have hZV : c.Z ≤ c.V₁ := by rw [←c.V₁_inf_V₂];exact inf_le_left
  have hZQ : c.Z ≤ c.Q := map_mono Matrix.PSL3Four.SylowModel.Z_le_Q
  have h8 : Nat.card (c.V₁ ⊓ c.Q : Subgroup G)=8 := by
    change Nat.card ((Matrix.PSL3Four.SylowModel.V₁.map c.embedding) ⊓
      (Matrix.PSL3Four.SylowModel.Q.map c.embedding) : Subgroup G)=8
    rw [←map_inf _ _ _ c.embedding_injective,card_map_of_injective c.embedding_injective,
      Matrix.PSL3Four.SylowModel.card_V₁_inf_Q]
  apply (four_flag_normalizer_isPGroup (zpowers c.z) c.Z (c.V₁ ⊓ c.Q) c.V₁
    (zpowers_le_of_mem c.z_mem_Z) (le_inf hZV hZQ) inf_le_left
    (by rw [Nat.card_zpowers];exact orderOf_eq_prime c.z_sq c.z_ne_one)
    c.card_Z h8 c.card_V₁ hself).to_le
  have hC : D ≤ normalizer (zpowers c.z : Set G) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    congr 1
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp (hz hg))
  exact le_inf (le_inf (le_inf hC hZ)
    ((le_inf hV hQ).trans inf_normalizer_le_normalizer_inf)) hV

end CFSG.Quasithin.Chapter5.Section03LinearSource

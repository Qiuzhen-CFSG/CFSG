module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.CartanFactors
public import Theory.ElementaryAbelian.SingerNormalizer
public import Theory.GroupAction.BinarySingerRegularity

/-!
# Actual Cartan actions and odd-dimensional binary roots

Conjugation defines the action of the entire source Cartan on each actual
Weyl-conjugate simple root. Its image is isomorphic to the faithful panel
Cartan image: the kernel is precisely the actual panel core, and conjugation
transports both the root and its actor. All representative maps are retained.

A normalizing involution on an elementary abelian root of odd binary
dimension is trivial when the Cartan image is cyclic of order q-1. The
existing Singer-normalizer fixed-space theorem would otherwise make q a
square. The argument includes q=2. LinearActions applies this to the
perpendicular root on the same finite marked quotient.

Source: Fong--Seitz I (1973), proof of (6H)(a), printed p.51, using the
odd-dimensional action argument of (6F), pp.45--46.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace RootAction
variable {Y : Type*} [Group Y] (H A : Subgroup Y)

/-- The literal conjugation action of H on a subgroup it normalizes. -/
def action (hA : H ≤ normalizer (A : Set Y)) : H →* MulAut A :=
  A.normalizerMonoidHom.comp (inclusion hA)

@[simp] theorem action_apply (hA : H ≤ normalizer (A : Set Y)) (h : H) (a : A) :
    (action H A hA h a : Y) = (h : Y)*a*(h : Y)⁻¹ := rfl

theorem action_kernel (hA : H ≤ normalizer (A : Set Y)) :
    (action H A hA).ker = (centralizer (A : Set Y)).subgroupOf H := by
  ext h
  constructor
  · intro hh
    rw [mem_subgroupOf, mem_centralizer_iff]
    intro a ha
    have he := congrArg (fun f : MulAut A => (f ⟨a,ha⟩ : Y)) hh
    change (h : Y)*a*(h : Y)⁻¹ = a at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hh
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    change (h : Y)*a*(h : Y)⁻¹ = a
    have he : (a : Y)*(h : Y) = (h : Y)*a :=
      (mem_centralizer_iff.mp hh) a a.property
    rw [← he, mul_inv_cancel_right]

/-- Transport the actual action on a right-conjugate root to the original root. -/
def conjugateEquiv (n : Y) : RootCoordinates.rightConjugate A n ≃* A where
  toFun x := ⟨n*x*n⁻¹,x.property⟩
  invFun x := ⟨n⁻¹*x*n, by
    change n*(n⁻¹*x*n)*n⁻¹ ∈ A
    simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using x.property⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

variable (hA : H ≤ normalizer (A : Set Y)) (n : normalizer (H : Set Y))

include hA in
theorem normalizes_conjugate : H ≤ normalizer (RootCoordinates.rightConjugate A n : Set Y) := by
  apply le_trans ?_ (le_normalizer_comap (H := A) (MulAut.conj (n : Y)).toMonoidHom)
  intro h hh
  exact hA ((mem_normalizer_iff.mp n.property h).mp hh)

theorem conjugate_action :
    (MulAut.congr (conjugateEquiv A n)).toMonoidHom.comp
      (action H (RootCoordinates.rightConjugate A n) (normalizes_conjugate H A hA n)) =
    (action H A hA).comp (H.normalizerMonoidHom n).toMonoidHom := by
  apply MonoidHom.ext
  intro h
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  change (n : Y)*((h : Y)*((n : Y)⁻¹*a*n)*(h : Y)⁻¹)*(n : Y)⁻¹ =
    ((n : Y)*h*(n : Y)⁻¹)*a*((n : Y)*h*(n : Y)⁻¹)⁻¹
  group

def conjugateImageEquiv :
    (action H (RootCoordinates.rightConjugate A n) (normalizes_conjugate H A hA n)).range ≃*
      (action H A hA).range :=
  ((MulAut.congr (conjugateEquiv A n)).subgroupMap _).trans
    (MulEquiv.subgroupCongr (by
      rw [← MonoidHom.range_comp]
      change ((MulAut.congr (conjugateEquiv A n)).toMonoidHom.comp
        (action H (RootCoordinates.rightConjugate A n) (normalizes_conjugate H A hA n))).range = _
      rw [conjugate_action H A hA n, MonoidHom.range_comp,
        show (H.normalizerMonoidHom n).toMonoidHom.range = ⊤ from
          MonoidHom.range_eq_top.mpr (H.normalizerMonoidHom n).surjective,
        ← MonoidHom.range_eq_map]))

theorem action_normalizes_image (s : normalizer (A : Set Y))
    (hsH : (s : Y) ∈ normalizer (H : Set Y)) :
    A.normalizerMonoidHom s ∈ normalizer ((action H A hA).range : Set (MulAut A)) := by
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · rintro ⟨h,rfl⟩
    refine ⟨H.normalizerMonoidHom ⟨s,hsH⟩ h,?_⟩
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    simp only [← map_inv A.normalizerMonoidHom, MulAut.mul_apply]
    change ((s : Y)*h*(s : Y)⁻¹)*a*((s : Y)*h*(s : Y)⁻¹)⁻¹ =
      (s : Y)*((h : Y)*((s : Y)⁻¹*a*((s : Y)⁻¹)⁻¹)*(h : Y)⁻¹)*(s : Y)⁻¹
    group
  · intro hx
    obtain ⟨h,hh⟩ := hx
    refine ⟨H.normalizerMonoidHom ⟨(s : Y)⁻¹, (normalizer (H : Set Y)).inv_mem hsH⟩ h,?_⟩
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    have he := congrArg (fun f : MulAut A => (f ((A.normalizerMonoidHom s) a) : Y)) hh
    simp only [MulAut.mul_apply, MulAut.inv_apply_self] at he
    change (h : Y)*((s : Y)*a*(s : Y)⁻¹)*(h : Y)⁻¹ = (s : Y)*(x a : Y)*(s : Y)⁻¹ at he
    have he' := congrArg (fun y : Y => (s : Y)⁻¹*y*(s : Y)) he
    change ((s : Y)⁻¹*h*((s : Y)⁻¹)⁻¹)*a*((s : Y)⁻¹*h*((s : Y)⁻¹)⁻¹)⁻¹ = (x a : Y)
    simpa only [inv_inv, mul_inv_rev, mul_assoc, inv_mul_cancel_left,
      inv_mul_cancel, mul_one] using he'

/-- A cyclic faithful binary action of degree q-1 is regular, also at q=2. -/
theorem regular_of_card {E C : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    [Group C] [Finite C] [IsCyclic C] (ρ : C →* MulAut E) (hρ : Function.Injective ρ)
    {d : ℕ} (hd : 0 < d) (hC : Nat.card C = 2^d-1) (hE : Nat.card E = 2^d)
    (x y : E) (hx : x ≠ 1) (hy : y ≠ 1) : ∃! c : C, ρ c x = y := by
  classical
  by_cases hd1 : 1 < d
  · exact Theory.GroupAction.faithful_cyclic_binary_singer_regular ρ hρ hd1 hC hE x y hx hy
  · have hd' : d = 1 := by omega
    subst d
    let : Fintype E := Fintype.ofFinite E
    have hc : Nat.card C = 1 := by simpa using hC
    have hsub : Subsingleton C := (Nat.card_eq_one_iff_unique.mp hc).1
    have hn : Nat.card {v : E // v ≠ 1} = 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
        show Fintype.card {v : E // v = 1} = 1 from Fintype.card_unique,
        ← Nat.card_eq_fintype_card, hE]
      decide
    have hsubE : Subsingleton {v : E // v ≠ 1} := (Nat.card_eq_one_iff_unique.mp hn).1
    have he : x = y := congrArg Subtype.val (@Subsingleton.elim _ hsubE ⟨x,hx⟩ ⟨y,hy⟩)
    refine ⟨1,by simpa using he,fun c _ => @Subsingleton.elim C hsub c 1⟩

/-- Odd binary dimension rules out a nonidentity involution normalizing
this entire regular cyclic image. -/
theorem involution_eq_one {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (C : Subgroup (MulAut E)) [IsCyclic C]
    {d : ℕ} (hd : Odd d) (hC : Nat.card C = 2^d-1) (hE : Nat.card E = 2^d)
    (t : MulAut E) (ht : t^2 = 1) (hn : t ∈ normalizer (C : Set (MulAut E))) : t = 1 := by
  by_contra hne
  have hreg := regular_of_card C.subtype C.subtype_injective hd.pos hC hE
  have he := Theory.GroupTheory.regular_cyclic_automorphism_normalizer_involution_fixed_card
    C hreg t hne ht hn
  obtain ⟨k,hk⟩ := ((IsElementaryAbelian.isPGroup 2 E).to_subgroup
    (t.toMonoidHom.eqLocus (MonoidHom.id E))).exists_card_eq
  rw [hk,hE,← pow_mul] at he
  have hkd := Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)) he
  obtain ⟨l,hl⟩ := hd
  omega

/-- Apply the normalizer calculation to literal ambient conjugation. -/
theorem normalizing_involution_centralizes [Finite A] [IsElementaryAbelian 2 A]
    [IsCyclic (action H A hA).range] {d : ℕ} (hd : Odd d)
    (hC : Nat.card (action H A hA).range = 2^d-1) (hE : Nat.card A = 2^d)
    (s : Y) (hsA : s ∈ normalizer (A : Set Y))
    (hsH : s ∈ normalizer (H : Set Y)) (hs2 : s^2 = 1) :
    s ∈ centralizer (A : Set Y) := by
  have ht : (A.normalizerMonoidHom ⟨s,hsA⟩)^2 = 1 := by
    rw [← map_pow]
    have he : (⟨s,hsA⟩ : normalizer (A : Set Y))^2 = 1 := Subtype.ext hs2
    rw [he,map_one]
  have he := involution_eq_one (action H A hA).range hd hC hE _ ht
    (action_normalizes_image H A hA ⟨s,hsA⟩ hsH)
  rw [mem_centralizer_iff]
  intro a ha
  have hc := congrArg (fun f : MulAut A => (f ⟨a,ha⟩ : Y)) he
  change s*a*s⁻¹ = a at hc
  exact (mul_inv_eq_iff_eq_mul.mp hc).symm

end RootAction
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource

@[expose] public noncomputable section
open Subgroup
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)

def simpleRootAction (i : Fin 2) :
    (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) →* MulAut (simpleRoot Q split i) :=
  RootAction.action _ _ (torus_normalizes_simpleRoot Q split i)

theorem simpleRootAction_kernel (i : Fin 2) :
    (simpleRootAction Q split i).ker = (cartanPanelMap Q i).ker := by
  rw [simpleRootAction, RootAction.action_kernel, cartanPanelMap_kernel]
  ext h
  change (h : X ⧸ Q.D) ∈ centralizer (simpleRoot Q split i : Set (X ⧸ Q.D)) ↔
    (h : X ⧸ Q.D) ∈ embeddedPanelKernel Q i
  constructor
  · intro hc
    have hh : (h : X ⧸ Q.D) ∈ (Q.tits.B ⊓ Q.tits.N) ⊓
        centralizer (simpleRoot Q split i : Set (X ⧸ Q.D)) := ⟨h.property,hc⟩
    rw [cartan_centralizer_simpleRoot Q split i] at hh
    exact hh.2
  · intro hk
    have hh : (h : X ⧸ Q.D) ∈ (Q.tits.B ⊓ Q.tits.N) ⊓ embeddedPanelKernel Q i := ⟨h.property,hk⟩
    rw [← cartan_centralizer_simpleRoot Q split i] at hh
    exact hh.2

def simpleRootActionImageEquiv (i : Fin 2) :
    (simpleRootAction Q split i).range ≃* (cartanPanelMap Q i).range :=
  (QuotientGroup.quotientKerEquivRange (simpleRootAction Q split i)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (simpleRootAction_kernel Q split i)).trans
      (QuotientGroup.quotientKerEquivRange (cartanPanelMap Q i)))

def rootAction (i : Fin 2) (w : Weyl Q) :
    (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) →* MulAut (rootAt Q split i w) :=
  RootAction.action _ _ (rootAt_torus_normalizes Q split i w)

def rootActionImageEquiv (i : Fin 2) (w : Weyl Q) :
    (rootAction Q split i w).range ≃* (cartanPanelMap Q i).range :=
  (RootAction.conjugateImageEquiv (Q.tits.B ⊓ Q.tits.N) (simpleRoot Q split i)
    (torus_normalizes_simpleRoot Q split i)
    ⟨representative w,torus_normalizes (representative w)⟩).trans
      (simpleRootActionImageEquiv Q split i)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource

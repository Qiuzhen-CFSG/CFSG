module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.SuzukiRootLayers
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.CartanCyclic
public import Theory.GroupTheory.PGroup.CoprimeFrattiniAction

/-!
# The literal action on the barred Suzuki source root

Transport normalizer conjugation through the Frattini quotient chart on the
same source root. The representative formulas distinguish left conjugation
from the right-conjugation convention of Fong--Seitz. Coprime faithfulness
shows that passing to this quotient loses none of the odd Cartan image:
its kernel is exactly the actual panel kernel and its image is cyclic of
order q-1, also when q=2.

Squares force a scalar k on this barred root line to act by k*pi(k) on
root Omega. This proves the relation between the two root weights used
in II (10.10) and (10.12); it does not assume or establish the still-needed
specific Cartan scalar values or the natural four-dimensional section.

Source: Fong--Seitz I (1973), (6H), pp.51--56, and II (1974), §10,
pp.221--224. OriginalRootLayers retains the original full-Cartan and
endpoint representatives for this action. Every statement includes m=0.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2) (m : ℕ)
  (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

def suzukiBarAction : normalizer (simpleRoot Q split i : Set (X ⧸ Q.D)) →*
    MulAut (Multiplicative (BinaryGaloisField (2*m+1))) :=
  (MulAut.congr (suzukiFrattiniQuotientEquiv Q split i m μ hB)).toMonoidHom.comp
    ((quotientAut (frattini (simpleRoot Q split i))).comp
      (simpleRoot Q split i).normalizerMonoidHom)

theorem suzukiFrattiniQuotientEquiv_mk (x : simpleRoot Q split i) :
    suzukiFrattiniQuotientEquiv Q split i m μ hB (QuotientGroup.mk x) =
      suzukiFirstCoordinate Q split i m μ hB x := rfl

theorem suzukiBarAction_representative
    (h : normalizer (simpleRoot Q split i : Set (X ⧸ Q.D))) (x : simpleRoot Q split i) :
    suzukiBarAction Q split i m μ hB h (suzukiFirstCoordinate Q split i m μ hB x) =
      suzukiFirstCoordinate Q split i m μ hB ((simpleRoot Q split i).normalizerMonoidHom h x) := by
  rw [← suzukiFrattiniQuotientEquiv_mk Q split i m μ hB x]
  change suzukiFrattiniQuotientEquiv Q split i m μ hB
    (quotientAut (frattini (simpleRoot Q split i)) ((simpleRoot Q split i).normalizerMonoidHom h)
      ((suzukiFrattiniQuotientEquiv Q split i m μ hB).symm
        (suzukiFrattiniQuotientEquiv Q split i m μ hB (QuotientGroup.mk x)))) = _
  rw [MulEquiv.symm_apply_apply]
  exact congrArg (suzukiFrattiniQuotientEquiv Q split i m μ hB)
    (quotientAut_apply_mk _ _ x)

theorem suzukiBarAction_right_representative
    (h : normalizer (simpleRoot Q split i : Set (X ⧸ Q.D))) (x : simpleRoot Q split i) :
    suzukiBarAction Q split i m μ hB h⁻¹ (suzukiFirstCoordinate Q split i m μ hB x) =
      suzukiFirstCoordinate Q split i m μ hB
        ⟨(h : X ⧸ Q.D)⁻¹*x*(h : X ⧸ Q.D),
          by
            have hx := ((simpleRoot Q split i).normalizerMonoidHom h⁻¹ x).property
            change (h : X ⧸ Q.D)⁻¹*x*((h : X ⧸ Q.D)⁻¹)⁻¹ ∈ simpleRoot Q split i at hx
            simpa only [inv_inv] using hx⟩ := by
  rw [suzukiBarAction_representative]
  congr 1
  apply Subtype.ext
  change (h : X ⧸ Q.D)⁻¹*x*((h : X ⧸ Q.D)⁻¹)⁻¹ = _
  rw [inv_inv]

theorem suzukiBarAction_scalar_omega
    (h : normalizer (simpleRoot Q split i : Set (X ⧸ Q.D)))
    (k : BinaryGaloisField (2*m+1))
    (hk : ∀ a, suzukiBarAction Q split i m μ hB h (Multiplicative.ofAdd a) =
      Multiplicative.ofAdd (k*a)) (b : BinaryGaloisField (2*m+1)) :
    (simpleRoot Q split i).normalizerMonoidHom h (suzukiParameter Q split i m μ hB 0 b) =
      suzukiParameter Q split i m μ hB 0 (k*suzukiTits m k*b) := by
  let a := suzukiTits m b / b
  obtain ⟨⟨c,d⟩,hx⟩ := (suzukiParameter_bijective Q split i m μ hB).surjective
    ((simpleRoot Q split i).normalizerMonoidHom h (suzukiParameter Q split i m μ hB a 0))
  change suzukiParameter Q split i m μ hB c d = _ at hx
  have hc : c = k*a := by
    apply Multiplicative.ofAdd.injective
    calc
      Multiplicative.ofAdd c = suzukiFirstCoordinate Q split i m μ hB
        (suzukiParameter Q split i m μ hB c d) :=
          (suzukiFirstCoordinate_parameter Q split i m μ hB c d).symm
      _ = suzukiFirstCoordinate Q split i m μ hB
        ((simpleRoot Q split i).normalizerMonoidHom h (suzukiParameter Q split i m μ hB a 0)) :=
          congrArg (suzukiFirstCoordinate Q split i m μ hB) hx
      _ = suzukiBarAction Q split i m μ hB h (Multiplicative.ofAdd a) := by
        rw [← suzukiBarAction_representative, suzukiFirstCoordinate_parameter]
      _ = Multiplicative.ofAdd (k*a) := hk a
  rw [← suzukiParameter_square_root Q split i m μ hB b, map_pow, ← hx,
    suzukiParameter_square, hc]
  congr 1
  calc
    (k*a)*suzukiTits m (k*a) = k*suzukiTits m k*(a*suzukiTits m a) := by rw [map_mul]; ring
    _ = k*suzukiTits m k*b := by rw [tits_norm_inverse]

theorem suzukiBarAction_scalar_omega_right
    (h : normalizer (simpleRoot Q split i : Set (X ⧸ Q.D)))
    (k : BinaryGaloisField (2*m+1))
    (hk : ∀ a, suzukiBarAction Q split i m μ hB h⁻¹ (Multiplicative.ofAdd a) =
      Multiplicative.ofAdd (k*a)) (b : BinaryGaloisField (2*m+1)) :
    (h : X ⧸ Q.D)⁻¹ * suzukiParameter Q split i m μ hB 0 b * (h : X ⧸ Q.D) =
      (suzukiParameter Q split i m μ hB 0 (k*suzukiTits m k*b) : X ⧸ Q.D) := by
  have he := congrArg Subtype.val (suzukiBarAction_scalar_omega Q split i m μ hB h⁻¹ k hk b)
  change (h : X ⧸ Q.D)⁻¹ * suzukiParameter Q split i m μ hB 0 b * ((h : X ⧸ Q.D)⁻¹)⁻¹ = _ at he
  simpa only [inv_inv] using he

def suzukiBarCartanAction : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) →*
    MulAut (Multiplicative (BinaryGaloisField (2*m+1))) :=
  (suzukiBarAction Q split i m μ hB).comp (inclusion (torus_normalizes_simpleRoot Q split i))

theorem suzukiBarCartanAction_kernel :
    (suzukiBarCartanAction Q split i m μ hB).ker = (cartanPanelMap Q i).ker := by
  rw [← simpleRootAction_kernel Q split i]
  let a := simpleRootAction Q split i
  let f := quotientAut (frattini (simpleRoot Q split i))
  let e := suzukiFrattiniQuotientEquiv Q split i m μ hB
  have ho : Nat.Coprime (Nat.card a.range) 2 :=
    (split.odd.of_dvd_right (card_dvd_of_surjective a.rangeRestrict a.rangeRestrict_surjective)).symm
  have hf := MonoidHom.injective_frattini_action_of_coprime
    (split.isTwo.to_le (simpleRoot_le Q split i)) a.range.subtype a.range.subtype_injective ho
  ext h
  change MulAut.congr e (f (a h)) = 1 ↔ a h = 1
  constructor
  · intro hh
    have hq : f (a h) = 1 := (MulAut.congr e).injective (hh.trans (map_one _).symm)
    have hh' : a.rangeRestrict h = 1 := hf (by
      change f (a h) = f 1
      rw [map_one]
      exact hq)
    exact congrArg Subtype.val hh'
  · intro ha
    rw [ha, map_one, map_one]

def suzukiBarCartanImageEquiv :
    (suzukiBarCartanAction Q split i m μ hB).range ≃* (cartanPanelMap Q i).range :=
  (QuotientGroup.quotientKerEquivRange (suzukiBarCartanAction Q split i m μ hB)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (suzukiBarCartanAction_kernel Q split i m μ hB)).trans
      (QuotientGroup.quotientKerEquivRange (cartanPanelMap Q i)))

theorem suzukiBarCartanAction_card (s : RootReflection Q split i) :
    Nat.card (suzukiBarCartanAction Q split i m μ hB).range = 2^(2*m+1)-1 := by
  rw [Nat.card_congr (suzukiBarCartanImageEquiv Q split i m μ hB).toEquiv]
  exact suzuki_cartanImage_card Q split i m μ hB s

theorem suzukiBarCartanAction_cyclic (s : RootReflection Q split i) :
    IsCyclic (suzukiBarCartanAction Q split i m μ hB).range :=
  (suzukiBarCartanImageEquiv Q split i m μ hB).isCyclic.mpr
    (suzuki_cartanImage_cyclic Q split i m μ hB s)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource

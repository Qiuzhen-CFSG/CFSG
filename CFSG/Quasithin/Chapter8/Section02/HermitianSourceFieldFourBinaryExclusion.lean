module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourDiagramLift
public import CFSG.Quasithin.ChapterE.Section02.Structure.LinearThree.Placement
public import Theory.Representation.PSL3Two.FieldFourTransvection
public import Theory.Representation.Quotient

/-!
# Excluding the embedded binary residual with its actual outer actor

Long-root placement puts the original elementary marker in the full binary
component. An injective action-quotient embedding containing that component
then pulls back both the transvection and its separate outer normalizer.
The resulting action on the same coefficient space contradicts the intrinsic
field-four transvection theorem. Neither a full H-kernel nor a linearity
assumption on the outer actor is used.

Source: Aschbacher–Smith 8.2.9, printed p.721, refs/quasithin.pdf.
The original chosen-module application discharges the embedding and all
conjugation equations in the companion Chapter12 module.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterB ChapterE
variable {X : Type*} [Group X] [Finite X]
set_option backward.isDefEq.respectTransparency false

/-- The original elementary marker lies in the actual binary component. -/
theorem corefree_binary_marker_le_component
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (K : Subgroup X) [K.Normal] (hgen : K ⊔ (S : Subgroup X)=⊤)
    (hcore : (minimalParabolicMax S hP).normalCore=⊥)
    (W : Subgroup X) [IsElementaryAbelian 2 W]
    (hWS : W ≤ S) (hSW : (S : Subgroup X) ≤ normalizer (W : Set X))
    (hm : ClassicalGroup.IsPSL K 3 2) : W ≤ K := by
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1)
    (by simpa only [Nat.card_eq_fintype_card,pow_one] using hcard)
  let : IsSimpleGroup PSL(3,F) := Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup K := e.isSimpleGroup
  obtain ⟨g,_,_,hW⟩ := Structure.LinearThree.exists_longRoot_placement
    F (n := 1) (by decide) (by simpa using hcard) K e S hgen hP hcore W hWS hSW
  intro x hx
  obtain ⟨a,_,rfl⟩ := hW hx
  exact ((e.trans (MulAut.conj g)).symm a).property

omit [Finite X] in
/-- The actual residual embedding transfers both the marked transvection and
the separate outer actor to the same field-four representation. -/
theorem embedded_binary_residual_transvection_false
    (K : Subgroup X) (hm : ClassicalGroup.IsPSL K 3 2)
    {A F Y : Type*} [Group A] [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup Y] [Module F Y] [Module (ZMod 2) Y]
    [IsScalarTower (ZMod 2) F Y] [FiniteDimensional F Y]
    (hF : Nat.card F=4) (j : A →* X) (hj : Function.Injective j) (hKj : K ≤ j.range)
    (μ : Representation F A Y)
    (a : A) (haK : j a ∈ K) (ha : a^2=1) (hane : j a≠1)
    (hr : Module.finrank F (LinearMap.range (μ a-1))=1)
    (x : X) (α : MulAut K) (hα : α ∉ MulAut.innerSubgroup K)
    (hαx : ∀ k : K, (α k : X)=x*(k : X)*x⁻¹)
    (γ : MulAut A) (hγ : ∀ b, j (γ b)=x*j b*x⁻¹)
    (f : Y ≃ₗ[ZMod 2] Y) (hf : ∀ b v, f (μ b v)=μ (γ b) (f v)) : False := by
  let ej : A ≃* j.range := MulEquiv.ofBijective j.rangeRestrict
    ⟨fun b c h => hj (congrArg Subtype.val h),j.rangeRestrict_surjective⟩
  let ι : K →* A := ej.symm.toMonoidHom.comp (inclusion hKj)
  have hι (k : K) : j (ι k)=(k : X) := congrArg Subtype.val (ej.apply_symm_apply (inclusion hKj k))
  let b : K := ⟨j a,haK⟩
  have hιb : ι b=a := hj (hι b)
  have hγι (k : K) : γ (ι k)=ι (α k) := by
    apply hj
    rw [hγ,hι,hι,hαx]
  obtain ⟨F₀,hF₀,hfin,hcard,⟨e₀⟩⟩ := hm
  let : Fintype F₀ := Fintype.ofFinite F₀
  let eF : F₀ ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F₀ Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hcard)).symm
  let e : K ≃* BinaryLinearThree.Group :=
    (e₀.trans (Atlas.fieldEquivPSL 3 eF)).trans Matrix.PSL3Two.equiv.symm
  let ν := μ.comp (ι.comp e.symm.toMonoidHom)
  let β := MulAut.congr e α
  have hβ : β ∉ MulAut.innerSubgroup BinaryLinearThree.Group := by
    intro hh
    rw [←MulAut.map_innerSubgroup_congr e] at hh
    obtain ⟨δ,hδ,he⟩ := hh
    exact hα ((MulAut.congr e).injective he ▸ hδ)
  have hbr : Module.finrank F (LinearMap.range (ν (e b)-1))=1 := by
    have hh : ι (e.symm (e b))=a := (congrArg ι (e.symm_apply_apply b)).trans hιb
    exact (congrArg (fun z : A => Module.finrank F (LinearMap.range (μ z-1))) hh).trans hr
  have hb2 : b^2=1 := by
    apply Subtype.ext
    change (j a)^2=1
    rw [←map_pow,ha,map_one]
  have hbne : b≠1 := fun hh => hane (congrArg Subtype.val hh)
  apply BinaryLinearThree.no_field_four_transvection_outer hF ν (e b)
    (by rw [←map_pow,hb2,map_one]) (by simpa using hbne) hbr β hβ f
  intro g v
  change f (μ (ι (e.symm g)) v)=μ (ι (e.symm (β g))) (f v)
  have hb : e.symm (β g)=α (e.symm g) := by
    change e.symm (e (α (e.symm g)))=α (e.symm g)
    exact e.symm_apply_apply _
  rw [hf,hγι,hb]
end CFSG.Quasithin.Chapter8.Section02.HermitianSource

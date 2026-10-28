module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.PositiveRoots
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.SuzukiLayers

/-!
# Unique coordinates on the Section 10 Frattini subgroup

Carter's eight-root coordinates make multiplication on the five middle roots
injective, also in the reverse order used in (10.3)(i). Restricting three
factors to their literal Omega subgroups and using that source product
identity gives unique coordinates on the whole Frattini subgroup. Comparison
with a single perpendicular-root coordinate identifies its intersection
with the Frattini subgroup as exactly Omega of that root.

No mixed field coefficients or natural-module identification are assumed.
In particular the binary cyclic Suzuki root is not replaced by its center.
Source: Fong--Seitz II (1974), (10.3)(i), printed p.221, and I (3G).
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
open ReeF4 ReeF4.RootPresentationRecognition
namespace Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)

/-- The five central factors in the source order of (10.3)(i). -/
def middleFactors : List (Subgroup (X ⧸ Q.D)) :=
  [positiveRoot Q split (.inr 3), positiveRoot Q split (.inl 3),
   positiveRoot Q split (.inr 1), positiveRoot Q split (.inl 2),
   positiveRoot Q split (.inr 2)]

include c in
theorem middleProduct_injective : Function.Injective (rootProduct (middleFactors Q split)) := by
  have hi : Function.Injective (rootProduct (orderedRoots Q split false 8)) := by
    intro p q he
    apply (orderedCoordinates Q split false 8 (by rw [c.rotation_eight])).injective
    apply Subtype.ext
    simpa only [orderedCoordinates_apply] using he
  rw [positiveRoot_ordered Q split c.rotation_eight] at hi
  change Function.Injective (rootProduct
    [positiveRoot Q split (.inl 0), positiveRoot Q split (.inr 2),
     positiveRoot Q split (.inl 2), positiveRoot Q split (.inr 1),
     positiveRoot Q split (.inl 3), positiveRoot Q split (.inr 3),
     positiveRoot Q split (.inl 1), positiveRoot Q split (.inr 0)]) at hi
  rintro ⟨a,b,d,e,f,u⟩ ⟨a',b',d',e',f',u'⟩ he
  have hh := hi (a₁ := (1,f⁻¹,e⁻¹,d⁻¹,b⁻¹,a⁻¹,1,1,PUnit.unit))
    (a₂ := (1,f'⁻¹,e'⁻¹,d'⁻¹,b'⁻¹,a'⁻¹,1,1,PUnit.unit)) (by
      simpa only [middleFactors,rootProduct,Subgroup.coe_inv,OneMemClass.coe_one,
        one_mul,mul_one,mul_inv_rev,mul_assoc] using congrArg Inv.inv he)
  have ha := inv_injective (congrArg (fun z => z.2.2.2.2.2.1) hh)
  have hb := inv_injective (congrArg (fun z => z.2.2.2.2.1) hh)
  have hd := inv_injective (congrArg (fun z => z.2.2.2.1) hh)
  have he := inv_injective (congrArg (fun z => z.2.2.1) hh)
  have hf := inv_injective (congrArg (fun z => z.2.1) hh)
  exact Prod.ext ha (Prod.ext hb (Prod.ext hd (Prod.ext he (Prod.ext hf (show u = u' from @Subsingleton.elim PUnit inferInstance _ _)))))

/-- Literal Omega factors, retaining the cyclic Suzuki root at m = 0. -/
def phiFactors : List (Subgroup (X ⧸ Q.D)) :=
  [omegaOneAmbient (positiveRoot Q split (.inr 3)), positiveRoot Q split (.inl 3),
   omegaOneAmbient (positiveRoot Q split (.inr 1)), positiveRoot Q split (.inl 2),
   omegaOneAmbient (positiveRoot Q split (.inr 2))]

def phiTupleInclusion : RootTuple (phiFactors Q split) → RootTuple (middleFactors Q split)
  | (a,b,d,e,f,u) =>
    (inclusion (omegaOneAmbient_le _) a,b,inclusion (omegaOneAmbient_le _) d,e,
      inclusion (omegaOneAmbient_le _) f,u)

include c in
theorem phiProduct_injective : Function.Injective (rootProduct (phiFactors Q split)) := by
  intro p q he
  have hh := middleProduct_injective Q split c
    (a₁ := phiTupleInclusion Q split p) (a₂ := phiTupleInclusion Q split q) he
  rcases p with ⟨a,b,d,e,f,u⟩
  rcases q with ⟨a',b',d',e',f',u'⟩
  have ha := inclusion_injective (omegaOneAmbient_le _) (congrArg (fun z => z.1) hh)
  have hb := congrArg (fun z => z.2.1) hh
  have hd := inclusion_injective (omegaOneAmbient_le _) (congrArg (fun z => z.2.2.1) hh)
  have he := congrArg (fun z => z.2.2.2.1) hh
  have hf := inclusion_injective (omegaOneAmbient_le _) (congrArg (fun z => z.2.2.2.2.1) hh)
  exact Prod.ext ha (Prod.ext hb (Prod.ext hd (Prod.ext he (Prod.ext hf (show u = u' from @Subsingleton.elim PUnit inferInstance _ _)))))

include c in
theorem phiProduct_range : Set.range (rootProduct (phiFactors Q split)) =
    (phi (simpleRemainder Q split 1) : Set (X ⧸ Q.D)) := by
  rw [rootProduct_range]
  have hp := c.relations.ten_three_product 1
  change (omegaOneAmbient (positiveRoot Q split (.inr 3)) : Set (X ⧸ Q.D)) *
    ((positiveRoot Q split (.inl 3) : Set (X ⧸ Q.D)) *
      ((omegaOneAmbient (positiveRoot Q split (.inr 1)) : Set (X ⧸ Q.D)) *
        ((positiveRoot Q split (.inl 2) : Set (X ⧸ Q.D)) *
          ((omegaOneAmbient (positiveRoot Q split (.inr 2)) : Set (X ⧸ Q.D)) * 1)))) = _
  simpa [Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.omega,nConj,Uat,positiveRoot,positiveKind,positiveWord,mul_assoc] using hp.symm

/-- Unique coordinates on the whole Frattini subgroup, with no mixed coefficient premise. -/
def phiCoordinates : RootTuple (phiFactors Q split) ≃ phi (simpleRemainder Q split 1) :=
  Equiv.ofBijective (fun p => ⟨rootProduct (phiFactors Q split) p,
    by
      change rootProduct (phiFactors Q split) p ∈ (phi (simpleRemainder Q split 1) : Set (X ⧸ Q.D))
      rw [←phiProduct_range Q split c]
      exact Set.mem_range_self p⟩) ⟨
    fun _ _ he => phiProduct_injective Q split c (congrArg Subtype.val he),
    fun x => by
      have hx : (x : X ⧸ Q.D) ∈ (phi (simpleRemainder Q split 1) : Set (X ⧸ Q.D)) := x.property
      rw [←phiProduct_range Q split c] at hx
      obtain ⟨p,hp⟩ := hx
      exact ⟨p,Subtype.ext hp⟩⟩

@[simp] theorem phiCoordinates_apply (p : RootTuple (phiFactors Q split)) :
    (phiCoordinates Q split c p : X ⧸ Q.D) = rootProduct (phiFactors Q split) p := rfl

include c in
theorem phi_inf_perpendicular :
    phi (simpleRemainder Q split 1) ⊓ perpendicularSuzuki Q split =
      omegaOneAmbient (perpendicularSuzuki Q split) := by
  apply le_antisymm
  · intro x hx
    have hp : x ∈ (phi (simpleRemainder Q split 1) : Set (X ⧸ Q.D)) := hx.1
    rw [←phiProduct_range Q split c] at hp
    obtain ⟨p,hp⟩ := hp
    have hperp : positiveRoot Q split (.inr 1) = perpendicularSuzuki Q split := rfl
    let x' : positiveRoot Q split (.inr 1) := ⟨x,hx.2⟩
    have he : rootProduct (middleFactors Q split) (phiTupleInclusion Q split p) =
        rootProduct (middleFactors Q split) (1,1,x',1,1,PUnit.unit) := by
      change rootProduct (phiFactors Q split) p = _
      simpa only [middleFactors,rootProduct,OneMemClass.coe_one,one_mul,mul_one] using hp
    have hh := middleProduct_injective Q split c he
    have hd := congrArg (fun z => (z.2.2.1 : X ⧸ Q.D)) hh
    change (p.2.2.1 : X ⧸ Q.D) = x at hd
    rw [←hd]
    exact p.2.2.1.property
  · intro x hx
    refine ⟨?_,omegaOneAmbient_le _ hx⟩
    change x ∈ (phi (simpleRemainder Q split 1) : Set (X ⧸ Q.D))
    rw [←phiProduct_range Q split c]
    exact ⟨(1,1,⟨x,hx⟩,1,1,PUnit.unit),by simp only [phiFactors,rootProduct,
      OneMemClass.coe_one,one_mul,mul_one]⟩

end Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10

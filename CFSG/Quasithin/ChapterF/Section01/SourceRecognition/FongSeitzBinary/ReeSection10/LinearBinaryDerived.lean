module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.LinearAbelianization
/-!
# The exact binary derived radical in the linear Section 10 branch

Ordered root coordinates give |U_s₁|=q¹¹, |T₁|=q⁷, and a q⁵ lower bound
for the five-factor derived seed. The second V₂ coordinate vanishes on that
seed and is nonzero on the printed diagonal generator. Thus adjoining the
diagonal doubles the seed's order in the binary case. The source
noncontainment hypothesis and the derived upper bound put the derived
radical strictly inside T₁, so its order is at most 64. These bounds prove
the exact generated-subgroup equality printed on p.222 and the actual
abelianization order 2⁵. In the other binary branch the derived subgroup is T₁.

The diagonal uses the corrected native Suzuki chart, in the printed order
U₂^(s₁s₂s₁)(1,0) U₂^(s₁s₂)(1,0). No natural action on V₁ is assumed.
LinearSection transports the result to the original radical and quotient.
Source: Fong--Seitz II (1974), printed p.222, before (10.6).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory ReeF4
open scoped Pointwise IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)

include c in
theorem linearRemainder_card : Nat.card (simpleRemainder Q split 0) = (2^(2*m+1))^11 := by
  let pack : RootTuple (linearFactors Q split) → simpleRemainder Q split 0 := fun p =>
    ⟨rootProduct _ p,by
      change rootProduct _ p ∈ (simpleRemainder Q split 0 : Set (X ⧸ Q.D))
      rw [←linearProduct_range Q split c]
      exact ⟨p,rfl⟩⟩
  have hf : Function.Bijective pack := by
    constructor
    · intro p q h
      exact linearProduct_injective Q split c (congrArg Subtype.val h)
    · intro x
      have hx := x.property
      change (x : X ⧸ Q.D) ∈ (simpleRemainder Q split 0 : Set (X ⧸ Q.D)) at hx
      rw [←linearProduct_range Q split c] at hx
      obtain ⟨p,hp⟩ := hx
      exact ⟨p,Subtype.ext hp⟩
  rw [←Nat.card_congr (Equiv.ofBijective pack hf),card_rootTuple]
  simp only [linearFactors,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    linear_positiveRoot_card Q split c,suzuki_positiveRoot_card Q split c,mul_one]
  ring

include c in
theorem linearT1_card : Nat.card (T1 Q split) = (2^(2*m+1))^7 := by
  let pack : RootTuple (V2InteriorFactors Q split) → linearInterior Q split c := fun p =>
    ⟨rootProduct _ p,by
      change rootProduct _ p ∈ (linearInterior Q split c : Set (X ⧸ Q.D))
      rw [←interiorProduct_range Q split c]
      exact ⟨p,rfl⟩⟩
  have hf : Function.Bijective pack := by
    constructor
    · rintro ⟨a,b,d,e,f,t⟩ ⟨a',b',d',e',f',t'⟩ h
      have hh := linearProduct_injective Q split c
        (a₁ := (1,a,b,d,e,f,1,t)) (a₂ := (1,a',b',d',e',f',1,t')) (by
          simpa only [pack,linearFactors,V2InteriorFactors,rootProduct,OneMemClass.coe_one,
            one_mul,mul_one] using congrArg Subtype.val h)
      exact Prod.ext (congrArg (fun z => z.2.1) hh)
        (Prod.ext (congrArg (fun z => z.2.2.1) hh)
          (Prod.ext (congrArg (fun z => z.2.2.2.1) hh)
            (Prod.ext (congrArg (fun z => z.2.2.2.2.1) hh)
              (Prod.ext (congrArg (fun z => z.2.2.2.2.2.1) hh) (show t = t' from @Subsingleton.elim PUnit inferInstance _ _)))))
    · intro x
      have hx := x.property
      change (x : X ⧸ Q.D) ∈ (linearInterior Q split c : Set (X ⧸ Q.D)) at hx
      rw [←interiorProduct_range Q split c] at hx
      obtain ⟨p,hp⟩ := hx
      exact ⟨p,Subtype.ext hp⟩
  rw [T1_eq_linearInterior Q split c,←Nat.card_congr (Equiv.ofBijective pack hf),card_rootTuple]
  simp only [V2InteriorFactors,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    linear_positiveRoot_card Q split c,suzuki_positiveRoot_card Q split c,mul_one]
  ring

private def seedFactors : List (Subgroup (X ⧸ Q.D)) :=
  [positiveRoot Q split (.inl 2),omegaOneAmbient (positiveRoot Q split (.inr 1)),
   positiveRoot Q split (.inl 3),omegaOneAmbient (positiveRoot Q split (.inr 3)),
   positiveRoot Q split (.inl 1)]

include c in
theorem linearDerivedSeed_card_lower : (2^(2*m+1))^5 ≤ Nat.card (linearDerivedSeed Q split) := by
  have hle : ∀ A ∈ seedFactors Q split, A ≤ linearDerivedSeed Q split := by
    intro A hA
    simp only [seedFactors,List.mem_cons,List.not_mem_nil,or_false] at hA
    rcases hA with rfl | rfl | rfl | rfl | rfl
    · exact le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))
    · exact le_sup_right.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))
    · exact le_sup_right.trans (le_sup_left.trans le_sup_left)
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right
  let pack : RootTuple (seedFactors Q split) → linearDerivedSeed Q split :=
    fun p => ⟨rootProduct _ p,rootProduct_mem _ _ hle p⟩
  have hf : Function.Injective pack := by
    rintro ⟨a,b,d,e,f,t⟩ ⟨a',b',d',e',f',t'⟩ h
    have hh := linearProduct_injective Q split c
      (a₁ := (1,a,inclusion (omegaOneAmbient_le _) b,d,inclusion (omegaOneAmbient_le _) e,f,1,t))
      (a₂ := (1,a',inclusion (omegaOneAmbient_le _) b',d',inclusion (omegaOneAmbient_le _) e',f',1,t')) (by
        simpa only [pack,linearFactors,seedFactors,rootProduct,coe_inclusion,OneMemClass.coe_one,
          one_mul,mul_one] using congrArg Subtype.val h)
    exact Prod.ext (congrArg (fun z => z.2.1) hh)
      (Prod.ext ((inclusion_injective (omegaOneAmbient_le _)) (congrArg (fun z => z.2.2.1) hh))
        (Prod.ext (congrArg (fun z => z.2.2.2.1) hh)
          (Prod.ext ((inclusion_injective (omegaOneAmbient_le _)) (congrArg (fun z => z.2.2.2.2.1) hh))
            (Prod.ext (congrArg (fun z => z.2.2.2.2.2.1) hh) (show t = t' from @Subsingleton.elim PUnit inferInstance _ _)))))
  have hh := Nat.card_le_card_of_injective pack hf
  rw [card_rootTuple] at hh
  simp only [seedFactors,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    linear_positiveRoot_card Q split c,omega_positiveRoot_card Q split c,mul_one] at hh
  convert hh using 1; ring

private def secondCoordinate : (V2Section Q split (pinnedInput Q split c)).numerator →* Multiplicative (CoefficientField m) where
  toFun v := Multiplicative.ofAdd (V2Coordinates Q split (pinnedInput Q split c)
    (Additive.ofMul (QuotientGroup.mk v)) 1)
  map_one' := by
    change Multiplicative.ofAdd (V2Coordinates Q split (pinnedInput Q split c) 0 1) = 1
    rw [map_zero]; rfl
  map_mul' v w := by
    change Multiplicative.ofAdd (V2Coordinates Q split (pinnedInput Q split c)
      (Additive.ofMul (QuotientGroup.mk' _ (v*w))) 1) = _
    rw [map_mul]
    change Multiplicative.ofAdd (V2Coordinates Q split (pinnedInput Q split c)
      (Additive.ofMul (QuotientGroup.mk v)+Additive.ofMul (QuotientGroup.mk w)) 1) = _
    rw [map_add]
    rfl

include c in
private theorem secondCoordinate_T2 (v : simpleRemainder Q split 1)
    (hv : (v : X ⧸ Q.D) ∈ T2 Q split) : secondCoordinate Q split c v = 1 := by
  have hq : (QuotientGroup.mk v : (V2Section Q split (pinnedInput Q split c)).Carrier) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hv
  change Multiplicative.ofAdd (V2Coordinates Q split (pinnedInput Q split c)
    (Additive.ofMul (QuotientGroup.mk v)) 1) = 1
  rw [hq]
  change Multiplicative.ofAdd (V2Coordinates Q split (pinnedInput Q split c) 0 1) = 1
  rw [map_zero]; rfl

include c in
private theorem seed_secondCoordinate : linearDerivedSeed Q split ≤
    (secondCoordinate Q split c).ker.map (simpleRemainder Q split 1).subtype := by
  let c' := pinnedInput Q split c
  have hT2 : T2 Q split ≤ (secondCoordinate Q split c).ker.map (simpleRemainder Q split 1).subtype := by
    intro x hx
    exact ⟨⟨x,T2_le_remainder Q split c' hx⟩,secondCoordinate_T2 Q split c _ hx,rfl⟩
  have hphi : phi (simpleRemainder Q split 1) ≤
      (secondCoordinate Q split c).ker.map (simpleRemainder Q split 1).subtype := le_sup_left.trans hT2
  apply sup_le (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_) ?_
  · exact (nextLinear_le_phi Q split c').trans hphi
  · exact (omegaOneAmbient_le _).trans (le_sup_right.trans hT2)
  · exact (perpendicularLinear_le_phi Q split c').trans hphi
  · exact (shiftedOmega_le_phi Q split c').trans hphi
  · intro x hx
    let a : positiveRoot Q split (.inl 1) := ⟨x,hx⟩
    let v : simpleRemainder Q split 1 := inclusion
      (positiveRoot_le_remainder Q split c' (.inl 1) 1 (by decide)) a
    refine ⟨v,?_,rfl⟩
    have hh := congrFun (V2Coordinates_reflectedLinear Q split c' a) 1
    change V2Coordinates Q split c' (Additive.ofMul (QuotientGroup.mk v)) 1 = 0 at hh
    change Multiplicative.ofAdd (V2Coordinates Q split c'
      (Additive.ofMul (QuotientGroup.mk v)) 1) = 1
    rw [hh]; rfl

/-- The source diagonal generator, in the order printed on p.222. -/
def binaryDerivedDiagonal (c₀ : ReeSixHData Q split n 0) : X ⧸ Q.D :=
  positivePoint Q split (pinnedInput Q split c₀) (RingEquiv.refl _) (.inr 1) (1,0) *
    positivePoint Q split (pinnedInput Q split c₀) (RingEquiv.refl _) (.inr 3) (1,0)

/-- The subgroup generated by the five-factor seed and the printed diagonal. -/
def binaryDerivedClosure (c₀ : ReeSixHData Q split n 0) : Subgroup (X ⧸ Q.D) :=
  linearDerivedSeed Q split ⊔ zpowers (binaryDerivedDiagonal Q split c₀)

theorem binaryDerivedDiagonal_not_mem_seed (c₀ : ReeSixHData Q split n 0) :
    binaryDerivedDiagonal Q split c₀ ∉ linearDerivedSeed Q split := by
  let c' := pinnedInput Q split c₀
  let b := positiveChart Q split c' (RingEquiv.refl _) (.inr 1) (1,0)
  let a := positiveChart Q split c' (RingEquiv.refl _) (.inr 3) (1,0)
  let v : simpleRemainder Q split 1 := ⟨(b : X ⧸ Q.D)*a,
    mul_mem (positiveRoot_le_remainder Q split c' (.inr 1) 1 (by decide) b.property)
      (positiveRoot_le_remainder Q split c' (.inr 3) 1 (by decide) a.property)⟩
  have hv : (v : X ⧸ Q.D) = (1 : positiveRoot Q split (.inl 2))*b*
      (1 : positiveRoot Q split (.inl 3))*
      positivePoint Q split c' (RingEquiv.refl _) (.inr 3) (1,0)*(1 : positiveRoot Q split (.inl 1)) := by
    simp only [OneMemClass.coe_one,one_mul,mul_one]
    rfl
  have hh := congrFun (V2_interior_coordinates Q split c₀ 1 b 1 1 0 1 v hv) 1
  change V2Coordinates Q split c' (Additive.ofMul (QuotientGroup.mk v)) 1 =
    V2MiddleFieldLabel Q split c₀ 1 at hh
  intro hs
  have hs' : (v : X ⧸ Q.D) ∈ linearDerivedSeed Q split := hs
  have hz : v ∈ (secondCoordinate Q split c₀).ker :=
    (mem_map_iff_mem (simpleRemainder Q split 1).subtype_injective).mp
      (seed_secondCoordinate Q split c₀ hs')
  change Multiplicative.ofAdd (V2Coordinates Q split c' (Additive.ofMul (QuotientGroup.mk v)) 1) = 1 at hz
  rw [hh] at hz
  have hz' : V2MiddleFieldLabel Q split c₀ 1 = V2MiddleFieldLabel Q split c₀ 0 :=
    (congrArg Multiplicative.toAdd hz).trans (map_zero _).symm
  exact one_ne_zero ((V2MiddleFieldLabel Q split c₀).injective hz')

private theorem binaryDerivedCalculation (c₀ : ReeSixHData Q split n 0)
    (hn : ¬positiveRoot Q split (.inr 3) ≤ linearDerived Q split) :
    Nat.card (linearDerived Q split) = 64 ∧
      linearDerived Q split = binaryDerivedClosure Q split c₀ := by
  let A := linearDerivedSeed Q split
  let K := binaryDerivedClosure Q split c₀
  let D := linearDerived Q split
  have hKD : K ≤ D := sup_le (linearDerivedSeed_le Q split c₀)
    (zpowers_le.mpr (binary_linearDerived_source_diagonal Q split c₀ hn))
  have hAK : A ≤ K := le_sup_left
  have hproper : A ≠ K := by
    intro he
    have hk : binaryDerivedDiagonal Q split c₀ ∈ K :=
      (show zpowers (binaryDerivedDiagonal Q split c₀) ≤ K from le_sup_right) (mem_zpowers _)
    exact binaryDerivedDiagonal_not_mem_seed Q split c₀ (he.ge hk)
  have hA : 32 ≤ Nat.card A := by simpa using linearDerivedSeed_card_lower Q split c₀
  have hK : 64 ≤ Nat.card K := by
    obtain ⟨k,hk⟩ := card_dvd_of_le hAK
    have hk2 : 2 ≤ k := by
      by_contra hn
      have hh : Nat.card K ≤ Nat.card A := by nlinarith
      exact hproper (eq_of_le_of_card_ge hAK hh)
    nlinarith
  have hDT := binary_linearDerived_le_T1 Q split c₀
  have hT : Nat.card (T1 Q split) = 128 := by simpa using linearT1_card Q split c₀
  have hD : Nat.card D ≤ 64 := by
    obtain ⟨k,hk⟩ := card_dvd_of_le hDT
    have hk2 : 2 ≤ k := by
      by_contra hk2
      have hh : Nat.card (T1 Q split) ≤ Nat.card D := by nlinarith
      have he := eq_of_le_of_card_ge hDT hh
      apply hn
      rw [he]
      exact le_sup_right.trans le_sup_left
    change Nat.card (T1 Q split) = Nat.card D*k at hk
    rw [hT] at hk
    nlinarith
  exact ⟨le_antisymm hD (hK.trans (card_le_of_le hKD)),
    (eq_of_le_of_card_ge hKD (hD.trans hK)).symm⟩

/-- In the other binary branch the derived subgroup is the whole T₁. -/
theorem binary_linearDerived_eq_T1_of_shifted (c₀ : ReeSixHData Q split n 0)
    (hs : positiveRoot Q split (.inr 3) ≤ linearDerived Q split) :
    linearDerived Q split = T1 Q split :=
  le_antisymm (binary_linearDerived_le_T1 Q split c₀)
    (T1_le_linearDerived_of_shifted Q split c₀ hs)

/-- The exact generated subgroup printed in the binary noncontainment branch. -/
theorem binary_linearDerived_eq_generated (c₀ : ReeSixHData Q split n 0)
    (hn : ¬positiveRoot Q split (.inr 3) ≤ linearDerived Q split) :
    linearDerived Q split = binaryDerivedClosure Q split c₀ :=
  (binaryDerivedCalculation Q split c₀ hn).2

/-- The derived radical has order 64 in the binary noncontainment branch. -/
theorem binary_linearDerived_card (c₀ : ReeSixHData Q split n 0)
    (hn : ¬positiveRoot Q split (.inr 3) ≤ linearDerived Q split) :
    Nat.card (linearDerived Q split) = 64 :=
  (binaryDerivedCalculation Q split c₀ hn).1

/-- The actual abelianization has the source order 2⁵. -/
theorem binary_linearAbelianization_card (c₀ : ReeSixHData Q split n 0)
    (hn : ¬positiveRoot Q split (.inr 3) ≤ linearDerived Q split) :
    Nat.card (Abelianization (simpleRemainder Q split 0)) = 32 := by
  have hR : Nat.card (simpleRemainder Q split 0) = 2048 := by
    simpa using linearRemainder_card Q split c₀
  have hm : (commutator (simpleRemainder Q split 0)).map (simpleRemainder Q split 0).subtype =
      linearDerived Q split := map_subtype_commutator _
  have hD : Nat.card (commutator (simpleRemainder Q split 0)) = 64 := by
    rw [←card_map_of_injective (simpleRemainder Q split 0).subtype_injective,
      hm,binary_linearDerived_card Q split c₀ hn]
  have hh := (commutator (simpleRemainder Q split 0)).card_mul_index
  change Nat.card (commutator (simpleRemainder Q split 0)) *
    Nat.card (Abelianization (simpleRemainder Q split 0)) = Nat.card (simpleRemainder Q split 0) at hh
  rw [hR,hD] at hh
  omega

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10

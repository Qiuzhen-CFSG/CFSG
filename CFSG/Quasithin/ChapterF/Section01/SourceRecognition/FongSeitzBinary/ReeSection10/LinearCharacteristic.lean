module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.LinearDenominator
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.OriginalLinearDerived

/-!
# The characteristic linear denominator and its original quotient

The p.222 derived lower bound combines with LinearDenominator's upper bound
to identify X₁ with Phi(U_s₁) for q>2, and also in the binary branch where
the whole shifted Suzuki root is derived. Thus X₁ is characteristic and
normalized by the actual linear rank-one group in the positive-parameter
case. In the binary case the quotient by T₁ is a product of two cyclic
order-four roots, giving the additional upper bound [U_s₁,U_s₁] ≤ T₁.

The same endpoint equivalence transports X₁ to the original first two-core.
Its quotient is elementary abelian of order q² for every m>=0, with an
actual group isomorphism to the two barred root coordinates. Both ordered
endpoint inclusion squares and the literal original Q.q formula are retained.
These coordinates do not yet identify the faithful irreducible rank-one
action or synchronize its field labels. The binary noncontainment branch
still needs the exact diagonal derived subgroup and characteristic
abelianization-preimage argument before the natural basis (10.6).

Source: Fong--Seitz II (1974), printed p.222, after (10.5) and before (10.6).
The retained input is ReeSixHData on the same marked quotient and split group;
no additional Section 10 equations or natural action are assumed.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
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
/-- The whole-shifted-root branch on p.222 also includes the printed binary
alternative. Reflection supplies the other full Suzuki factor. -/
theorem T1_le_linearDerived_of_shifted
    (hs : positiveRoot Q split (.inr 3) ≤ linearDerived Q split) :
    T1 Q split ≤ linearDerived Q split := by
  exact sup_le (sup_le (sup_le (sup_le (nextLinear_le_linearDerived Q split c)
    (perpendicular_le_linearDerived_of_shifted Q split c hs))
      (perpendicularLinear_le_linearDerived Q split c)) hs)
        (reflectedLinear_le_linearDerived Q split c)

include c in
theorem X1_eq_linearPhi_of_shifted
    (hs : positiveRoot Q split (.inr 3) ≤ linearDerived Q split) :
    X1 Q split = phi (simpleRemainder Q split 0) :=
  X1_eq_linearPhi_of_T1_le_derived Q split c (T1_le_linearDerived_of_shifted Q split c hs)

include c in
theorem X1_characteristic_of_shifted
    (hs : positiveRoot Q split (.inr 3) ≤ linearDerived Q split) :
    ((X1 Q split).subgroupOf (simpleRemainder Q split 0)).Characteristic :=
  X1_characteristic_of_T1_le_derived Q split c (T1_le_linearDerived_of_shifted Q split c hs)

include c in
/-- For every nonbinary parameter the printed denominator is exactly the
Frattini subgroup of the actual linear radical. -/
theorem X1_eq_linearPhi_of_pos (hm : 0 < m) :
    X1 Q split = phi (simpleRemainder Q split 0) :=
  X1_eq_linearPhi_of_T1_le_derived Q split c (T1_le_linearDerived_of_pos Q split c hm)

include c in
theorem X1_characteristic_of_pos (hm : 0 < m) :
    ((X1 Q split).subgroupOf (simpleRemainder Q split 0)).Characteristic :=
  X1_characteristic_of_T1_le_derived Q split c (T1_le_linearDerived_of_pos Q split c hm)

include c in
/-- The rank-one action on the denominator is derived from the source
Frattini identification and relative radical normality. -/
theorem rankOne_normalizes_X1_of_pos (hm : 0 < m) :
    rankOne Q split 0 ≤ normalizer (X1 Q split : Set (X ⧸ Q.D)) := by
  have hk := remainder_le_panelKernel_of_marking Q split 0 c.linear c.linearSylow c.linearBorel
    (ReeSource.linear_normalizer_index c.linearSylow)
  rw [X1_eq_linearPhi_of_pos Q split c hm]
  exact ((rankOne_le_parabolic Q split 0).trans
    (remainder_parabolic_normalizes Q split 0 hk)).trans
      (normalizer_le_normalizer_characteristic_image _ (frattini _))

include c in
theorem linearFrattini_quotient_card_of_pos (hm : 0 < m) :
    Nat.card (simpleRemainder Q split 0 ⧸ frattini (simpleRemainder Q split 0)) =
      (2^(2*m+1))^2 := by
  have hc := X1_quotient_card Q split c
  rw [X1_eq_linearPhi_of_pos Q split c hm] at hc
  have he : (phi (simpleRemainder Q split 0)).subgroupOf (simpleRemainder Q split 0) =
      frattini (simpleRemainder Q split 0) :=
    comap_map_eq_self_of_injective (simpleRemainder Q split 0).subtype_injective _
  rwa [he] at hc

open scoped IsMulCommutative
/-- In the binary case the two endpoint roots are cyclic of order four,
so the whole derived radical lies in T₁. This is the upper bound before
the separate diagonal-subgroup calculation in the noncontainment branch. -/
theorem binary_linearDerived_le_T1 (c₀ : ReeSixHData Q split n 0) :
    linearDerived Q split ≤ T1 Q split := by
  let : IsCyclic (simpleRoot Q split 1) :=
    binary_suzuki_root_cyclic Q split 1 c₀.suzuki c₀.suzukiBorel
  let a : simpleRoot Q split 1 ≃* positiveRoot Q split (.inr 2) :=
    positiveRootEquiv Q split c₀ (.inr 2)
  let b : simpleRoot Q split 1 ≃* positiveRoot Q split (.inr 0) :=
    positiveRootEquiv Q split c₀ (.inr 0)
  let : IsCyclic (positiveRoot Q split (.inr 2)) :=
    isCyclic_of_surjective a.toMonoidHom a.surjective
  let : IsCyclic (positiveRoot Q split (.inr 0)) :=
    isCyclic_of_surjective b.toMonoidHom b.surjective
  have hc := Abelianization.commutator_subset_ker (linearBoundary Q split c₀)
  rw [linearDerived,←map_subtype_commutator]
  rintro x ⟨v,hv,rfl⟩
  have he : linearBoundary Q split c₀ v = 1 := hc hv
  have hq := congrArg (linearEdgeEquiv Q split c₀) he
  change linearEdgeEquiv Q split c₀ ((linearEdgeEquiv Q split c₀).symm
    (QuotientGroup.mk' _ v)) = linearEdgeEquiv Q split c₀ 1 at hq
  rw [MulEquiv.apply_symm_apply,map_one] at hq
  have hi := (QuotientGroup.eq_one_iff
    (N := (linearInterior Q split c₀).subgroupOf (simpleRemainder Q split 0)) v).mp hq
  exact (T1_eq_linearInterior Q split c₀).ge hi

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10

open BenderSuzuki.PFAppendixIII MarkedLocal ReeSource
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (split : SplitData Q.tits) {n m : ℕ} (c : ReeSixHData Q split n m)

/-- The actual original first endpoint two-core, with its literal inclusion. -/
def originalV1NumeratorEquiv : pCore 2 (parabolic L S 0) ≃* simpleRemainder Q split 0 :=
  originalRadicalEquiv Q e split 0
    (remainder_le_panelKernel_of_marking Q split 0 c.linear c.linearSylow c.linearBorel
      (ReeSource.linear_normalizer_index c.linearSylow))

/-- The printed X₁ denominator inside the original first endpoint two-core. -/
def originalX1 : Subgroup (pCore 2 (parabolic L S 0)) :=
  ((X1 Q split).subgroupOf (simpleRemainder Q split 0)).comap
    (originalV1NumeratorEquiv Q e split c).toMonoidHom

theorem mem_originalX1 (v : pCore 2 (parabolic L S 0)) :
    v ∈ originalX1 Q e split c ↔ endpointMap Q e 0 v ∈ X1 Q split := Iff.rfl

/-- Both barred coordinates on the original radical, before identifying its
rank-one action or synchronizing their field labels. -/
def originalLinearBarBoundary : pCore 2 (parabolic L S 0) →*
    (Multiplicative (BinaryGaloisField (2*m+1)) ×
     Multiplicative (BinaryGaloisField (2*m+1))) :=
  (linearBarBoundary Q split c).comp (originalV1NumeratorEquiv Q e split c).toMonoidHom

theorem originalLinearBarBoundary_surjective :
    Function.Surjective (originalLinearBarBoundary Q e split c) :=
  (linearBarBoundary_surjective Q split c).comp (originalV1NumeratorEquiv Q e split c).surjective

theorem originalLinearBarBoundary_kernel :
    (originalLinearBarBoundary Q e split c).ker = originalX1 Q e split c := by
  change (linearBarBoundary Q split c).ker.comap
    (originalV1NumeratorEquiv Q e split c).toMonoidHom = _
  rw [linearBarBoundary_kernel]
  rfl

instance originalX1_normal : (originalX1 Q e split c).Normal := by
  rw [←originalLinearBarBoundary_kernel Q e split c]
  infer_instance

/-- The actual original quotient by X₁ has the two barred endpoint
coordinates. This is a group isomorphism, not yet a natural-module marking. -/
def originalV1BarEquiv :
    (pCore 2 (parabolic L S 0) ⧸ originalX1 Q e split c) ≃*
      (Multiplicative (BinaryGaloisField (2*m+1)) ×
       Multiplicative (BinaryGaloisField (2*m+1))) :=
  (QuotientGroup.quotientMulEquivOfEq (originalLinearBarBoundary_kernel Q e split c).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (originalLinearBarBoundary Q e split c)
      (originalLinearBarBoundary_surjective Q e split c))

@[simp] theorem originalV1BarEquiv_mk (v : pCore 2 (parabolic L S 0)) :
    originalV1BarEquiv Q e split c (QuotientGroup.mk v) =
      linearBarBoundary Q split c (originalV1NumeratorEquiv Q e split c v) := rfl

theorem originalV1_card : Nat.card (pCore 2 (parabolic L S 0) ⧸ originalX1 Q e split c) =
    (2^(2*m+1))^2 := by
  rw [Nat.card_congr (originalV1BarEquiv Q e split c).toEquiv,Nat.card_prod]
  have hf : Nat.card (Multiplicative (BinaryGaloisField (2*m+1))) = 2^(2*m+1) :=
    (Nat.card_congr Multiplicative.toAdd).trans (GaloisField.card 2 (2*m+1) (by omega))
  rw [hf,pow_two]

instance originalV1_elementary :
    IsElementaryAbelian 2 (pCore 2 (parabolic L S 0) ⧸ originalX1 Q e split c) where
  toIsMulCommutative := IsMulCommutative.of_comm (fun x y =>
    (originalV1BarEquiv Q e split c).injective (by rw [map_mul,map_mul]; exact mul_comm _ _))
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
    apply (originalV1BarEquiv Q e split c).injective
    rw [map_pow,map_one]
    apply Prod.ext
    all_goals change 2 • _ = (0 : BinaryGaloisField (2*m+1))
    all_goals exact (two_nsmul _).trans (CharTwo.add_self_eq_zero _))

include c in
theorem originalX1_eq_frattini_of_shifted
    (hs : positiveRoot Q split (.inr 3) ≤ linearDerived Q split) :
    originalX1 Q e split c = frattini (pCore 2 (parabolic L S 0)) := by
  rw [originalX1,X1_eq_linearPhi_of_shifted Q split c hs]
  have he : (phi (simpleRemainder Q split 0)).subgroupOf (simpleRemainder Q split 0) =
      frattini (simpleRemainder Q split 0) :=
    comap_map_eq_self_of_injective (simpleRemainder Q split 0).subtype_injective _
  rw [he,←frattini_map_equiv (originalV1NumeratorEquiv Q e split c)]
  exact comap_map_eq_self_of_injective (originalV1NumeratorEquiv Q e split c).injective _

include c in
theorem originalX1_eq_frattini_of_pos (hm : 0 < m) :
    originalX1 Q e split c = frattini (pCore 2 (parabolic L S 0)) :=
  originalX1_eq_frattini_of_shifted Q e split c (shiftedSuzuki_le_linearDerived_of_pos Q split c hm)

include c in
theorem originalX1_characteristic_of_pos (hm : 0 < m) :
    (originalX1 Q e split c).Characteristic := by
  rw [originalX1_eq_frattini_of_pos Q e split c hm]
  infer_instance

/-- The binary derived upper bound holds inside the original first endpoint
and uses the actual marked image of every derived-radical representative. -/
theorem original_binaryDerived_in_T1 (c₀ : ReeSixHData Q split n 0)
    (v : commutator (pCore 2 (parabolic L S 0))) :
    endpointMap Q e 0 v.val.val ∈ T1 Q split := by
  have hk := remainder_le_panelKernel_of_marking Q split 0 c₀.linear c₀.linearSylow c₀.linearBorel
    (ReeSource.linear_normalizer_index c₀.linearSylow)
  exact binary_linearDerived_le_T1 Q split c₀
    (originalDerivedRadicalEquiv Q e split 0 hk v).property

/-- Every original radical representative lies in the common Sylow, and
both ordered endpoint maps give the same denominator membership test. -/
theorem originalX1_endpoints (h : HypothesisF11 L S) (v : pCore 2 (parabolic L S 0)) :
    ∀ i : Fin 2, ∃ hi : (v.val.val : G) ∈ parabolic L S i,
      endpointMap Q e i ⟨v.val.val,hi⟩ = (originalV1NumeratorEquiv Q e split c v : X ⧸ Q.D) ∧
      (v ∈ originalX1 Q e split c ↔ endpointMap Q e i ⟨v.val.val,hi⟩ ∈ X1 Q split) := by
  let a := originalV1NumeratorEquiv Q e split c v
  let x : S := (ReePresentation.sourceSylowEquiv Q e h split).symm ⟨a,a.property.1⟩
  have hx : sylowMap Q e h x = (a : X ⧸ Q.D) :=
    congrArg Subtype.val ((ReePresentation.sourceSylowEquiv Q e h split).apply_symm_apply _)
  have hv : v.val = (⟨x,(show S ≤ parabolic L S 0 from le_sup_right.trans le_sup_left)
      x.property⟩ : parabolic L S 0) := by
    apply (Endpoint Q 0).subtype_injective.comp (endpoint Q e 0).injective
    change endpointMap Q e 0 v.val = endpointMap Q e 0 _
    rw [endpoint_sylow Q e h,hx]
    rfl
  have hv' : (v.val.val : G) = x := congrArg (fun z : parabolic L S 0 => (z : G)) hv
  intro i
  have hi : (v.val.val : G) ∈ parabolic L S i := by
    rw [hv']
    exact (show S ≤ parabolic L S i from le_sup_right.trans le_sup_left) x.property
  refine ⟨hi,?_,?_⟩
  · have hh : (⟨v.val.val,hi⟩ : parabolic L S i) =
        ⟨x,(show S ≤ parabolic L S i from le_sup_right.trans le_sup_left) x.property⟩ :=
      Subtype.ext hv'
    rw [hh,endpoint_sylow Q e h]
    exact hx
  · have hh : (⟨v.val.val,hi⟩ : parabolic L S i) =
        ⟨x,(show S ≤ parabolic L S i from le_sup_right.trans le_sup_left) x.property⟩ :=
      Subtype.ext hv'
    rw [hh,endpoint_sylow Q e h,hx]
    rfl

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
open ReeSource
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits) {n m : ℕ} (c : ReeSixHData Q split n m)

/-- Denominator membership uses precisely the original generated-group
quotient, without changing either endpoint or the original kernel D. -/
theorem originalX1_quotient (v : pCore 2 (parabolic L S 0)) :
    v ∈ originalX1 Q (originalMarkedIso Q) split c ↔
      Q.q ⟨v,parabolic_le_generated 0 v.val.property⟩ ∈ X1 Q split := by
  rw [mem_originalX1]
  exact Iff.of_eq (congrArg (fun x => x ∈ X1 Q split) (originalMarkedIso_left_apply Q v.val))

/-- The two-bar quotient marking retains the literal Q.q representative. -/
theorem originalV1BarEquiv_quotient (v : pCore 2 (parabolic L S 0)) :
    originalV1BarEquiv Q (originalMarkedIso Q) split c (QuotientGroup.mk v) =
      linearBarBoundary Q split c
        (⟨Q.q ⟨v,parabolic_le_generated 0 v.val.property⟩,
          by rw [←originalRadicalEquiv_quotient Q split 0
            (remainder_le_panelKernel_of_marking Q split 0 c.linear c.linearSylow c.linearBorel
              (ReeSource.linear_normalizer_index c.linearSylow)) v]
             exact (originalV1NumeratorEquiv Q (originalMarkedIso Q) split c v).property⟩ :
          simpleRemainder Q split 0) := by
  rw [originalV1BarEquiv_mk]
  congr 1
  exact Subtype.ext (originalRadicalEquiv_quotient Q split 0
    (remainder_le_panelKernel_of_marking Q split 0 c.linear c.linearSylow c.linearBorel
      (ReeSource.linear_normalizer_index c.linearSylow)) v)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10

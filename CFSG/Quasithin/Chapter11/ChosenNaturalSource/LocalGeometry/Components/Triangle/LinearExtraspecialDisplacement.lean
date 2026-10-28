module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.LinearCentralizerSpan
public import Theory.GroupAction.ExtraspecialCubicDisplacement

/-!
# Cubic displacement of the original linear centralizer span

Apply extraspecial fixed-point generation to the original
U = ⟨V^{C_G(V₁)}⟩. The proved G.2.2 span theorem gives U ≤ T and the
actual KX action. Faithfulness of the chosen central quotient puts C_L(V)
inside O₂(L), so the cubic X_K = X intersect K cannot centralize U.
The original X₁ moves V₁ whereas X_K fixes V₁, distinguishing these two
cubic subgroups. The source Cartan is elementary of order nine.

Consequently [C_U(X₁),X_K] and [C_U(X₁),X] are nontrivial whenever an
extraspecial three-subgroup P ≤ KX contains the original X with
Z(P) = X_K. The common-Q application removes the previous explicit
nonzero-displacement premise from the centralizer-span/core dichotomy.
It retains the same full SL₃ quotient, original normalizers and cores.
No abelianness or separate faithfulness assumption on U is required.

The marked P is an explicit remaining model obligation: its existence has
not been deduced here from KX/O₂(KX) ≃ PGL₃(4). This owner retains that
construction, both subsequent centralizer/module branches, common-normal
existence, the original SL₃(4) exclusion, both triangle orientations and
full 11.1.1--3 assembly. Earlier-source inputs retain their producers and
final discharge by qt-d-1222-natural-local-geometry.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004, proof of
11.1.2, printed p.763, the extraspecial Sylow-three action paragraph.
-/

open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
public noncomputable section
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

include S in
private theorem seed_centralizer_le_core :
    L ⊓ centralizer (V : Set G) ≤ L.pCoreIn 2 := by
  rintro l ⟨hl,hc⟩
  have hq : QuotientGroup.mk' (pCore 2 L) (⟨l,hl⟩ : L) = 1 := by
    apply S.faithful
    rw [map_one,D.centralQuotientAction_mk]
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ v =>
      have hv : (v.val.toMul.val : G) ∈ V :=
        D.image_eq.le (mem_map_of_mem _ (mem_map_of_mem _ v.property))
      have he : D.chosenAction ⟨l,hl⟩ v = v := by
        apply Subtype.ext
        apply Additive.toMul.injective
        apply Subtype.ext
        apply Subtype.ext
        change l * (v.val.toMul.val : G) * l⁻¹ = (v.val.toMul.val : G)
        exact mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp hc) _ hv).symm
      change Submodule.Quotient.mk (D.chosenAction ⟨l,hl⟩ v) = Submodule.Quotient.mk v
      rw [he]
  exact mem_map_of_mem L.subtype ((QuotientGroup.eq_one_iff _).mp hq)

include m in
private theorem cartan_elementary (hd : S.field.degree = 2)
    {X : Subgroup G} (hX : IsCartan T L X) : IsElementaryAbelian 3 X := by
  let e := (Coordinates.sl3 m).cartanTorusEquiv hX
  have hF : Nat.card S.field.Carrier = 4 := by simpa [hd] using S.field.card_eq
  have hunit : Nat.card S.field.Carrierˣ = 3 := by rw [Nat.card_units,hF]
  refine { toIsMulCommutative := .of_comm fun a b => e.injective (by simp [mul_comm])
           exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro x
  apply e.injective
  rw [map_pow,map_one]
  exact Prod.ext (hunit ▸ pow_card_eq_one' (x := (e x).1))
    (hunit ▸ pow_card_eq_one' (x := (e x).2))

/-- The actual source span has nonzero displacement under both original actors.
The marked extraspecial subgroup is the remaining PGL₃(4) model input. -/
theorem linear_cubic_displacement_of_marked_extraspecial
    (f : InvariantFlag (.sl3 m)) (hd : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X P : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.ComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 ≤ K)
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 0) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 0) ≤ centralizer (f.Vi 0 : Set G))
    [IsExtraspecial 3 P] (hP : P ≤ K ⊔ X) (hXP : X ≤ P)
    (hZ : (center P).map P.subtype = X ⊓ K) :
    let E := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
    let U := conjugateSpanBy V (centralizer (f.Vi 0 : Set G))
    ⁅U ⊓ centralizer (E : Set G),X ⊓ K⁆ ≠ ⊥ ∧
      ⁅U ⊓ centralizer (E : Set G),X⁆ ≠ ⊥ := by
  intro E U
  let Z := (center P).map P.subtype
  let : IsElementaryAbelian 3 X := cartan_elementary D S m hd hX
  have hXcard : Nat.card X = 9 := by
    rw [(Coordinates.sl3 m).cartan_card hX,hd]
    norm_num
  have hZcard : Nat.card Z = 3 :=
    (card_map_of_injective P.subtype_injective).trans (IsExtraspecial.center_order_p 3 P)
  have hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree) :=
    ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,
      ⟨SL3.flagLocalCoreEquiv S m f 0⟩⟩
  have hKC := subspace_containing_component_centralizes D S f (f.Vi 0)
    le_rfl hm hfix hK hLK
  have hEZ : E ≠ Z := by
    intro he
    apply hmove
    change E ≤ centralizer (f.Vi 0 : Set G)
    rw [he]
    exact hZ.le.trans (inf_le_right.trans hKC)
  have hZU : ¬ Z ≤ centralizer (U : Set G) := by
    intro hc
    have hZL : Z ≤ L := hZ.le.trans (inf_le_left.trans (hX.1.trans inf_le_left))
    have hZV : Z ≤ centralizer (V : Set G) := hc.trans (centralizer_le (le_conjugateSpanBy _ _))
    have hp : IsPGroup 2 Z := (isPGroup_pCoreIn 2 L).to_le
      ((le_inf hZL hZV).trans (seed_centralizer_le_core D S))
    rcases hp.card_eq_or_dvd with h | h
    · omega
    · rw [hZcard] at h
      norm_num at h
  have hU := (linear_point_centralizer_span D S m f).2.1
  have hactors := (linear_point_centralizer_span_actors D S m f hfix hX hK hLK).1
  have hnonzero := extraspecial_cubic_fixed_commutator_ne_bot P X E U
    (T.isPGroup'.to_le hU) (hP.trans (le_sup_left.trans hactors)) hXP inf_le_left
    hXcard hcard (hZ.le.trans inf_le_left) hEZ hZU
  have hnonzero' : ⁅U ⊓ centralizer (E : Set G),X ⊓ K⁆ ≠ ⊥ := by
    simpa only [hZ] using hnonzero
  exact ⟨hnonzero',fun h => hnonzero' (bot_unique (h ▸ commutator_mono le_rfl inf_le_left))⟩

/-- The literal common-Q consumer with nonzero displacement derived from the
marked extraspecial action, preserving all conclusions of the span theorem. -/
theorem linear_triangle_cubic_displacement_of_common_normal
    (f : InvariantFlag (.sl3 m)) (hd : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K K₀ X Q : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hgen : f.Li 0 ⊔ K₀ = K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 1) ≤ centralizer (f.Vi 0 : Set G))
    (hQ : Q ≠ ⊥) (hQT : Q ≤ (T : Subgroup G))
    (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hKQ : K₀ ≤ normalizer (Q : Set G)) (hLQ : f.Li 1 ≤ normalizer (Q : Set G))
    {P : Subgroup G} [IsExtraspecial 3 P]
    (hP : P ≤ K ⊔ X) (hXP : X ≤ P)
    (hZ : (center P).map P.subtype = X ⊓ K) :
    let E := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
    let H := localResidual L E
    let U := conjugateSpanBy V (centralizer (f.Vi 0 : Set G))
    ⁅U ⊓ centralizer (E : Set G),X⁆ ≠ ⊥ ∧
    (let C := centralizer (f.Vi 0 : Set G)
     let P := (f.Vi 0).subgroupOf C
     let : P.Normal := normal_subgroupOf_of_le_normalizer (Subgroup.centralizer_le_normalizer _)
     (U.subgroupOf C).map (QuotientGroup.mk' P) ≤
       (center (pCore 2 (C ⧸ P))).map (pCore 2 (C ⧸ P)).subtype) ∧
    U ≤ (centralizer (f.Vi 0 : Set G)).pCoreIn 2 ∧
    U ≤ (T : Subgroup G) ∧ (frattini U).map U.subtype ≤ f.Vi 0 ∧
    ⁅U,U⁆ ≤ f.Vi 0 ∧ (K ⊔ X) ⊔ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
    (U.subgroupOf (T : Subgroup G)).Normal ∧ E ≤ H ∧ X ≤ H ∧ H ≤ centralizer (E : Set G) ∧
    Source.IsSL (H ⧸ pCore 2 H) 3 4 ∧
    H.pCoreIn 2 = H ⊓ L.pCoreIn 2 ∧ H ⊔ L.pCoreIn 2 = L ∧
    V = ⁅V,H⁆ ∧ ¬ normalizer (E : Set G) ≤ normalizer (L : Set G) ∧
    (⁅H.pCoreIn 2,H⁆ ≠ ⊥ ∨
      (¬ ⁅U ⊓ centralizer (E : Set G),X⁆ ≤
        (L ⊔ (T : Subgroup G)).pCoreIn 2) ∧
      ¬ U ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2) := by
  intro E H U
  have he := linear_four_cartan_kernels_eq D S m hd f hX
  have hc : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 0) : Subgroup G) = 3 := by
    simpa only [he] using hcard
  have hm : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 0) ≤ centralizer (f.Vi 0 : Set G) := by
    simpa only [he] using hmove
  have hY := (linear_cubic_displacement_of_marked_extraspecial D S m f hd hfix hX
    hK.1 hLK.le hc hm hP hXP hZ).2
  exact ⟨hY,linear_triangle_centralizer_span_of_common_normal D S m f hd hfix hX hK hLK
    hK₀ hK₀K hTK₀ hgen hk hp hcard hmove hQ hQT hTQ hKQ hLQ hY⟩

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle

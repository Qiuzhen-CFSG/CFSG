module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiTorusCentralizer
public import Theory.GroupAction.Quotient
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCentralizerSpanLayer

/-!
# No torus-fixed coset in the literal centralizer quotient

Select the same full-edge complement whose linear part D has centralizer
of order q inside the full third kernel H. The natural W/H calculation
identifies C_W(D) with C_H(D), so every D-fixed element of C=C_(Q_m)(H)
is in W. Coprime fixed-point lifting across the elementary normal subgroup
W then makes the fixed subgroup of the actual C/W trivial.

Construct the action on this literal quotient by conjugation, kill Q_m,
and descend through the original/starred endpoint quotient equivalence.
The conclusion records that same action on every starred representative
and the same selected D. It retains the original completion and all earlier
field, natural-center and reciprocal-commutator inputs. This removes the
fixed-point premise in the remaining irreducibility argument, without
asserting irreducibility or the equality G_m^(2)=W.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
proof of (12.9), printed pp.189--190.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem quotient_fixed_eq_one
    {X : Type*} [Group X] (C W D : Subgroup X) [Finite C] [Finite D]
    (hWC : W ≤ C) (hW : (W.subgroupOf C).Normal)
    [IsMulCommutative (W.subgroupOf C)]
    (hDC : D ≤ normalizer (C : Set X)) (hDW : D ≤ normalizer (W : Set X))
    (hcop : Nat.Coprime (Nat.card D) (Nat.card W))
    (hfix : C ⊓ centralizer (D : Set X) ≤ W) :
    let _ := hW
    ∀ α : D →* MulAut (C ⧸ W.subgroupOf C),
      (∀ d : D, ∀ c : C, α d (QuotientGroup.mk c) =
        QuotientGroup.mk ⟨(d : X)*c*(d : X)⁻¹,
          (mem_normalizer_iff.mp (hDC d.property) c).mp c.property⟩) →
      ∀ v, (∀ d, α d v = v) → v = 1 := by
  let _ := hW
  dsimp only
  intro α hα v hv
  let _ : MulDistribMulAction D C := conjMulDistribMulActionOfLeNormalizer D C hDC
  have hInv : IsInvariant D C (W.subgroupOf C) := by
    constructor
    intro d c
    exact mem_normalizer_iff.mp (hDW d.property) c
  let _ := quotientMulDistribMulAction (W.subgroupOf C) hInv
  have hv' : v ∈ FixedPoints.subgroup D (C ⧸ W.subgroupOf C) := by
    intro d
    obtain ⟨c,rfl⟩ := QuotientGroup.mk'_surjective (W.subgroupOf C) v
    change QuotientGroup.mk' (W.subgroupOf C) (d • c) = QuotientGroup.mk' (W.subgroupOf C) c
    exact (hα d c).symm.trans (hv d)
  have hcop' : Nat.Coprime (Nat.card D) (Nat.card (W.subgroupOf C)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hWC).toEquiv]
    exact hcop
  rw [fixedPoints_subgroup_quotient_eq_map_of_isMulCommutative _ hInv hcop'] at hv'
  obtain ⟨c,hc,rfl⟩ := hv'
  apply (QuotientGroup.eq_one_iff c).mpr
  apply hfix
  refine ⟨c.property,?_⟩
  intro d hd
  have he := congrArg Subtype.val (hc (⟨d,hd⟩ : D))
  change d*(c : X)*d⁻¹ = c at he
  exact mul_inv_eq_iff_eq_mul.mp he

/-- The selected torus has no nonidentity fixed coset on the literal C/W with its original endpoint action. -/
theorem source_suzuki_selected_torus_quotient_fixed
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb3 : b (reducedFamily L S) = 3)
    {a x σ : Vertex (reducedFamily L S)}
    (hxadj : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x)
    (hne : x ≠ base (reducedFamily L S) (!i))
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k)
    (hz : center (star L S i) = ⊥)
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzx : Z (reducedFamily L S) x ≤ Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hcommx : ⁅V (reducedFamily L S) x 1, Q (reducedFamily L S) x⁆ ≤ Z (reducedFamily L S) x)
    (hcommy : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ =
        Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcross : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) σ,
      V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥)
    (hsmall : (Q (reducedFamily L S) σ).relIndex
      (V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1) ≤ Nat.card k)
    (hactor : (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex
      (V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (hfield : Nat.card k = 2 ^ (2 * n + 1))
    (Ry : Sylow 2 (star L S (!i)))
    (hRy : (Ry : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) (!i)))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i))
    (hnat : Noncommuting.HasNaturalCenter (star L S i)
      (Z (reducedFamily L S) (base (reducedFamily L S) i))
      (Q (reducedFamily L S) (base (reducedFamily L S) i)))
    (hbranch : ⁅V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥)
    (hnear : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) x,
      V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥) :
    let F := reducedFamily L S
    let m := base F i
    let B := stabilizer F (base F (!i)) ⊓ stabilizer F m
    let A := star L S i
    let C := Q F m ⊓ centralizer (ballKernel F m 3 : Set (G₀ L S))
    let W := conjugateSpanBy (V F (base F (!i)) 1 ⊓ Q F x) (stabilizer F m)
    ∃ K : Subgroup B, (pCore 2 B).IsComplement' K ∧ Odd (Nat.card K) ∧
      K.map B.subtype ≤ stabilizer F x ∧
      let D := K.map B.subtype ⊓ A
      D ≠ ⊥ ∧ Odd (Nat.card D) ∧
      Q F m ⊓ centralizer (D : Set (G₀ L S)) ≤ ballKernel F m 3 ∧
      Nat.card (Q F m ⊓ centralizer (D : Set (G₀ L S)) : Subgroup (G₀ L S)) = Nat.card k ∧
      ∃ hAC : A ≤ normalizer (C : Set (G₀ L S)),
      ∃ hW : (W.subgroupOf C).Normal,
        let _ := hW
        W ≤ C ∧ IsElementaryAbelian 2 (C ⧸ W.subgroupOf C) ∧
        ∃ ρ : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) →*
          MulAut (C ⧸ W.subgroupOf C),
          (∀ t : A, ∀ c : C,
            ρ ((originalQuotient h i).symm (QuotientGroup.mk t)) (QuotientGroup.mk c) =
              QuotientGroup.mk ⟨(t : G₀ L S)*c*(t : G₀ L S)⁻¹,
                (mem_normalizer_iff.mp (hAC t.property) c).mp c.property⟩) ∧
          ∀ v : C ⧸ W.subgroupOf C,
            (∀ d : D, ρ ((originalQuotient h i).symm
              (QuotientGroup.mk (⟨(d : G₀ L S),d.property.2⟩ : A))) v = v) → v = 1 := by
  let F := reducedFamily L S
  let m := base F i
  let A := star L S i
  let B := stabilizer F (base F (!i)) ⊓ stabilizer F m
  let H := ballKernel F m 3
  let C := Q F m ⊓ centralizer (H : Set (G₀ L S))
  let W := conjugateSpanBy (V F (base F (!i)) 1 ⊓ Q F x) (stabilizer F m)
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite C := Finite.of_injective (inclusion
    (show C ≤ stabilizer F m from inf_le_left.trans (Q_le_stabilizer F m))) (inclusion_injective _)
  obtain ⟨K,hK,ho,hKx,hDne,hDo,hJH,hJeq,hJsize,_,_,_⟩ := source_suzuki_selected_torus_centralizer
    h i hb3 hxadj hne T R hT hR e hz hcard hcardy hzx hzy hcommx hcommy
    hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear
  let D := K.map B.subtype ⊓ A
  have hDA : D ≤ A := inf_le_right
  let : Finite D := Finite.of_injective (inclusion (hDA.trans (star_le_stabilizer i))) (inclusion_injective _)
  have hb : 2 < b F := by change 2 < b (reducedFamily L S); omega
  obtain ⟨hWel,hW2,_,hnW,_,_,_,_,_⟩ :=
    source_linear_second_kernel_span h i hb hxadj hne T hT e hcommy.le hnear
  let : IsElementaryAbelian 2 W := hWel
  have hAW : A ≤ normalizer (W : Set (G₀ L S)) := (star_le_stabilizer i).trans hnW
  obtain ⟨hAC,hW,hWC,hCE,_,_⟩ := source_suzuki_centralizer_span_action h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear
  let _ := hW
  let : Finite W := Finite.of_injective (inclusion hWC) (inclusion_injective _)
  let : IsElementaryAbelian 2 (W.subgroupOf C) :=
    IsElementaryAbelian.of_injective (subgroupOfEquivOfLe hWC).toMonoidHom (subgroupOfEquivOfLe hWC).injective
  obtain ⟨α,hα⟩ := exists_quotient_conjugation_action A C W hAC hAW hW
  have hCQ := (source_suzuki_centralizer_span_frattini h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear).2.1
  have hkill := quotient_conjugation_action_kills_commutator_layer A C W (Q F m) hW hAC hCQ α hα
  have hk : pCore 2 A ≤ α.ker := by
    intro t ht
    apply hkill
    change (t : G₀ L S) ∈ Q F m
    rw [←star_core h i]
    exact mem_map_of_mem A.subtype ht
  let β := QuotientGroup.lift (pCore 2 A) α hk
  let ρ := β.comp (originalQuotient h i).toMonoidHom
  have hρ (t : A) : ρ ((originalQuotient h i).symm (QuotientGroup.mk t)) = α t := by
    change β ((originalQuotient h i) ((originalQuotient h i).symm (QuotientGroup.mk t))) = _
    rw [(originalQuotient h i).apply_symm_apply]
    rfl
  have hWfix := (source_suzuki_odd_span_centralizer h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear
    D hDA hDo hDne).1
  have hfix : C ⊓ centralizer (D : Set (G₀ L S)) ≤ W := by
    have he : Q F m ⊓ centralizer (D : Set (G₀ L S)) = W ⊓ centralizer (D : Set (G₀ L S)) :=
      hJeq.trans hWfix.symm
    exact (inf_le_inf_right _ (show C ≤ Q F m from inf_le_left)).trans (he.le.trans inf_le_left)
  have hcop : Nat.Coprime (Nat.card D) (Nat.card W) := by
    obtain ⟨j,hj⟩ := (IsElementaryAbelian.isPGroup 2 W).exists_card_eq
    rw [hj]
    exact hDo.coprime_two_right.pow_right j
  refine ⟨K,hK,ho,hKx,hDne,hDo,hJH,hJsize,hAC,hW,hWC,hCE,ρ,?_,?_⟩
  · intro t c
    rw [hρ]
    exact hα t c
  · intro v hv
    apply quotient_fixed_eq_one C W D hWC hW (hDA.trans hAC) (hDA.trans hAW) hcop hfix
      (α.comp (inclusion hDA)) (fun d c => hα (inclusion hDA d) c) v
    intro d
    have hh := hv d
    rw [hρ] at hh
    exact hh
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer

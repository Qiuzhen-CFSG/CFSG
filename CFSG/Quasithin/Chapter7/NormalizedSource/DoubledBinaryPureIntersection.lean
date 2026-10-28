module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureOddCore
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryInnerAction
import all CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlanes

/-!
# The source pure-line intersection and its paired-plane actor

The pure-line fixer factors through the original component whenever its
marked action is inner. This supplies the missing factorization in source
7.7.5 at H1, where the overgroup centralizes only the line.

Each pure line lies in a paired plane of the same natural–dual marking.
The plane residual moves an elementary subgroup of order sixteen inside
the full pure-line residual movement. This subgroup acts inner on every
ordinary component of the same line overgroup. Adding the line gives the
source hyperplane of order thirty-two. Faithfulness still requires the
rank-three kernel exclusion; it is not inferred from innerness.

The actual chosen-module applications, including the two-central fixed-point
exclusion, are in NonFFSourceDoubledBinaryPureIntersection.
Source: Aschbacher–Smith 7.7.5 and the H1 argument on printed pp.704–706,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureIntersection
open ChapterE BinaryLinearThree NaturalDual DoubledBinaryPlanes DoubledBinaryLocalCore
open DoubledBinaryIntersection DoubledBinaryOddCore DoubledBinaryInnerAction
variable {G : Type*} [_root_.Group G]

/-- A point fixer with inner marked action factors through its original component. -/
theorem factor_of_inner_action
    (W₀ L Z B M : Subgroup G) [IsElementaryAbelian 2 W₀]
    (hZW : Z ≤ W₀) (hLN : L ≤ normalizer (W₀ : Set G))
    (hMN : M ≤ normalizer (W₀ : Set G))
    (q : L →* Group) (hq : Function.Surjective q)
    (a : Automizer W₀ ≃* MulAut Group)
    (ha : ∀ l, a (W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) = MulAut.conj (q l))
    (hi : ∀ n : normalizer (W₀ : Set G), (n : G) ∈ centralizer (Z : Set G) →
      a (W₀.normalizerMonoidHom.rangeRestrict n) ∈ MulAut.innerSubgroup Group)
    (hLB : L ⊓ centralizer (Z : Set G) ≤ B) :
    ∀ m ∈ M ⊓ centralizer (Z : Set G),
      ∃ b ∈ B, ∃ c ∈ centralizer (W₀ : Set G), m = b * c := by
  intro m hm
  let n : normalizer (W₀ : Set G) := ⟨m,hMN hm.1⟩
  obtain ⟨g,hg⟩ := hi n hm.2
  obtain ⟨l,hl⟩ := hq g
  have he : W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l) =
      W₀.normalizerMonoidHom.rangeRestrict n := by
    apply a.injective
    rw [ha,hl]
    exact hg
  have hlZ : (l : G) ∈ centralizer (Z : Set G) := by
    intro z hz
    let w : W₀ := ⟨z,hZW hz⟩
    have hh := congrArg (fun b : Automizer W₀ => ((b.val w : W₀) : G)) he
    change (l : G) * z * (l : G)⁻¹ = m * z * m⁻¹ at hh
    rw [← hm.2 z hz,mul_inv_cancel_right] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  let c := (inclusion hLN l)⁻¹ * n
  have hc : (c : G) ∈ centralizer (W₀ : Set G) := by
    have hh : W₀.normalizerMonoidHom c = 1 := by
      change W₀.normalizerMonoidHom ((inclusion hLN l)⁻¹ * n) = 1
      have hh : W₀.normalizerMonoidHom (inclusion hLN l) = W₀.normalizerMonoidHom n :=
        congrArg Subtype.val he
      rw [map_mul,map_inv,hh,inv_mul_cancel]
    change c ∈ W₀.normalizerMonoidHom.ker at hh
    rw [normalizerMonoidHom_ker] at hh
    exact hh
  exact ⟨l,hLB ⟨l.property,hlZ⟩,c,hc,by change m = (l : G) * ((l : G)⁻¹ * m); group⟩

/-- Every line in either marked factor lies in an actual paired plane. -/
theorem exists_pairedPlane_over_pureLine [Finite G]
    (W₀ Z : Subgroup G) [IsElementaryAbelian 2 W₀]
    (E : Additive W₀ ≃ₗ[ZMod 2] Space) (hZW : Z ≤ W₀) (hZ : Nat.card Z = 2)
    (hpure : (∀ w : Additive W₀, (w.toMul : G) ∈ Z → (E w).2 = 0) ∨
      (∀ w : Additive W₀, (w.toMul : G) ∈ Z → (E w).1 = 0)) :
    ∃ v : Vector, ∃ f : Module.Dual (ZMod 2) Vector, f v = 1 ∧
      Z ≤ ambientPlane W₀ E v f := by
  obtain ⟨z,hz,hall⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hZ
  let w : Additive W₀ := Additive.ofMul ⟨z,hZW z.property⟩
  have hn : E w ≠ 0 := by
    intro he
    have hh := E.map_eq_zero_iff.mp he
    exact hz (Subtype.ext (congrArg (fun a : Additive W₀ => (a.toMul : G)) hh))
  have lift (v : Vector) (f : Module.Dual (ZMod 2) Vector)
      (hw : E w ∈ pairedPlane v f) : Z ≤ ambientPlane W₀ E v f := by
    have hzU : (z : G) ∈ ambientPlane W₀ E v f := ⟨w.toMul,hw,rfl⟩
    intro x hx
    by_cases he : (⟨x,hx⟩ : Z) = 1
    · have he' : x = 1 := congrArg Subtype.val he
      exact he'.symm ▸ (ambientPlane W₀ E v f).one_mem
    · have he' : x = z := congrArg Subtype.val (hall ⟨x,hx⟩ he)
      exact he'.symm ▸ hzU
  rcases hpure with hnatur | hdual
  · have h2 := hnatur w z.property
    have h1 : (E w).1 ≠ 0 := fun hh => hn (Prod.ext hh h2)
    obtain ⟨f,hf⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) h1
    refine ⟨(E w).1,f,hf,lift _ _ ?_⟩
    rw [← show ((E w).1,0) = E w from Prod.ext rfl h2.symm]
    exact Submodule.subset_span (by simp)
  · have h1 := hdual w z.property
    have h2 : (E w).2 ≠ 0 := fun hh => hn (Prod.ext h1 hh)
    obtain ⟨v,hv⟩ : ∃ v, (E w).2 v ≠ 0 := by
      by_contra he
      push Not at he
      exact h2 (LinearMap.ext he)
    have hv1 : (E w).2 v = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) _ hv
    refine ⟨v,(E w).2,hv1,lift _ _ ?_⟩
    rw [← show (0,(E w).2) = E w from Prod.ext h1.symm rfl]
    exact Submodule.subset_span (by simp)

/-- Adding the actual pure line to the plane movement gives the source hyperplane. -/
theorem pureLine_movement_corank [Finite G]
    (W₀ Z U A : Subgroup G) [IsElementaryAbelian 2 W₀]
    (hZW : Z ≤ W₀) (hZU : Z ≤ U) (hAW : A ≤ W₀)
    (hZ : Nat.card Z = 2) (hA : Nat.card A = 16)
    (hW : Nat.card W₀ = 64) (hdis : Disjoint U A) :
    Nat.card (Z ⊔ A : Subgroup G) = 32 ∧ subgroupCorank W₀ (Z ⊔ A) = 1 := by
  have hn : A ≤ normalizer (Z : Set G) := hAW.trans
    (((le_centralizer W₀).trans (centralizer_le hZW)).trans
      (Subgroup.centralizer_le_normalizer _))
  have hc := card_sup_eq_mul_of_normalizes_of_disjoint Z A hn (hdis.mono_left hZU)
  rw [hZ,hA] at hc
  have hi := relIndex_mul_relIndex (⊥ : Subgroup G) (Z ⊔ A) W₀ bot_le (sup_le hZW hAW)
  simp only [relIndex_bot_left,hW,hc] at hi
  have he : (Z ⊔ A).relIndex W₀ = 2 := by omega
  exact ⟨hc,by change Nat.log 2 _ = 1; rw [he]; decide⟩

/-- The rank-four plane movement is the literal subgroup in the same line overgroup. -/
theorem pairedPlane_component_inner [Finite G]
    (W₀ L Z H K : Subgroup G) [IsElementaryAbelian 2 W₀]
    (hLN : L ≤ normalizer (W₀ : Set G))
    (q : L →* Group) (hq : Function.Surjective q)
    (E : Additive W₀ ≃ₗ[ZMod 2] Space)
    (hE : ∀ l w, E (automizerRepresentation W₀
      (W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) w) = action (q l) (E w))
    (v : Vector) (f : Module.Dual (ZMod 2) Vector) (hfv : f v = 1)
    (hZU : Z ≤ ambientPlane W₀ E v f)
    (hWH : W₀ ≤ H) (hRH : localResidual L Z ≤ H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (hK : IsComponentIn K H) :
    let U := ambientPlane W₀ E v f
    let A := ⁅W₀,localResidual L U⁆
    Disjoint U A ∧ Nat.card A = 16 ∧
      A ≤ ⁅W₀,localResidual L Z⁆ ∧
      ∃ hAN : A ≤ normalizer (K : Set G),
        ∀ a : A, K.normalizerMonoidHom (inclusion hAN a) ∈ MulAut.innerSubgroup K := by
  let U := ambientPlane W₀ E v f
  have hR : localResidual L U ≤ localResidual L Z :=
    embedded_pResidual_mono 2 (inf_le_inf_left L (centralizer_le hZU))
  refine ⟨pairedPlane_residual_disjoint W₀ L hLN q E hE v f hfv,
    pairedPlane_residual_card W₀ L hLN q E hE v f hfv
      (pairedPlane_residual_supplement W₀ L hLN q hq E hE v f hfv),
    commutator_mono le_rfl hR,?_⟩
  exact component_movement_inner H W₀ (localResidual L U) K hH hK hWH (hR.trans hRH)
    (IsElementaryAbelian.isPGroup 2 W₀)
    (isPPerfect_embedded_pResidual 2 (L ⊓ centralizer (U : Set G)))
    ((map_subtype_le _).trans (inf_le_left.trans hLN))

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureIntersection

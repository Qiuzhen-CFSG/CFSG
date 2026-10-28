module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FiveParabolics.DiagramAction.Core
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FiveParabolics.DiagramAction.Model
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FiveParabolics.DiagramAction.Action

/-!
# Trivial diagram action from the actual product quotient

Write X = Y₊(S ∩ L) and H = Y₊S. The marked image of X is a solvable
Sylow overgroup with three-part nine, so it is the flag deleting two
nonadjacent nodes and has intrinsic core quotient S₃ × S₃. The map
from X to this image has two-group kernel. Thus X/O₂(X) and the given
H/O₂(H) both have order 36.

Consequently X surjects onto H/O₂(H). For each s ∈ S choose v ∈ X with
the same image there. Every displacement of v⁻¹s on X lies in O₂(X).
In the marked linear group these displacements lie in the two-core of
the base flag, hence in either of its minimal parabolics. The adjusted
automorphism preserves that actual minimal parabolic. The graph theorem
in dimension five forces it to be inner, so the original action of s is
inner as well. The action formula retains the original quotient marking.

The allowed E₉ quotient of Y₊ is not additionally needed once solvability
and the three-part of the base image are supplied. No node fixation,
parabolic normalization or outside-parabolic witness is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.24, printed pp.1129–1130 (PDF pp.1146–1147), refs/quasithin.pdf.
-/

@[expose] public section
open Subgroup BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FiveParabolics
open DiagramAction

private instance : Finite (LinearGroup 5) :=
  Finite.of_injective (fun g : LinearGroup 5 => (g : Space 5 → Space 5)) DFunLike.coe_injective

variable {G : Type*} [Group G] [Finite G]

/-- The genuine product quotient forces each element of S to act by an
inner automorphism of the marked L₅(2) quotient. The remaining inputs are
precisely the Sylow/component and solvable-base source preparation. -/
theorem isInnerOnModel_of_product_quotient (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (e : (c.L ⧸ pCore 2 c.L) ≃* Projective 5)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hYL : d.Yplus ≤ c.L)
    (hθ : c.L = theta I)
    (hH : Nonempty (((d.Yplus ⊔ d.S : Subgroup G) ⧸ pCore 2 (d.Yplus ⊔ d.S : Subgroup G)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (hsol : Group.IsSolvable (baseImage d e))
    (h3 : (Nat.card (baseImage d e)).factorization 3 = 2) :
    IsInnerOnModel e d.S
      ((Chapter1.isSylowIn_iff.mp hS).2.1.trans (normalizes_of_eq_theta hθ)) := by
  let q := linearAction (by decide) e
  let X := d.Yplus ⊔ (d.S ⊓ c.L)
  have hXL : X ≤ c.L := sup_le hYL inf_le_right
  have hXH : X ≤ d.Yplus ⊔ d.S := sup_le_sup_left inf_le_left _
  have hnL : d.S ≤ normalizer (c.L : Set G) :=
    (Chapter1.isSylowIn_iff.mp hS).2.1.trans (normalizes_of_eq_theta hθ)
  have hnY : d.S ≤ normalizer (d.Yplus : Set G) :=
    le_sup_right.trans (OutsideStructure.LocalBranches.ys_normalizes_yplus d)
  have hnD : d.S ≤ normalizer ((d.S ⊓ c.L : Subgroup G) : Set G) := by
    apply le_normalizer_iff.mpr
    intro s hs x hx
    exact ⟨(d.S.le_normalizer hs x).mp hx.1, (hnL hs x).mp hx.2⟩
  have hnX : d.S ≤ normalizer (X : Set G) :=
    (le_inf hnY hnD).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  obtain ⟨T, hT⟩ := sylow_intersection_of_eq_theta d hS hθ
  have hT' : (T : Subgroup c.L) = (d.S ⊓ c.L).subgroupOf c.L := by
    rw [← hT]
    exact (comap_map_eq_self_of_injective c.L.subtype_injective _).symm
  let U := T.mapSurjective (f := q) (linearAction_surjective (by decide) e)
  have hU : (U : Subgroup (LinearGroup 5)) =
      ((d.S ⊓ c.L).subgroupOf c.L).map q := by
    change (T : Subgroup c.L).map q = _
    rw [hT']
  have hUB : (U : Subgroup (LinearGroup 5)) ≤ baseImage d e := by
    rw [hU]
    exact map_mono (subgroupOf_mono c.L le_sup_right)
  obtain ⟨b, i, j, hij, hgap, hflag, hbase, hcard, hPB, hcoreP⟩ :=
    solvable_base_marking U (baseImage d e) hUB hsol h3
  have hcardX : Nat.card (X ⧸ pCore 2 X) = 36 :=
    (Nat.card_congr (subgroupImageCoreEquiv e hXL).toEquiv).trans hcard
  obtain ⟨eH⟩ := hH
  have hcardH : Nat.card ((d.Yplus ⊔ d.S : Subgroup G) ⧸
      pCore 2 (d.Yplus ⊔ d.S : Subgroup G)) = 36 := by
    rw [Nat.card_congr eH.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  let f : X →* baseImage d e := subgroupImageMap e hXL
  have hf : Function.Surjective f := subgroupImageMap_surjective e hXL
  have hcore : (pCore 2 X).map f ≤ pCore 2 (baseImage d e) :=
    le_sSup ⟨Subgroup.Normal.map inferInstance f hf, pCore_isPGroup.map f⟩
  intro s
  obtain ⟨v, hv⟩ := core_adjustment hXH (hcardX.trans hcardH.symm) s.val
    ((le_sup_right : d.S ≤ d.Yplus ⊔ d.S) s.property) (hnX s.property)
  let a := modelNormalizerAction e (inclusion hnL s)
  let g : LinearGroup 5 := (f v).val
  let a' := MulAut.conj g⁻¹ * a
  have ha' : a' ∈ MulAut.innerSubgroup _ := by
    apply inner_of_minimal_displacement b i a'
    intro z hz
    obtain ⟨y, hy⟩ := hf ⟨z, hPB hz⟩
    let r : X →* LinearGroup 5 := (baseImage d e).subtype.comp f
    have hy' : r y = z := congrArg Subtype.val hy
    have hact : r (X.normalizerMonoidHom ⟨s.val, hnX s.property⟩ y) = a (r y) :=
      (modelNormalizerAction_subgroupImage e hXL s.val (hnL s.property)
        (hnX s.property) y).symm
    let t : X := v⁻¹ * X.normalizerMonoidHom ⟨s.val, hnX s.property⟩ y * v * y⁻¹
    have ht : t ∈ pCore 2 X := hv y
    have hm : r t ∈ (baseImage d e).pCoreIn 2 :=
      mem_map_of_mem (baseImage d e).subtype (hcore (mem_map.mpr ⟨t, ht, rfl⟩))
    have he : r t = a' z * z⁻¹ := by
      change r (v⁻¹ * X.normalizerMonoidHom ⟨s.val, hnX s.property⟩ y * v * y⁻¹) =
        g⁻¹ * a z * g * z⁻¹
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hact, hy']
      rfl
    rw [← he]
    exact hcoreP hm
  have hea : MulAut.conj g * a' = a := by
    simp only [a', ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have ha : a ∈ MulAut.innerSubgroup _ := by
    rw [← hea]
    exact (MulAut.innerSubgroup _).mul_mem ⟨g, rfl⟩ ha'
  obtain ⟨k, hk⟩ := ha
  refine ⟨k, fun l => ?_⟩
  rw [← modelNormalizerAction_apply e (inclusion hnL s) l]
  change a (q l) = k * q l * k⁻¹
  rw [← hk]
  rfl

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FiveParabolics
end

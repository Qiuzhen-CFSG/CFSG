module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.SmallNormal
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic.ResidualInverter
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.WreathOuter
public import Theory.GroupTheory.PPerfectHom
/-!
# Excluding an order-nine residual in the solvable small-automizer source

The original witness supplies a normal quaternion central product P. Its
conjugate-span identity gives P = O₂(H) ∩ O²(H) and [P,O²(H)] = P.
The literal orthogonal action cannot kill O²(H): its remaining action would
be inner, hence a two-group image of a two-perfect group, and would centralize P.
When the maximal core equals O₂(H), the normal-subgroup dichotomy therefore
places the action kernel inside O₂(H). Its residual image has the exact order
of O²(H/O₂(H)), contradicting the source inverter when that order is nine.

Source: Aschbacher–Smith E.2.17, printed pp.229–230. The source consumer
constructs the witness, normal core and order-two V-image internally. The
primitive quotient and its order-nine residual remain literal source premises.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
variable {H : Type*} [Group H] [Finite H]
private theorem residual_wreath_image_card
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hJ : ChapterB.minimalParabolicCore T hP = pCore 2 H)
    (P : Subgroup H) [P.Normal] (d : QuaternionCentralProductData P)
    (hPQ : P = pCore 2 H ⊓ pResidual 2 H)
    (hmove : ⁅P,pResidual 2 H⁆ = P) :
    Nat.card ((pResidual 2 H).map (d.quotientWreathAction.comp MulAut.conjNormal)) =
      Nat.card (pResidual 2 (H ⧸ pCore 2 H)) := by
  let a : H →* MulAut P := MulAut.conjNormal
  let f := d.quotientWreathAction.comp a
  have hPk : P ≤ f.ker := by
    intro x hx
    change a x ∈ d.quotientWreathAction.ker
    rw [d.quotientWreathAction_ker]
    exact ⟨⟨x,hx⟩,by ext y; rfl⟩
  have hn : ¬ pResidual 2 H ≤ f.ker := by
    intro hR
    have him : ∀x : pResidual 2 H, (a.comp (pResidual 2 H).subtype) x ∈ MulAut.innerSubgroup P := by
      intro x
      rw [←d.quotientWreathAction_ker]
      exact hR x.property
    let g := (a.comp (pResidual 2 H).subtype).codRestrict (MulAut.innerSubgroup P) him
    have hp : IsPGroup 2 P := IsPGroup.of_card (n:=5) (by rw [d.card]; norm_num)
    have hpI : IsPGroup 2 (MulAut.innerSubgroup P) :=
      hp.of_surjective (MulAut.conj : P →* MulAut P).rangeRestrict
        (MulAut.conj : P →* MulAut P).rangeRestrict_surjective
    have hg := (isPPerfect_pResidual 2 (G:=H)).hom_eq_one_of_isPGroup hpI g
    have hcent : pResidual 2 H ≤ centralizer (P : Set H) := by
      intro x hx y hy
      have hh : g (⟨x,hx⟩ : pResidual 2 H)=1 := DFunLike.congr_fun hg _
      have hauto : a x=1 := congrArg Subtype.val hh
      have he := congrArg (fun b : MulAut P => (b ⟨y,hy⟩ : H)) hauto
      change x*y*x⁻¹=y at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    have hbot : P=⊥ := by
      rw [←hmove,commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.mpr hcent
    have hc := d.card
    rw [hbot,card_bot] at hc
    omega
  have hkQ : f.ker ≤ pCore 2 H := by
    rw [←hJ]
    exact (ChapterB.minimalParabolic_normal_subgroup_residual_dichotomy T hP f.ker).resolve_right hn
  have hkR : f.ker.subgroupOf (pResidual 2 H) =
      (pCore 2 H).subgroupOf (pResidual 2 H) := by
    ext x
    exact ⟨fun hx => hkQ hx,fun hx => hPk (hPQ ▸ ⟨hx,x.property⟩)⟩
  rw [←relIndex_ker]
  change Nat.card ((pResidual 2 H) ⧸ f.ker.subgroupOf (pResidual 2 H)) = _
  rw [hkR]
  exact Nat.card_congr (pResidualQuotientEquiv 2 (pCore 2 H)).toEquiv
variable {D : Type*} [Group D] [Finite D]
  {V U : Subgroup H} [IsElementaryAbelian 2 V]
/-- The original solvable small-automizer configuration cannot have primitive
residual quotient of order nine. -/
theorem source_solvable_small_residual_nine_false
    {κ : GroupClass} (hH : IsSQTK κ H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : Group.IsSolvable H)
    (hVT : V ≤ T) (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVM : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP)
    (hfit : generalizedFitting H = pCore 2 H) (hV : Nat.card V = 16)
    (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H))
    (q : U →* D) (hq : Function.Surjective q)
    (hk : q.ker = (centralizer (V : Set H)).subgroupOf U)
    (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio (DihedralCubic.representation U V hU q hq hk))
    (hres : (pResidual 2 (ChapterB.minimalParabolicMax T hP)).map
      (ChapterB.minimalParabolicMax T hP).subtype ≤ centralizer (V : Set H))
    (hJ : ChapterB.minimalParabolicCore T hP = pCore 2 H)
    (h9 : Nat.card (pResidual 2 (H ⧸ pCore 2 H)) = 9) : False := by
  obtain ⟨w₀⟩ := Solvable.solvable_witness T hP hs V hVT hvn hVM hout
  let w : OriginalWitness T (ChapterB.minimalParabolicMax T hP) V 1 :=
    OriginalWitness.of_dihedral w₀
  have hTV := (normal_subgroupOf_iff_le_normalizer hVT).mp hvn
  let P := w.pair.subgroup.pCoreIn 2
  obtain ⟨hPn,_,⟨d⟩,_⟩ := w.small_normal_core_of_solvable hH hP hs
    hVT hTV hVM hout hfit hV hTU hU q hq hk hD hratio hres
  let : P.Normal := hPn
  have hplace := w.small_core_placement_of_solvable hH hP hs hVT hTV hVM hout
    hfit hV hTU hU q hq hk hD hratio
  have hspan := w.small_span_residual_of_solvable hH hP hs hVT hTV hVM hout
    hfit hV hTU hU q hq hk hD hratio
  rw [←hplace.2] at hspan
  change P ≤ conjugateSpanBy (P ⊓ V) ⊤ ∧
    conjugateSpanBy (P ⊓ V) ⊤ = pCore 2 H ⊓ pResidual 2 H ∧
    ⁅conjugateSpanBy (P ⊓ V) ⊤,pResidual 2 H⁆ = conjugateSpanBy (P ⊓ V) ⊤ at hspan
  have hPL : P = conjugateSpanBy (P ⊓ V) ⊤ := le_antisymm hspan.1
    (conjugateSpanBy_le inf_le_left le_normalizer_of_normal)
  have hPQ : P = pCore 2 H ⊓ pResidual 2 H := hPL.trans hspan.2.1
  have hmove : ⁅P,pResidual 2 H⁆=P := by simpa only [←hPL] using hspan.2.2
  have hcard := w.small_module_image_card_of_solvable hH hP hs hVT hTV hVM hout
    hfit hV hTU hU q hq hk hD hratio
  have hne := DihedralCubic.source_residual_image_ne_nine_of_two_actor_image
    T hP hs P V d hVT hvn hcard
  exact hne ((residual_wreath_image_card T hP hJ P d hPQ hmove).trans h9)

end CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement

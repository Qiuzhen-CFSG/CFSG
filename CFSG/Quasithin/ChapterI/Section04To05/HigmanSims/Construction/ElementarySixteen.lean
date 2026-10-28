module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PlaneMatrices
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PlaneLiftCorrection
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.ElementaryPlaneJoin

/-!
# An actual elementary sixteen in an original HS plane centralizer

The original point cores supply three involutory lifts of the two binary
plane shears and their product. The distinct-point square calculation and
the determinant-one action on C₄³ allow a core correction making the first
two lifts commute. Their actions remain the two independent shears. Adjoining
them to the fixed plane therefore gives an elementary subgroup of order
sixteen, meeting the whole normalizer core in precisely that plane.

All data are constructed from the original HS1--HS2 hypotheses of I.4.8.
In particular, no splitting, elementary-sixteen existence, endpoint marking
or ambient recognition is assumed. The plane centralizer is kept distinct
from the point-overlap two-core, which also has order256.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
open BinaryPlane
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- Original HS local data construct a literal elementary sixteen inside a
full seed-plane centralizer, with its full-core intersection retained. -/
theorem TypeAt.exists_elementary_sixteen_in_plane_centralizer (h : TypeAt z V) :
    ∃ W A : Subgroup G, W ≤ V ∧ Nat.card W = 4 ∧
      IsElementaryAbelian 2 A ∧ Nat.card A = 16 ∧
      W ≤ A ∧ A ≤ centralizer (W : Set G) ∧
      A ⊓ (normalizer (V : Set G)).pCoreIn 2 = W := by
  let M := normalizer (V : Set G)
  let P := pCore 2 M
  let e : P ≃* Multiplicative (Fin 3 → ZMod 4) :=
    (MulEquiv.subgroupCongr h.normalizer_fitting.symm).trans
      (h.normalizer_core.some.trans (MulEquiv.funMultiplicative (Fin 3) (ZMod 4)).symm)
  let c := h.seedCoordinates e
  let W := planeAt c
  have hWV : W ≤ V := planeAt_le c
  have hWM : W ≤ M := hWV.trans V.le_normalizer
  have hW4 : Nat.card W = 4 := planeAt_card c
  let : IsElementaryAbelian 2 W := planeAt_elementary c
  obtain ⟨d⟩ := h.exists_binary_plane_lifts c
  obtain ⟨p, hp2, hpb, _⟩ := h.correct_plane_lifts e d.a d.b d.t d.a_square d.b_square
    d.t_square d.commutator_core d.commutator_square d.product_core
    (h.first_plane_matrix_reduction e d.a d.a_action)
    (h.second_plane_matrix_reduction e d.b d.b_action)
  let a : M := (p : M) * d.a
  let f := V.normalizerMonoidHom
  have hker : f.ker = P := by
    rw [normalizerMonoidHom_ker, h.seed_centralizer]
    exact comap_map_eq_self_of_injective M.subtype_injective P
  have hpker : f (p : M) = 1 := by
    change (p : M) ∈ f.ker
    rw [hker]
    exact p.property
  have haf : f a = alphaAt c := by
    rw [show f a = f (p : M) * f d.a from f.map_mul _ _, hpker, one_mul]
    exact d.a_action
  have hbf : f d.b = betaAt c := d.b_action
  have hpC : ((p : M) : G) ∈ centralizer (W : Set G) := by
    apply centralizer_le hWV
    rw [h.seed_centralizer]
    exact ⟨p, p.property, rfl⟩
  have haC : (a : G) ∈ centralizer (W : Set G) :=
    (centralizer (W : Set G)).mul_mem hpC d.a_plane
  let WM := W.subgroupOf M
  have hWM4 : Nat.card WM = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hWM).toEquiv).trans hW4
  let : IsElementaryAbelian 2 WM := IsElementaryAbelian.subgroupOf hWM
  have hWK : WM ≤ f.ker := by
    intro w hw
    rw [normalizerMonoidHom_ker]
    intro v hv
    let := h.elementary
    exact setLike_mul_comm hv (hWV hw)
  have hfa : f a ≠ 1 := by
    rw [haf]
    exact alphaAt_ne_one c
  have hfb : f d.b ≠ 1 := by
    rw [hbf]
    exact betaAt_ne_one c
  have hfab : f a ≠ f d.b := by
    rw [haf, hbf]
    exact alphaAt_ne_betaAt c
  have haWM : a ∈ centralizer (WM : Set M) := by
    intro w hw
    exact Subtype.ext (haC w hw)
  have hbWM : d.b ∈ centralizer (WM : Set M) := by
    intro w hw
    exact Subtype.ext (d.b_plane w hw)
  obtain ⟨hAE, hA16, hAK⟩ := elementary_plane_join f WM hWM4 hWK a d.b hp2
    d.b_square hpb haWM hbWM hfa hfb hfab
  let AM := WM ⊔ (zpowers a ⊔ zpowers d.b)
  let A := AM.map M.subtype
  let : IsElementaryAbelian 2 AM := hAE
  have hAelem : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hAc : Nat.card A = 16 := by
    rw [card_map_of_injective M.subtype_injective]
    exact hA16
  have hWmap : WM.map M.subtype = W := map_subgroupOf_eq_of_le hWM
  have hWA : W ≤ A := hWmap ▸ map_mono (show WM ≤ AM from le_sup_left)
  have hAC : A ≤ centralizer (W : Set G) := by
    change (WM ⊔ (zpowers a ⊔ zpowers d.b)).map M.subtype ≤ _
    rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers,
      MonoidHom.map_zpowers, hWmap]
    refine sup_le ?_ (sup_le (zpowers_le.mpr haC) (zpowers_le.mpr d.b_plane))
    exact le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hAP : A ⊓ M.pCoreIn 2 = W := by
    change AM.map M.subtype ⊓ P.map M.subtype = W
    rw [← map_inf _ _ _ M.subtype_injective, ← hker, hAK, hWmap]
  exact ⟨W, A, hWV, hW4, hAelem, hAc, hWA, hAC, hAP⟩

end CFSG.Quasithin.HigmanSims

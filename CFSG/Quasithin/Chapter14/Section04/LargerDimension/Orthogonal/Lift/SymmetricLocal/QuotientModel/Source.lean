module
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.SymmetricLocal.QuotientModel
public import Theory.Representation.OrthogonalFourPlusMatrix.QuotientLocal.ComponentAction
/-!
# Source component inputs for the orthogonal quotient calculations

The input retains the actual normal PΩ₄⁺(4) component square as F*(H/U),
the selected involution's component-exchanging action, and the literal image
of K₀=O²(C_H(i)) as its fixed subgroup. An arbitrary involutive exchange is
straightened on group coordinates while preserving i. The checked orthogonal
carrier comparison and generalized-Fitting centralizer theorem supply a
faithful action, whose fixed component image is the inner diagonal A₅.

The diagonal sandwich theorem then proves both quotient-core bounds and
applies them to the two actual Core contracts. The Sylow definitions at the
end preserve exactly the image of the original T and membership of i*.
`QuotientModel.QuotientSylow` proves that its centralizer intersection is Sylow;
`QuotientModel.LocalSylow` applies that calculation to the literal local witness.

The earlier configuration and selected residual-image equality belong to the
Selection owner. No ordinary-centralizer surjectivity is assumed; the separate
centralizer modulo ⟨z⟩ comparison remains the input of LocalSylow.

Source: Aschbacher–Smith, G.11.2(7), 14.4.2(3), printed pp.1006–1007,
and Lemma 14.4.9, printed p.1010.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.QuotientModel
open Subgroup Theory.GroupTheory ClassicalOrthogonal.FourPlusMatrix
open ClassicalOrthogonal.FourPlusMatrix.QuotientLocal

/-- The selected group-component outputs of case (3). The actual residual
image is the fixed subgroup of the normal component square. Neither a
core conclusion nor a Sylow-centralizer assertion is a field. -/
structure SelectedComponentData (Q : Type*) [Group Q] (i : Q) (K₀ : Subgroup Q) where
  square : Subgroup Q
  normal : square.Normal
  orthogonal : square ≃* ClassicalOrthogonal.POmegaPlus 2 Binary.F
  fitting : generalizedFitting Q = square
  exchange : letI := normal
    componentAction square (orthogonal.trans orthogonalAlternatingEquiv) i = swap
  fixed : K₀ = square ⊓ centralizer ({i} : Set Q)

namespace SelectedComponentData
variable {Q : Type*} [Group Q] {i : Q} {K₀ : Subgroup Q}

def action (d : SelectedComponentData Q i K₀) : Q →* MulAut (A5 × A5) :=
  let _ : d.square.Normal := d.normal
  componentAction d.square (d.orthogonal.trans orthogonalAlternatingEquiv)

theorem action_injective [Finite Q] (d : SelectedComponentData Q i K₀) :
    Function.Injective d.action := by
  let _ : d.square.Normal := d.normal
  exact componentAction_injective_of_generalizedFitting d.square
    (d.orthogonal.trans orthogonalAlternatingEquiv) d.fitting
    (alternatingGroup.center_eq_bot (by simp))

theorem action_exchange (d : SelectedComponentData Q i K₀) : d.action i = swap :=
  d.exchange

theorem action_diagonal (d : SelectedComponentData Q i K₀) :
    K₀.map d.action = diagonalInner.range := by
  let _ : d.square.Normal := d.normal
  calc
    K₀.map d.action = (d.square ⊓ centralizer ({i} : Set Q)).map d.action :=
      congrArg (fun B : Subgroup Q => B.map d.action) d.fixed
    _ = diagonalInner.range := fixed_component_image d.square
      (d.orthogonal.trans orthogonalAlternatingEquiv) i d.exchange

/-- The whole inner square lies in the action image, the structural input
for the independent selected-Sylow calculation. -/
theorem inner_le_range (d : SelectedComponentData Q i K₀) :
    (MulAut.conj : A5 × A5 →* MulAut (A5 × A5)).range ≤ d.action.range := by
  let _ : d.square.Normal := d.normal
  exact componentAction_inner_le_range d.square (d.orthogonal.trans orthogonalAlternatingEquiv)

/-- Straighten an actual involutive component exchange without changing i.
The only group model is the supplied orthogonal carrier; the resulting
coordinates concern conjugation on its two components. -/
theorem of_exchange (K : Subgroup Q) [K.Normal]
    (eK : K ≃* ClassicalOrthogonal.POmegaPlus 2 Binary.F)
    (hK : generalizedFitting Q = K) (hi : i ^ 2 = 1)
    (hex : ∃ a b : MulAut A5,
      componentAction K (eK.trans orthogonalAlternatingEquiv) i =
        a.prodCongr b * (MulEquiv.prodComm : MulAut (A5 × A5)))
    (hfixed : K₀ = K ⊓ centralizer ({i} : Set Q)) :
    Nonempty (SelectedComponentData Q i K₀) := by
  obtain ⟨a,b,hab⟩ := hex
  let e := eK.trans orthogonalAlternatingEquiv
  let c : MulAut (A5 × A5) := (MulEquiv.refl A5).prodCongr a
  let e' := (e.trans c).trans orthogonalAlternatingEquiv.symm
  have hcoords : e'.trans orthogonalAlternatingEquiv = e.trans c := by
    apply MulEquiv.ext
    intro k
    exact orthogonalAlternatingEquiv.apply_symm_apply _
  refine ⟨⟨K, inferInstance, e', hK, ?_, hfixed⟩⟩
  rw [hcoords]
  have hs : (a.prodCongr b * (MulEquiv.prodComm : MulAut (A5 × A5))) ^ 2 = 1 := by
    rw [← hab, ← map_pow, hi, map_one]
  have he : componentAction K (e.trans c) i = MulAut.congr c (componentAction K e i) := by
    apply MulEquiv.ext
    intro s
    rfl
  rw [he, hab]
  exact straighten_exchange a b hs

end SelectedComponentData

variable {G : Type*} [Group G] [Finite G]

/-- Both quotient-core bounds from the genuine selected component structure.
The actual image of C_H(i) is only sandwiched, never assumed surjective. -/
theorem quotient_core_bounds_of_selected
    (U : Subgroup G) (z i : G)
    (hZ : (center U).map U.subtype = zpowers z)
    (hUcore : (centralizer ({z} : Set G)).pCoreIn 2 = U)
    (hiz : i ∈ centralizer ({z} : Set G))
    (d : SelectedComponentData
      ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G)))
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))) ⟨i,hiz⟩)
      (((diagonalResidual (centralizer ({z} : Set G)) i).subgroupOf
        (centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))))) :
    let H := centralizer ({z} : Set G)
    let q := QuotientGroup.mk' (pCore 2 H)
    (((H ⊓ centralizer ({i} : Set G)).subgroupOf H).map q).pCoreIn 2 ≤
      (zpowers (⟨i,hiz⟩ : H)).map q ∧
    (((diagonalResidual H i ⊔ U ⊔ centralizerLift U z i).subgroupOf H).map q).pCoreIn 2 ≤
      (zpowers (⟨i,hiz⟩ : H)).map q :=
  quotient_core_bounds U z i hZ hUcore hiz d.action d.action_injective
    d.action_exchange d.action_diagonal

/-- Actual applications to both built Core contracts, with their model premises
proved from the selected component square. -/
theorem core_identities_of_selected
    (U : Subgroup G) [IsExtraspecial 2 U] (z i : G)
    (hZ : (center U).map U.subtype = zpowers z)
    (hUcore : (centralizer ({z} : Set G)).pCoreIn 2 = U)
    (hiz : i ∈ centralizer ({z} : Set G))
    (hUcard : Nat.card U = 512)
    (hD : IsElementaryAbelian 2 (centralizerLift U z i))
    (hA : IsElementaryAbelian 2 (liftBase U z i))
    (hAcard : Nat.card (liftBase U z i) = 32)
    (hmoved : Nat.card (((⁅U,zpowers i⁆).subgroupOf U).map
      (QuotientGroup.mk' (center U))) = 16)
    (d : SelectedComponentData
      ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G)))
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))) ⟨i,hiz⟩)
      (((diagonalResidual (centralizer ({z} : Set G)) i).subgroupOf
        (centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))))) :
    (centralizer ({z} : Set G) ⊓ centralizer ({i} : Set G)).pCoreIn 2 =
      centralizerLift U z i ∧
    (diagonalResidual (centralizer ({z} : Set G)) i ⊔ U ⊔
      centralizerLift U z i).pCoreIn 2 = U ⊔ centralizerLift U z i :=
  core_identities_of_components U z i hZ hUcore hiz hUcard hD hA hAcard hmoved
    d.action d.action_injective d.action_exchange d.action_diagonal

/-- The quotient Sylow retains the literal image of the original T. -/
def quotientSylow (T : Sylow 2 G) (z : G)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    Sylow 2 ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))) :=
  (T.subtype hTz).mapSurjective (QuotientGroup.mk'_surjective _)

theorem quotientSylow_coe (T : Sylow 2 G) (z : G)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    (quotientSylow T z hTz : Subgroup
      ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G)))) =
    ((T : Subgroup G).subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) := rfl

theorem selected_mem_quotientSylow (T : Sylow 2 G) (z i : G)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G)) (hiT : i ∈ T) :
    QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))) ⟨i,hTz hiT⟩ ∈
      quotientSylow T z hTz := mem_map_of_mem _ hiT
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.QuotientModel

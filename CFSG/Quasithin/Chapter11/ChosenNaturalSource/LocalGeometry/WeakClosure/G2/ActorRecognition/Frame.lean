module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ActorRecognition.Source

/-!
# Recognized G₂ root transfer on the original flag

An actual model conjugator recenters both the group marking and the natural
coordinates. This leaves the action on the full chosen module unchanged.
Lifting the same conjugator through L/O₂(L) identifies the recentered third
preimage with an L-conjugate of the supplied original flag.

The proved actor recognition now discharges the image premise of RootPullback.
Under the permitted earlier-source clauses, every noncentral Vᵍ in T gives
V₃ˡ ≤ Vᵍ C_V(L), and V₃ˡ ≤ Vᵍ exactly when C_V(L) ≤ Vᵍ. The entire central
kernel and literal ambient conjugations are retained. Recovery of that central
containment and reciprocal plane reconstruction remain obligations of
qt-d-1222-natural-weak-closure-source; this is not unconditional 11.2.2(5).
The earlier-source premises are discharged by qt-d-1222-natural-local-geometry.
Source: Aschbacher--Smith B.4.6(3,9) and 11.2.2(5), printed pp.88--89,768.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ActorRecognition
open Atlas.G2 Atlas.G2.Natural
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))

/-- Recenter the same quotient marking by its actual model conjugator. -/
def recentered (u : Model S.field.Carrier) :
    ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)) where
  groupEquiv := m.groupEquiv.trans (MulAut.conj u⁻¹)
  linearEquiv := m.linearEquiv.trans
    ((OrthogonalCover.SylowFlag.Transport.linear (Natural.action S.field.Carrier) u⁻¹).restrictScalars (ZMod 2))
  intertwines b v := by
    change Natural.action S.field.Carrier u⁻¹ (m.linearEquiv (D.centralQuotientAction b v)) =
      Natural.action S.field.Carrier (u⁻¹ * m.groupEquiv b * (u⁻¹)⁻¹)
        (Natural.action S.field.Carrier u⁻¹ (m.linearEquiv v))
    rw [m.intertwines]
    change Natural.action S.field.Carrier u⁻¹ (Natural.action S.field.Carrier (m.groupEquiv b) _) = _
    simp only [map_mul,Module.End.mul_apply,inv_inv,
      (Natural.action S.field.Carrier).self_inv_apply]

/-- Recentering retains the operator on the full chosen module. -/
theorem recentered_action (u x : Model S.field.Carrier) :
    Preliminary.markedAction D (recentered D S m u) (MulAut.conj u⁻¹ x) =
      Preliminary.markedAction D m x := by
  change (QuotientGroup.lift (pCore 2 L) D.chosenAction D.chosenAction_core)
      (m.groupEquiv.symm ((MulAut.conj u⁻¹).symm (MulAut.conj u⁻¹ x))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The original full preimage is rotated by the same natural operator. -/
theorem recentered_preimage (u : Model S.field.Carrier)
    (U : Submodule S.field.Carrier (Natural.Space S.field.Carrier)) :
    (Coordinates.g2 (recentered D S m u)).preimage U =
      (Coordinates.g2 m).preimage (U.map (Natural.action S.field.Carrier u)) := by
  apply le_antisymm
  · intro x hx
    let v : V := ⟨x,D.centralQuotientPreimage_le _ hx⟩
    have hv := ((Coordinates.g2 (recentered D S m u)).mem_preimage U v).mp hx
    apply ((Coordinates.g2 m).mem_preimage _ v).mpr
    refine ⟨Natural.action S.field.Carrier u⁻¹
      (m.linearEquiv (D.toCentralQuotient v).toAdd),hv,?_⟩
    exact (Natural.action S.field.Carrier).self_inv_apply u _
  · intro x hx
    let v : V := ⟨x,D.centralQuotientPreimage_le _ hx⟩
    obtain ⟨w,hw,he⟩ := ((Coordinates.g2 m).mem_preimage _ v).mp hx
    apply ((Coordinates.g2 (recentered D S m u)).mem_preimage U v).mpr
    change Natural.action S.field.Carrier u⁻¹ (m.linearEquiv (D.toCentralQuotient v).toAdd) ∈ U
    change Natural.action S.field.Carrier u w = m.linearEquiv (D.toCentralQuotient v).toAdd at he
    rw [←he,(Natural.action S.field.Carrier).inv_self_apply]
    exact hw

/-- Recognition now supplies the actual root-pullback consumer. The full
original third preimage is contained in Vᵍ joined with C_V(L), and its
containment in Vᵍ is exactly containment of that central kernel. -/
theorem flag_containment_of_preceding
    (f : InvariantFlag (Coordinates.g2 m))
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ≤ N → N = normalizer (L : Set G))
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hline : f.Vi 0 ≤ V ⊓ centralizer (sourceTL T L : Set G))
    (g : G) (hg : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hnon : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    ∃ l : L,
      (f.Vi 2).map (MulAut.conj (l : G)).toMonoidHom ≤
        V.map (MulAut.conj g).toMonoidHom ⊔ (V ⊓ centralizer (L : Set G)) ∧
      ((f.Vi 2).map (MulAut.conj (l : G)).toMonoidHom ≤
          V.map (MulAut.conj g).toMonoidHom ↔
        V ⊓ centralizer (L : Set G) ≤ V.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨a,u,hact,-,ha⟩ := exists_conjugate_actor_of_preceding D S m f hunique hthree hline g hg hnon
  let m' := recentered D S m u
  let a' := (MulAut.conj u⁻¹).toMonoidHom.comp a
  have ha' : a'.range = EvenTwoRank.elementary S.field.Carrier := by
    rw [MonoidHom.range_comp,ha,map_map]
    have he : (MulAut.conj u⁻¹).toMonoidHom.comp (MulAut.conj u).toMonoidHom =
        MonoidHom.id (Model S.field.Carrier) := by
      ext x
      simp [MulAut.conj_apply,mul_assoc]
    rw [he,map_id]
  have hact' (x : V.map (MulAut.conj g).toMonoidHom) (v : D.space) :
      (D.spaceEquiv (Multiplicative.ofAdd (Preliminary.markedAction D m' (a' x) v)) : G) =
        (x : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (x : G)⁻¹ := by
    change (D.spaceEquiv (Multiplicative.ofAdd
      (Preliminary.markedAction D (recentered D S m u) (MulAut.conj u⁻¹ (a x)) v)) : G) = _
    rw [recentered_action]
    exact hact x v
  have hr := RootPullback.strict_globalR_of_preceding D S m f hunique hthree hline
  obtain ⟨l₀,hl₀⟩ := RootPullback.exists_flag_conjugate D S m f
  obtain ⟨l₁,hl₁⟩ := (Coordinates.g2 m).quotientMap_surjective u
  let U := (NaturalOffenders.upper (F:=S.field.Carrier)).comap
    (Restricted.NaturalCoordinates.coordinates S.field.Carrier)
  have hflag : (Coordinates.g2 m').preimage U =
      (f.Vi 2).map (MulAut.conj ((l₁*l₀ : L) : G)).toMonoidHom := by
    rw [recentered_preimage]
    have hm := (Coordinates.g2 m).preimage_conjugate l₁ U
    change ((Coordinates.g2 m).preimage U).map (MulAut.conj (l₁ : G)).toMonoidHom =
      (Coordinates.g2 m).preimage (U.map (Natural.action S.field.Carrier ((Coordinates.g2 m).quotientMap l₁))) at hm
    rw [hl₁] at hm
    rw [←hm,hl₀,map_map]
    congr 1
    ext x
    change (l₁ : G)*((l₀ : G)*x*(l₀ : G)⁻¹)*(l₁ : G)⁻¹ =
      ((l₁ : G)*(l₀ : G))*x*((l₁ : G)*(l₀ : G))⁻¹
    group
  refine ⟨l₁*l₀,?_,?_⟩
  · rw [←hflag]
    exact RootPullback.threePreimage_le_conjugate_sup D S m' g a' hact' ha' hr
  · rw [←hflag]
    exact RootPullback.threePreimage_le_conjugate_iff D S m' g a' hact' ha' hr
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ActorRecognition

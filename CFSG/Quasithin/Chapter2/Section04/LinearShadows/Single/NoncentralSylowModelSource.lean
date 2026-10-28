module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.ModelSource.Recognition
public import Theory.SpecificGroups.SymplecticFour.Sylow
/-!
# The original noncentral Thompson subgroup is a symplectic Sylow group

Original 2.4.8(4) identifies the block with the derived plane parabolic of
Sp₄ over the actual field of order 2ⁿ. The absorbed Sylow subgroup is the
original Thompson subgroup. Transporting it into the plane local group and
using Sylow conjugacy gives its unipotent model over the same field.

Source: Aschbacher–Smith 2.4.8(4), for the noncentral case of 2.4.24(2).
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
theorem source_noncenterless_thompson_model
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0=d.block) {n:ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T:Subgroup G)≤M)
    (hu : ∀ N, IsMaximalTwoLocal N→(T:Subgroup G)≤N→N=M)
    (hZ : center (d.block.map d.H.subtype)≠⊥) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype)
    ∃ (F:Type) (_:Field F) (_:Finite F) (_:CharP F 2), Nat.card F=2^n ∧
      Nonempty (R≃*unipotent (F:=F)) := by
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype)
  obtain ⟨F,_,_,_,hF,D,_,_,_,x,_,_,hEL,hmodel⟩ :=
    lemma_2_4_8_4 d hG T hST hsingle hL hM hTM hu
  rcases hmodel with hc | hc
  · exact (hZ hc.1).elim
  obtain ⟨e⟩ := hc.2.2.2.1
  let f : L≃*planeLocal (F:=F) := e.trans (Plane.OrthogonalCover.residualLocalEquiv hF hL.1)
  obtain ⟨P,hP⟩ := (source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hu).2.2.1
  let P' : Sylow 2 (planeLocal (F:=F)) := P.mapSurjective (f:=f.toMonoidHom) f.surjective
  let Q : Sylow 2 (planeLocal (F:=F)) := (unipotentSylow hF (le_trans (by decide : 1≤2) hL.1)).subtype inf_le_right
  let e₀ : R≃*P := (MulEquiv.subgroupCongr hP.symm).trans
    (equivMapOfInjective (P:Subgroup L) L.subtype L.subtype_injective).symm
  let e₁ : P≃*P' := equivMapOfInjective (P:Subgroup L) f.toMonoidHom f.injective
  let e₂ : P'≃*Q := Sylow.equiv P' Q
  let e₃ : Q≃*unipotent (F:=F) := subgroupOfEquivOfLe (show unipotent (F:=F)≤planeLocal from inf_le_right)
  exact ⟨F,inferInstance,inferInstance,inferInstance,hF,⟨e₀.trans (e₁.trans (e₂.trans e₃))⟩⟩
end CFSG.Quasithin.Chapter2.LinearShadows.Single

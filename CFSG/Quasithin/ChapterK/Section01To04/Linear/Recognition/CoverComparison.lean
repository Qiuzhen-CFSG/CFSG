module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.HermitianDescent
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions
public import Theory.Representation.HermitianTensorThree.ImageOuter.Overgroups

/-!
# Identifying the faithful component through its actual tensor-cover kernel

An intertwiner between two actions inflated from the same cover identifies
the two kernels when both quotient actions are faithful. The quotient
isomorphisms then give a group equivalence compatible with that same binary
intertwiner. Applied to the Hermitian tensor, this identifies the original
component with the literal binary image, preserving its actual covering map.
The kernel is the full center for odd half-degree and trivial for even
half-degree; hence the component is respectively PSL₃ or SL₃.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, K.3.2(c),
printed pp.454–456, and H.4.4(7), pp.380–381. This is a comparison after
recognition of the inflated action, not a module-classification assumption.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Representation Subgroup
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
noncomputable section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition
section Comparison
variable {D L J V W : Type*} [Group D] [Group L] [Group J]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) L V) (σ : Representation (ZMod 2) J W)
  (π : D →* L) (κ : D →* J) (e : V ≃ₗ[ZMod 2] W)
  (he : ∀ d v, e (ρ (π d) v) = σ (κ d) (e v))

include e he in
private theorem kernels_eq (hρ : Function.Injective ρ) (hσ : Function.Injective σ) :
    π.ker = κ.ker := by
  ext d
  change π d = 1 ↔ κ d = 1
  constructor
  · intro hd
    apply hσ
    ext w
    obtain ⟨v, rfl⟩ := e.surjective w
    rw [← he, hd, map_one, map_one]
    rfl
  · intro hd
    apply hρ
    ext v
    apply e.injective
    rw [he, hd, map_one, map_one]
    rfl

/-- The same binary intertwiner descends through the two exact covering maps. -/
private def actionEquivOfCommonCover (hπ : Function.Surjective π) (hκ : Function.Surjective κ)
    (hρ : Function.Injective ρ) (hσ : Function.Injective σ) : ActionEquiv ρ σ where
  groupEquiv := (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (kernels_eq ρ σ π κ e he hρ hσ)).trans
      (QuotientGroup.quotientKerEquivOfSurjective κ hκ))
  linearEquiv := e
  intertwines g v := by
    obtain ⟨d, rfl⟩ := hπ g
    change e (ρ (π d) v) = σ
      (QuotientGroup.quotientKerEquivOfSurjective κ hκ
        (QuotientGroup.quotientMulEquivOfEq (kernels_eq ρ σ π κ e he hρ hσ)
          ((QuotientGroup.quotientKerEquivOfSurjective π hπ).symm (π d)))) (e v)
    have hp : (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm (π d) =
        QuotientGroup.mk d := by
      apply (QuotientGroup.quotientKerEquivOfSurjective π hπ).injective
      rw [MulEquiv.apply_symm_apply]
      rfl
    rw [hp, QuotientGroup.quotientMulEquivOfEq_mk]
    exact he d v
end Comparison

variable {L V : Type*} [Group L] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) L V) (n : ℕ) [NeZero n]
  (π : Cover n →* L) (hπ : Function.Surjective π) (hf : Function.Injective ρ)
  (e : Representation.Equiv (ρ.comp π) (binaryAction n))

/-- The component acts through exactly the faithful Hermitian image. -/
def hermitianActionEquiv : ActionEquiv ρ (overgroupAction n (binaryImage n)) :=
  actionEquivOfCommonCover ρ (overgroupAction n (binaryImage n)) π
    (binaryActionHom n).rangeRestrict e.toLinearEquiv
    (fun g v => IntertwiningMap.isIntertwining (ρ.comp π) (binaryAction n) e.toIntertwiningMap g v)
    hπ (binaryActionHom n).rangeRestrict_surjective hf (overgroupAction_faithful n _)

/-- The quotient identification commutes with the original covering map and
the literal faithful binary image map. -/
theorem hermitianActionEquiv_cover (g : Cover n) :
    ((hermitianActionEquiv ρ n π hπ hf e).groupEquiv (π g)).val = binaryActionHom n g := by
  apply LinearEquiv.ext
  intro X
  obtain ⟨v, rfl⟩ := e.toLinearEquiv.surjective X
  have h₁ := (hermitianActionEquiv ρ n π hπ hf e).intertwines (π g) v
  have h₂ := IntertwiningMap.isIntertwining (ρ.comp π) (binaryAction n)
    e.toIntertwiningMap g v
  exact h₁.symm.trans h₂

include hf e in
/-- Faithfulness recovers the original cover kernel from its module action. -/
theorem hermitian_cover_kernel : π.ker = (actionHom n).ker := by
  have h := kernels_eq ρ (overgroupAction n (binaryImage n)) π
    (binaryActionHom n).rangeRestrict e.toLinearEquiv
    (fun g v => IntertwiningMap.isIntertwining (ρ.comp π) (binaryAction n) e.toIntertwiningMap g v)
    hf (overgroupAction_faithful n _)
  exact h.trans ((MonoidHom.ker_rangeRestrict (binaryActionHom n)).trans
    (binaryActionHom_ker_eq n))

include hf e in
theorem hermitian_cover_kernel_odd (hn : Odd n) : π.ker = center (Cover n) := by
  rw [hermitian_cover_kernel ρ n π hf e, actionHom_ker_odd n hn]

include hf e in
theorem hermitian_cover_kernel_even (hn : Even n) : π.ker = ⊥ := by
  rw [hermitian_cover_kernel ρ n π hf e, actionHom_ker_even n hn]

def hermitianGroupEquivPSL (hn : Odd n) :
    L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (E n) :=
  (hermitianActionEquiv ρ n π hπ hf e).groupEquiv.trans
    ((binaryImageEquiv n).symm.trans (imageEquivPSL n hn))

def hermitianGroupEquivSL (hn : Even n) : L ≃* Cover n :=
  (hermitianActionEquiv ρ n π hπ hf e).groupEquiv.trans
    ((binaryImageEquiv n).symm.trans (imageEquivSL n hn))

end CFSG.Quasithin.ChapterK.Linear.Recognition

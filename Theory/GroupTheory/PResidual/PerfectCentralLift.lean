module
public import Theory.GroupTheory.PerfectCentralSupplement
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Lifting p-perfect local subgroups through a perfect central cover

A local subgroup of index prime to p is p-perfect if its image through a
central p-kernel is p-perfect. Its residual has the same image, so the kernel
is a central supplement to that residual. Transfer in the perfect ambient
group removes this supplement. No splitting of the cover is needed.

Source application: the lifted Borel in Aschbacher--Smith 15.1.21(i),
printed pp.1097--1098; the central transfer argument is also used in 15.3.38.
-/

public section

open Subgroup
namespace Subgroup
variable {G H : Type*} [Group G] [Finite G] [Group H]
variable [Group.IsPerfect G] {p : ℕ} [Fact p.Prime]

/-- Prime-to-p index and perfect ambient transfer lift p-perfectness. -/
theorem isPPerfect_of_central_pKernel_image (f : G →* H) (K : Subgroup G)
    (hc : f.ker ≤ center G) (hp : IsPGroup p f.ker)
    (hk : f.ker ≤ K) (hi : ¬ p ∣ K.index)
    (himage : IsPPerfect p (K.map f)) : IsPPerfect p K := by
  let R := (pResidual p K).map K.subtype
  have he : R.map f = K.map f := by
    rw [show R = (pResidual p K).map K.subtype from rfl,
      map_embedded_pResidual, (pResidual_eq_top_iff p _).mpr himage,
      ← MonoidHom.range_eq_map, range_subtype]
  have hs : R ⊔ f.ker = K := by
    have hh := congrArg (comap f) he
    simpa only [comap_map_eq, sup_eq_left.mpr hk] using hh
  have hR : R = K := by
    have hh := sup_central_pSubgroup_eq R f.ker hc hp (hs ▸ hi)
    exact hh.symm.trans hs
  apply (pResidual_eq_top_iff p K).mp
  apply top_unique
  intro k _
  have hh : (k : G) ∈ R := hR.ge k.property
  obtain ⟨x,hx,hxk⟩ := hh
  exact (show x = k from Subtype.ext hxk) ▸ hx

end Subgroup

module

public import Theory.SpecificGroups.PSL3Four.CentralCover.GraphFieldKernel.Binary

/-! The perfect central four-cover is unique over the actual PSL₃(4).
The proved exceptional universal multiplier has a unique elementary quotient
of order four: its quotient by squares. Thus both universal lifts have the
same literal kernel, and their quotient identifications give the comparison.
This is source 44.1 in Aschbacher, Sporadic Groups (1994), p.236. -/

public noncomputable section
open Subgroup PerfectCentralCovering
namespace Matrix.PSL3Four
open CentralCover.GraphFieldKernel
open ExtendedCentralizer.CoverCentralizers.DiagonalCenter (BinaryKernelPlane)

private instance : Group.IsPerfect PSL := Atlas.psl_perfect (F := F) 3 (by decide)

private theorem kernel_twelve {K H : Type*} [Group K] [Group H]
    (f : K →* H) (hf : Function.Surjective f)
    (hK : Nat.card K = 48) (hH : Nat.card H = 4) : Nat.card f.ker = 12 := by
  have hc := card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv,
    hK, hH] at hc
  omega

private theorem universal_lift_kernel {E : Type*} [Group E]
    (c : FourCover E) (f : UniversalGroup PSL →* E)
    (hf : c.toMonoidHom.comp f = universalProjection PSL)
    (hs : Function.Surjective f) (x : UniversalGroup PSL) :
    f x = 1 ↔ ∃ hx : x ∈ (universalProjection PSL).ker,
      binaryProjection ⟨x,hx⟩ = 1 := by
  let := c.center_isKleinFour
  have hz (u : Kernel) : f u ∈ center E :=
    c.ker_le_center ((DFunLike.congr_fun hf (u : UniversalGroup PSL)).trans u.property)
  let k : Kernel →* center E := (f.comp (universalProjection PSL).ker.subtype).codRestrict _ hz
  have hk : Function.Surjective k := by
    intro z
    obtain ⟨u,hu⟩ := hs (z : E)
    have hzk : c.toMonoidHom (z : E)=1 := by
      change (z : E) ∈ c.toMonoidHom.ker
      rw [c.ker_eq_center]
      exact z.property
    have huK : u ∈ (universalProjection PSL).ker :=
      (DFunLike.congr_fun hf u).symm.trans
        ((congrArg c.toMonoidHom hu).trans hzk)
    exact ⟨⟨u,huK⟩,Subtype.ext hu⟩
  have hbin : binaryProjection.ker ≤ k.ker := by
    intro u hu
    obtain ⟨v,rfl⟩ := (binaryProjection_eq_one_iff_square u).mp hu
    change k (v^2)=1
    rw [map_pow,pow_two,IsKleinFour.mul_self]
  have hKc : Nat.card Kernel = 48 :=
    (Nat.card_congr PSL3.ExceptionalFourCover.canonicalKernelEquiv.toEquiv).trans
      PSL3.ExceptionalFourCover.card_multiplier
  have hkc := kernel_twelve k hk hKc IsKleinFour.card_four
  have hbc := kernel_twelve binaryProjection binaryProjection_surjective hKc
    (by rw [Nat.card_eq_fintype_card]; decide : Nat.card BinaryKernelPlane = 4)
  have he : binaryProjection.ker = k.ker := eq_of_le_of_card_ge hbin (by rw [hkc,hbc])
  constructor
  · intro hx
    have hxK : x ∈ (universalProjection PSL).ker := by
      rw [← hf]
      change c.toMonoidHom (f x)=1
      rw [hx,map_one]
    refine ⟨hxK,?_⟩
    change (⟨x,hxK⟩ : Kernel) ∈ binaryProjection.ker
    rw [he]
    exact Subtype.ext hx
  · rintro ⟨hx,hbinx⟩
    have hm : (⟨x,hx⟩ : Kernel) ∈ k.ker := he ▸ hbinx
    exact congrArg Subtype.val hm

/-- Perfect central covers with center E₄ are uniquely isomorphic over the
original PSL₃(4) projection. No choice of local coordinates is assumed. -/
theorem FourCover.existsUnique_mulEquiv_over
    {E E' : Type*} [Group E] [Group E'] (c : FourCover E) (c' : FourCover E') :
    ∃! e : E ≃* E', ∀ x, c'.toMonoidHom (e x) = c.toMonoidHom x := by
  let := c.isPerfect
  let := c'.isPerfect
  obtain ⟨f,hf,_⟩ := universalProjection_existsUnique_lift
    c.toMonoidHom c.surjective c.ker_le_center
  obtain ⟨g,hg,_⟩ := universalProjection_existsUnique_lift
    c'.toMonoidHom c'.surjective c'.ker_le_center
  have hfs : Function.Surjective f :=
    surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
      c.toMonoidHom f (hf ▸ universalProjection_surjective PSL) c.ker_le_center
  have hgs : Function.Surjective g :=
    surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
      c'.toMonoidHom g (hg ▸ universalProjection_surjective PSL) c'.ker_le_center
  have hker : f.ker = g.ker := by
    ext x
    exact (universal_lift_kernel c f hf hfs x).trans
      (universal_lift_kernel c' g hg hgs x).symm
  let ef := QuotientGroup.quotientKerEquivOfSurjective f hfs
  let eg := QuotientGroup.quotientKerEquivOfSurjective g hgs
  let e := ef.symm.trans ((QuotientGroup.quotientMulEquivOfEq hker).trans eg)
  have he (u : UniversalGroup PSL) : e (f u)=g u := by
    change eg (QuotientGroup.quotientMulEquivOfEq hker (ef.symm (ef (QuotientGroup.mk u)))) = _
    rw [ef.symm_apply_apply]
    rfl
  refine ⟨e,?_,?_⟩
  · intro x
    obtain ⟨u,rfl⟩ := hfs x
    rw [he]
    exact (DFunLike.congr_fun hg u).trans (DFunLike.congr_fun hf u).symm
  · intro e' he'
    apply MulEquiv.toMonoidHom_injective
    apply monoidHom_eq_of_isPerfect_of_comp_eq c'.toMonoidHom c'.ker_le_center
    ext x
    obtain ⟨u,rfl⟩ := hfs x
    exact (he' (f u)).trans ((DFunLike.congr_fun hf u).trans
      ((DFunLike.congr_fun hg u).symm.trans (congrArg c'.toMonoidHom (he u).symm)))

end Matrix.PSL3Four

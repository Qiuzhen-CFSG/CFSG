module

public import Theory.SpecificGroups.PSL3Four.CentralCover.NonElementaryParabolic
public import Theory.SpecificGroups.PSL3Four.CentralCover.FullPlaneNormalizer
public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.AmbientLocalCores
public import Theory.GroupTheory.PCoreImage

/-!
# The whole center of the PSL₃(4) point cover

An elementary subgroup projecting onto a root plane supplements the central
kernel in its full preimage. That preimage is abelian, so the parabolic-cover
theorem makes the kernel elementary. The proved two-generator bound for the
universal kernel then bounds this elementary quotient by four. Consequently
an original elementary subgroup meeting the center in four contains the
whole center.

Source: Aschbacher--Smith, I.1.3(6), I.2.2(3), and 12.7.5, pp.407--410,840.
-/

public noncomputable section
open Subgroup PerfectCentralCovering
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Matrix.PSL3Four Matrix.PSL3Four.ElementaryParabolic
open Matrix.PSL3.LinearThree Matrix.PSL3.RootPlaneGeometry
variable {B : Type*} [Group B] [Finite B] [Group.IsPerfect B]

private theorem point_cover_elementary_kernel_card_le_four
    (f : B →* PSL) (hf : Function.Surjective f) (hc : f.ker ≤ center B)
    (hs : ∀ z ∈ f.ker, z ^ 2 = 1) : Nat.card f.ker ≤ 4 := by
  let u := universalProjection PSL
  obtain ⟨a,ha,_⟩ := universalProjection_existsUnique_lift f hf hc
  have has : Function.Surjective a :=
    surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
      f a (ha ▸ universalProjection_surjective PSL) hc
  let k : u.ker →* f.ker := (a.comp u.ker.subtype).codRestrict f.ker (fun x => by
    change f (a x) = 1
    rw [← MonoidHom.comp_apply,ha]
    exact x.property)
  have hks : Function.Surjective k := by
    intro x
    obtain ⟨y,hy⟩ := has x
    have hyk : y ∈ u.ker := by
      change universalProjection PSL y = 1
      rw [← ha,MonoidHom.comp_apply,hy]
      exact x.property
    exact ⟨⟨y,hyk⟩,Subtype.ext hy⟩
  have hr : Group.rank u.ker ≤ 2 := by
    let : Finite Matrix.PSL3.ExceptionalFourCover.TwoGeneratorPresentation.Presentation :=
      Matrix.PSL3.ExceptionalFourCover.TwoGeneratorPresentation.finite_and_card_le.1
    apply Matrix.PSL3.ExceptionalFourCover.kernel_rank_le_two_of_presentation_equiv
      (MulEquiv.ofBijective
        Matrix.PSL3.ExceptionalFourCover.TwoGeneratorPresentation.matrixMap
        (Matrix.PSL3.ExceptionalFourCover.TwoGeneratorPresentation.matrixMap_surjective.bijective_of_nat_card_le ?_))
    rw [card_PSL]
    exact Matrix.PSL3.ExceptionalFourCover.TwoGeneratorPresentation.finite_and_card_le.2
  have hrf : Group.rank f.ker ≤ 2 := (Group.rank_le_of_surjective k hks).trans hr
  let : IsMulCommutative f.ker := ⟨⟨fun x y =>
    Subtype.ext (mem_center_iff.mp (hc x.property) y).symm⟩⟩
  let : CommGroup f.ker := IsMulCommutative.instCommGroup
  have hd := card_dvd_exponent_pow_rank' f.ker
    (fun z => Subtype.ext (hs z z.property))
  exact (Nat.le_of_dvd (by positivity) hd).trans
    (by simpa using pow_le_pow_right' (by decide : 1 ≤ 2) hrf)

private theorem point_cover_kernel_square_of_full_plane
    (f : B →* PSL) (hf : Function.Surjective f) (hc : f.ker ≤ center B)
    (hk : IsPGroup 2 f.ker) (U : Subgroup B) [IsElementaryAbelian 2 U]
    (b : Bool) (hU : U.map f = rootPlane F b) :
    ∀ z ∈ f.ker, z ^ 2 = 1 := by
  let R := U ⊔ f.ker
  have hRc : IsMulCommutative R := by
    have hZU : f.ker ≤ centralizer (U : Set B) := hc.trans (center_le_centralizer _)
    have hUZ : U ≤ centralizer (f.ker : Set B) := le_centralizer_iff.mp hZU
    have hZZ : f.ker ≤ centralizer (f.ker : Set B) := hc.trans (center_le_centralizer _)
    apply le_centralizer_iff_isMulCommutative.mp
    apply sup_le
    · apply le_centralizer_iff.mpr
      exact sup_le (le_centralizer_iff_isMulCommutative.mpr inferInstance) hZU
    · apply le_centralizer_iff.mpr
      exact sup_le hUZ hZZ
  let : IsMulCommutative R := hRc
  have hR : R = (rootPlane F b).comap f := by rw [← hU,comap_map_eq]
  let P := liftedParabolic f b
  have hm : (P.pCoreIn 2).map f = rootPlane F b := by
    rw [map_pCoreIn_of_ker_isPGroup f hk]
    change ((parabolic F b).comap f |>.map f).pCoreIn 2 = _
    rw [map_comap_eq_self_of_surjective hf,native_parabolic_eq_local]
    exact Matrix.PSL3.LinearThree.OuterExtensions.AmbientLocalCores.local_core_eq_rootPlane
      F (f := 2) (by decide) (by simpa using card_F) b
  have hPR : P.pCoreIn 2 ≤ R := by
    rw [hR,←hm]
    exact le_comap_map f _
  let : IsMulCommutative (pCore 2 P) := ⟨⟨fun x y => by
    have hx : x.val.val ∈ R := hPR (mem_map_of_mem P.subtype x.property)
    have hy : y.val.val ∈ R := hPR (mem_map_of_mem P.subtype y.property)
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : R => (z : B))
      (mul_comm (⟨x.val.val,hx⟩ : R) ⟨y.val.val,hy⟩)⟩⟩
  exact NonElementaryKernel.kernel_pow_two_of_abelian_core f hf hc hk b

/-- An elementary subgroup with full order-16 projective image forces the
entire central kernel to have order at most four. -/
theorem original_point_psl_three_four_kernel_card_le_four
    (f : B →* PSL) (hf : Function.Surjective f) (hc : f.ker ≤ center B)
    (hk : IsPGroup 2 f.ker) (U : Subgroup B) [IsElementaryAbelian 2 U]
    (hU : Nat.card (U.map f) = 16) : Nat.card f.ker ≤ 4 := by
  let A := U.map f
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map f
  obtain ⟨P,hP⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL P
    (unipotentSylow F (n := 2) (by decide) (by simpa using card_F))
  let f' := (MulAut.conj g).toMonoidHom.comp f
  have hf' : Function.Surjective f' := (MulAut.conj g).surjective.comp hf
  have hker : f'.ker = f.ker :=
    MonoidHom.ker_comp_of_injective _ _ (MulAut.conj g).injective
  have hAU : U.map f' ≤ unipotent F := by
    have hP' := congrArg Sylow.toSubgroup hg
    change (P : Subgroup PSL).map (MulAut.conj g).toMonoidHom = unipotent F at hP'
    rw [←hP',show f' = (MulAut.conj g).toMonoidHom.comp f from rfl,←Subgroup.map_map]
    exact map_mono hP
  let : IsElementaryAbelian 2 (U.map f') := IsElementaryAbelian.map f'
  have hAc' : Nat.card (U.map f') = 16 := by
    rw [show f' = (MulAut.conj g).toMonoidHom.comp f from rfl,←Subgroup.map_map,
      card_map_of_injective (MulAut.conj g).injective]
    exact hU
  obtain ⟨b,hb⟩ := FullPlaneNormalizer.elementary_plane (U.map f') hAU hAc'
  rw [←hker]
  exact point_cover_elementary_kernel_card_le_four f' hf' (hker ▸ hc)
    (point_cover_kernel_square_of_full_plane f' hf' (hker ▸ hc) (hker ▸ hk) U b hb)

/-- The intersection of order four with the original elementary U is the
whole center of the PSL₃(4) cover. -/
theorem original_point_psl_three_four_center_eq_inf
    (U : Subgroup B) [IsElementaryAbelian 2 U] (hU : Nat.card U = 64)
    (e : B ⧸ center B ≃* PSL) (hk : IsPGroup 2 (center B))
    (hI : Nat.card (U ⊓ center B : Subgroup B) = 4) :
    center B = U ⊓ center B := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center B))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = center B := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hmap : Nat.card (U.map f) = 16 := by
    have hh := IsElementaryAbelian.card_inf_ker_mul_card_map U f
    rw [hker,hI,hU] at hh
    omega
  have hbound := original_point_psl_three_four_kernel_card_le_four f hf
    hker.le (hker ▸ hk) U hmap
  rw [hker] at hbound
  exact (eq_of_le_of_card_ge inf_le_right (hI ▸ hbound)).symm

end CFSG.Quasithin.Chapter12.Section07

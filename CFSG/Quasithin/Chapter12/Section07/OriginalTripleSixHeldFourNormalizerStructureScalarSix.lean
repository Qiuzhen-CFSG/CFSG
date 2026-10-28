module

public import Theory.Representation.HexacodeAction.EvenOrbitWeights
public import Theory.Representation.HexacodeAction.Field
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.GroupTheory.TwoInvolutionsSymmetricThree
public import Theory.GroupTheory.SymmetricThreeImage

/-! An actual symmetric-three group on every full-weight scalar line.
A literal triple-transposition lift fixes a full-weight vector and inverts
the cubic scalar. Even transitivity transports it to the prescribed vector. -/

public noncomputable section
open Atlas.Codes Subgroup
namespace Representation.Hexacode
open BinaryOffender

private def tripleLift : HexAutomorphisms := hexLift 0 * hexLift 2 * hexLift 4

private theorem tripleLift_sq : tripleLift^2 = 1 := by
  apply Subtype.ext
  apply Monomial.ext
  · apply _root_.Equiv.ext
    intro i
    revert i
    decide +kernel
  · funext i
    apply LinearEquiv.ext
    intro u
    revert i u
    decide +kernel

private theorem tripleLift_odd : hexSign tripleLift = -1 := by
  simp [tripleLift]

private theorem tripleLift_seed : ∃ x : Fin 3 → K,
    hammingNorm (systematicEncoder x) = 6 ∧
      action tripleLift (⟨systematicEncoder x,systematic_mem x⟩ : hexacode) =
        ⟨systematicEncoder x,systematic_mem x⟩ := by decide +kernel

private theorem exists_odd_involution_fixed (v : hexacode) (hv : hammingNorm v.val=6) :
    ∃ r : HexAutomorphisms, r^2=1 ∧ hexSign r = -1 ∧ action r v=v := by
  obtain ⟨x,hx,hfix⟩ := tripleLift_seed
  let w : hexacode := ⟨systematicEncoder x,systematic_mem x⟩
  have hw : w≠0 := by intro he; have hh := hx; change hammingNorm w.val=6 at hh; simp [he] at hh
  have hvw : v ∈ Set.range (fun g : HexEvenAutomorphisms => evenAction g w) := by
    rw [evenAction_orbit_eq_weight w hw]
    exact hv.trans hx.symm
  obtain ⟨g,hg⟩ := hvw
  let r := (MulAut.conj g.val) tripleLift
  refine ⟨r,?_,?_,?_⟩
  · change (MulAut.conj g.val tripleLift)^2=1
    rw [←map_pow,tripleLift_sq,map_one]
  · change hexSign (g.val*tripleLift*g.val⁻¹) = -1
    rw [map_mul,map_mul,map_inv,g.property,tripleLift_odd]
    simp
  · rw [←hg]
    change action (g.val*tripleLift*g.val⁻¹) (action g.val w) = action g.val w
    simp only [map_mul,Module.End.mul_apply]
    have hcancel : action g.val⁻¹ (action g.val w)=w := by
      rw [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
    rw [hcancel,hfix]

private theorem scalar_line_stable (v : hexacode) (g : HexAutomorphisms)
    (hg : action g v ∈ Submodule.span F {v}) :
    g ∈ subspaceStabilizer action ((Submodule.span F {v}).restrictScalars Bit) := by
  let S := (Submodule.span F {v}).restrictScalars Bit
  have hle : S.map (hexAction g).toLinearMap ≤ S := by
    rintro _ ⟨w,hw,rfl⟩
    obtain ⟨s,rfl⟩ := Submodule.mem_span_singleton.mp hw
    rcases Int.units_eq_one_or (hexSign g) with he | ho
    · change action g (s • v)∈Submodule.span F {v}
      rw [action_even_smul g he]
      exact (Submodule.span F {v}).smul_mem _ hg
    · change action g (s • v)∈Submodule.span F {v}
      rw [action_odd_smul g ho]
      exact (Submodule.span F {v}).smul_mem _ hg
  have he : S.map (hexAction g).toLinearMap=S :=
    Submodule.eq_of_le_of_finrank_eq hle ((hexAction g).finrank_map_eq S)
  intro w
  constructor
  · intro hw
    have hh : action g w∈S.map (hexAction g).toLinearMap := he.symm ▸ hw
    obtain ⟨u,hu,hu'⟩ := hh
    exact (hexAction g).injective hu' ▸ hu
  · intro hw
    change action g w∈S
    rw [←he]
    exact ⟨w,hw,rfl⟩

/-- Every prescribed full-weight scalar line admits an actual S₃ subgroup
whose restriction to that line is faithful. -/
theorem exists_full_weight_scalar_symmetric_three
    (v : hexacode) (hv : hammingNorm v.val=6) :
    ∃ R : Subgroup HexAutomorphisms,
      Nonempty (R ≃* Equiv.Perm (Fin 3)) ∧
      R ≤ subspaceStabilizer action ((Submodule.span F {v}).restrictScalars Bit) ∧
      ∀ g∈R, (∀ w∈Submodule.span F {v}, action g w=w) → g=1 := by
  have hv0 : v≠0 := by intro he; simp [he] at hv
  obtain ⟨r,hr,ho,hfix⟩ := exists_odd_involution_fixed v hv
  have hri : r⁻¹=r := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hr)
  have hinv : r*hexZ*r=hexZ⁻¹ := by simpa only [hri] using hex_conjugation_odd r ho
  have hrz : (r*hexZ)^2=1 := by
    rw [pow_two,←mul_assoc,mul_assoc r hexZ r,←mul_assoc,hinv,inv_mul_cancel]
  have hprod : r*(r*hexZ)=hexZ := by rw [←mul_assoc,show r*r=1 by simpa only [pow_two] using hr,one_mul]
  let R := zpowers r ⊔ zpowers (r*hexZ)
  obtain ⟨e⟩ := symmetricThree_of_involutions_product_three r (r*hexZ) hr hrz
    (by rw [hprod]; exact hexZ_order)
  have hR : R ≤ subspaceStabilizer action ((Submodule.span F {v}).restrictScalars Bit) := by
    have hrr := scalar_line_stable v r (by rw [hfix]; exact Submodule.mem_span_singleton_self v)
    have hz := scalar_line_stable v hexZ (by
      rw [scalar_eq_omega_smul]
      exact (Submodule.span F {v}).smul_mem _ (Submodule.mem_span_singleton_self v))
    exact sup_le (zpowers_le.mpr hrr) (zpowers_le.mpr
      ((subspaceStabilizer action _).mul_mem hrr hz))
  let S := (Submodule.span F {v}).restrictScalars Bit
  let q := subgroupActionHom action S R hR
  have hzR : hexZ∈R := hprod ▸ R.mul_mem (mem_sup_left (mem_zpowers r))
    (mem_sup_right (mem_zpowers (r*hexZ)))
  let z : R := ⟨hexZ,hzR⟩
  have hqz : q z≠1 := by
    intro hh
    have hzK : hexZ ∈ subspaceKernel action S R := by
      rw [←subgroupActionHom_ker action S R hR]
      exact mem_map_of_mem R.subtype (show z∈q.ker from hh)
    exact hv0 ((scalar_fixed_iff v).mp (hzK.2 v (Submodule.mem_span_singleton_self v)))
  have hz3 : orderOf (q z)=3 := orderOf_eq_prime
    (by rw [←map_pow,show z^3=1 from Subtype.ext hexZ_cube,map_one]) hqz
  have hn : ¬IsPGroup 2 q.range := by
    intro hp
    have hd : 3∣Nat.card q.range := hz3 ▸
      q.range.orderOf_dvd_natCard (show q z∈q.range from ⟨z,rfl⟩)
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    rw [hn] at hd
    exact (by decide : ¬(3∣2)) (Nat.prime_three.dvd_of_dvd_pow hd)
  obtain ⟨j⟩ := symmetricThree_image_of_not_isPGroup e q hn
  have hq : Function.Injective q := by
    have hc : Nat.card q.range=Nat.card R :=
      (Nat.card_congr j.toEquiv).trans (Nat.card_congr e.toEquiv).symm
    have hh := (q.rangeRestrict_surjective.bijective_of_nat_card_le hc.symm.le).1
    intro a b hab
    exact hh (Subtype.ext hab)
  refine ⟨R,⟨e⟩,hR,?_⟩
  intro g hg hgf
  have hgK : g∈subspaceKernel action S R := ⟨hg,hgf⟩
  rw [←subgroupActionHom_ker action S R hR] at hgK
  obtain ⟨x,hx,hxg⟩ := hgK
  exact hxg.symm.trans (congrArg Subtype.val (hq (hx.trans q.map_one.symm)))

end Representation.Hexacode

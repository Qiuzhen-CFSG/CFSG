module

public import Theory.SpecificGroups.Suzuki.SubgroupFrobenius
public import Theory.SpecificGroups.Suzuki.AbelianRootGeometry
public import BenderSuzuki.External.Huppert.XI.FrobeniusKernel

/-!
# Noncommutative kernels in Suzuki subgroup actions

A Frobenius kernel in a point stabilizer of a doubly transitive Suzuki
subaction cannot be abelian. Conjugate the distinguished pair to infinity
and zero. The kernel lies in the root group and its nontrivial complement
lies in the split torus. Normality and commutativity would force every
kernel element to have first coordinate zero. Kernel regularity then
contradicts the effect of an element swapping the distinguished pair.

Source: Huppert--Blackburn, *Finite Groups III*, XI.3.12(e), XI.11.15,
and Suzuki (1962).
-/

namespace BenderSuzuki.MatrixGroups

open PFAppendixIII

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The point-stabilizer Frobenius kernels of a nonsolvable doubly transitive
Suzuki subaction are noncommutative. -/
public theorem suzukiSubaction_frobeniusKernel_not_isMulCommutative {m : ℕ} (hm : 0 < m) (H : Subgroup (SuzukiMatrixGroup m))
    (_hH : ¬ Group.IsSolvable H)
    (X : SubMulAction H (SuzukiOvoid m)) [Nonempty X]
    (htwo : MulAction.IsMultiplyPretransitive H X 2)
    (a b : X) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer H a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer H a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer H a))) : ¬ IsMulCommutative F := by
  intro hcomm
  let : IsMulCommutative F := hcomm
  let S := MulAction.stabilizer H a
  let b' : SubMulAction.ofStabilizer H a := ⟨b, hab.symm⟩
  let D := MulAction.stabilizer S b'
  change IsFrobeniusGroupWithKernelComplement F D at hFrob
  obtain ⟨k, hka, hkb⟩ := MulAction.is_two_pretransitive_iff.mp
    (suzukiOvoid_two_pretransitive m)
    (show a.val ≠ b.val from fun h => hab (Subtype.ext h))
    (suzukiOvoidInfinity_ne_zero m)
  let ρ : H →* SuzukiMatrixGroup m := (MulAut.conj k).toMonoidHom.comp H.subtype
  let e : X → SuzukiOvoid m := fun x => k • x.val
  have he (g : H) (x : X) : e (g • x) = ρ g • e x := by
    change k • (g.val • x.val) = (k * g.val * k⁻¹) • (k • x.val)
    simp only [mul_smul, inv_smul_smul]
  have hea : e a = suzukiOvoidInfinity m := hka
  have heb : e b = suzukiOvoidZero m := hkb
  have hρ : Function.Injective ρ := (MulAut.conj k).injective.comp H.subtype_injective
  let ψ : S →* SuzukiMatrixGroup m := ρ.comp S.subtype
  have hψ : Function.Injective ψ := hρ.comp S.subtype_injective
  have hfixa (s : S) : ψ s • suzukiOvoidInfinity m = suzukiOvoidInfinity m := by
    change ρ s.val • suzukiOvoidInfinity m = suzukiOvoidInfinity m
    rw [← hea, ← he]
    exact congrArg e s.property
  let ψB : S →* SuzukiBorelSubgroup m := ψ.codRestrict _ (fun s => by
    rw [suzukiBorelSubgroup_eq_stabilizer m hm, MulAction.mem_stabilizer_iff]
    exact hfixa s)
  have hroot (f : F) : ψ f.val ∈ SuzukiRootSubgroup m :=
    suzukiBorel_frobeniusKernel_le_root hm hFrob ψB f.property
  let : Nontrivial D := (Subgroup.nontrivial_iff_ne_bot D).2 hFrob.complement_ne_bot
  obtain ⟨d, hd⟩ := exists_ne (1 : D)
  have hdψ : ψ d.val ≠ 1 := by
    intro h
    apply hd
    apply Subtype.ext
    exact hψ (h.trans (map_one ψ).symm)
  have hdtorus : ψ d.val ∈ SuzukiSplitTorus m := by
    rw [mem_suzukiSplitTorus_iff_fix_pair]
    refine ⟨hfixa d.val, ?_⟩
    change ρ d.val.val • suzukiOvoidZero m = suzukiOvoidZero m
    rw [← heb, ← he]
    exact congrArg e (congrArg Subtype.val d.property)
  obtain ⟨t, ht⟩ := (mem_suzukiSplitTorus_iff m _).mp hdtorus
  have htne : t ≠ 1 := by
    intro htone
    apply hdψ
    apply Subtype.ext
    simpa [htone, External.suzukiTorusGL_one] using ht
  have hzero (f : F) : ∃ v, (ψ f.val).val = SuzukiRootGL m 0 v := by
    obtain ⟨u, v, huv⟩ := (mem_suzukiRootSubgroup_iff m _).mp (hroot f)
    let fc : F := ⟨d.val * f.val * d.val⁻¹, hFrob.normal.conj_mem _ f.property _⟩
    have hc : Commute (ψ f.val) (ψ d.val * ψ f.val * (ψ d.val)⁻¹) := by
      have hh := congrArg (fun z : F => ψ z.val) (mul_comm' f fc)
      rw [commute_iff_eq]
      simpa only [fc, Subgroup.coe_mul, map_mul, map_inv] using hh
    have hgl := congrArg Subtype.val hc.eq
    change (ψ f.val).val * ((ψ d.val).val * (ψ f.val).val * ((ψ d.val).val)⁻¹) =
      ((ψ d.val).val * (ψ f.val).val * ((ψ d.val).val)⁻¹) * (ψ f.val).val at hgl
    rw [huv, ht] at hgl
    have hu := suzukiRootGL_first_eq_zero_of_commute_conjugate m u v t htne ((commute_iff_eq _ _).mpr hgl)
    refine ⟨v, ?_⟩
    rw [huv, hu]
  let : Nontrivial F := (Subgroup.nontrivial_iff_ne_bot F).2 hFrob.kernel_ne_bot
  obtain ⟨f, hf⟩ := exists_ne (1 : F)
  let c : X := f.val.val • b
  have hcb : c ≠ b := by
    intro h
    have hmem : f.val ∈ D := by
      apply MulAction.mem_stabilizer_iff.mpr
      exact Subtype.ext h
    exact hf (Subtype.ext (Subgroup.disjoint_def.mp hFrob.isComplement'.disjoint f.property hmem))
  obtain ⟨w, hwa, hwb⟩ := MulAction.is_two_pretransitive_iff.mp htwo hab hab.symm
  have hwc : w • c ≠ a := by
    intro h
    apply hcb
    exact (MulAction.injective w) (h.trans hwb.symm)
  obtain ⟨E, hE⟩ := External.huppert_blackburn_XI_pointStabilizer_exists_kernelPointEquiv
    htwo a b hab F hFrob
  let f' : F := E.symm ⟨w • c, hwc⟩
  have hf' : f'.val.val • b = w • c := by
    have hh := (hE f').symm.trans (E.apply_symm_apply ⟨w • c, hwc⟩)
    exact congrArg Subtype.val hh
  have hwi : ρ w • suzukiOvoidInfinity m = suzukiOvoidZero m := by
    rw [← hea, ← heb, ← he, hwa]
  have hwz : ρ w • suzukiOvoidZero m = suzukiOvoidInfinity m := by
    rw [← hea, ← heb, ← he, hwb]
  obtain ⟨v, hv⟩ := hzero f
  obtain ⟨v', hv'⟩ := hzero f'
  have hrel : ρ w • (ψ f.val • suzukiOvoidZero m) = ψ f'.val • suzukiOvoidZero m := by
    change ρ w • (ρ f.val.val • suzukiOvoidZero m) = ρ f'.val.val • suzukiOvoidZero m
    calc
      ρ w • (ρ f.val.val • suzukiOvoidZero m) = ρ w • e c := by
        apply congrArg (ρ w • ·)
        exact (congrArg (ρ f.val.val • ·) heb.symm).trans (he f.val.val b).symm
      _ = e (w • c) := (he w c).symm
      _ = e (f'.val.val • b) := congrArg e hf'.symm
      _ = ρ f'.val.val • e b := he f'.val.val b
      _ = ρ f'.val.val • suzukiOvoidZero m := congrArg (ρ f'.val.val • ·) heb
  have hfψ := suzukiOvoid_swap_root_first_zero m (ρ w) (ψ f.val) (ψ f'.val)
    hwi hwz v v' hv hv' hrel
  apply hf
  apply Subtype.ext
  exact hψ (hfψ.trans (map_one ψ).symm)
end BenderSuzuki.MatrixGroups

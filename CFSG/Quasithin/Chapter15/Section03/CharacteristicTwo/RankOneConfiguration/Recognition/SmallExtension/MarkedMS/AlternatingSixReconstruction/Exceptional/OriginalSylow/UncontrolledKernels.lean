module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.KernelMovers
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.EndSlices
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeKernelLine
import all Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreTranspositionFixed
import all Theory.SpecificGroups.SymmetricSix.BinaryFlags.CoreCrossing

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneComparison
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicBorelThompson
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneEscape

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicOmegaGeneration


/-!
# Uncontrolled full reverse kernels on a Borel edge

For either full moving cover, an elementary Borel actor commuting with a
critical transposition satisfies endpoint displacement control or moves at
most a line of its fixed hyperplane. The point-core calculation is made in
the actual six-letter augmentation module and transported to both covers.

On the original exceptional graph, failure of endpoint control therefore
bounds the full reverse-kernel commutator by two, without assuming small
forward or predecessor slices. The whole kernel lies in the neighboring
proper Thompson mover. In the centrally generated branch its nonzero line
lies in the starting Baumann slice. Distinct movers make that line fixed by
the actual starting residual and produce a residual-invariant kernel-fixed
span. This retains residual normalization, the full cubic kernel and both
cover orders; it does not identify the cubic kernel E with the two-core Q.

CentralStrict uses this span at a strict slice. The literal original-source
applications are in OriginalSylowExceptional. The natural import supplies
only a six-letter representation calculation, never a graph identification.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.7), printed p.919; Aschbacher--Smith C.1.31--32, pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement Pointwise
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags CoreCrossing
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance Exhaustion.LargeDistance.CubicFull
local notation "borel" => Theory.SpecificGroups.SymmetricSix.borel

private theorem point_core_fixed_line :
    subspaceCommutator (coreRepresentation (Fin 6))
      (fixedSpace (coreRepresentation (Fin 6)) (zpowers swap45)) pointCore ≤
        Submodule.span (ZMod 2) {pairWord 0 1 + pairWord 2 3} := by
  have cert : ∀ (j : Fin 8) (w : Fin 6 → ZMod 2),
      augmentation (Fin 6) w = 0 → representation (Fin 6) swap45 w = w →
      ∃ c : ZMod 2, representation (Fin 6) (pointWord j) w-w =
        c • ((pairWord 0 1 + pairWord 2 3 : C) : Fin 6 → ZMod 2) := by
    decide +kernel
  apply Submodule.span_le.mpr
  rintro _ ⟨g,hg,v,hv,rfl⟩
  have hw : g ∈ PointCoreGeneration.coreWords := PointCoreTranspositionFixed.core_in_certificate hg
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp hw
  have hj' : pointWord ⟨j.val,by simpa only [PointCoreGeneration.coreWords,List.length_cons,List.length_nil] using j.isLt⟩ = g := hj
  obtain ⟨c,hc⟩ := cert ⟨j.val,by simpa only [PointCoreGeneration.coreWords,List.length_cons,List.length_nil] using j.isLt⟩ v.val v.property
    (congrArg Subtype.val ((mem_fixedSpace_zpowers_iff _ _ _).mp hv))
  rw [hj'] at hc
  apply Submodule.mem_span_singleton.mpr
  exact ⟨c,Subtype.ext hc.symm⟩

private theorem point_mapped_fixed_finrank
    {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (σ : Representation (ZMod 2) S Y) (f : C →ₗ[ZMod 2] Y)
    (hf : Function.Surjective f) (he : ∀ g v, f (coreRepresentation (Fin 6) g v)=σ g (f v))
    (hn : f (pairWord 4 5) ≠ 0) (P : Subgroup S) (hP : P ≤ pointCore) :
    Module.finrank (ZMod 2) (subspaceCommutator σ (fixedSpace σ (zpowers swap45)) P) ≤ 1 := by
  have hF : (fixedSpace (coreRepresentation (Fin 6)) (zpowers swap45)).map f = fixedSpace σ (zpowers swap45) := by
    apply le_antisymm
    · rintro _ ⟨v,hv,rfl⟩
      apply (mem_fixedSpace_zpowers_iff _ _ _).mpr
      rw [←he,(mem_fixedSpace_zpowers_iff _ _ _).mp hv]
    · intro w hw
      obtain ⟨v,rfl⟩ := hf w
      refine ⟨v,?_,rfl⟩
      have hh : (v.val 4+v.val 5) • f (pairWord 4 5)=0 := by
        rw [←map_smul,←swap45_displacement,map_sub,he,
          (mem_fixedSpace_zpowers_iff _ _ _).mp hw,sub_self]
      have hz : v.val 4+v.val 5=0 := (smul_eq_zero.mp hh).resolve_right hn
      apply (mem_fixedSpace_zpowers_iff _ _ _).mpr
      apply sub_eq_zero.mp
      rw [swap45_displacement,hz,zero_smul]
  have hle : subspaceCommutator (coreRepresentation (Fin 6))
      (fixedSpace (coreRepresentation (Fin 6)) (zpowers swap45)) P ≤
        Submodule.span (ZMod 2) {pairWord 0 1 + pairWord 2 3} := by
    apply le_trans _ point_core_fixed_line
    apply Submodule.span_mono
    rintro _ ⟨g,hg,v,hv,rfl⟩
    exact ⟨g,hP hg,v,hv,rfl⟩
  have hm := Submodule.map_mono (f := f) hle
  have hh := subspaceCommutator_map_embedding σ (coreRepresentation (Fin 6))
    (MonoidHom.id S) f (fun g v => (he g v).symm) P
    (fixedSpace (coreRepresentation (Fin 6)) (zpowers swap45))
  simp only [map_id] at hh
  rw [←hh,hF] at hm
  exact (Submodule.finrank_mono hm).trans
    ((Submodule.finrank_map_le f _).trans (by simpa using (finrank_span_le_card ({pairWord 0 1 + pairWord 2 3} : Set C))))

private theorem point_cover_fixed_finrank
    {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (σ : Representation (ZMod 2) S Y)
    (hm : SixCover.IsNaturalOrCore σ (MonoidHom.id S))
    (u t : S) (P : Subgroup S)
    (hP : P ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (ht : t ∈ pointCore.map (MulAut.conj u).toMonoidHom) (hs : t.IsSwap) :
    Module.finrank (ZMod 2) (subspaceCommutator σ (fixedSpace σ (zpowers t)) P) ≤ 1 := by
  have hex : ∃ f : C →ₗ[ZMod 2] Y, Function.Surjective f ∧
      (∀ g v, f (coreRepresentation (Fin 6) g v)=σ g (f v)) ∧ f (pairWord 4 5) ≠ 0 := by
    rcases hm with ⟨E,hE⟩ | ⟨E,hE⟩
    · let f := E.symm.toLinearMap.comp (coreToNatural (Fin 6))
      refine ⟨f,E.symm.surjective.comp coreToNatural_surjective,?_,?_⟩
      · intro g v
        apply E.injective
        simp only [f,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,
          hE,MonoidHom.id_apply,coreToNatural_equivariant]
      · intro hz
        have hh := congrArg E hz
        apply NaturalGeometry.pairVector_ne_zero (by decide : (4 : Fin 6) ≠ 5)
        have hpair : coreToNatural (Fin 6) (pairWord 4 5)=NaturalGeometry.pairVector 4 5 := rfl
        simpa only [hpair,f,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,
          map_zero] using hh
    · refine ⟨E.symm.toLinearMap,E.symm.surjective,?_,?_⟩
      · intro g v
        apply E.injective
        simp only [LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,hE,MonoidHom.id_apply]
      · intro hz
        have hh := congrArg E hz
        have hp : pairWord 4 5 ≠ 0 := by decide +kernel
        apply hp
        simpa only [LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,map_zero] using hh
  obtain ⟨f,hf,hfe,hfn⟩ := hex
  let c := (MulAut.conj u).toMonoidHom
  let P₀ := P.comap c
  have hmap : P₀.map c=P := map_comap_eq_self_of_surjective (MulAut.conj u).surjective P
  have hP₀ : P₀ ≤ pointCore := by
    apply (map_le_map_iff_of_injective (f := c) (MulAut.conj u).injective).mp
    rw [hmap]
    exact hP
  let τ := σ.comp c
  let f₀ := (σ u).comp f
  have hs₀ : Function.Surjective f₀ := by
    intro v
    obtain ⟨a,ha⟩ := hf (σ u⁻¹ v)
    refine ⟨a,?_⟩
    change σ u (f a)=v
    rw [ha,σ.self_inv_apply]
  have he₀ (g : S) (v : C) : f₀ (coreRepresentation (Fin 6) g v)=τ g (f₀ v) := by
    change σ u (f (coreRepresentation (Fin 6) g v))=σ (u*g*u⁻¹) (σ u (f v))
    rw [hfe]
    simp only [map_mul,Module.End.mul_apply,σ.inv_self_apply]
  have hn₀ : f₀ (pairWord 4 5) ≠ 0 := by
    intro hz
    have hh := congrArg (σ u⁻¹) hz
    apply hfn
    simpa only [f₀,LinearMap.comp_apply,σ.inv_self_apply,map_zero] using hh
  have hA : (zpowers swap45).map c=zpowers t := by
    rw [MonoidHom.map_zpowers]
    exact congrArg zpowers (PointCoreTranspositionFixed.swap_eq_conjugate u t ht hs).symm
  have hh := point_mapped_fixed_finrank τ f₀ hs₀ he₀ hn₀ P₀ hP₀
  change Module.finrank (ZMod 2) (subspaceCommutator (σ.comp c) (fixedSpace (σ.comp c) (zpowers swap45)) P₀) ≤ 1 at hh
  rw [subspaceCommutator_comp_map,fixedSpace_comp_map,hA,hmap] at hh
  exact hh

/-- On either full cover, an elementary Borel actor commuting with the
critical transposition either satisfies the endpoint displacement bound or
moves at most a line of the full fixed hyperplane. -/
theorem borel_cover_control_or_fixed_line
    {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (σ : Representation (ZMod 2) S Y)
    (hm : SixCover.IsNaturalOrCore σ (MonoidHom.id S))
    (u t : S) (ht : t ∈ borel.map (MulAut.conj u).toMonoidHom) (hs : t.IsSwap)
    (P : Subgroup S) (hP : P ≤ borel.map (MulAut.conj u).toMonoidHom)
    (h2 : ∀ g ∈ P, g^2=1) (hab : ∀ g ∈ P, ∀ k ∈ P, Commute g k)
    (hc : ∀ g ∈ P, Commute t g) :
    (subspaceCommutator σ ⊤ P ≤
      subspaceCommutator σ (fixedSpace σ (zpowers t)) P ⊔
        subspaceCommutator σ ⊤ (zpowers t)) ∨
    Module.finrank (ZMod 2)
      (subspaceCommutator σ (fixedSpace σ (zpowers t)) P) ≤ 1 := by
  let f := (MulAut.conj u).toMonoidHom
  obtain ⟨t₀,ht₀,rfl⟩ := ht
  have hs₀ : t₀.IsSwap := by
    have hh : IsConj t₀ ((MulAut.conj u) t₀) := isConj_iff.mpr ⟨u,rfl⟩
    exact Equiv.Perm.isSwap_iff_cycleType.mpr
      ((Equiv.Perm.isConj_iff_cycleType_eq.mp hh).trans (Equiv.Perm.isSwap_iff_cycleType.mp hs))
  let P₀ := P.comap f
  have hmap : P₀.map f = P := map_comap_eq_self_of_surjective (MulAut.conj u).surjective P
  have hP₀ : P₀ ≤ borel := by
    apply (map_le_map_iff_of_injective (f := f) (MulAut.conj u).injective).mp
    rw [hmap]
    exact hP
  have hi : Function.Injective f := (MulAut.conj u).injective
  have h2₀ : ∀ g ∈ P₀, g^2=1 := by
    intro g hg
    apply hi
    simpa only [map_pow,map_one] using h2 (f g) hg
  have hab₀ : ∀ g ∈ P₀, ∀ k ∈ P₀, Commute g k := by
    intro g hg k hk
    change _ * _ = _ * _
    apply hi
    simpa only [map_mul] using (hab (f g) hg (f k) hk).eq
  have hc₀ : ∀ g ∈ P₀, Commute t₀ g := by
    intro g hg
    change _ * _ = _ * _
    apply hi
    simpa only [map_mul] using (hc (f g) hg).eq
  by_cases hsmall : Module.finrank (ZMod 2)
      (subspaceCommutator σ (fixedSpace σ (zpowers ((MulAut.conj u) t₀))) P) ≤ 1
  · exact Or.inr hsmall
  left
  have hlarge := Nat.lt_of_not_ge hsmall
  rcases borel_elementary_pair P₀ hP₀ h2₀ hab₀ t₀ ht₀ hs₀ hc₀ with ⟨hD,htD⟩ | ⟨hpoint,htpoint⟩
  · apply Natural.Exhaustion.LargeDistance.SectionFive.CubeKernelLine.model_comparison σ hm u
      ((MulAut.conj u) t₀) P _ _ hs hlarge
    · simpa only [CFSG.Quasithin.ChapterB.Offenders.SixCorePlane.cube_eq] using
        (show P ≤ D.map f from hmap ▸ map_mono hD)
    · simpa only [CFSG.Quasithin.ChapterB.Offenders.SixCorePlane.cube_eq] using
        (show ((MulAut.conj u) t₀) ∈ D.map (MulAut.conj u).toMonoidHom from mem_map_of_mem (MulAut.conj u).toMonoidHom htD)
  · have he : (pointCore.map (MulAut.conj flagRelabel).toMonoidHom).map f =
        pointCore.map (MulAut.conj (u*flagRelabel)).toMonoidHom := by
      rw [map_map]
      apply congrArg (Subgroup.map · pointCore)
      apply MonoidHom.ext
      intro g
      change u*(flagRelabel*g*flagRelabel⁻¹)*u⁻¹ = (u*flagRelabel)*g*(u*flagRelabel)⁻¹
      group
    exact (hsmall (point_cover_fixed_finrank σ hm (u*flagRelabel) _ P
      (he ▸ hmap ▸ map_mono hpoint) (he ▸ mem_map_of_mem f htpoint) hs)).elim
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "Rg" => edge L R
local notation "W₀" => (⁅centralOmega L R,L.subgroupOf M⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk
local instance : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.of_le (commutator_le_left _ _)
open Representation.NormalElementaryQuotient

include h e hz hk in
private theorem borel_cover_uncontrolled_fixed_card
    (u τ : S) (hτ : τ ∈ borel.map (MulAut.conj u).toMonoidHom) (hs : τ.IsSwap)
    (A P : Subgroup M) (hA : A.map π = zpowers τ)
    (hP : P.map π ≤ borel.map (MulAut.conj u).toMonoidHom)
    (h2 : ∀ g ∈ P.map π, g^2=1)
    (hab : ∀ g ∈ P.map π, ∀ k ∈ P.map π, Commute g k)
    (hc : ∀ g ∈ P.map π, Commute τ g)
    (hescape : ¬ ⁅W₀,P⁆ ≤ ⁅W₀ ⊓ centralizer (A : Set M),P⁆ ⊔ ⁅W₀,A⁆) :
    Nat.card (⁅W₀ ⊓ centralizer (A : Set M),P⁆ : Subgroup M) ≤ 2 := by
  let := h.relative_normal
  let F := W₀ ⊓ centralizer (A : Set M)
  let H := ⁅F,P⁆
  let σ : Representation (ZMod 2) S (Additive W₀) :=
    NormalElementaryQuotient.representation W₀ π (CubicEven.projection_surjective h e hz hk)
      (CubicAction.moved_projection_kernel h e hz hk)
  have hFW : F ≤ W₀ := inf_le_left
  have hHW : H ≤ W₀ := (commutator_mono hFW le_rfl).trans (commutator_le_left _ _)
  have hF : subgroupSpace W₀ F = fixedSpace σ (A.map π) := by
    ext v
    change ((v.toMul : M) ∈ W₀ ∧ (v.toMul : M) ∈ centralizer (A : Set M)) ↔ _
    rw [NormalElementaryQuotient.mem_fixedSpace_image W₀ π
      (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk)]
    exact and_iff_right v.toMul.property
  have htop : subgroupSpace W₀ W₀ = ⊤ := by
    ext v
    exact iff_of_true v.toMul.property (Submodule.mem_top)
  have hcomm (B C : Subgroup M) (hB : B ≤ W₀) :
      subspaceCommutator σ (subgroupSpace W₀ B) (C.map π) = subgroupSpace W₀ ⁅B,C⁆ :=
    (subgroupSpace_commutator W₀ π (CubicEven.projection_surjective h e hz hk)
      (CubicAction.moved_projection_kernel h e hz hk) B C hB).symm
  let : IsElementaryAbelian 2 H := IsElementaryAbelian.of_le hHW
  have hd := borel_cover_control_or_fixed_line σ (moved_subgroup_cover_model h e hz hk)
    u τ hτ hs (P.map π) hP h2 hab hc
  rw [←hA,←hF,←htop,hcomm F P hFW,hcomm W₀ P le_rfl,hcomm W₀ A le_rfl] at hd
  have hdim : Module.finrank (ZMod 2) (subgroupSpace W₀ H) ≤ 1 := by
    rcases hd with hbound | hsmall
    · exfalso
      apply hescape
      rw [←subgroupSpace_sup W₀ hHW (commutator_le_left _ _)] at hbound
      intro x hx
      exact hbound (show Additive.ofMul (⟨x,commutator_le_left W₀ P hx⟩ : W₀) ∈
        subgroupSpace W₀ ⁅W₀,P⁆ from hx)
    · exact hsmall
  calc
    Nat.card H = Nat.card (subgroupSpace W₀ H) :=
      Nat.card_congr (subgroupSpaceEquiv W₀ H hHW).toEquiv
    _ = 2 ^ Module.finrank (ZMod 2) (subgroupSpace W₀ H) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    _ ≤ 2 := Nat.pow_le_pow_right (by decide : 0 < 2) hdim

include h e hz hk in
/-- Failure of the endpoint bound forces a line in the full reverse kernel.
This holds without either small-slice hypothesis, on the original graph and
with both full moving covers. -/
theorem borel_uncontrolled_reverse_kernel_card
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hat : Adjacent Rg a t) (hct : Adjacent Rg c t)
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hescape : ¬ ⁅Z Rg c,Z Rg z⁆ ≤ Z Rg a ⊔ ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆) :
    Nat.card (⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆ : Subgroup (FreeAmalgam Rg)) ≤ 2 := by
  have hb := distance_gt_two h e hz hk
  have hc : color Rg c = false := by
    have h1 := adjacent_color_ne Rg hat
    have h2 := adjacent_color_ne Rg hct
    rw [p.start_color] at h1
    cases hh : color Rg c <;> cases hh' : color Rg t <;> simp_all
  have hfixed : ⁅U Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)),Z Rg c⁆ =
      ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆ := by
    rw [←critical_moving_kernel_eq_fixed h e p]
    exact ((critical_kernel_predecessor_moving h e hz hb p).2.2 _ hbad).symm
  have hcontrol : ¬ ⁅U Rg z,Z Rg c⁆ ≤
      ⁅U Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)),Z Rg c⁆ ⊔ ⁅U Rg z,Z Rg a⁆ := by
    intro hh
    apply hescape
    rw [commutator_comm,critical_predecessor_seed_movement h e hz hb p _ hbad]
    rw [hfixed] at hh
    exact hh.trans (sup_le le_sup_right (by
      rw [commutator_comm]
      exact ((commutator_mono le_rfl (DistanceEight.U_le_Z Rg z)).trans
        (critical_seed_commutator_le h p)).trans le_sup_left))
  let := h.relative_normal
  obtain ⟨i,hi,hir,hiR,hiQ,hiU,hA,hP,hJ,hAr,hPr,hJr,hApi,hPpi,hJpi,hFi,hfix⟩ :=
    borel_predecessor_cover_chart h e hz hk u hR p (Z Rg c) hbad 1 (one_mem _)
  obtain ⟨⟨τ,hτ,hτswap,hτeq⟩,hcrit⟩ :=
    plane_small_critical_chart_actor h e hz hk p hp i hi hiQ hiU hA hAr
  let A := (Z Rg a).comap i
  let P := (Z Rg c).comap i
  have hZcX := (sourceGeometry h).omega_bound c hc (by
    rw [(sourceGeometry h).distance_constant c hc]
    exact sourceDistance_pos h)
  have h2 : ∀ g ∈ P.map π, g^2=1 := by
    rintro _ ⟨g,hg,rfl⟩
    rw [←map_pow]
    have hg2 : g^2=1 := by
      apply hi
      simpa only [map_pow,map_one] using (mem_omegaCenter_iff.mp (hZcX hg)).2.1
    rw [hg2,map_one]
  have hab : ∀ g ∈ P.map π, ∀ k ∈ P.map π, Commute g k := by
    rintro _ ⟨g,hg,rfl⟩ _ ⟨j,hj,rfl⟩
    change _ * _ = _ * _
    rw [←map_mul,←map_mul]
    congr 1
    apply hi
    simp only [map_mul]
    exact ((mem_omegaCenter_iff.mp (hZcX hg)).2.2 (i j)
      (omegaCenter_le _ (hZcX hj))).symm
  have hPcQ : Z Rg c ≤ Q Rg a :=
    ((Z_le_localZSpan Rg _ _).trans (localZSpan_le_V Rg
      (CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.neighbor_distance_le_two hat hct))).trans
        ((sourceGeometry h).V_le_Q hb a p.start_color)
  have hcomm : ∀ g ∈ P.map π, Commute τ g := by
    obtain ⟨j,hj,hje⟩ := hτ
    rintro _ ⟨g,hg,rfl⟩
    rw [←hje]
    change _ * _ = _ * _
    rw [←map_mul,←map_mul]
    congr 1
    apply hi
    simp only [map_mul]
    exact (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg a p.start_color)
      hj (i g) (hPcQ hg)).symm
  have hF : (W₀ ⊓ centralizer (A : Set M)).map i =
      U Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)) := by
    rw [←map_inf_centralizer_of_injective i hi,hiU,hA]
  have hbound := borel_cover_uncontrolled_fixed_card h e hz hk u τ (hApi hτ)
    hτswap A P hτeq hPpi h2 hab hcomm (by
      intro hh
      apply hcontrol
      have hm := map_mono (f := i) hh
      rwa [Subgroup.map_sup,map_commutator W₀ P i,hiU,hP,
        map_commutator _ P i,hF,hP,map_commutator W₀ A i,hiU,hA] at hm)
  rw [←card_map_of_injective hi,map_commutator,hF,hP,hfixed] at hbound
  exact hbound

include h e hz hk in
/-- An uncontrolled small critical endpoint puts its entire reverse kernel
in the proper neighboring Thompson mover, with the resulting full-kernel
commutator fixed by that mover. No forward or predecessor slice bound is used. -/
theorem borel_uncontrolled_reverse_kernel_mover
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hat : Adjacent Rg a t) (hct : Adjacent Rg c t)
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hescape : ¬ ⁅Z Rg c,Z Rg z⁆ ≤ Z Rg a ⊔ ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆) :
    Nat.card (⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆ : Subgroup (FreeAmalgam Rg)) ≤ 2 ∧
      Z Rg z ⊓ Q Rg a ≤ edgeOffenderJoin c t ∧
      ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆ ≤ centralizer (edgeOffenderJoin c t : Set (FreeAmalgam Rg)) := by
  let K := Z Rg z ⊓ Q Rg a
  let H := ⁅K,Z Rg c⁆
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    rw [p.start_color] at hh
    cases he : color Rg t <;> simp_all
  have hc : color Rg c = false := by
    have hh := adjacent_color_ne Rg hct
    rw [ht] at hh
    cases he : color Rg c <;> simp_all
  have hKT : K ≤ Q Rg t := inf_le_right.trans (Q_le_adjacent_h Rg ht hat)
  have hKG : K ≤ stabilizer Rg c := hKT.trans (fun _ hx => hx.2 _ (adjacent_symm Rg hct))
  have hHZ : H ≤ Z Rg c := le_normalizer_iff_commutator_le_right.mp
    (hKG.trans (Z_normalized Rg c))
  let := finite_Z Rg c
  let : Finite H := Finite.of_injective (inclusion hHZ) (inclusion_injective _)
  have hcard := borel_uncontrolled_reverse_kernel_card h e hz hk u hR p hp hat hct hbad hescape
  have hsmall : Nat.card (⁅U Rg c,K⁆ : Subgroup (FreeAmalgam Rg)) ≤ 2 := by
    have hle : ⁅U Rg c,K⁆ ≤ H := by
      dsimp only [H]
      rw [commutator_comm K]
      exact commutator_mono (DistanceEight.U_le_Z Rg c) le_rfl
    exact (card_le_of_le hle).trans hcard
  have hKJ := borel_small_commutator_actor_le_mover h e hz hk u hR hc hct K hKT hsmall
  have hquad : ⁅H,edgeOffenderJoin c t⁆ = ⊥ := by
    apply le_bot_iff.mp
    dsimp only [H]
    rw [commutator_comm K]
    exact (commutator_mono (commutator_mono le_rfl hKJ) le_rfl).trans_eq
      (remaining_edge_full_seed_quadratic h e hz hk u (Or.inr hR) hc hct)
  exact ⟨hcard,hKJ,commutator_eq_bot_iff_le_centralizer.mp hquad⟩
include h e hz hk in
/-- In the centrally generated branch, an uncontrolled endpoint has a
nonzero full-omega kernel line in the starting Baumann slice. Opposite-mover
generation supplies residual centrality in the distinct case; equal movers
put the line in the starting seed. Neither end slice is assumed small. -/
theorem borel_central_uncontrolled_kernel_line
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hat : Adjacent Rg a t) (hct : Adjacent Rg c t)
    (hgen : Q Rg t ⊔ Z Rg z = stabilizer Rg a)
    (hsplit : X Rg a = U Rg a ⊔
      (X Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))))
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hescape : ¬ ⁅Z Rg c,X Rg z⁆ ≤ Z Rg a ⊔ ⁅X Rg z ⊓ Q Rg a,Z Rg c⁆) :
    Nat.card (⁅X Rg z ⊓ Q Rg a,Z Rg c⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
      X Rg z ⊓ Q Rg a ≤ edgeOffenderJoin c t ∧
      ⁅X Rg z ⊓ Q Rg a,Z Rg c⁆ ≤ B Rg a ((sourceGeometry h).Z_normal _) ∧
      (edgeOffenderJoin a t ≠ edgeOffenderJoin c t →
        ⁅X Rg z ⊓ Q Rg a,Z Rg c⁆ ≤ centralizer (Ltilde Rg a : Set (FreeAmalgam Rg))) := by
  have hb := distance_gt_two h e hz hk
  have hXz : X Rg z = Z Rg z := omega_eq_seed_of_central_generation h z p.end_color
    (omega_generation_transport p.start_color p.end_color hsplit)
  rw [hXz] at hescape ⊢
  have hc : color Rg c = false := by
    have h1 := adjacent_color_ne Rg hat
    have h2 := adjacent_color_ne Rg hct
    rw [p.start_color] at h1
    cases hh : color Rg c <;> cases hh' : color Rg t <;> simp_all
  obtain ⟨hcard,hKJ,hHJ⟩ :=
    borel_uncontrolled_reverse_kernel_mover h e hz hk u hR p hp hat hct hbad hescape
  let H := ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆
  have hne : H ≠ ⊥ := by
    intro he
    apply hescape
    have he' : ⁅Z Rg c,Z Rg z ⊓ Q Rg a⁆ = ⊥ := (commutator_comm _ _).trans he
    exact (small_critical_predecessor_commutator h e hz hk hb p hp (Z Rg c) hbad
      (commutator_eq_bot_iff_le_centralizer.mp he')).trans le_sup_left
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    rw [p.start_color] at hh
    cases he : color Rg t <;> simp_all
  have hKG : Z Rg z ⊓ Q Rg a ≤ stabilizer Rg c :=
    (inf_le_right.trans (Q_le_adjacent_h Rg ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg hct))
  have hHc : H ≤ Z Rg c := le_normalizer_iff_commutator_le_right.mp
    (hKG.trans (Z_normalized Rg c))
  let := finite_Z Rg c
  let : Finite H := Finite.of_injective (inclusion hHc) (inclusion_injective _)
  have hpos : 1 < Nat.card H := (one_lt_card_iff_ne_bot H).mpr hne
  have hline : Nat.card H = 2 := by
    change Nat.card H ≤ 2 at hcard
    omega
  have hLa (hneJ : edgeOffenderJoin a t ≠ edgeOffenderJoin c t) :
      H ≤ centralizer (Ltilde Rg a : Set (FreeAmalgam Rg)) := by
    have hcore : ¬ Q Rg a ≤ edgeOffenderJoin c t := by
      intro hcore
      exact borel_opposite_containing_core_nonsplit h e hz hk u hR p.start_color hc
        hat hct hneJ hcore hsplit
    have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
    have hlast : Adjacent Rg z (p.walk.getVert (p.walk.length-1)) := by
      have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
      rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
      exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
    have hlastcol : color Rg (p.walk.getVert (p.walk.length-1)) = true := by
      have hh := adjacent_color_ne Rg hlast
      rw [p.end_color] at hh
      cases he : color Rg (p.walk.getVert (p.walk.length-1)) <;> simp_all
    have hprelast : Adjacent Rg (p.walk.getVert (p.walk.length-2))
        (p.walk.getVert (p.walk.length-1)) := by
      have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
      rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
      exact (cosetGraph_adj Rg _ _).mp hh
    have hZcG : Z Rg c ≤ stabilizer Rg z :=
      (hbad.trans (Q_le_adjacent_h Rg hlastcol hprelast)).trans
        (fun _ hx => hx.2 _ (adjacent_symm Rg hlast))
    have hHz : H ≤ Z Rg z := (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hZcG.trans (Z_normalized Rg z)))
    let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) z p.end_color
    have hHCz : H ≤ centralizer (Z Rg z : Set (FreeAmalgam Rg)) :=
      hHz.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)
    have hLC := (borel_opposite_generation_of_core_not_le h e hz hk u hR p.start_color hc
      hat hct (Z Rg z) hgen hcore).2
    exact le_centralizer_iff.mp
      (hLC.trans (sup_le (le_centralizer_iff.mp hHJ) (le_centralizer_iff.mp hHCz)))
  refine ⟨hline,hKJ,?_,hLa⟩
  have hVG := (sourceGeometry h).V_local a p.start_color (by
      rw [(sourceGeometry h).distance_constant a p.start_color]; exact hb)
  have hHV : H ≤ V Rg a := hHc.trans ((Z_le_localZSpan Rg _ _).trans
    (localZSpan_le_V Rg
      (CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.neighbor_distance_le_two hat hct)))
  by_cases heq : edgeOffenderJoin a t = edgeOffenderJoin c t
  · have hHZ : H ≤ Z Rg a := by
      dsimp only [H]
      rw [←hXz]
      exact (borel_equal_thompson_reverse_kernel_control h e hz hk u hR p hp hc hat hct heq z).1.trans inf_le_left
    intro v hv
    exact (mem_B_iff Rg a _ hVG v).mpr ⟨hHV hv,fun l hl =>
      (le_normalizer_iff_commutator_le_right.mp
        ((Ltilde_le_stabilizer a).trans (Z_normalized Rg a)))
        (commutator_mem_commutator hl (hHZ hv))⟩
  · intro v hv
    apply (mem_B_iff Rg a _ hVG v).mpr
    refine ⟨hHV hv,?_⟩
    intro l hl
    have hz := commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp (hLa heq))
    exact (bot_le : (⊥ : Subgroup (FreeAmalgam Rg)) ≤ Z Rg a)
      (hz ▸ commutator_mem_commutator hl hv)
include h e hz hk in
/-- At a distinct opposite mover, failure of endpoint control constructs the
actual kernel-fixed neighboring span. The component residual normalizes it,
and its intersection with the full moving cover has index at most two.
This retains residual normality, without promoting it to whole-stabilizer
normality or to containment in the Baumann slice. -/
theorem borel_central_uncontrolled_fixed_span
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hat : Adjacent Rg a t) (hct : Adjacent Rg c t)
    (hgen : Q Rg t ⊔ Z Rg z = stabilizer Rg a)
    (hsplit : X Rg a = U Rg a ⊔
      (X Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))))
    (hne : edgeOffenderJoin a t ≠ edgeOffenderJoin c t)
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hescape : ¬ ⁅Z Rg c,X Rg z⁆ ≤ Z Rg a ⊔ ⁅X Rg z ⊓ Q Rg a,Z Rg c⁆) :
    let K := X Rg z ⊓ Q Rg a
    let D := Z Rg c ⊓ centralizer (K : Set (FreeAmalgam Rg))
    D.relIndex (U Rg c) ≤ 2 ∧
      D ⊔ Z Rg a ≤ V Rg a ∧
      Ltilde Rg a ≤ normalizer ((D ⊔ Z Rg a : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
      ⁅D,Z Rg z⁆ ≤ Z Rg a := by
  have hb := distance_gt_two h e hz hk
  have hXz : X Rg z = Z Rg z := omega_eq_seed_of_central_generation h z p.end_color
    (omega_generation_transport p.start_color p.end_color hsplit)
  obtain ⟨hcard,hKJ,hHB,hHC⟩ :=
    borel_central_uncontrolled_kernel_line h e hz hk u hR p hp hat hct hgen hsplit hbad hescape
  dsimp only
  rw [hXz] at hcard hKJ hHB hHC ⊢
  let K := Z Rg z ⊓ Q Rg a
  let D := Z Rg c ⊓ centralizer (K : Set (FreeAmalgam Rg))
  let J := edgeOffenderJoin c t
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    rw [p.start_color] at hh
    cases he : color Rg t <;> simp_all
  have hc : color Rg c = false := by
    have hh := adjacent_color_ne Rg hct
    rw [ht] at hh
    cases he : color Rg c <;> simp_all
  have hKT : K ≤ Q Rg t := inf_le_right.trans (Q_le_adjacent_h Rg ht hat)
  have hKG : K ≤ stabilizer Rg c := hKT.trans (fun _ hx => hx.2 _ (adjacent_symm Rg hct))
  have hHZ : ⁅K,Z Rg c⁆ ≤ Z Rg c := le_normalizer_iff_commutator_le_right.mp
    (hKG.trans (Z_normalized Rg c))
  let := finite_Z Rg c
  let : Finite (⁅K,Z Rg c⁆ : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion hHZ) (inclusion_injective _)
  have hsmall : Nat.card (⁅U Rg c,K⁆ : Subgroup (FreeAmalgam Rg)) ≤ 2 := by
    have hle : ⁅U Rg c,K⁆ ≤ ⁅K,Z Rg c⁆ := by
      rw [commutator_comm K]
      exact commutator_mono (DistanceEight.U_le_Z Rg c) le_rfl
    exact (card_le_of_le hle).trans hcard.le
  have hindex := moving_small_commutator_fixed_index h e hz hk hc K hKG hsmall
  have hDcomm : ⁅D,Z Rg z⁆ ≤ Z Rg a :=
    small_critical_predecessor_commutator h e hz hk hb p hp D
      (inf_le_left.trans hbad) inf_le_right
  have hZcV : Z Rg c ≤ V Rg a := (Z_le_localZSpan Rg _ _).trans
    (localZSpan_le_V Rg
      (CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.neighbor_distance_le_two hat hct))
  have hJT : J ≤ Q Rg t := (remaining_edge_thompson h e hz hk u (Or.inr hR) hc hct).2.2.1
  have hquad : ⁅⁅Z Rg c,J⁆,J⁆ = ⊥ :=
    remaining_edge_full_seed_quadratic h e hz hk u (Or.inr hR) hc hct
  have habelian : ⁅J,J⁆ ≤ centralizer (Z Rg c : Set (FreeAmalgam Rg)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply commutator_commutator_eq_bot_of_rotate
    · simpa only [commutator_comm J (Z Rg c)] using hquad
    · exact hquad
  have hJD : J ≤ normalizer (D : Set (FreeAmalgam Rg)) :=
    abelian_action_preserves_fixed J (Z Rg c) K
      ((hJT.trans (fun _ hx => hx.2 _ (adjacent_symm Rg hct))).trans (Z_normalized Rg c))
      hKJ habelian
  have hJZ : J ≤ normalizer (Z Rg a : Set (FreeAmalgam Rg)) :=
    (hJT.trans (fun _ hx => hx.2 _ (adjacent_symm Rg hat))).trans (Z_normalized Rg a)
  have hZN : Z Rg z ≤ normalizer ((D ⊔ Z Rg a : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) := by
    have hZlocal := critical_Z_le_stabilizer Rg (sourceGeometry h) a p.start_color
      (by rw [(sourceGeometry h).distance_constant a p.start_color]; exact sourceDistance_pos h) p.critical
    have hcomm : ⁅D ⊔ Z Rg a,Z Rg z⁆ ≤ Z Rg a := by
      apply commutator_sup_le_of_relative_normal (stabilizer Rg a)
        D (Z Rg a) (Z Rg z) (Z Rg a) (Z_normalized Rg a)
        ((inf_le_left.trans hZcV).trans ((sourceGeometry h).V_local a p.start_color (by
      rw [(sourceGeometry h).distance_constant a p.start_color]; exact hb)))
        (Z_le_stabilizer Rg a) hDcomm
      exact le_normalizer_iff_commutator_le_left.mp (hZlocal.trans (Z_normalized Rg a))
    exact le_normalizer_iff_commutator_le_left.mpr (hcomm.trans le_sup_right)
  have hcore : ¬ Q Rg a ≤ J := by
    intro hh
    exact borel_opposite_containing_core_nonsplit h e hz hk u hR p.start_color hc
      hat hct hne hh hsplit
  refine ⟨?_,sup_le (inf_le_left.trans hZcV) (Z_le_VBall Rg _ 2),?_,hDcomm⟩
  · change (Z Rg c ⊓ centralizer (K : Set (FreeAmalgam Rg))).relIndex (U Rg c) ≤ 2
    have he : (Z Rg c ⊓ centralizer (K : Set (FreeAmalgam Rg))) ⊓ U Rg c =
        U Rg c ⊓ centralizer (K : Set (FreeAmalgam Rg)) := by
      rw [inf_right_comm,inf_of_le_right (DistanceEight.U_le_Z Rg c)]
    rw [←inf_relIndex_right (Z Rg c ⊓ centralizer (K : Set (FreeAmalgam Rg))) (U Rg c),
      he,inf_relIndex_left]
    exact hindex
  · exact (borel_opposite_generation_of_core_not_le h e hz hk u hR p.start_color hc
      hat hct (Z Rg z) hgen hcore).2.trans
        (sup_le ((le_inf hJD hJZ).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)) hZN)

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

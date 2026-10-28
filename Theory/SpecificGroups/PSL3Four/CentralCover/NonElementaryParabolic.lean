module
public import Theory.SpecificGroups.PSL3.ExceptionalFourCover
public import Theory.GroupTheory.PerfectCentralCoverKernelLowerBound
public import Theory.GroupTheory.CentralSquareCommutator
public import Theory.SpecificGroups.PSL3Four.CentralCover.ElementaryParabolic.Commutator
/-! # Non-elementary central covers of PSL₃(4)
Quotienting by the central squares makes the kernel elementary. The proved
parabolic commutator identity then shows that an abelian original radical
would have exponent two, contradicting the non-elementary covering kernel.
Irreducibility and faithfulness of the actual affine plane imply that the
Sylow center is precisely the covering kernel. All field, parabolic and
quotient maps remain the literal native maps; no covering classification
or additional local geometry is assumed.
Source: Aschbacher--Smith I.2.2(3a), printed pp.409--411, used in 2.5.7. -/
public section
open Subgroup PerfectCentralCovering
open scoped commutatorElement IsMulCommutative
namespace Matrix.PSL3Four.NonElementaryKernel
variable {E : Type*} [Group E] [Group.IsPerfect E]
theorem kernel_pow_four (f : E →* PSL) (hf:Function.Surjective f)
    (hc:f.ker≤center E) (hk:IsPGroup 2 f.ker) (z:E) (hz:z∈f.ker) : z^4=1 := by
  let : Group.IsPerfect PSL := Atlas.psl_perfect (F:=F) 3 (by decide)
  obtain ⟨a,ha,_⟩ := universalProjection_existsUnique_lift f hf hc
  have hs : Function.Surjective a :=
    surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
      f a (ha ▸ universalProjection_surjective PSL) hc
  obtain ⟨u,hu⟩ := hs z
  have huk : u∈(universalProjection PSL).ker := by
    change universalProjection PSL u=1
    rw [← ha]
    change f (a u)=1
    rw [hu]
    exact hz
  have hum : (⟨u,huk⟩:(universalProjection PSL).ker)^12=1 := by
    apply Matrix.PSL3.ExceptionalFourCover.canonicalKernelEquiv.injective
    rw [map_pow,map_one]
    exact (by decide +kernel : ∀ v : Matrix.PSL3.ExceptionalFourCover.Multiplier, v^12=1) _
  have hz12 : z^12=1 := by
    rw [←hu,←map_pow,show u^12=1 from congrArg Subtype.val hum,map_one]
  have hz4 : (⟨z,hz⟩:f.ker)^4=1 := by
    apply (hk.powEquiv (by decide : Nat.Coprime 2 3)).injective
    change ((⟨z,hz⟩:f.ker)^4)^3=1^3
    rw [←pow_mul]
    exact Subtype.ext (by simpa only [Subgroup.coe_pow,Subgroup.coe_one,one_pow] using hz12)
  exact congrArg Subtype.val hz4
end Matrix.PSL3Four.NonElementaryKernel


namespace Matrix.PSL3Four.NonElementaryKernel
open ElementaryParabolic
variable {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
/-- An abelian full parabolic core forces the covering kernel elementary. -/
theorem kernel_pow_two_of_abelian_core (f:E→*PSL) (hf:Function.Surjective f)
    (hc:f.ker≤center E) (hk:IsPGroup 2 f.ker) (b:Bool)
    [IsMulCommutative (pCore 2 (liftedParabolic f b))] :
    ∀z∈f.ker,z^2=1 := by
  let : IsMulCommutative f.ker := ⟨⟨fun x y => Subtype.ext (mem_center_iff.mp (hc x.property) y).symm⟩⟩
  let : CommGroup f.ker := IsMulCommutative.instCommGroup
  let W : Subgroup E := (powMonoidHom 2 : f.ker→*f.ker).range.map f.ker.subtype
  have hWker : W≤f.ker := by
    rintro _ ⟨w,hw,rfl⟩
    exact w.property
  have hW2 : ∀w∈W,w^2=1 := by
    rintro _ ⟨w,⟨v,hv⟩,rfl⟩
    have hv' : (v:E)^2=(w:E) := congrArg Subtype.val hv
    change (w:E)^2=1
    rw [←hv',←pow_mul]
    exact kernel_pow_four f hf hc hk v v.property
  let : W.Normal := ⟨fun x hx y => by
    rw [mem_center_iff.mp (hc (hWker hx)) y,mul_inv_cancel_right]
    exact hx⟩
  let q := QuotientGroup.mk' W
  let g : E ⧸ W →* PSL := QuotientGroup.lift W f hWker
  have hg : Function.Surjective g := QuotientGroup.lift_surjective_of_surjective W f hf hWker
  have hgker : g.ker=f.ker.map q := QuotientGroup.ker_lift W f hWker
  have hgc : g.ker≤center (E ⧸ W) := by
    rw [hgker]
    rintro _ ⟨x,hx,rfl⟩
    apply mem_center_iff.mpr
    intro y
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective W y
    exact (map_mul q y x).symm.trans
      ((congrArg q (mem_center_iff.mp (hc hx) y)).trans (map_mul q x y))
  have hgs : ∀z∈g.ker,z^2=1 := by
    rw [hgker]
    rintro _ ⟨z,hz,rfl⟩
    rw [←map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨⟨z^2,f.ker.pow_mem hz 2⟩,⟨⟨z,hz⟩,rfl⟩,rfl⟩
  let : Group.IsPerfect (E ⧸ W) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective W)
  let P := liftedParabolic f b
  let P' := liftedParabolic g b
  let r : P→*P' := (q.comp P.subtype).codRestrict P' (fun x=>x.property)
  have hr : Function.Surjective r := by
    intro y
    obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective W (y:E ⧸ W)
    have hp : x∈P := by
      change f x∈Matrix.PSL3.RootPlaneGeometry.parabolic F b
      have hh : g (q x)∈Matrix.PSL3.RootPlaneGeometry.parabolic F b := hx.symm ▸ y.property
      exact hh
    exact ⟨⟨x,hp⟩,Subtype.ext hx⟩
  have hr2 : ∀x∈r.ker,x^2=1 := by
    intro x hx
    have hh : (x:E)∈W := (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hx)
    exact Subtype.ext (hW2 x hh)
  have hrk : IsPGroup 2 r.ker := fun x=> ⟨1,by simpa using Subtype.ext (hr2 x x.property)⟩
  have hmap : (pCore 2 P).map r=pCore 2 P' := by
    rw [← r.comap_pCore_of_ker_isPGroup hr hrk,map_comap_eq_self]
    rw [MonoidHom.range_eq_top.mpr hr]
    exact le_top
  have hPs : ∀x∈pCore 2 P,x^2∈center P := by
    intro x hx
    have hpk : IsPGroup 2 (parabolicAffine f b).ker := by
      rw [parabolicAffine_ker]
      exact hk.comap_of_injective _ P.subtype_injective
    have hh := (parabolicAffine f b).comap_pCore_of_ker_isPGroup
      (parabolicAffine_surjective f hf b) hpk
    have him := hh.ge hx
    rw [mem_comap,Matrix.SL2.affine_twoCore_eq] at him
    have hsq := elemPow_eq_one_of_isElementaryAbelian (p:=2) _ him
    have hhker : x^2∈(parabolicAffine f b).ker := by
      rw [MonoidHom.mem_ker,map_pow]
      exact hsq
    rw [parabolicAffine_ker] at hhker
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_center_iff.mp (hc hhker) y)
  have hR2 : ∀x∈pCore 2 P,x^2=1 :=
    Theory.GroupTheory.CentralSquares.pow_two_of_full_commutator_image r hr hr2
      (pCore 2 P) hPs (by rw [hmap]; exact parabolicCore_commutator g hg hgc hgs b)
  intro z hz
  have hzP : z∈P := by
    change f z∈Matrix.PSL3.RootPlaneGeometry.parabolic F b
    rw [show f z=1 from hz]
    exact one_mem _
  have hpk : IsPGroup 2 (f.ker.subgroupOf P) := hk.comap_of_injective _ P.subtype_injective
  have hle : f.ker.subgroupOf P≤pCore 2 P := le_sSup ⟨inferInstance,hpk⟩
  have hzR : (⟨z,hzP⟩:P)∈pCore 2 P := hle hz
  exact congrArg Subtype.val (hR2 ⟨z,hzP⟩ hzR)
end Matrix.PSL3Four.NonElementaryKernel
namespace Matrix.SL2
open Matrix.PSL3Four.ElementaryParabolic
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {P : Type*} [Group P] [Finite P]
/-- For a central affine cover, an abelian or central two-core are the only
possibilities for its center image in the irreducible natural plane. -/
theorem affine_core_center_le_kernel (f:P→*Affine F) (hf:Function.Surjective f)
    (hk:IsPGroup 2 f.ker) (hc:f.ker≤center P)
    (hna:¬IsMulCommutative (pCore 2 P)) :
    (center (pCore 2 P)).map (pCore 2 P).subtype≤f.ker := by
  let R := pCore 2 P
  let v := coreVectorMap F f hf hk
  let Z := (center R).map v
  have hinv : ∀g a,a∈Z→naturalAction F g a∈Z := by
    intro g a ha
    obtain ⟨x,hx,rfl⟩ := ha
    obtain ⟨u,hu⟩ := hf (SemidirectProduct.inr g)
    have hx' : MulAut.conjNormal u x∈center R :=
      (centerCongr (MulAut.conjNormal u) ⟨x,hx⟩).property
    refine ⟨MulAut.conjNormal u x,hx',?_⟩
    rw [coreVectorMap_conjugate,hu]
    rfl
  rcases naturalAction_irreducible F Z hinv with hb | ht
  · rintro _ ⟨x,hx,rfl⟩
    have hv : v x=1 := by
      have hh : v x∈Z := mem_map_of_mem v hx
      rwa [hb,mem_bot] at hh
    change f (x:P)=1
    rw [←coreVectorMap_inl F f hf hk x,hv,map_one]
  · exfalso
    apply hna
    have hcenter : ∀x:R,x∈center R := by
      intro x
      obtain ⟨y,hy,hyx⟩ := (show v x∈Z from ht ▸ mem_top _)
      have hxy : x*y⁻¹∈v.ker := by rw [MonoidHom.mem_ker,map_mul,map_inv,hyx,mul_inv_cancel]
      rw [coreVectorMap_ker F f hf hk hc] at hxy
      have hz : x*y⁻¹∈center R := by
        rw [mem_center_iff]
        intro r
        exact Subtype.ext (mem_center_iff.mp hxy r)
      have hm := (center R).mul_mem hz hy
      simpa only [inv_mul_cancel_right] using hm
    exact ⟨⟨fun x y => (mem_center_iff.mp (hcenter x) y).symm⟩⟩

/-- A central cover of the affine natural action has no extra elements
centralizing its two-core outside that core. -/
theorem affine_core_centralizer_le (f:P→*Affine F) (hf:Function.Surjective f)
    (hk:IsPGroup 2 f.ker) : centralizer (pCore 2 P:Set P)≤pCore 2 P := by
  intro x hx
  have ha : naturalAction F (f x).right=1 := by
    apply MulEquiv.ext
    intro v
    obtain ⟨r,hr⟩ := coreVectorMap_surjective F f hf hk v
    have he : MulAut.conjNormal x r=r := by
      apply Subtype.ext
      change x*(r:P)*x⁻¹=(r:P)
      rw [←hx r r.property,mul_inv_cancel_right]
    have hh := coreVectorMap_conjugate F f hf hk x r
    rw [he,hr] at hh
    exact hh.symm
  have hr : (f x).right=1 := naturalAction_injective F (by simpa only [map_one] using ha)
  rw [← f.comap_pCore_of_ker_isPGroup hf hk,mem_comap,affine_twoCore_eq]
  exact hr
end Matrix.SL2
namespace Matrix.PSL3Four.NonElementaryKernel
open ElementaryParabolic
variable {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
theorem center_sylow_le_kernel_of_contained (f:E→*PSL) (hf:Function.Surjective f)
    (hc:f.ker≤center E) (hk:IsPGroup 2 f.ker) (b:Bool)
    (hne:∃z∈f.ker,z^2≠1) (S:Sylow 2 E)
    (hSP:(S:Subgroup E)≤liftedParabolic f b) :
    (center S).map (S:Subgroup E).subtype≤f.ker := by
  let P := liftedParabolic f b
  let a := parabolicAffine f b
  have ha : Function.Surjective a := parabolicAffine_surjective f hf b
  have hak : IsPGroup 2 a.ker := by
    rw [parabolicAffine_ker]
    exact hk.comap_of_injective _ P.subtype_injective
  have hac : a.ker≤center P := by
    rw [parabolicAffine_ker]
    intro x hx
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_center_iff.mp (hc hx) y)
  have hna : ¬IsMulCommutative (pCore 2 P) := by
    intro h
    let := h
    obtain ⟨z,hz,hz2⟩ := hne
    exact hz2 (kernel_pow_two_of_abelian_core f hf hc hk b z hz)
  have hR : (pCore 2 P).map P.subtype≤(S:Subgroup E) := by
    have hh := pCore_isPGroup.le_sylow_of_normal (S.subtype hSP)
    rintro _ ⟨x,hx,rfl⟩
    exact hh hx
  rintro _ ⟨z,hz,rfl⟩
  let zP : P := ⟨z,hSP z.property⟩
  have hzC : zP∈centralizer (pCore 2 P:Set P) := by
    intro r hr
    exact Subtype.ext (congrArg (fun u:S=>(u:E)) (mem_center_iff.mp hz ⟨r,hR (mem_map_of_mem P.subtype hr)⟩))
  have hzR : zP∈pCore 2 P := Matrix.SL2.affine_core_centralizer_le a ha hak hzC
  have hzz : (⟨zP,hzR⟩:pCore 2 P)∈center (pCore 2 P) := by
    rw [mem_center_iff]
    intro r
    exact Subtype.ext (hzC r r.property)
  have hzker := Matrix.SL2.affine_core_center_le_kernel a ha hak hac hna
    (mem_map_of_mem (pCore 2 P).subtype hzz)
  rw [parabolicAffine_ker] at hzker
  exact hzker

theorem center_sylow_le_kernel (f:E→*PSL) (hf:Function.Surjective f)
    (hc:f.ker≤center E) (hk:IsPGroup 2 f.ker)
    (hne:∃z∈f.ker,z^2≠1) (S:Sylow 2 E) :
    (center S).map (S:Subgroup E).subtype≤f.ker := by
  let T : Sylow 2 PSL := S.mapSurjective (f:=f) hf
  let U := Matrix.PSL3.LinearThree.unipotentSylow F (n:=2) (by decide) (by exact card_F)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL T U
  let e : PSL≃*PSL := MulAut.conj g
  let f' := e.toMonoidHom.comp f
  have heker : f'.ker=f.ker := by ext x; exact e.injective.eq_iff' (by simp)
  have heS : (S:Subgroup E).map f'=Matrix.PSL3.LinearThree.unipotent F := by
    rw [← Subgroup.map_map]
    exact congrArg Sylow.toSubgroup hg
  have hSP : (S:Subgroup E)≤liftedParabolic f' true := by
    intro x hx
    have hh : f' x∈Matrix.PSL3.LinearThree.unipotent F :=
      heS ▸ mem_map_of_mem f' hx
    change f' x∈Matrix.PSL3.RootPlaneGeometry.parabolic F true
    rw [native_parabolic_eq_local]
    exact Matrix.PSL3.LinearThree.unipotent_le_pointLocal F hh
  rw [←heker]
  exact center_sylow_le_kernel_of_contained f' (e.surjective.comp hf)
    (heker ▸ hc) (heker.symm ▸ hk) true (heker.symm ▸ hne) S hSP
end Matrix.PSL3Four.NonElementaryKernel

namespace Matrix.PSL3Four.NonElementaryKernel
open ElementaryParabolic
variable {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
theorem source_nonElementary_center (e:E ⧸ center E ≃* PSL)
    (hk:IsPGroup 2 (center E)) (hphi:frattini (center E)≠⊥) (S:Sylow 2 E) :
    (center S).map (S:Subgroup E).subtype=center E ∧
    ∀b:Bool,¬IsMulCommutative (pCore 2 (liftedParabolic (centerProjection e) b)) := by
  let f := centerProjection e
  have hc : f.ker≤center E := (centerProjection_ker e).le
  have hker : IsPGroup 2 f.ker := (centerProjection_ker e).symm ▸ hk
  have hne : ∃z∈f.ker,z^2≠1 := by
    by_contra! hh
    let : Fact (IsPGroup 2 (center E)) := ⟨hk⟩
    let : IsElementaryAbelian 2 (center E) := {
      toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun z=>
        Subtype.ext (hh z ((centerProjection_ker e).symm ▸ z.property))) }
    exact hphi (frattini_eq_bot_of_isElementaryAbelian (p:=2))
  refine ⟨le_antisymm ((center_sylow_le_kernel f (centerProjection_surjective e) hc hker hne S).trans
      (centerProjection_ker e).le) ?_,?_⟩
  · intro z hz
    have hzS := hk.le_sylow_of_normal S hz
    exact ⟨⟨z,hzS⟩,mem_center_iff.mpr (fun s=>Subtype.ext (mem_center_iff.mp hz s)),rfl⟩
  · intro b hn
    let := hn
    obtain ⟨z,hz,hz2⟩ := hne
    exact hz2 (kernel_pow_two_of_abelian_core f (centerProjection_surjective e) hc hker b z hz)
end Matrix.PSL3Four.NonElementaryKernel

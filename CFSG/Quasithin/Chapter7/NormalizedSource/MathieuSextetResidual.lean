module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuCocodeSylow
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Layers.CoordinateTransport
public import Theory.Representation.HexacodeAction.Cover
public import Theory.Mathieu.M24.LocalGeometry.Stabilizers
public import Theory.Mathieu.M24.LocalGeometry.SubnormalSextet
public import Theory.GroupTheory.SolvableResidual.Transport
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import CFSG.Quasithin.Chapter8.Section02.Centralizer.Definitions
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy

/-!
# The original M24 cocode point centralizer

The unique nonzero cocode vector fixed by a Sylow two-subgroup is the
common tetrad class of a concrete sextet. Its stabilizer is therefore the
literal sextet stabilizer. The perfect residual of the full hexacode
automorphism group is its even subgroup, the nonsplit triple cover 3.A₆.
Surjective residual maps and two-core quotient maps retain this full cover
through an arbitrary two-group kernel. Relative normality then makes the
original embedded point residual a C-component of C_{N_G(L)}(z). The cubic
scalar absorbs every native translation into the perfect residual; its
full two-core, and the original two-core, therefore cover all 64 translations.

NonFFSourceMathieuM24Centralizer constructs the marking on the original
chosen-module central involution. These results prove source 8.2.11(1)
and the group quotient in (2); the module factors, transvection action,
normal closure and ambient J4 recognition remain with
qt-d-1222-nonff-mathieu. Source: Aschbacher–Smith H.15.3 and 8.2.11,
printed pp.400,722, refs/quasithin.pdf.

The imported affine hexacode coordinates are by Gerald Höhn and ATLAS
contributors, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917, under the
ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open MathieuCode MathieuCode.SextetLayers.CoordinateTransport Atlas.Codes
open Sporadic.Mathieu.M24LocalGeometry.Stabilizers
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextet

private theorem hex_residual : solvableResidual HexAutomorphisms = hexSign.ker := by
  let : Group.IsPerfect HexEvenAutomorphisms := Hexacode.even_isPerfect
  apply le_antisymm
  · intro x hx
    have hm := map_solvableResidual_le hexSign (mem_map_of_mem hexSign hx)
    rw [solvableResidual_eq_bot] at hm
    exact hm
  · exact le_solvableResidual_of_isPerfect hexSign.ker

private theorem hex_even_core : pCore 2 HexEvenAutomorphisms = ⊥ := by
  have he := (inferInstance : hexSign.ker.Normal).isSubnormal.pCore_subgroupOf 2
  rw [SextetCore.hex_core,bot_subgroupOf] at he
  exact he.symm

/-- A cover of the full affine sextet quotient has the actual triple-six
quotient on its perfect residual, even with a noncentral two-group kernel. -/
theorem residual_core_quotient {A : Type*} [Group A] [Finite A]
    (f : A →* HexAutomorphisms) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    Nonempty ((solvableResidual A ⧸ pCore 2 (solvableResidual A)) ≃* HexEvenAutomorphisms) := by
  have hm : (solvableResidual A).map f = hexSign.ker :=
    (map_solvableResidual_eq f hf).trans hex_residual
  let r : solvableResidual A →* HexEvenAutomorphisms :=
    (f.comp (solvableResidual A).subtype).codRestrict _
      (fun x => by
        change f x.val ∈ hexSign.ker
        rw [←hm]
        exact mem_map_of_mem f x.property)
  have hr : Function.Surjective r := by
    intro y
    obtain ⟨x,hx,hxy⟩ := (show y.val ∈ (solvableResidual A).map f from hm.symm ▸ y.property)
    exact ⟨⟨x,hx⟩,Subtype.ext hxy⟩
  have hkr : IsPGroup 2 r.ker := by
    have he : r.ker = f.ker.subgroupOf (solvableResidual A) := by
      ext x
      exact Subtype.ext_iff
    rw [he]
    exact hk.comap_subtype
  exact ⟨(r.pCoreQuotientEquiv hr hkr).trans
    ((QuotientGroup.quotientMulEquivOfEq hex_even_core).trans QuotientGroup.quotientBot)⟩

/-- The intrinsic quotient of the native sextet residual is the nonsplit
triple cover of A₆, with no suppression of its cubic center. -/
theorem native_residual_quotient (S : Sextet) :
    Nonempty ((solvableResidual (sextetStabilizer S) ⧸
      pCore 2 (solvableResidual (sextetStabilizer S))) ≃* HexEvenAutomorphisms) := by
  apply residual_core_quotient (nativeQuotient S) (nativeQuotient_surjective S)
  change IsPGroup 2 (sextetQuotient.ker.comap (nativeStabilizerEquiv S).symm.toMonoidHom)
  exact (SextetCore.atlas_kernel_elementary.isPGroup 2 _).comap_of_injective _
    (nativeStabilizerEquiv S).symm.injective

/-- The nonzero Sylow-fixed cocode vector is a tetrad class. -/
theorem sylow_fixed_sextet (P : Sylow 2 M24) (v : Cocode) (hv : v ≠ 0)
    (hfix : ∀ g : P, cocodeRepresentation g.val v = v) :
    ∃ S : Sextet, v = sextetVector S ∧ (P : Subgroup M24) ≤ sextetStabilizer S := by
  obtain ⟨g,hg⟩ := SextetCore.exists_conjugate_standardSylow P
  let S := conjugateSextet g standardSextet
  have hP : (P : Subgroup M24) ≤ sextetStabilizer S := by
    rw [conjugateSextet_stabilizer,←hg]
    exact map_mono SextetCore.standardSylow_le_stabilizer
  let x : fixedSpace cocodeRepresentation P := ⟨v,hfix⟩
  let y : fixedSpace cocodeRepresentation P :=
    ⟨sextetVector S,fun k => sextetVector_fixed S ⟨k,hP k.property⟩⟩
  have hx : x ≠ 0 := fun he => hv (congrArg Subtype.val he)
  have hy : y ≠ 0 := fun he => sextetVector_ne_zero S (congrArg Subtype.val he)
  let := Fintype.ofFinite (fixedSpace cocodeRepresentation P)
  have hn : 1 < Nat.card (fixedSpace cocodeRepresentation P) := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card_iff_nontrivial.mpr ⟨⟨x,0,hx⟩⟩
  have hc : Nat.card (fixedSpace cocodeRepresentation P) = 2 :=
    Nat.le_antisymm (MathieuCocodeSylow.fixed_card_le_two P) (by omega)
  obtain ⟨w,hw,hu⟩ := (Nat.card_eq_two_iff' (0 : fixedSpace cocodeRepresentation P)).mp hc
  exact ⟨S,congrArg Subtype.val ((hu x hx).trans (hu y hy).symm),hP⟩

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Equivariance identifies the full original centralizer with a cover of
its native sextet stabilizer; the kernel retains its two-group property. -/
theorem marked_centralizer_action
    (W L : Subgroup G) [IsElementaryAbelian 2 W]
    (hLW : L ≤ normalizer (W : Set G))
    (q : L →* M24) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (F : Additive W ≃ₗ[ZMod 2] Cocode)
    (hF : ∀ (l : L) (w : W),
      F (Additive.ofMul (W.normalizerMonoidHom ⟨l,hLW l.property⟩ w)) =
        cocodeRepresentation (q l) (F (Additive.ofMul w)))
    (z : W) (S : Sextet) (hz : F (Additive.ofMul z) = sextetVector S) :
    ∃ c : (L ⊓ centralizer ({(z : G)} : Set G) : Subgroup G) →* sextetStabilizer S,
      Function.Surjective c ∧ IsPGroup 2 c.ker ∧
      ∀ l, (c l).val = q ⟨l,l.property.1⟩ := by
  let C := L ⊓ centralizer ({(z : G)} : Set G)
  have hf (l : L) : q l ∈ sextetStabilizer S ↔
      l.val ∈ centralizer ({(z : G)} : Set G) := by
    rw [←sextetVector_stabilizer]
    change cocodeRepresentation (q l) (sextetVector S) = sextetVector S ↔ _
    rw [←hz,←hF,F.injective.eq_iff,mem_centralizer_singleton_iff]
    change (Additive.ofMul ⟨l.val*z.val*l.val⁻¹,_⟩ : Additive W) =
      Additive.ofMul z ↔ l.val*z.val=z.val*l.val
    rw [Additive.ofMul.injective.eq_iff,Subtype.ext_iff,mul_inv_eq_iff_eq_mul]
  let j : C →* L := inclusion inf_le_left
  let c : C →* sextetStabilizer S := (q.comp j).codRestrict _
    (fun l => (hf (j l)).mpr l.property.2)
  refine ⟨c,?_,?_,fun _ => rfl⟩
  · intro y
    obtain ⟨l,hl⟩ := hq y.val
    have hc : l.val ∈ C := ⟨l.property,(hf l).mp (hl.symm ▸ y.property)⟩
    exact ⟨⟨l,hc⟩,Subtype.ext hl⟩
  · have he : c.ker = q.ker.comap j := by
      ext l
      exact Subtype.ext_iff
    rw [he]
    exact hk.comap_of_injective j (inclusion_injective _)

/-- Removing the full intrinsic two-core of the original point residual
gives the native nonsplit 3.A₆, through the same centralizer marking. -/
theorem marked_residual_quotient (L : Subgroup G) (z : G) (S : Sextet)
    (c : (L ⊓ centralizer ({z} : Set G) : Subgroup G) →* sextetStabilizer S)
    (hc : Function.Surjective c) (hk : IsPGroup 2 c.ker) :
    Nonempty ((Chapter8.Section02.Centralizer.localResidual L z ⧸
      pCore 2 (Chapter8.Section02.Centralizer.localResidual L z)) ≃* HexEvenAutomorphisms) := by
  let C := L ⊓ centralizer ({z} : Set G)
  let e : solvableResidual C ≃* Chapter8.Section02.Centralizer.localResidual L z :=
    (solvableResidual C).equivMapOfInjective C.subtype C.subtype_injective
  obtain ⟨m⟩ := native_residual_quotient S
  exact ⟨(e.symm.toMonoidHom.pCoreQuotientEquiv e.symm.surjective
      (IsPGroup.ker_isPGroup_of_injective e.symm.injective)).trans
    ((c.solvableResidualMap.pCoreQuotientEquiv (c.solvableResidualMap_surjective hc)
      (c.solvableResidualMap_ker_isPGroup hk)).trans m)⟩

omit [Finite G] in
/-- The relative normality used by the source is inside C_{N_G(L)}(z). -/
theorem residual_normalized (L : Subgroup G) (z : G) :
    normalizer (L : Set G) ⊓ centralizer ({z} : Set G) ≤
      normalizer (Chapter8.Section02.Centralizer.localResidual L z : Set G) := by
  apply le_trans ?_ (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))
  exact (le_inf inf_le_left
    (inf_le_right.trans (centralizer ({z} : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf

private theorem perfect_twoPerfect {A : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] : IsPPerfect 2 A := by
  intro N hN hq
  let : N.Normal := hN
  by_contra hne
  let : Nontrivial (A ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (A ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent (A ⧸ N) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (A ⧸ N) inferInstance

/-- The actual point residual is a C-component in the original relative
centralizer, retaining the nonsplit triple-six quotient. -/
theorem marked_residual_component (L : Subgroup G) (z : G)
    (e : (Chapter8.Section02.Centralizer.localResidual L z ⧸
      pCore 2 (Chapter8.Section02.Centralizer.localResidual L z)) ≃* HexEvenAutomorphisms) :
    ((Chapter8.Section02.Centralizer.localResidual L z).subgroupOf
      (normalizer (L : Set G) ⊓ centralizer ({z} : Set G))).IsCComponent := by
  let R := Chapter8.Section02.Centralizer.localResidual L z
  let M := normalizer (L : Set G) ⊓ centralizer ({z} : Set G)
  have hRM : R ≤ M := (Chapter8.Section02.Centralizer.localResidual_le L z).trans
    (inf_le_inf_right _ L.le_normalizer)
  let : (R.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer
    (residual_normalized L z)
  let : Group.IsPerfect R := Group.IsPerfect.map _
  let : IsQuasisimple HexEvenAutomorphisms := Hexacode.even_isQuasisimple
  let : IsQuasisimple (R ⧸ pCore 2 R) := IsQuasisimple.of_mulEquiv e.symm
  have ht := isCComponent_top_of_isPPerfect_of_quasisimple_quotient
    (pCore 2 R) (pCore_isPGroup (p := 2)) (perfect_twoPerfect (A := R))
  have htop : (⊤ : Subgroup (R.subgroupOf M)).IsCComponent := by
    simpa using ht.map_equiv (subgroupOfEquivOfLe hRM).symm
  simpa only [←MonoidHom.range_eq_map,range_subtype] using
    htop.map_subtype (inferInstance : (R.subgroupOf M).Normal).isSubnormal

private theorem native_kernel_two (S : Sextet) : IsPGroup 2 (nativeQuotient S).ker := by
  change IsPGroup 2 (sextetQuotient.ker.comap (nativeStabilizerEquiv S).symm.toMonoidHom)
  exact (SextetCore.atlas_kernel_elementary.isPGroup 2 _).comap_of_injective _
    (nativeStabilizerEquiv S).symm.injective

/-- The native hexacode projection has precisely the intrinsic two-core
as kernel. -/
theorem native_core_kernel (S : Sextet) :
    pCore 2 (sextetStabilizer S) = (nativeQuotient S).ker := by
  have he := (nativeQuotient S).comap_pCore_of_ker_isPGroup
    (nativeQuotient_surjective S) (native_kernel_two S)
  rw [SextetCore.hex_core,MonoidHom.comap_bot] at he
  exact he.symm

/-- The cubic scalar in the perfect residual absorbs all native
translations, so the full sextet two-core lies in that residual. -/
theorem native_core_le_residual (S : Sextet) :
    pCore 2 (sextetStabilizer S) ≤ solvableResidual (sextetStabilizer S) := by
  let e := nativeStabilizerEquiv S
  let : Group.IsPerfect HexEvenAutomorphisms := Hexacode.even_isPerfect
  have hz : hexZ ∈ (solvableResidual SextetStabilizer).map sextetQuotient := by
    rw [map_solvableResidual_eq sextetQuotient sextetQuotient_surjective]
    exact le_solvableResidual_of_isPerfect hexSign.ker hexSign_Z
  have hk := SubnormalSextet.translations_le_of_scalar_mem
    (solvableResidual SextetStabilizer) (inferInstance : (solvableResidual SextetStabilizer).Normal).isSubnormal hz
  intro x hx
  rw [native_core_kernel] at hx
  have hx' : e.symm x ∈ sextetQuotient.ker := hx
  have hm := mem_map_of_mem e.toMonoidHom (hk hx')
  rw [map_solvableResidual_eq e.toMonoidHom e.surjective] at hm
  simpa only [MulEquiv.coe_toMonoidHom,MulEquiv.apply_symm_apply] using hm

/-- The embedded two-core of the native residual is the full translation
kernel; passing to the perfect residual loses none of its 64 translations. -/
theorem native_residual_core (S : Sextet) :
    (pCore 2 (solvableResidual (sextetStabilizer S))).map
      (solvableResidual (sextetStabilizer S)).subtype = (nativeQuotient S).ker := by
  rw [←(inferInstance : (solvableResidual (sextetStabilizer S)).Normal).isSubnormal.pCore_subgroupOf 2,
    map_subgroupOf_eq_of_le (native_core_le_residual S),native_core_kernel]


/-- The same literal original residual maps onto the native residual and
its full two-core maps onto every native translation. -/
theorem marked_residual_core_action (L : Subgroup G) (z : G) (S : Sextet)
    (c : (L ⊓ centralizer ({z} : Set G) : Subgroup G) →* sextetStabilizer S)
    (hc : Function.Surjective c) (hk : IsPGroup 2 c.ker) :
    ∃ r : Chapter8.Section02.Centralizer.localResidual L z →* sextetStabilizer S,
      r.range = solvableResidual (sextetStabilizer S) ∧ IsPGroup 2 r.ker ∧
      (pCore 2 (Chapter8.Section02.Centralizer.localResidual L z)).map r =
        (nativeQuotient S).ker ∧
      ∀ x, r x = c (inclusion (Chapter8.Section02.Centralizer.localResidual_le L z) x) := by
  let C := L ⊓ centralizer ({z} : Set G)
  let R := Chapter8.Section02.Centralizer.localResidual L z
  let N := solvableResidual (sextetStabilizer S)
  let e : solvableResidual C ≃* R :=
    (solvableResidual C).equivMapOfInjective C.subtype C.subtype_injective
  let f : R →* N := c.solvableResidualMap.comp e.symm.toMonoidHom
  have hf : Function.Surjective f := (c.solvableResidualMap_surjective hc).comp e.symm.surjective
  have hfk : IsPGroup 2 f.ker := by
    change IsPGroup 2 (c.solvableResidualMap.ker.comap e.symm.toMonoidHom)
    exact (c.solvableResidualMap_ker_isPGroup hk).comap_of_injective _ e.symm.injective
  let r := N.subtype.comp f
  have hrk : r.ker = f.ker := MonoidHom.ker_comp_of_injective _ _ N.subtype_injective
  have hm : (pCore 2 R).map f = pCore 2 N := by
    rw [←f.comap_pCore_of_ker_isPGroup hf hfk,map_comap_eq_self]
    rw [f.range_eq_top_of_surjective hf]
    exact le_top
  refine ⟨r,?_,hrk.symm ▸ hfk,?_,?_⟩
  · rw [MonoidHom.range_comp,f.range_eq_top_of_surjective hf,←MonoidHom.range_eq_map,range_subtype]
  · change (pCore 2 R).map (N.subtype.comp f) = _
    rw [←map_map,hm]
    exact native_residual_core S
  · intro x
    have he : (e.symm x).val = inclusion (Chapter8.Section02.Centralizer.localResidual_le L z) x := by
      apply Subtype.ext
      exact congrArg (fun y : R => (y : G)) (e.apply_symm_apply x)
    change c (e.symm x).val = _
    rw [he]

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextet

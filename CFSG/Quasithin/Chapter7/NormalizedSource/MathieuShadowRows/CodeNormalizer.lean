module
public import Theory.Representation.MathieuCodeRestriction.CodeLocal.Flags
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextetResidual
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.GroupDeductions

/-!
# The original M24 code four-space normalizer

A marking of the original fixed subgroup by the native sextet code four-space
restricts the original component map to a surjection from its literal relative
normalizer onto the sextet stabilizer. Its kernel is the full original action
kernel; its action on the four-space has the separate column kernel, retaining
the cubic factor of order three.

The intrinsic solvable residual covers the native perfect residual. Its full
two-core maps onto all sextet translations, and its quotient by that two-core
is the actual triple cover 3.A6. Relative normality makes it a C-component of
N_{N_G(L)}(U). The Chapter12 application constructs these markings on the same
original rank-six code pair, discharging the normalizer and kernel premises.

Source: Aschbacher--Smith 8.2.5--6 and H.16.1--6, printed pp.716--717,
402--405, refs/quasithin.pdf. The native Golay and affine hexacode models
are the existing licensed ATLAS ports; see LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open MathieuCode.CodeFlags MathieuCode.SextetLayers.CoordinateTransport
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuShadowRows.CodeNormalizer
variable {G : Type*} [Group G]

/-- The literal normalizer of a marked code four-space covers its native
sextet stabilizer. The full original action kernel is retained. -/
theorem marked_normalizer_action
    (W L U : Subgroup G) [IsElementaryAbelian 2 W]
    (hLW : L ≤ normalizer (W : Set G)) (hUW : U ≤ W)
    (q : L →* M24) (hq : Function.Surjective q)
    (F : Additive W ≃ₗ[ZMod 2] Code)
    (hF : ∀ (l : L) (w : W),
      F (Additive.ofMul (W.normalizerMonoidHom ⟨l,hLW l.property⟩ w)) =
        codeRepresentation (q l) (F (Additive.ofMul w)))
    (S : Sextet)
    (hspace : ∀ w : W, (w : G) ∈ U ↔ F (Additive.ofMul w) ∈ sextetCodeSpace S) :
    ∃ f : (L ⊓ normalizer (U : Set G) : Subgroup G) →* sextetStabilizer S,
      Function.Surjective f ∧
      f.ker = q.ker.comap (inclusion (show L ⊓ normalizer (U : Set G) ≤ L from inf_le_left)) ∧
      (∀ l, (f l).val = q ⟨l,l.property.1⟩) ∧
      ((sextetPartPerm S).comp f).ker =
        (centralizer (U : Set G)).subgroupOf (L ⊓ normalizer (U : Set G)) := by
  let N := L ⊓ normalizer (U : Set G)
  have hn (l : L) : q l ∈ sextetStabilizer S ↔ l.val ∈ normalizer (U : Set G) := by
    rw [←sextetCodeSpace_stabilizer]
    constructor
    · intro ht
      rw [mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have hxW := hUW hx
        have hh := (ht (F (Additive.ofMul ⟨x,hxW⟩))).mpr ((hspace _).mp hx)
        rw [←hF,←hspace] at hh
        exact hh
      · intro hx
        have hxW := (mem_normalizer_iff.mp (hLW l.property) x).mpr (hUW hx)
        apply (hspace ⟨x,hxW⟩).mpr
        apply (ht _).mp
        rw [←hF]
        exact (hspace _).mp hx
    · intro hl v
      obtain ⟨w,rfl⟩ := F.surjective v
      have he := hF l w.toMul
      simp only [ofMul_toMul] at he
      rw [←he,←hspace]
      have hp := hspace w.toMul
      simp only [ofMul_toMul] at hp
      rw [←hp]
      exact (mem_normalizer_iff.mp hl w.toMul.val).symm
  let j : N →* L := inclusion inf_le_left
  let f : N →* sextetStabilizer S := (q.comp j).codRestrict _
    (fun n => (hn (j n)).mpr n.property.2)
  refine ⟨f,?_,?_,fun _ => rfl,?_⟩
  · intro t
    obtain ⟨l,hl⟩ := hq t.val
    exact ⟨⟨l,l.property,(hn l).mp (hl.symm ▸ t.property)⟩,Subtype.ext hl⟩
  · ext n
    exact Subtype.ext_iff
  · ext n
    change sextetPartPerm S (f n) = 1 ↔ n.val ∈ centralizer (U : Set G)
    rw [←sextetCodeSpace_fixed_iff_partPerm]
    constructor
    · intro hf
      rw [mem_centralizer_iff]
      intro u hu
      have he := (hF (j n) ⟨u,hUW hu⟩).trans (hf _ ((hspace _).mp hu))
      have hc : n.val * u * n.val⁻¹ = u :=
        congrArg (fun w : Additive W => w.toMul.val) (F.injective he)
      exact (mul_inv_eq_iff_eq_mul).mp hc |>.symm
    · intro hc v hv
      obtain ⟨w,rfl⟩ := F.surjective v
      have hu : w.toMul.val ∈ U := (hspace w.toMul).mpr hv
      change codeRepresentation (q (j n)) (F w) = F w
      have he := hF (j n) w.toMul
      simp only [ofMul_toMul] at he
      rw [←he]
      apply congrArg F
      apply Additive.ofMul.injective.eq_iff.mpr
      apply Subtype.ext
      exact (mul_inv_eq_iff_eq_mul).mpr (mem_centralizer_iff.mp hc _ hu).symm

variable [Finite G]

/-- The intrinsic residual of the original normalizer has quotient 3.A6
modulo its intrinsic two-core, through the same covering map. -/
theorem marked_residual_quotient (L U : Subgroup G) (S : Sextet)
    (f : (L ⊓ normalizer (U : Set G) : Subgroup G) →* sextetStabilizer S)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    Nonempty ((Chapter8.Section02.Normalizer.localResidual L U ⧸
      pCore 2 (Chapter8.Section02.Normalizer.localResidual L U)) ≃* Atlas.Codes.HexEvenAutomorphisms) := by
  let N := L ⊓ normalizer (U : Set G)
  let e : solvableResidual N ≃* Chapter8.Section02.Normalizer.localResidual L U :=
    (solvableResidual N).equivMapOfInjective N.subtype N.subtype_injective
  obtain ⟨m⟩ := MathieuSextet.native_residual_quotient S
  exact ⟨(e.symm.toMonoidHom.pCoreQuotientEquiv e.symm.surjective
      (IsPGroup.ker_isPGroup_of_injective e.symm.injective)).trans
    ((f.solvableResidualMap.pCoreQuotientEquiv (f.solvableResidualMap_surjective hf)
      (f.solvableResidualMap_ker_isPGroup hk)).trans m)⟩

/-- The original normalizer residual maps onto the native residual, and
its two-core maps onto all sextet translations. -/
theorem marked_residual_core_action (L U : Subgroup G) (S : Sextet)
    (f : (L ⊓ normalizer (U : Set G) : Subgroup G) →* sextetStabilizer S)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    ∃ r : Chapter8.Section02.Normalizer.localResidual L U →* sextetStabilizer S,
      r.range = solvableResidual (sextetStabilizer S) ∧ IsPGroup 2 r.ker ∧
      (pCore 2 (Chapter8.Section02.Normalizer.localResidual L U)).map r =
        (nativeQuotient S).ker ∧
      ∀ x, r x = f (inclusion (Chapter8.Section02.Normalizer.localResidual_le L U) x) := by
  let N := L ⊓ normalizer (U : Set G)
  let R := Chapter8.Section02.Normalizer.localResidual L U
  let P := solvableResidual (sextetStabilizer S)
  let e : solvableResidual N ≃* R :=
    (solvableResidual N).equivMapOfInjective N.subtype N.subtype_injective
  let q : R →* P := f.solvableResidualMap.comp e.symm.toMonoidHom
  have hq : Function.Surjective q := (f.solvableResidualMap_surjective hf).comp e.symm.surjective
  have hqk : IsPGroup 2 q.ker := by
    change IsPGroup 2 (f.solvableResidualMap.ker.comap e.symm.toMonoidHom)
    exact (f.solvableResidualMap_ker_isPGroup hk).comap_of_injective _ e.symm.injective
  let r := P.subtype.comp q
  have hrk : r.ker = q.ker := MonoidHom.ker_comp_of_injective _ _ P.subtype_injective
  have hm : (pCore 2 R).map q = pCore 2 P := by
    rw [←q.comap_pCore_of_ker_isPGroup hq hqk,map_comap_eq_self]
    rw [q.range_eq_top_of_surjective hq]
    exact le_top
  refine ⟨r,?_,hrk.symm ▸ hqk,?_,?_⟩
  · rw [MonoidHom.range_comp,q.range_eq_top_of_surjective hq,←MonoidHom.range_eq_map,range_subtype]
  · change (pCore 2 R).map (P.subtype.comp q) = _
    rw [←map_map,hm]
    exact MathieuSextet.native_residual_core S
  · intro x
    have he : (e.symm x).val = inclusion (Chapter8.Section02.Normalizer.localResidual_le L U) x := by
      apply Subtype.ext
      exact congrArg (fun y : R => (y : G)) (e.apply_symm_apply x)
    change f (e.symm x).val = _
    rw [he]

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

/-- The original residual is a C-component of N_{N_G(L)}(U).
Normality is relative to that actual normalizer. -/
theorem marked_residual_component (L U : Subgroup G)
    (e : (Chapter8.Section02.Normalizer.localResidual L U ⧸
      pCore 2 (Chapter8.Section02.Normalizer.localResidual L U)) ≃* Atlas.Codes.HexEvenAutomorphisms) :
    ((Chapter8.Section02.Normalizer.localResidual L U).subgroupOf
      (normalizer (L : Set G) ⊓ normalizer (U : Set G))).IsCComponent := by
  let R := Chapter8.Section02.Normalizer.localResidual L U
  let M := normalizer (L : Set G) ⊓ normalizer (U : Set G)
  have hRM : R ≤ M := (Chapter8.Section02.Normalizer.localResidual_le L U).trans
    (inf_le_inf_right _ L.le_normalizer)
  let : (R.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer
    (Chapter8.Section02.Normalizer.normalizes_localResidual L U M inf_le_left inf_le_right)
  let : Group.IsPerfect R := Group.IsPerfect.map _
  let : IsQuasisimple Atlas.Codes.HexEvenAutomorphisms := Hexacode.even_isQuasisimple
  let : IsQuasisimple (R ⧸ pCore 2 R) := IsQuasisimple.of_mulEquiv e.symm
  have ht := isCComponent_top_of_isPPerfect_of_quasisimple_quotient
    (pCore 2 R) (pCore_isPGroup (p := 2)) (perfect_twoPerfect (A := R))
  have htop : (⊤ : Subgroup (R.subgroupOf M)).IsCComponent := by
    simpa using ht.map_equiv (subgroupOfEquivOfLe hRM).symm
  simpa only [←MonoidHom.range_eq_map,range_subtype] using
    htop.map_subtype (inferInstance : (R.subgroupOf M).Normal).isSubnormal

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuShadowRows.CodeNormalizer

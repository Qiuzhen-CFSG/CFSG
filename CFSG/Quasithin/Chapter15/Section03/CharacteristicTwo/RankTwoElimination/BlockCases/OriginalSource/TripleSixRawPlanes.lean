module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.TripleSixFixed
public import Theory.Representation.CubicFourGroup
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.Geometry
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches.Geometry
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData

/-!
# The marked-plane contradiction on an injected triple-six section

A central cubic has no fixed vector on the faithful irreducible section.
Each definite four-group therefore has nontrivial cubic symmetry. A
commuting component element of quotient order four fixes both four-groups,
hence the original sixteen. The raw F₄³ fixed-space bound gives at most four.
All conjugation maps are retained by the assumed actual seed injection,
constructed in `TripleSixRawSeed` and applied in `TripleSixRaw`.

Source: Aschbacher–Smith 15.3.21, printed p.1127; B.4.2(8), K.1.3.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open ChapterB.QuasisimpleSource
variable {G D W : Type*} [Group G] [Finite G] [Group D] [AddCommGroup W] [Module (ZMod 2) W]

theorem tripleSix_firstChoice_plane_contradiction
    (d : LocalData G) (K : Subgroup G) (L : Subgroup D)
    (ρ : Representation (ZMod 2) D W) (q : K →* L)
    (a : ChapterB.SourceInduction.ProjectiveLine.TripleSixAction ρ L)
    (hf : Function.Injective (ρ.comp L.subtype)) (hir : IsIrreducible (ρ.comp L.subtype))
    (hfirst : d.Yplus=d.Y) (j : d.V → W) (hj : Function.Injective j) (hj1 : j 1=0)
    (hact : ∀ (l : K) (hl : (l:G) ∈ normalizer (d.V:Set G)) (v:d.V),
      j (d.V.normalizerMonoidHom ⟨l,hl⟩ v)=ρ (q l) (j v))
    (y t : K) (hy : (y:G)∈d.Yplus) (ht : (t:G)∈d.S)
    (hyz : q y ∈ center L) (hyne : q y ≠ 1) (hy3 : (q y)^3=1)
    (ht4 : orderOf (q t)=4) : False := by
  have hzero (v : W) (hv : ρ (q y) v=v) : v=0 := by
    have hh := LinearMap.congr_fun (centralCubicNorm_eq_zero_of_irreducible
      (ρ.comp L.subtype) hir hf (q y) hyz hyne hy3) v
    change ρ (q y) (ρ (q y) v)+ρ (q y) v+v=0 at hh
    rw [hv,hv] at hh
    have htwo : v+v=0 := by
      have he := @two_smul (ZMod 2) W _ _ _ v
      simpa only [show (2:ZMod 2)=0 by decide,zero_smul] using he.symm
    simpa only [htwo,zero_add] using hh
  have hyV : (y:G)∈normalizer (d.V:Set G) := d.action.normalizes
    ((show d.Y ≤ d.M from Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc) (hfirst ▸ hy))
  have htV : (t:G)∈normalizer (d.V:Set G) := d.action.normalizes (d.sylow_le ht.1)
  have hfix (i : OrthogonalPlaneIndex) : (t:G)∈centralizer (d.action.plane i:Set G) := by
    let E := d.action.plane i
    let := d.action.elementary_of_le (d.action.plane_le i)
    let : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by rw [d.action.card_plane]; decide)
    let : IsKleinFour E := ⟨d.action.card_plane i,IsElementaryAbelian.exponent_eq_prime⟩
    have hyN : (y:G)∈normalizer (E:Set G) :=
      OutsideStructure.LocalBranches.y_normalizes_plane d i (hfirst ▸ hy)
    have htN : (t:G)∈normalizer (E:Set G) :=
      OutsideStructure.LocalBranches.s_normalizes_plane d i ht
    let u := inclusion (d.action.plane_le i)
    let k : E → W := fun x => j (u x)
    have hka (l:K) (hl:(l:G)∈normalizer (E:Set G))
        (hlV:(l:G)∈normalizer (d.V:Set G)) (x:E) :
        k (E.normalizerMonoidHom ⟨l,hl⟩ x)=ρ (q l) (k x) := by
      rw [←hact l hlV]
      rfl
    have hb := cubic_fourgroup_fixed (ρ.comp L.subtype)
      (q y) (q t) hy3 (ht4 ▸ pow_orderOf_eq_one _) (by exact (mem_center_iff.mp hyz (q t)).symm)
      (E.normalizerMonoidHom ⟨y,hyN⟩) (E.normalizerMonoidHom ⟨t,htN⟩)
      k (hj.comp (inclusion_injective _)) (by exact hj1)
      (hka y hyN hyV) (hka t htN htV) hzero
    have hk : (⟨(t:G),htN⟩ : normalizer (E:Set G))∈E.normalizerMonoidHom.ker := hb
    rw [normalizerMonoidHom_ker] at hk
    exact hk
  have hVC' : d.V ≤ centralizer ({(t:G)}:Set G) := by
    have he : d.action.plane 1 ⊔ d.action.plane (Multiplicative.ofAdd (1:ZMod 2))=d.V :=
      RankTwo.natural_planes_sup d.action (by decide)
    rw [←he]
    apply sup_le
    · intro v hv
      exact mem_centralizer_singleton_iff.mpr (hfix 1 v hv)
    · intro v hv
      exact mem_centralizer_singleton_iff.mpr (hfix (Multiplicative.ofAdd (1:ZMod 2)) v hv)
  have hbound := tripleSix_four_fixed_card a hf (q t) ht4 j hj (fun v => by
    rw [←hact t htV]
    apply congrArg j
    apply Subtype.ext
    change (t:G)*(v:G)*(t:G)⁻¹=(v:G)
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp (hVC' v.property)).symm)
  have hcard : Nat.card d.V=16 := d.action.card_vector
  omega

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource

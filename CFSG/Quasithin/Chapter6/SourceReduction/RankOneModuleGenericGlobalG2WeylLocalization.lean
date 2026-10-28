module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2WeylTorus
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2WeylTorus
import all Theory.AtlasPort.LinearGroups.G2.Torus
import all Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage.FrameAlignment.WeylCorrection
import all Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage.FrameAlignment.RankOneNormalizers

/-!
# Localizing the canonical G₂ Weyl obstruction

In each marked parabolic, the centralizer of the whole split torus is the
torus itself. The checked rank-one normalizer covers reduce this to excluding
the reflection coset: a nonidentity unit detects the reflection's nontrivial
action on torus coordinates, also over F₄. Both endpoint embeddings transport
this calculation to the same torus in the original whole overlap.

The canonical sixth power already centralizes this torus. If it lies in either
original parabolic, it therefore lies in the torus and is killed by the proved
cube-inversion identity. This gives an exact localization criterion and an
actual concrete-recognition consumer. An ambient proof of that placement,
exhaustive amalgam comparison and original uniqueness remain required; the
local centralizer equalities do not assert full ambient self-centralization.

The internal imports reuse native coordinate identities and the existing
completion-to-source torus transport without changing their public boundaries.
The coordinate calculations retain LICENSES/ATLAS.txt attribution.
Source: Aschbacher–Smith F.4.8, F.4.24–26 and F.4.31–44, printed pp.278,
287–296, and their use in 5.3.3–4, p.659 (`refs/quasithin.pdf`).
-/

open Subgroup Theory.GroupTheory Atlas.G2 Atlas.G2.LieParabolicSetup
open Atlas.G2.LieAutomorphismExtensions.InnerFieldCoverage
public noncomputable section
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2CompletionGeometry
variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
private theorem torus_conj (l m a b : Fˣ) :
    MulAut.conj (torus l m) (torus a b) = torus a b := by
  apply mul_inv_eq_iff_eq_mul.mpr
  rw [torus_product,torus_product,mul_comm l a,mul_comm m b]

private theorem native_torus_centralizer_left (hq : 2 < Nat.card F)
    (g : Model F) (hg : g ∈ parabolic₁)
    (hc : g ∈ centralizer (splitTorus (K := F) : Set (Model F))) : g ∈ splitTorus := by
  rcases rankOne_torusNormalizerCover_short hq g hg
      (Subgroup.centralizer_le_normalizer _ hc) with ht | ⟨l,m,rfl⟩
  · exact ht
  obtain ⟨a,ha,_⟩ := exists_separating_unit hq
  have hh : MulAut.conj (torus l m * weylS) (torus a 1) = torus a 1 :=
    mul_inv_eq_iff_eq_mul.mpr (hc _ ⟨(a,1),rfl⟩).symm
  rw [map_mul,MulAut.mul_apply,show MulAut.conj (weylS : Model F) (torus a 1)=torus 1 a
    from weylS_torus a 1,torus_conj] at hh
  have he : (1,a)=(a,1) := torusHom_injective hh
  exact (ha (congrArg Prod.fst he).symm).elim

private theorem native_torus_centralizer_right (hq : 2 < Nat.card F)
    (g : Model F) (hg : g ∈ parabolic₂)
    (hc : g ∈ centralizer (splitTorus (K := F) : Set (Model F))) : g ∈ splitTorus := by
  rcases rankOne_torusNormalizerCover_long hq g hg
      (Subgroup.centralizer_le_normalizer _ hc) with ht | ⟨l,m,rfl⟩
  · exact ht
  obtain ⟨a,ha,_⟩ := exists_separating_unit hq
  have hh : MulAut.conj (torus l m * weylR) (torus a 1) = torus a 1 :=
    mul_inv_eq_iff_eq_mul.mpr (hc _ ⟨(a,1),rfl⟩).symm
  rw [map_mul,MulAut.mul_apply,show MulAut.conj (weylR : Model F) (torus a 1)=torus a (a*1⁻¹)
    from weylR_torus a 1,torus_conj] at hh
  have he : (a,a*1⁻¹)=(a,1) := torusHom_injective hh
  exact (ha (by simpa using congrArg Prod.snd he)).elim

namespace Completion
variable {G : Type*} [Group G] (c : Completion F G)

omit [Finite F] [CharP F 2] in
private theorem torus_centralizes : c.markedTorus ≤ centralizer (c.markedTorus : Set G) := by
  rintro x ⟨p,rfl⟩ y ⟨r,rfl⟩
  exact (map_mul c.torusMap r p).symm.trans ((congrArg c.torusMap (mul_comm r p)).trans
    (map_mul c.torusMap p r))

/-- In the first marked parabolic the full torus has no additional centralizer. -/
theorem left_torus_centralizer (hq : 2 < Nat.card F) :
    c.left.range ⊓ centralizer (c.markedTorus : Set G) = c.markedTorus := by
  apply le_antisymm
  · rintro x ⟨⟨g,rfl⟩,hc⟩
    have hg : g.val ∈ centralizer (splitTorus (K := F) : Set (Model F)) := by
      rintro y ⟨p,rfl⟩
      have hh : c.left (nativeTorus₁ p * g) = c.left (g * nativeTorus₁ p) := by
        simpa only [map_mul,torusMap,nativeTorus₁,MonoidHom.comp_apply] using hc (c.torusMap p) ⟨p,rfl⟩
      exact congrArg Subtype.val (c.left_injective hh)
    obtain ⟨p,hp⟩ := native_torus_centralizer_left hq g.val g.property hg
    exact ⟨p,congrArg c.left (Subtype.ext hp)⟩
  · exact le_inf (by rintro x ⟨p,rfl⟩; exact ⟨nativeTorus₁ p,rfl⟩) c.torus_centralizes

/-- The second parabolic has the same torus centralizer, through its own map. -/
theorem right_torus_centralizer (hq : 2 < Nat.card F) :
    c.right.range ⊓ centralizer (c.markedTorus : Set G) = c.markedTorus := by
  apply le_antisymm
  · rintro x ⟨⟨g,rfl⟩,hc⟩
    have hg : g.val ∈ centralizer (splitTorus (K := F) : Set (Model F)) := by
      rintro y ⟨p,rfl⟩
      have hh := hc (c.torusMap p) ⟨p,rfl⟩
      rw [c.torusMap_right] at hh
      have he : c.right (nativeTorus₂ p * g) = c.right (g * nativeTorus₂ p) := by
        simpa only [map_mul] using hh
      exact congrArg Subtype.val (c.right_injective he)
    obtain ⟨p,hp⟩ := native_torus_centralizer_right hq g.val g.property hg
    exact ⟨p,(c.torusMap_right p).trans (congrArg c.right (Subtype.ext hp))⟩
  · refine le_inf ?_ c.torus_centralizes
    rintro x ⟨p,rfl⟩
    exact ⟨nativeTorus₂ p,(c.torusMap_right p).symm⟩

end Completion
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2CompletionGeometry

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open G2CompletionGeometry
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}

/-- Both original parabolics have exactly the marked torus as its centralizer. -/
theorem Preparation.g2_parabolic_torus_centralizers
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse) :
    ∀ i : Fin 2, ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i ⊓
      centralizer (g2MarkedTorus e : Set G) = g2MarkedTorus e := by
  obtain ⟨c,hl,hr,_,_,_,_,_⟩ := d.g2_ambient_completion_geometry h hH hp F e
  have hD := completion_markedTorus e c hl
  have hq : 2 < Nat.card F := by
    rw [(d.g2_local_structure h hH.1.1.2 hp F (Or.inr ⟨e⟩)).1]
    exact Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) h.exponent
  have hleft := c.left_torus_centralizer hq
  have hright := c.right_torus_centralizer hq
  have her : e.right.symm.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr e.right.symm.surjective
  have hel : e.left.symm.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr e.left.symm.surjective
  rw [hD,hl,MonoidHom.range_comp,her,←MonoidHom.range_eq_map,range_subtype] at hleft
  rw [hD,hr,MonoidHom.range_comp,hel,←MonoidHom.range_eq_map,range_subtype] at hright
  intro i
  fin_cases i
  · exact hright
  · exact hleft

/-- The sixth-power obstruction vanishes exactly when it is in one of the
original parabolics. Thus a nontrivial obstruction escapes both endpoints. -/
theorem Preparation.g2_weyl_localization
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse) :
    let w := (e.right.symm (nativeS (F := F))).val *
      (e.left.symm (nativeR (F := F))).val
    (∃ i : Fin 2, w^6 ∈ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i) ↔
      w^6=1 := by
  obtain ⟨c,hl,hr,_,_,_,_,_⟩ := d.g2_ambient_completion_geometry h hH hp F e
  have hw : c.weylProduct=(e.right.symm (nativeS (F := F))).val *
      (e.left.symm (nativeR (F := F))).val := by
    simp only [G2CompletionGeometry.Completion.weylProduct,hl,hr,MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom,coe_subtype]
  have hD := completion_markedTorus e c hl
  dsimp only
  constructor
  · rintro ⟨i,hi⟩
    rw [←hw]
    apply c.weylProduct_six_eq_one_of_mem
    rw [hD,hw]
    exact (d.g2_parabolic_torus_centralizers h hH hp F e i).le
      ⟨hi,(d.g2_weyl_torus_geometry h hH hp e).2.2.2.2⟩
  · intro hh
    exact ⟨0,hh ▸ one_mem _⟩

/-- Placement of the actual sixth power in either original parabolic suffices
for concrete recognition. That placement is still an explicit source premise. -/
theorem Preparation.g2_ambient_recognition_of_weyl_localized
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)
    (hw : ∃ i : Fin 2,
      ((e.right.symm (nativeS (F := F))).val * (e.left.symm (nativeR (F := F))).val)^6 ∈
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i) :
    Nat.card F=2^n ∧ Nonempty (G ≃* Model F) :=
  d.g2_ambient_recognition_of_weyl h hH hp F e ((d.g2_weyl_localization h hH hp F e).mp hw)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

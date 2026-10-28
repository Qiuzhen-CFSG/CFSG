module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2ShortActionModel
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2ShortSylow
public import CFSG.Quasithin.ChapterI.Section06To08.UniqueFixedSource
public import Theory.GroupTheory.UniqueFixedCosetQuotient
public import Theory.GroupTheory.Commutator.PerfectLocalReduction

/-!
# The perfect-action contradiction in the G₂ short-root centralizer

Let t be the pinned short root, C = C_G(t), and X = C ∩ N_G(L).
The derived group of the original O₂(L) is the A–B root plane V, by the
model calculation and the literal left parabolic map. Thus X normalizes V.
The affine block in the model short-root centralizer embeds in X. It is
perfect for q > 2 and moves V, so X/C_X(V) is not solvable.

If the pinned long root fixes a unique coset of X in C, the explicit torus,
Weyl and root conjugations inside the short-root centralizer transfer this
to every nonidentity element of V. Original I.8.5 then makes X/C_X(V)
solvable whenever X is proper, a contradiction. This completes the terminal
F.4.42 argument from its single unique-fixed-coset premise, including q = 4.
The source and Chapter 12 applications construct the plane and its action
from the original inputs and retain both roots under the same compatible maps.

The unique-fixed-coset premise is still the ambient orbital comparison in
F.4.42; this module does not assert it or full centralizer containment without
it. Even-degree transfer, exhaustive comparison, original uniqueness and
concrete completion recognition remain with the generic-global assembly.
Source: Aschbacher–Smith F.4.42 and I.8.5, printed pp.295 and 430, and
5.3.3, p.659 (`refs/quasithin.pdf`). Coordinate identities reuse the licensed
ATLAS port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Atlas.G2 Atlas.G2.LieParabolicSetup
open Atlas.G2.ShortRootProducts.CentralizerCore
open scoped commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2ShortAction
variable {F : Type} [Field F] [CharP F 2] [Finite F]
variable {G : Type*} [Group G] [Finite G]

@[expose] def plane (f : parabolic₂ (F := F) →* G) : Subgroup G :=
  (longRootLocal.subgroupOf parabolic₂).map f

@[expose] def short : parabolic₂ (F := F) :=
  ⟨rootC 1,centralizer_rootC_le_parabolic 1 one_ne_zero
    (mem_centralizer_singleton_iff.mpr (Commute.refl _).eq)⟩

omit [Finite F] [Finite G] in
theorem plane_derived (f : parabolic₂ (F := F) →* G) :
    plane f = ⁅(radical₂.subgroupOf parabolic₂).map f,
      (radical₂.subgroupOf parabolic₂).map f⁆ := by
  unfold plane
  rw [←map_commutator]
  congr 1
  apply map_injective (parabolic₂ (F := F)).subtype_injective
  rw [map_commutator,map_subgroupOf_eq_of_le (radical₂_le_local₂.trans local₂_le_parabolic₂),
    map_subgroupOf_eq_of_le (longRootLocal_le_unipotent.trans
      (unipotent_le_local₂.trans local₂_le_parabolic₂)),radical_commutator]

omit [Finite F] [Finite G] in
private theorem plane_normalized (f : parabolic₂ (F := F) →* G) (N : Subgroup G)
    (hn : N ≤ normalizer ((radical₂.subgroupOf parabolic₂).map f : Set G)) :
    N ≤ normalizer (plane f : Set G) := by
  rw [plane_derived,←map_subtype_commutator]
  exact hn.trans (normalizer_le_normalizer_characteristic_image _ (commutator _))

omit [Finite F] [Finite G] in
theorem plane_centralizes (f : parabolic₂ (F := F) →* G) :
    plane f ≤ centralizer ({f short} : Set G) := by
  rintro x ⟨a,ha,rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  rw [←map_mul,←map_mul]
  exact congrArg f (Subtype.ext (mem_centralizer_singleton_iff.mp
    (residualBlock_le_centralizer_rootC 1 (mem_sup_left ha))))

omit [Finite F] [Finite G] in
private theorem plane_elementary (f : parabolic₂ (F := F) →* G) :
    IsElementaryAbelian 2 (plane f) := by
  let : IsElementaryAbelian 2 (longRootLocal (F := F)) := LongRootPlaneLift.elementary
  let : IsElementaryAbelian 2 ((longRootLocal (F := F)).subgroupOf parabolic₂) :=
    IsElementaryAbelian.subgroupOf (longRootLocal_le_unipotent.trans
      (unipotent_le_local₂.trans local₂_le_parabolic₂))
  exact IsElementaryAbelian.map f

omit [Finite G] in
/-- The perfect affine block rules out a solvable induced action on the
actual plane in any overgroup of the long parabolic image. -/
private theorem action_not_solvable
    (hq : 2 < Nat.card F) (f : parabolic₂ (F := F) →* G) (hf : Function.Injective f)
    (N : Subgroup G) (hN : f.range ≤ N)
    (hn : N ≤ normalizer ((radical₂.subgroupOf parabolic₂).map f : Set G)) :
    let C := centralizer ({f short} : Set G)
    let X := N.subgroupOf C
    let V := (plane f).subgroupOf C
    letI : (V.subgroupOf X).Normal := normal_subgroupOf_of_le_normalizer (by
      intro x hx
      apply mem_normalizer_iff.mpr
      intro a
      exact mem_normalizer_iff.mp (plane_normalized f N hn hx) a.val)
    ¬ Group.IsSolvable (X ⧸ centralizer (V.subgroupOf X : Set X)) := by
  dsimp only
  let C := centralizer ({f short} : Set G)
  let X := N.subgroupOf C
  let V := (plane f).subgroupOf C
  let : (V.subgroupOf X).Normal := normal_subgroupOf_of_le_normalizer (by
    intro x hx
    apply mem_normalizer_iff.mpr
    intro a
    exact mem_normalizer_iff.mp (plane_normalized f N hn hx) a.val)
  let k : residualBlock (F := F) →* X := {
    toFun a := ⟨⟨f ⟨a,residualBlock_le_local.trans local₂_le_parabolic₂ a.property⟩,
      mem_centralizer_singleton_iff.mpr (by
        rw [←map_mul,←map_mul]
        exact congrArg f (Subtype.ext (mem_centralizer_singleton_iff.mp
          (residualBlock_le_centralizer_rootC 1 a.property))))⟩,hN ⟨_,rfl⟩⟩
    map_one' := by apply Subtype.ext; apply Subtype.ext; exact map_one f
    map_mul' a b := by
      apply Subtype.ext
      apply Subtype.ext
      exact map_mul f ⟨a.val,residualBlock_le_local.trans local₂_le_parabolic₂ a.property⟩
        ⟨b.val,residualBlock_le_local.trans local₂_le_parabolic₂ b.property⟩ }
  intro hs
  let : Group.IsSolvable (X ⧸ centralizer (V.subgroupOf X : Set X)) := hs
  let : Group.IsPerfect (residualBlock (F := F)) := residualBlock_isPerfect hq
  let : Group.IsPerfect k.range := Group.IsPerfect.range k
  have hk := le_of_isPerfect_of_solvable_quotient k.range
    (centralizer (V.subgroupOf X : Set X))
  apply block_moves_plane (F := F)
  intro a ha b hb
  let bX : X := ⟨⟨f ⟨b,longRootLocal_le_unipotent.trans
      (unipotent_le_local₂.trans local₂_le_parabolic₂) hb⟩,
    plane_centralizes f (mem_map_of_mem f hb)⟩,hN ⟨_,rfl⟩⟩
  have hbV : bX ∈ V.subgroupOf X := mem_map_of_mem f hb
  have hh := hk (show k ⟨a,ha⟩ ∈ k.range from ⟨_,rfl⟩) bX hbV
  have he := congrArg (fun x : X => x.val.val) hh
  change f _ * f _ = f _ * f _ at he
  rw [←map_mul,←map_mul] at he
  exact congrArg Subtype.val (hf he)

/-- I.8.5 closes the short-root centralizer argument once its unique fixed
cosets are established. The plane and nonsolvable action are constructed. -/
theorem centralizer_le_of_unique_fixed
    (hq : 2 < Nat.card F) (f : parabolic₂ (F := F) →* G) (hf : Function.Injective f)
    (N : Subgroup G) (hN : f.range ≤ N)
    (hn : N ≤ normalizer ((radical₂.subgroupOf parabolic₂).map f : Set G))
    (hfix : ∀ v : centralizer ({f short} : Set G),
      v.val ∈ plane f → v ≠ 1 →
        ∃! q : centralizer ({f short} : Set G) ⧸ N.subgroupOf
          (centralizer ({f short} : Set G)), v • q = q) :
    centralizer ({f short} : Set G) ≤ N := by
  let C := centralizer ({f short} : Set G)
  let X := N.subgroupOf C
  let V := (plane f).subgroupOf C
  have hVC : plane f ≤ C := plane_centralizes f
  let : IsElementaryAbelian 2 (plane f) := plane_elementary f
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hVC).toMonoidHom (subgroupOfEquivOfLe hVC).injective
  have hVX : V ≤ X := fun v hv => hN ((map_le_range f _) hv)
  let : (V.subgroupOf X).Normal := normal_subgroupOf_of_le_normalizer (by
    intro x hx
    apply mem_normalizer_iff.mpr
    intro a
    exact mem_normalizer_iff.mp (plane_normalized f N hn hx) a.val)
  have hVne : V ≠ ⊥ := by
    intro he
    let a : parabolic₂ (F := F) := ⟨rootA 1,longRootLocal_le_unipotent.trans
      (unipotent_le_local₂.trans local₂_le_parabolic₂) (rootA_mem_longRootLocal 1)⟩
    have ha : f a ∈ plane f := mem_map_of_mem f (rootA_mem_longRootLocal 1)
    have hh : (⟨f a,hVC ha⟩ : C) ∈ V := ha
    rw [he,mem_bot] at hh
    have ha1 : rootA (1:F)=1 := congrArg Subtype.val
      (hf ((congrArg Subtype.val hh).trans (map_one f).symm))
    exact one_ne_zero (rootA_injective (ha1.trans rootA_zero.symm))
  by_contra hle
  have hproper : X ≠ ⊤ := by
    intro he
    exact hle (fun x hx => show (⟨x,hx⟩ : C) ∈ X from he ▸ mem_top _)
  exact action_not_solvable hq f hf N hN hn
    (ChapterI.Section06To08.lemma_I_8_5_automizer V X hVX hVne hproper hfix)


@[expose] def long : parabolic₂ (F := F) :=
  ⟨rootA 1,longRootLocal_le_unipotent.trans (unipotent_le_local₂.trans local₂_le_parabolic₂)
    (rootA_mem_longRootLocal 1)⟩

omit [Finite F] [Finite G] in
private theorem plane_orbit (f : parabolic₂ (F := F) →* G)
    (x : centralizer ({f short} : Set G)) (hx : x.val ∈ plane f) (hx1 : x ≠ 1) :
    IsConj (⟨f long,plane_centralizes f
      (mem_map_of_mem f (rootA_mem_longRootLocal 1))⟩ : centralizer ({f short} : Set G)) x := by
  obtain ⟨a,ha,he⟩ := hx
  obtain ⟨p,hp⟩ := ha
  change longRootHom p = a.val at hp
  have ha1 : a.val ≠ 1 := by
    intro hh
    apply hx1
    apply Subtype.ext
    rw [←he,show a=1 from Subtype.ext hh,map_one]
    rfl
  have ht (u : Fˣ) : torus 1 u ∈ centralizer ({rootC (1:F)} : Set (Model F)) := by
    apply mem_centralizer_singleton_iff.mpr
    apply mul_inv_eq_iff_eq_mul.mp
    simpa using torus_rootC (1:Fˣ) u (1:F)
  have hE (b : F) : rootE b ∈ centralizer ({rootC (1:F)} : Set (Model F)) := by
    rw [←block_upper]
    exact residualBlock_le_centralizer_rootC 1 (mem_sup_right ⟨_,rfl⟩)
  have hR : (weylR : Model F) ∈ centralizer ({rootC (1:F)} : Set (Model F)) := by
    rw [←long_block_J]
    exact residualBlock_le_centralizer_rootC 1 (mem_sup_right ⟨_,rfl⟩)
  have hg : ∃ g ∈ centralizer ({rootC (1:F)} : Set (Model F)),
      g * rootA 1 * g⁻¹=a.val := by
    by_cases hb : p.toAdd.2=0
    · have hpa : p.toAdd.1 ≠ 0 := by
        intro hz
        apply ha1
        rw [←hp]
        simp [longRootHom,hz,hb]
      refine ⟨torus 1 (Units.mk0 p.toAdd.1 hpa),ht _,?_⟩
      rw [torus_rootA,←hp]
      simp [longRootHom,hb]
    · let u := Units.mk0 p.toAdd.2 hb
      refine ⟨rootE (p.toAdd.1/p.toAdd.2)*weylR*torus 1 u,
        mul_mem (mul_mem (hE _) hR) (ht u),?_⟩
      change MulAut.conj (rootE (p.toAdd.1/p.toAdd.2)*weylR*torus 1 u) (rootA 1)=a.val
      rw [map_mul,map_mul,MulAut.mul_apply,MulAut.mul_apply]
      rw [show MulAut.conj (torus 1 u) (rootA 1)=rootA p.toAdd.2 by
        simpa [u] using torus_rootA (1:Fˣ) u (1:F)]
      rw [show MulAut.conj weylR (rootA p.toAdd.2)=rootB p.toAdd.2 from weylR_rootA _,
        ShortRootProducts.rootE_conjugate_rootB,div_mul_cancel₀ _ hb]
      exact hp
  obtain ⟨g,hgc,hga⟩ := hg
  let gP : parabolic₂ (F := F) := ⟨g,centralizer_rootC_le_parabolic 1 one_ne_zero hgc⟩
  have hfg : f gP ∈ centralizer ({f short} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    rw [←map_mul,←map_mul]
    exact congrArg f (Subtype.ext (mem_centralizer_singleton_iff.mp hgc))
  apply isConj_iff.mpr
  refine ⟨⟨f gP,hfg⟩,?_⟩
  apply Subtype.ext
  change f gP*f long*(f gP)⁻¹=x.val
  rw [←map_inv,←map_mul,←map_mul,←he]
  exact congrArg f (Subtype.ext hga)

/-- The pinned long root inside the actual short-root centralizer. -/
@[expose] def longMark (f : parabolic₂ (F := F) →* G) : centralizer ({f short} : Set G) :=
  ⟨f long,plane_centralizes f (mem_map_of_mem f (rootA_mem_longRootLocal 1))⟩

/-- It suffices to establish the fixed-coset statement for the one pinned
long root; the concrete centralizer acts transitively on the plane's
nonidentity elements. -/
theorem centralizer_le_of_long_unique_fixed
    (hq : 2 < Nat.card F) (f : parabolic₂ (F := F) →* G) (hf : Function.Injective f)
    (N : Subgroup G) (hN : f.range ≤ N)
    (hn : N ≤ normalizer ((radical₂.subgroupOf parabolic₂).map f : Set G))
    (hfix : ∃! q : centralizer ({f short} : Set G) ⧸ N.subgroupOf
        (centralizer ({f short} : Set G)),
      longMark f • q=q) :
    centralizer ({f short} : Set G) ≤ N := by
  apply centralizer_le_of_unique_fixed hq f hf N hN hn
  intro x hx hx1
  exact UniqueFixedCoset.unique_of_isConj hfix (plane_orbit f x hx hx1)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2ShortAction

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

/-- The original long-core derived group is the actual A–B root plane.
I.8.5 discharges the last short-centralizer contradiction from the precise
remaining unique-fixed-coset premise. No ambient recognition is assumed. -/
theorem Preparation.g2_short_centralizer_of_long_unique_fixed
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse) :
    let f := (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0).subtype.comp
      e.left.symm.toMonoidHom
    let v : G := f G2ShortAction.short
    v = (e.right.symm (G2CompletionFusion.short (1:F))).val ∧
      (G2ShortAction.longMark f).val = (e.right.symm (G2CompletionFusion.long (1:F))).val ∧
      G2ShortAction.plane f = ⁅L.pCoreIn 2,L.pCoreIn 2⁆ ∧
      ((∃! q : centralizer ({v} : Set G) ⧸ (normalizer (L : Set G)).subgroupOf
          (centralizer ({v} : Set G)), G2ShortAction.longMark f • q=q) →
      centralizer ({v} : Set G) ≤ normalizer (L : Set G)) := by
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
  let f := P.subtype.comp e.left.symm.toMonoidHom
  have hf : Function.Injective f := P.subtype_injective.comp e.left.symm.injective
  have hq : 2 < Nat.card F := by
    rw [(d.g2_local_structure h hTH hp F (Or.inr ⟨e⟩)).1]
    exact Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) h.exponent
  let J := (local₂ (F := F)).subgroupOf parabolic₂
  have hJ : J = solvableResidual (parabolic₂ (F := F)) := by
    apply map_injective (parabolic₂ (F := F)).subtype_injective
    rw [map_subgroupOf_eq_of_le local₂_le_parabolic₂,
      HigherFieldResiduals.parabolic₂_residual hq]
  have hJf : J.map f = L := by
    rw [hJ,show f=P.subtype.comp e.left.symm.toMonoidHom from rfl,
      ←map_map,map_solvableResidual_eq e.left.symm.toMonoidHom e.left.symm.surjective]
    exact d.parabolic_residuals h hTH hp 0
  have hQ : ((radical₂ (F := F)).subgroupOf parabolic₂).map f=L.pCoreIn 2 := by
    have hh := map_pCoreIn_of_injective 2 J f hf
    rw [hJf,pCoreIn_subgroupOf 2 local₂ parabolic₂ local₂_le_parabolic₂,local₂_pCoreIn] at hh
    exact hh
  have hplane : G2ShortAction.plane f=⁅L.pCoreIn 2,L.pCoreIn 2⁆ := by
    rw [G2ShortAction.plane_derived,hQ]
  have hPN : P ≤ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer
      (show L ≤ P from le_sup_left.trans le_sup_left)).mp
      ((d.hypothesisF11 h hTH).local_normal_in_parabolic 0)
  have hN : f.range ≤ normalizer (L : Set G) := by
    rintro _ ⟨x,rfl⟩
    exact hPN (e.left.symm x).property
  have hn : normalizer (L : Set G) ≤
      normalizer (((radical₂ (F := F)).subgroupOf parabolic₂).map f : Set G) := by
    rw [hQ]
    exact normalizer_le_normalizer_characteristic_image L (pCore 2 L)
  have hv : f (G2ShortAction.short (F := F)) =
      (e.right.symm (G2CompletionFusion.short (1:F))).val := by
    let b : ChapterF.GreenBook.LieModels.G2.overlap (F := F) :=
      ⟨rootC 1,(G2CompletionFusion.short (1:F)).property,(G2ShortAction.short (F := F)).property⟩
    exact (congrArg Subtype.val (e.symm.left_commutes b)).trans
      (congrArg Subtype.val (e.symm.right_commutes b)).symm
  have hz : (G2ShortAction.longMark f).val =
      (e.right.symm (G2CompletionFusion.long (1:F))).val := by
    let b : ChapterF.GreenBook.LieModels.G2.overlap (F := F) :=
      ⟨rootA 1,(G2CompletionFusion.long (1:F)).property,(G2ShortAction.long (F := F)).property⟩
    exact (congrArg Subtype.val (e.symm.left_commutes b)).trans
      (congrArg Subtype.val (e.symm.right_commutes b)).symm
  exact ⟨hv,hz,hplane,
    G2ShortAction.centralizer_le_of_long_unique_fixed hq f hf (normalizer (L : Set G)) hN hn⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

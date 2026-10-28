module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Identification.Block.Model
public import Theory.SpecificGroups.PSL3.OrdinaryCenterRecognition

/-!
# The literal central cover and the field-four alternative

The original projection to SL₃(q) factors through L/V. The identity
[O₂(L),L]=V makes its kernel central, and the original component makes
L/V perfect. Its central quotient is consequently PSL₃(q), while the
cover itself retains the full special-linear target and representative map.
For q different from four, the proved ordinary multiplier bound makes the
center odd and kills O₂(L/V). Pulling back recovers V=O₂(L)=C_L(V).

The exceptional branch explicitly retains q=4 and O₂(L/V) nontrivial.
Its invariant-complement exclusion and the final P=O₂(L₂) remain with
qt-d-1222-shadow-common-identification. Block/Source.lean applies this
alternative after discharging the local commutator premise.
Source: Aschbacher--Smith, refs/quasithin.pdf, printed p.774, using I.1.3.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Matrix
open scoped IsMulCommutative MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.OriginalBlock
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
  (a : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

/-- The original quotient by V, with normality supplied by its chosen action. -/
def SeedQuotient (_D : ChosenModule T L V) : Type _ := L ⧸ V.subgroupOf L

instance : Group (SeedQuotient D) :=
  let : (V.subgroupOf L).Normal := normal_subgroupOf_of_le_normalizer D.normalizes
  inferInstanceAs (Group (L ⧸ V.subgroupOf L))

instance : Finite (SeedQuotient D) := inferInstanceAs (Finite (L ⧸ V.subgroupOf L))

/-- The literal projection L → L/V. -/
def seedProjection : L →* SeedQuotient D :=
  let : (V.subgroupOf L).Normal := normal_subgroupOf_of_le_normalizer D.normalizes
  QuotientGroup.mk' (V.subgroupOf L)

omit [Finite G] in
include D in
theorem seed_le_core : V.subgroupOf L ≤ pCore 2 L := by
  intro l hl
  obtain ⟨z,hz,he⟩ := D.le_componentCore hl
  exact (Subtype.ext he : z = l) ▸ hz

/-- The full SL₃ quotient map factors through the same V. -/
def seedQuotientModel : SeedQuotient D →* SL(3,S.field.Carrier) :=
  let : (V.subgroupOf L).Normal := normal_subgroupOf_of_le_normalizer D.normalizes
  QuotientGroup.lift (V.subgroupOf L)
    (a.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) (by
    rw [MonoidHom.ker_comp_of_injective _ _ a.groupEquiv.injective,QuotientGroup.ker_mk']
    exact seed_le_core D)

theorem seedQuotientModel_mk (l : L) :
    seedQuotientModel D S a (seedProjection D l) =
      a.groupEquiv (QuotientGroup.mk' (pCore 2 L) l) := rfl

theorem seedQuotientModel_surjective : Function.Surjective (seedQuotientModel D S a) := by
  intro x
  obtain ⟨l,rfl⟩ := (Coordinates.sl3 a).quotientMap_surjective x
  exact ⟨seedProjection D l,rfl⟩

theorem seedQuotientModel_ker :
    (seedQuotientModel D S a).ker = (pCore 2 L).map (seedProjection D) := by
  let : (V.subgroupOf L).Normal := normal_subgroupOf_of_le_normalizer D.normalizes
  have hker : V.subgroupOf L ≤
      (a.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))).ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ a.groupEquiv.injective,QuotientGroup.ker_mk']
    exact seed_le_core D
  change (QuotientGroup.lift (V.subgroupOf L)
    (a.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) hker).ker = _
  rw [QuotientGroup.ker_lift]
  congr 1
  rw [MonoidHom.ker_comp_of_injective _ _ a.groupEquiv.injective,QuotientGroup.ker_mk']

/-- The source L/V is a perfect central cover of the full SL₃(q).
Its kernel is allowed to be nontrivial, including q=4. -/
def seedCover (hcomm : ⁅L.pCoreIn 2,L⁆ = V) :
    PerfectCentralCovering.Cover (SeedQuotient D) SL(3,S.field.Carrier) where
  toMonoidHom := seedQuotientModel D S a
  surjective := seedQuotientModel_surjective D S a
  isPerfect := by
    let : (V.subgroupOf L).Normal := normal_subgroupOf_of_le_normalizer D.normalizes
    let : Group.IsPerfect L := Chapter1.mem_L_isPerfect S.source.maximal_faithful.1.1
    exact Group.IsPerfect.ofSurjective (f := seedProjection D)
      (QuotientGroup.mk'_surjective (V.subgroupOf L))
  ker_le_center := by
    let : (V.subgroupOf L).Normal := normal_subgroupOf_of_le_normalizer D.normalizes
    rw [seedQuotientModel_ker]
    apply commutator_top_right_eq_bot_iff_le_center.mp
    rw [←(seedProjection D).range_eq_top.mpr
      (QuotientGroup.mk'_surjective (V.subgroupOf L)),MonoidHom.range_eq_map,
      ←map_commutator,Subgroup.map_eq_bot_iff]
    change ChapterC.blockU L ≤ (QuotientGroup.mk' (V.subgroupOf L)).ker
    rw [QuotientGroup.ker_mk']
    apply (map_le_map_iff_of_injective L.subtype_injective).mp
    rw [blockU_map hcomm,map_subgroupOf_eq_of_le D.le_component]

/-- The cover keeps the original chosen quotient on every representative. -/
theorem seedCover_mk (hcomm : ⁅L.pCoreIn 2,L⁆ = V) (l : L) :
    (seedCover D S a hcomm).toMonoidHom (seedProjection D l) =
      a.groupEquiv (QuotientGroup.mk' (pCore 2 L) l) := rfl

include D S a in
/-- The original action kernel in L is exactly O₂(L). -/
theorem seed_centralizer : (centralizer (V : Set G)).subgroupOf L = pCore 2 L := by
  apply le_antisymm
  · intro l hl
    have he : a.groupEquiv (QuotientGroup.mk' (pCore 2 L) l) = 1 := by
      apply Matrix.SpecialLinearGroup.toLin'_injective
      rw [map_one]
      ext w : 1
      obtain ⟨v,rfl⟩ := (SL3.naturalEquiv D S a).surjective (Multiplicative.ofAdd w)
      change (a.groupEquiv (QuotientGroup.mk' (pCore 2 L) l)).val *ᵥ
        (SL3.naturalEquiv D S a v).toAdd = (SL3.naturalEquiv D S a v).toAdd
      rw [←natural_conjugation D S a l v]
      congr 2
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp hl) _ v.property).symm
    exact (QuotientGroup.eq_one_iff l).mp
      (a.groupEquiv.injective (he.trans a.groupEquiv.map_one.symm))
  · intro l hl
    have hcore : L.pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
      pCoreIn_mono_of_normalizes le_sup_left
        (sup_le L.le_normalizer D.sylow_normalizes_component)
    exact D.core_centralizes (hcore (mem_map_of_mem L.subtype hl))

include S a in
theorem seedQuotient_quasisimple (hcomm : ⁅L.pCoreIn 2,L⁆ = V) :
    IsQuasisimple (SeedQuotient D) := by
  let := S.source.quasisimple
  let : IsQuasisimple SL(3,S.field.Carrier) := IsQuasisimple.of_mulEquiv a.groupEquiv
  exact (seedCover D S a hcomm).isQuasisimple

/-- The same quotient's central quotient is the projective model. The cover
itself remains over the full special-linear group. -/
def seedQuotientCenterEquiv (hcomm : ⁅L.pCoreIn 2,L⁆ = V) :
    (SeedQuotient D ⧸ center (SeedQuotient D)) ≃* PSL(3,S.field.Carrier) :=
  (seedCover D S a hcomm).quotientCenterEquiv

include D S a in
/-- The ordinary multiplier calculation kills the original quotient two-core
for q≠4; the exceptional parameter is explicit. -/
theorem seedQuotient_core_eq_bot_of_not_four (hcomm : ⁅L.pCoreIn 2,L⁆ = V)
    (h4 : 2 ^ S.field.degree ≠ 4) : pCore 2 (SeedQuotient D) = ⊥ := by
  let := seedQuotient_quasisimple D S a hcomm
  have h2 : Nat.card S.field.Carrier ≠ 2 := by
    rw [S.field.card_eq]
    have hn := S.nonbinary
    have hp : 2 ^ 1 < 2 ^ S.field.degree := (Nat.pow_lt_pow_iff_right (by decide)).mpr hn
    norm_num at hp
    omega
  have hd := Matrix.PSL3.OrdinaryCenterRecognition.center_card_dvd h2
    (by rwa [S.field.card_eq]) (seedQuotientCenterEquiv D S a hcomm)
  have hc := (card_dvd_of_le
    (IsQuasisimple.pCore_le_center (G := SeedQuotient D) 2)).trans
      (hd.trans (Nat.gcd_dvd_left 3 _))
  obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := SeedQuotient D)).exists_card_eq
  have hk0 : k = 0 := by
    by_contra hne
    have hh : 2 ∣ 3 := (dvd_pow_self 2 hne).trans (hk ▸ hc)
    omega
  exact (pCore 2 (SeedQuotient D)).eq_bot_of_card_eq (by simpa [hk0] using hk)

include D in
/-- A trivial quotient two-core recovers the actual embedded core. -/
theorem component_core_eq_of_quotient_core_eq_bot
    (hq : pCore 2 (SeedQuotient D) = ⊥) : L.pCoreIn 2 = V := by
  let : (V.subgroupOf L).Normal := normal_subgroupOf_of_le_normalizer D.normalizes
  let := D.elementary
  have hk : IsPGroup 2 (seedProjection D).ker := by
    change IsPGroup 2 (QuotientGroup.mk' (V.subgroupOf L)).ker
    rw [QuotientGroup.ker_mk']
    exact (IsElementaryAbelian.isPGroup 2 V).comap_subtype
  have hh := (seedProjection D).comap_pCore_of_ker_isPGroup
    (QuotientGroup.mk'_surjective _) hk
  rw [hq,MonoidHom.comap_bot] at hh
  have he : pCore 2 L = V.subgroupOf L := hh.symm.trans (QuotientGroup.ker_mk' _)
  have hm := congrArg (map L.subtype) he
  change (pCore 2 L).map L.subtype = V
  simpa only [map_subgroupOf_eq_of_le D.le_component] using hm

include a in
/-- The original multiplier alternative, retaining precisely the possible
field-four two-core instead of assuming it away. -/
theorem core_alternative (hcomm : ⁅L.pCoreIn 2,L⁆ = V) :
    (L.pCoreIn 2 = V ∧ L ⊓ centralizer (V : Set G) = V) ∨
      (2 ^ S.field.degree = 4 ∧ pCore 2 (SeedQuotient D) ≠ ⊥) := by
  by_cases hc : pCore 2 (SeedQuotient D) = ⊥
  · left
    have he := component_core_eq_of_quotient_core_eq_bot D hc
    refine ⟨he,?_⟩
    have hm := congrArg (map L.subtype) (seed_centralizer D S a)
    rw [subgroupOf_map_subtype,inf_comm] at hm
    exact hm.trans he
  · right
    exact ⟨by_contra fun h4 => hc (seedQuotient_core_eq_bot_of_not_four D S a hcomm h4),hc⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.OriginalBlock

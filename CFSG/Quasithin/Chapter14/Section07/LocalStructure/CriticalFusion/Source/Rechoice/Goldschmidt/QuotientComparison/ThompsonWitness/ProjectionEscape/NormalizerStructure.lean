module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.ProjectionEscape
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Coverage
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceMarking
public import CFSG.Quasithin.Chapter12.Section08.Setup.NaturalActions
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.GroupTheory.CentralCommutatorQuotient
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterOrder

/-!
# The genuine normalizer projection and its centralizer factor

The full natural action realizes the action of every element of T inside L.
The correcting element centralizes V, so its commutators with L lie in
C_L(V)=O₂(L). Since Out(SL₃(2)) is a two-group, triviality on the Sylow
subgroup makes the whole normalizer action inner. Centerlessness then gives
an actual homomorphism M=N_G(L) → SL₃(2), extending the literal quotient
L → L/O₂(L) under any chosen quotient equivalence.

The kernel is the centralizer of the literal quotient action. Relative
normality and the paired map to SL₃(2) × M/L identify
M/O₂(L) with L/O₂(L) × C_M(L/O₂(L))/O₂(L); the first coordinate is exactly
the constructed projection. No equality M=LT or two-group kernel is used.

For a quotient marking aligned with the original flag, residual transport
gives the required pointA and lineA images. The point-normalizer preimage
normalizes the actual stabilizer in L, hence its characteristic two-residual.
The final application feeds these fields into the existing escape consumer.
The flag-alignment witness is discharged in the extension
NormalizerStructure.OriginalFlag, whose nonempty_of_source constructs the
complete NormalizerProjection from Source.Data and the earlier structural theorem.

The only earlier universal input is the complete Structural1222 contract
from Chapter12.Section02.SourceHypotheses, produced by qt-12-02-reduction.
Its applicability is supplied by d.natural.source and d.natural.chosen via
the existing HigherRankHypothesis normalizer lemmas. Its final discharge
remains with the Chapter 12 and source-theorem assembly owners.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
Notation 14.7.1, printed p.1043, and Lemma 14.7.70, printed p.1074.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.ProjectionEscape.NormalizerStructure
open Chapter12.Section08 Matrix.PSL3Two
universe u
variable {G : Type u} [Group G] (L : Subgroup G)

noncomputable def quotientAction : normalizer (L : Set G) →* MulAut (L ⧸ pCore 2 L) :=
  (quotientAut (pCore 2 L)).comp L.normalizerMonoidHom

@[simp] theorem quotientAction_apply (x : normalizer (L : Set G)) (l : L) :
    quotientAction L x (QuotientGroup.mk' (pCore 2 L) l) =
      QuotientGroup.mk' (pCore 2 L) (L.normalizerMonoidHom x l) :=
  quotientAut_apply_mk _ _ _

theorem quotientAction_inner (l : L) :
    quotientAction L (inclusion L.le_normalizer l) =
      MulAut.conj (QuotientGroup.mk' (pCore 2 L) l) := by
  ext q
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  rw [quotientAction_apply]
  change QuotientGroup.mk' (pCore 2 L) (l * a * l⁻¹) = _
  simp only [map_mul, map_inv, MulAut.conj_apply]

noncomputable def markedAction (e : (L ⧸ pCore 2 L) ≃* SL) :
    normalizer (L : Set G) →* MulAut SL :=
  (MulAut.congr e).toMonoidHom.comp (quotientAction L)

@[simp] theorem markedAction_apply (e : (L ⧸ pCore 2 L) ≃* SL)
    (x : normalizer (L : Set G)) (l : L) :
    markedAction L e x (e (QuotientGroup.mk' (pCore 2 L) l)) =
      e (QuotientGroup.mk' (pCore 2 L) (L.normalizerMonoidHom x l)) := by
  change e (quotientAction L x (e.symm (e _))) = _
  rw [e.symm_apply_apply, quotientAction_apply]

theorem markedAction_inner (e : (L ⧸ pCore 2 L) ≃* SL) (l : L) :
    markedAction L e (inclusion L.le_normalizer l) =
      MulAut.conj (e (QuotientGroup.mk' (pCore 2 L) l)) := by
  apply MulEquiv.ext
  intro s
  obtain ⟨q, rfl⟩ := e.surjective s
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  rw [markedAction_apply]
  change e (QuotientGroup.mk' (pCore 2 L) (l * a * l⁻¹)) = _
  simp only [map_mul, map_inv, MulAut.conj_apply]

variable {L} {V : Subgroup G}

theorem seed_centralizer_fixes_quotient (hLV : L ≤ normalizer (V : Set G))
    (hker : L ⊓ centralizer (V : Set G) = L.pCoreIn 2)
    (x : normalizer (L : Set G)) (hx : (x : G) ∈ centralizer (V : Set G)) :
    quotientAction L x = 1 := by
  ext q
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  rw [quotientAction_apply]
  change QuotientGroup.mk' (pCore 2 L) (L.normalizerMonoidHom x l) =
    QuotientGroup.mk' (pCore 2 L) l
  apply QuotientGroup.eq_iff_div_mem.mpr
  have hc : ⁅(x : G), (l : G)⁆ ∈ centralizer (V : Set G) :=
    Subgroup.commutator_mem_centralizer_of_normalizes V hx (hLV l.property)
  have hl : ⁅(x : G), (l : G)⁆ ∈ L := by
    exact L.mul_mem ((mem_normalizer_iff.mp x.property l).mp l.property) (L.inv_mem l.property)
  have hm : ⁅(x : G), (l : G)⁆ ∈ L.pCoreIn 2 := hker ▸ ⟨hl, hc⟩
  obtain ⟨a, ha, he⟩ := hm
  have he' : a = L.normalizerMonoidHom x l / l := Subtype.ext (by
    rw [Subgroup.coe_div, normalizerMonoidHom_apply_apply_coe, div_eq_mul_inv]
    simpa only [commutatorElement_def, Subgroup.subtype_apply] using he)
  exact he' ▸ ha

/-- Membership in the kernel means centralizing every coset of the literal quotient. -/
theorem mem_quotientAction_ker (x : normalizer (L : Set G)) :
    x ∈ (quotientAction L).ker ↔ ∀ l : L,
      L.normalizerMonoidHom x l / l ∈ pCore 2 L := by
  constructor
  · intro hx l
    have he := DFunLike.congr_fun hx (QuotientGroup.mk' (pCore 2 L) l)
    rw [quotientAction_apply] at he
    exact QuotientGroup.eq_iff_div_mem.mp he
  · intro hx
    apply MulEquiv.ext
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
    rw [quotientAction_apply]
    exact QuotientGroup.eq_iff_div_mem.mpr (hx l)

variable [Finite G] {T : Sylow 2 G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)
include d

/-- T implements its quotient action inside L, using the full natural action on V. -/
theorem sylow_action_inner (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (t : T) : ∃ l : L,
      quotientAction L ⟨t, d.natural.sylow_normalizes structural t.property⟩ =
        MulAut.conj (QuotientGroup.mk' (pCore 2 L) l) := by
  let a := V.normalizerMonoidHom
    ⟨t, d.natural.sylow_normalizes_seed structural t.property⟩
  obtain ⟨l, hl, he⟩ := d.natural.full_L_action a
  let l' : L := ⟨l, hl⟩
  let t' : normalizer (L : Set G) :=
    ⟨t, d.natural.sylow_normalizes structural t.property⟩
  let lM := inclusion L.le_normalizer l'
  have hc : ((lM⁻¹ * t' : normalizer (L : Set G)) : G) ∈ centralizer (V : Set G) := by
    intro v hv
    have h := he ⟨v, hv⟩
    change l * v * l⁻¹ = (t : G) * v * (t : G)⁻¹ at h
    change v * (l⁻¹ * (t : G)) = (l⁻¹ * (t : G)) * v
    calc
      _ = l⁻¹ * (l * v * l⁻¹) * (t : G) := by group
      _ = l⁻¹ * ((t : G) * v * (t : G)⁻¹) * (t : G) := by rw [h]
      _ = _ := by group
  have hk := seed_centralizer_fixes_quotient d.natural.chosen.normalizes
    d.natural.centralizer_L (lM⁻¹ * t') hc
  rw [map_mul, map_inv, inv_mul_eq_one] at hk
  exact ⟨l', hk.symm.trans (quotientAction_inner L l')⟩

omit [Group G] [Finite G] [AddCommGroup W] [Module (ZMod 2) W] d in
/-- A two-group homomorphic image is detected by any Sylow two-subgroup. -/
private theorem hom_eq_one_of_sylow {X A : Type*} [Group X] [Finite X] [Group A]
    (S : Sylow 2 X) (f : X →* A) (hp : IsPGroup 2 A)
    (hS : ∀ s ∈ S, f s = 1) : ∀ x, f x = 1 := by
  let P := S.mapSurjective f.rangeRestrict_surjective
  have he : (P : Subgroup f.range) = ⊤ :=
    (P.is_maximal' ((hp.to_subgroup f.range).to_subgroup ⊤) le_top).symm
  intro x
  have hx : f.rangeRestrict x ∈ (P : Subgroup f.range) := he ▸ mem_top _
  obtain ⟨s, hs, hse⟩ := hx
  exact (congrArg Subtype.val hse).symm.trans (hS s hs)

/-- The genuine outer-two-group argument extends innerness from T to N_G(L). -/
theorem markedAction_range_inner
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : (L ⧸ pCore 2 L) ≃* SL) :
    (markedAction L e).range ≤ MulAut.innerSubgroup SL := by
  let f := (QuotientGroup.mk' (MulAut.innerSubgroup SL)).comp (markedAction L e)
  have hf : ∀ x, f x = 1 := by
    apply hom_eq_one_of_sylow (T.subtype (d.natural.sylow_normalizes structural)) f
      Automorphisms.outer_sl_isTwoGroup
    intro t ht
    obtain ⟨l, hl⟩ := sylow_action_inner d structural ⟨t, ht⟩
    have he : markedAction L e t = markedAction L e (inclusion L.le_normalizer l) := by
      apply congrArg (MulAut.congr e)
      exact hl.trans (quotientAction_inner L l).symm
    change QuotientGroup.mk' (MulAut.innerSubgroup SL) (markedAction L e t) = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [he, markedAction_inner]
    exact ⟨_, rfl⟩
  rintro a ⟨x, rfl⟩
  exact (QuotientGroup.eq_one_iff _).mp (hf x)


/-- Centerlessness identifies SL₃(2) with its actual inner automorphism subgroup. -/
noncomputable def innerEquiv : SL ≃* MulAut.innerSubgroup SL :=
  MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot Matrix.PSL3Two.center_eq_bot)

/-- The projection obtained from the proved inner action of the full normalizer. -/
noncomputable def project
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : (L ⧸ pCore 2 L) ≃* SL) : normalizer (L : Set G) →* SL :=
  innerEquiv.symm.toMonoidHom.comp ((markedAction L e).codRestrict
    (MulAut.innerSubgroup SL) (fun x => markedAction_range_inner d structural e ⟨x, rfl⟩))

theorem conj_project
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : (L ⧸ pCore 2 L) ≃* SL) (x : normalizer (L : Set G)) :
    MulAut.conj (project d structural e x) = markedAction L e x := by
  exact congrArg Subtype.val (innerEquiv.apply_symm_apply
    (⟨markedAction L e x, markedAction_range_inner d structural e ⟨x, rfl⟩⟩))

theorem project_on_L
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : (L ⧸ pCore 2 L) ≃* SL) :
    (project d structural e).comp (inclusion L.le_normalizer) =
      e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)) := by
  apply MonoidHom.ext
  intro l
  apply MulAut.conj_injective_of_center_eq_bot Matrix.PSL3Two.center_eq_bot
  exact (conj_project d structural e _).trans (markedAction_inner L e l)


@[simp] theorem project_apply_L
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : (L ⧸ pCore 2 L) ≃* SL) (l : L) :
    project d structural e (inclusion L.le_normalizer l) =
      e (QuotientGroup.mk' (pCore 2 L) l) :=
  DFunLike.congr_fun (project_on_L d structural e) l

/-- The projection kernel is precisely the centralizer of the quotient action. -/
theorem project_ker
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : (L ⧸ pCore 2 L) ≃* SL) :
    (project d structural e).ker = (quotientAction L).ker := by
  ext x
  change project d structural e x = 1 ↔ quotientAction L x = 1
  constructor
  · intro h
    have ha := conj_project d structural e x
    rw [h, map_one] at ha
    exact (MulAut.congr e).injective (ha.symm.trans (MulAut.congr e).map_one.symm)
  · intro h
    apply MulAut.conj_injective_of_center_eq_bot Matrix.PSL3Two.center_eq_bot
    rw [conj_project, map_one]
    change (MulAut.congr e) (quotientAction L x) = 1
    rw [h, map_one]

private theorem original_ker : d.qL.ker = pCore 2 L := by
  rw [d.qL_ker]
  exact comap_map_eq_self_of_injective L.subtype_injective _

/-- The source qL gives the original quotient marking through its public
surjectivity and exact-kernel theorems. -/
noncomputable def originalEquiv : (L ⧸ pCore 2 L) ≃* SL :=
  (QuotientGroup.quotientMulEquivOfEq (by exact (original_ker d).symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective d.qL d.qL_surjective)

/-- The original equivalence uses exactly the source's existing qL. -/
theorem originalEquiv_quotient (l : L) :
    originalEquiv d (QuotientGroup.mk' (pCore 2 L) l) = d.qL l := rfl

/-- Relative normality of the literal two-core in the source normalizer. -/
instance core_normal_in_normalizer :
    ((L.pCoreIn 2).subgroupOf (normalizer (L : Set G))).Normal :=
  normal_subgroupOf_of_le_normalizer
    (normalizer_le_normalizer_characteristic_image L (pCore 2 L))

/-- The quotient-action centralizer is a genuine normal supplement to L in M. -/
theorem centralizer_supplement
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : (L ⧸ pCore 2 L) ≃* SL) :
    L.subgroupOf (normalizer (L : Set G)) ⊔ (quotientAction L).ker = ⊤ := by
  apply top_unique
  intro m _
  obtain ⟨q, hq⟩ := e.surjective (project d structural e m)
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  let lM := inclusion L.le_normalizer l
  have hl : project d structural e lM = project d structural e m :=
    (DFunLike.congr_fun (project_on_L d structural e) l).trans hq
  have hk : lM⁻¹ * m ∈ (quotientAction L).ker := by
    rw [← project_ker d structural e, MonoidHom.mem_ker, map_mul, map_inv, hl, inv_mul_cancel]
  have hmem := (L.subgroupOf (normalizer (L : Set G)) ⊔ (quotientAction L).ker).mul_mem
    (mem_sup_left (show lM ∈ L.subgroupOf (normalizer (L : Set G)) from l.property))
    (mem_sup_right hk)
  simpa only [mul_inv_cancel_left] using hmem

/-- The two factors intersect in exactly the embedded O₂(L). -/
theorem centralizer_intersection
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : (L ⧸ pCore 2 L) ≃* SL) :
    L.subgroupOf (normalizer (L : Set G)) ⊓ (quotientAction L).ker =
      (L.pCoreIn 2).subgroupOf (normalizer (L : Set G)) := by
  ext m
  rw [mem_inf, ← project_ker d structural e]
  constructor
  · rintro ⟨hm, hp⟩
    let l : L := ⟨m, hm⟩
    have he : e (QuotientGroup.mk' (pCore 2 L) l) = 1 :=
      (DFunLike.congr_fun (project_on_L d structural e) l).symm.trans hp
    have hl : l ∈ pCore 2 L := (QuotientGroup.eq_one_iff _).mp
      (e.injective (he.trans e.map_one.symm))
    exact ⟨l, hl, rfl⟩
  · rintro ⟨l, hl, he⟩
    have hm : m = inclusion L.le_normalizer l := Subtype.ext he.symm
    subst m
    refine ⟨l.property, ?_⟩
    change project d structural e (inclusion L.le_normalizer l) = 1
    rw [project_apply_L]
    exact (congrArg e ((QuotientGroup.eq_one_iff _).mpr hl)).trans e.map_one

/-- Pair the projection with the literal quotient by the relatively normal L. -/
noncomputable def pairedProjection
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : (L ⧸ pCore 2 L) ≃* SL) :
    normalizer (L : Set G) →* SL ×
      (normalizer (L : Set G) ⧸ L.subgroupOf (normalizer (L : Set G))) :=
  (project d structural e).prod (QuotientGroup.mk' (L.subgroupOf (normalizer (L : Set G))))

theorem pairedProjection_surjective
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : (L ⧸ pCore 2 L) ≃* SL) : Function.Surjective (pairedProjection d structural e) := by
  rintro ⟨s, q⟩
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (L.subgroupOf (normalizer (L : Set G))) q
  obtain ⟨r, hr⟩ := e.surjective (s * (project d structural e m)⁻¹)
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) r
  refine ⟨inclusion L.le_normalizer l * m, Prod.ext ?_ ?_⟩
  · change project d structural e (inclusion L.le_normalizer l * m) = s
    rw [map_mul, project_apply_L]
    rw [hr, inv_mul_cancel_right]
  · change QuotientGroup.mk' (L.subgroupOf (normalizer (L : Set G)))
      (inclusion L.le_normalizer l * m) = _
    have hq : QuotientGroup.mk' (L.subgroupOf (normalizer (L : Set G)))
        (inclusion L.le_normalizer l) = 1 := (QuotientGroup.eq_one_iff _).mpr l.property
    rw [map_mul, hq, one_mul]

theorem pairedProjection_ker
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : (L ⧸ pCore 2 L) ≃* SL) :
    (pairedProjection d structural e).ker =
      (L.pCoreIn 2).subgroupOf (normalizer (L : Set G)) := by
  rw [pairedProjection, MonoidHom.ker_prod, QuotientGroup.ker_mk', project_ker,
    inf_comm, centralizer_intersection d structural e]

/-- M/O₂(L) is the direct product of its marked L-factor and M/L. -/
noncomputable def quotientProduct
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : (L ⧸ pCore 2 L) ≃* SL) :
    (normalizer (L : Set G) ⧸ (L.pCoreIn 2).subgroupOf (normalizer (L : Set G))) ≃*
      SL × (normalizer (L : Set G) ⧸ L.subgroupOf (normalizer (L : Set G))) :=
  (QuotientGroup.quotientMulEquivOfEq (pairedProjection_ker d structural e).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (pairedProjection d structural e)
      (pairedProjection_surjective d structural e))

/-- The direct-factor projection agrees with the constructed ambient map. -/
theorem quotientProduct_mk
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : (L ⧸ pCore 2 L) ≃* SL) (m : normalizer (L : Set G)) :
    quotientProduct d structural e (QuotientGroup.mk' _ m) =
      (project d structural e m, QuotientGroup.mk' _ m) := rfl

/-- Restrict the quotient M → M/L to the quotient-action centralizer. -/
noncomputable def centralizerToQuotient : (quotientAction L).ker →*
    (normalizer (L : Set G) ⧸ L.subgroupOf (normalizer (L : Set G))) :=
  (QuotientGroup.mk' (L.subgroupOf (normalizer (L : Set G)))).comp
    (quotientAction L).ker.subtype

theorem centralizerToQuotient_surjective
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : (L ⧸ pCore 2 L) ≃* SL) : Function.Surjective (centralizerToQuotient (L := L)) := by
  intro q
  obtain ⟨m, hm⟩ := pairedProjection_surjective d structural e (1, q)
  have hp : project d structural e m = 1 := congrArg Prod.fst hm
  have hc : m ∈ (quotientAction L).ker := by
    rw [← project_ker d structural e]
    exact hp
  exact ⟨⟨m, hc⟩, congrArg Prod.snd hm⟩

/-- The kernel on C_M(L/O₂(L)) is still the same literal O₂(L). -/
theorem centralizerToQuotient_ker
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : (L ⧸ pCore 2 L) ≃* SL) :
    (centralizerToQuotient (L := L)).ker =
      ((L.pCoreIn 2).subgroupOf (normalizer (L : Set G))).subgroupOf (quotientAction L).ker := by
  ext c
  change QuotientGroup.mk' (L.subgroupOf (normalizer (L : Set G))) c.val = 1 ↔ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro hc
    exact centralizer_intersection d structural e ▸
      (show c.val ∈ L.subgroupOf (normalizer (L : Set G)) ⊓ (quotientAction L).ker
        from ⟨hc, c.property⟩)
  · rintro ⟨l, _, he⟩
    change (c.val : G) ∈ L
    have he' : (l : G) = (c.val : G) := by
      simpa only [Subgroup.subtype_apply] using he
    exact he' ▸ l.property

/-- The centralizer factor of M/O₂(L) is canonically isomorphic to M/L. -/
noncomputable def centralizerQuotientEquiv
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : (L ⧸ pCore 2 L) ≃* SL) :
    ((quotientAction L).ker ⧸
      ((L.pCoreIn 2).subgroupOf (normalizer (L : Set G))).subgroupOf (quotientAction L).ker) ≃*
      (normalizer (L : Set G) ⧸ L.subgroupOf (normalizer (L : Set G))) :=
  (QuotientGroup.quotientMulEquivOfEq (centralizerToQuotient_ker d structural e).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (centralizerToQuotient (L := L))
      (centralizerToQuotient_surjective d structural e))

/-- The source direct product with its actual quotient-action centralizer factor. -/
noncomputable def sourceQuotientProduct
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : (L ⧸ pCore 2 L) ≃* SL) :
    (normalizer (L : Set G) ⧸ (L.pCoreIn 2).subgroupOf (normalizer (L : Set G))) ≃*
      (L ⧸ pCore 2 L) × ((quotientAction L).ker ⧸
        ((L.pCoreIn 2).subgroupOf (normalizer (L : Set G))).subgroupOf (quotientAction L).ker) :=
  (quotientProduct d structural e).trans
    (e.symm.prodCongr (centralizerQuotientEquiv d structural e).symm)

/-- Projection in the source direct product is the constructed homomorphism. -/
theorem sourceQuotientProduct_first
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : (L ⧸ pCore 2 L) ≃* SL) (m : normalizer (L : Set G)) :
    e (sourceQuotientProduct d structural e (QuotientGroup.mk' _ m)).1 =
      project d structural e m := e.apply_symm_apply _

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.ProjectionEscape.NormalizerStructure

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.ProjectionEscape.NormalizerStructure
open Subgroup Chapter12.Section08 Matrix.PSL3Two
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

omit [Finite G] in
private theorem map_subgroupOf_inclusion (A H J : Subgroup G)
    (hAH : A ≤ H) (hHJ : H ≤ J) :
    (A.subgroupOf H).map (inclusion hHJ) = A.subgroupOf J := by
  apply map_injective J.subtype_injective
  rw [map_map, show J.subtype.comp (inclusion hHJ) = H.subtype from rfl,
    map_subgroupOf_eq_of_le hAH, map_subgroupOf_eq_of_le (hAH.trans hHJ)]

private theorem residual_subgroupOf (i : ℕ) :
    (F.Li L i).subgroupOf (normalizer (L : Set G)) =
      (pResidual 2 ((L ⊓ F.Gi i).subgroupOf (normalizer (L : Set G)))).map
        ((L ⊓ F.Gi i).subgroupOf (normalizer (L : Set G))).subtype := by
  apply map_injective (normalizer (L : Set G)).subtype_injective
  rw [map_subgroupOf_eq_of_le ((F.Li_le L i).trans (inf_le_left.trans L.le_normalizer)),
    map_embedded_pResidual,
    map_subgroupOf_eq_of_le (show L ⊓ F.Gi i ≤ normalizer (L : Set G)
      from inf_le_left.trans L.le_normalizer)]
  simp only [InvariantFlag.Li, show ¬ (3 = 5 ∧ (i = 2 ∨ i = 3)) by omega, if_false]

variable (d : Data T L V F W)
  (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
  (e : (L ⧸ pCore 2 L) ≃* SL)

private theorem stabilizer_image (i : ℕ) (P : Subgroup SL)
    (hP : (F.Gi i).subgroupOf L =
      P.comap (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) :
    ((L ⊓ F.Gi i).subgroupOf (normalizer (L : Set G))).map
      (project d structural e) = P := by
  rw [← map_subgroupOf_inclusion _ _ _ (inf_le_left : L ⊓ F.Gi i ≤ L) L.le_normalizer,
    map_map, project_on_L]
  have hH : (L ⊓ F.Gi i).subgroupOf L = (F.Gi i).subgroupOf L := by
    ext l
    exact and_iff_right l.property
  rw [hH, hP, map_comap_eq_self_of_surjective
    (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L)))]

private theorem residual_image (i : ℕ) (P : Subgroup SL)
    (hP : (F.Gi i).subgroupOf L =
      P.comap (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) :
    ((F.Li L i).subgroupOf (normalizer (L : Set G))).map (project d structural e) =
      MarkedAutomorphisms.residual P := by
  rw [residual_subgroupOf, map_embedded_pResidual, stabilizer_image d structural e i P hP]
  rfl

private theorem point_normalizer_le :
    normalizer (MarkedAutomorphisms.pointA : Set SL) ≤ pointParabolicSL := by
  intro x hx
  obtain ⟨g, hg, he⟩ := MarkedAutomorphisms.point_implementer (MulAut.conj x)
    (fun a ha => (mem_normalizer_iff.mp hx a).mp ha)
  have heq : x = g := MulAut.conj_injective_of_center_eq_bot Matrix.PSL3Two.center_eq_bot he
  exact heq ▸ hg

private theorem stabilizer_preimage (i : ℕ) (P : Subgroup SL)
    (hP : (F.Gi i).subgroupOf L =
      P.comap (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) :
    (L ⊓ F.Gi i).subgroupOf (normalizer (L : Set G)) =
      L.subgroupOf (normalizer (L : Set G)) ⊓ P.comap (project d structural e) := by
  ext m
  constructor
  · rintro ⟨hmL, hmH⟩
    refine ⟨hmL, ?_⟩
    have hl : (⟨m, hmL⟩ : L) ∈ (F.Gi i).subgroupOf L := hmH
    rw [hP] at hl
    change e (QuotientGroup.mk' (pCore 2 L) ⟨m, hmL⟩) ∈ P at hl
    rw [← project_apply_L d structural e] at hl
    exact hl
  · rintro ⟨hmL, hmP⟩
    refine ⟨hmL, ?_⟩
    have hl : (⟨m, hmL⟩ : L) ∈ P.comap
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) := by
      change e (QuotientGroup.mk' (pCore 2 L) ⟨m, hmL⟩) ∈ P
      rw [← project_apply_L d structural e]
      exact hmP
    rw [← hP] at hl
    exact hl

/-- Lifting uses the literal stabilizer preimage and its characteristic residual.
It places no two-group condition on the ambient projection kernel. -/
theorem lift_point_normalizer
    (hP : (F.Gi 1).subgroupOf L =
      pointParabolicSL.comap (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) :
    (normalizer (MarkedAutomorphisms.pointA : Set SL)).comap (project d structural e) ≤
      (normalizer (F.Li L 1 : Set G)).subgroupOf (normalizer (L : Set G)) := by
  let M := normalizer (L : Set G)
  let H := (L ⊓ F.Gi 1).subgroupOf M
  let C := pointParabolicSL.comap (project d structural e)
  have hn : C ≤ normalizer (H : Set M) := by
    rw [show H = L.subgroupOf M ⊓ C from stabilizer_preimage d structural e 1 _ hP]
    apply le_normalizer_iff.mpr
    intro m hm a ha
    exact ⟨(inferInstance : (L.subgroupOf M).Normal).conj_mem a ha.1 m,
      C.mul_mem (C.mul_mem hm ha.2) (C.inv_mem hm)⟩
  have hr := normalizer_le_normalizer_characteristic_image H (pResidual 2 H)
  have hLi : (pResidual 2 H).map H.subtype = (F.Li L 1).subgroupOf M :=
    (residual_subgroupOf 1).symm
  rw [hLi] at hr
  rw [subgroupOf_normalizer_eq ((F.Li_le L 1).trans (inf_le_left.trans L.le_normalizer))]
  exact (comap_mono point_normalizer_le).trans (hn.trans hr)

include d structural

/-- All projection fields follow once one quotient marking matches the original
Sylow, point, and plane stabilizers. The missing flag marking is independent
of the ambient inner-action and direct-product construction. -/
theorem nonempty_of_flag_marking
    (hB : (((T : Subgroup G) ⊓ L).subgroupOf L).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) = borelSL)
    (hP : (F.Gi 1).subgroupOf L =
      pointParabolicSL.comap (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))
    (hQ : (F.Gi 2).subgroupOf L =
      lineParabolicSL.comap (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) :
    Nonempty (NormalizerProjection T L V F) := by
  refine ⟨{
    quotientEquiv := e
    project := project d structural e
    on_L := project_on_L d structural e
    sylow_le := d.natural.sylow_normalizes structural
    inner_sylow_image := ?_
    point_image := ?_
    line_image := ?_
    lift_point_normalizer := lift_point_normalizer d structural e hP }⟩
  · rw [← map_subgroupOf_inclusion _ _ _ (inf_le_right : (T : Subgroup G) ⊓ L ≤ L)
      L.le_normalizer, map_map, project_on_L]
    exact hB
  · rw [residual_image d structural e 1 _ hP, MarkedAutomorphisms.point_residual]
  · rw [residual_image d structural e 2 _ hQ, MarkedAutomorphisms.line_residual]

/-- Application of all constructed fields to the literal normalizer-escape consumer. -/
theorem normalizer_escape_of_flag_marking
    (hB : (((T : Subgroup G) ⊓ L).subgroupOf L).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) = borelSL)
    (hP : (F.Gi 1).subgroupOf L =
      pointParabolicSL.comap (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))
    (hQ : (F.Gi 2).subgroupOf L =
      lineParabolicSL.comap (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))
    (model : ParabolicImageTheorem.{u}) {c : CriticalPath (L := L) F}
    (h : Geometry d c) (k : CoreFacts c) :
    ¬ Y c ≤ normalizer (L : Set G) := by
  obtain ⟨p⟩ := nonempty_of_flag_marking d structural e hB hP hQ
  exact normalizer_escape_of_projection p model h k

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.ProjectionEscape.NormalizerStructure

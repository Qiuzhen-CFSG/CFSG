module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape.Alternatives
public import CFSG.Quasithin.ChapterG.Section08.ThetaFaithfulness
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# The actual two-perfect lifts of the odd theta factors

In 13.1.6 the theta factors are first defined as full preimages in H and
then used as two-perfect groups. We take the two-residual of each full
preimage explicitly. Its image is the original odd supercritical factor;
its kernel is its intrinsic two-core. Thus the exponent and class bounds
hold for the literal quotient used in the escaping-subgroup witness.

Source: Aschbacher--Smith 13.1.6, printed p.868, and G.8.9.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape.Theta
open Chapter1 ChapterG.Section08
variable {G : Type*} [Group G] [Finite G]

/-- The full preimage in H of a supercritical subgroup of O_d(H/O₂(H)). -/
def factorPreimage (H : Subgroup G) (d : ℕ)
    (D : Subgroup (pCore d (XiQuotient H))) : Subgroup H :=
  (D.map (pCore d (XiQuotient H)).subtype).comap (QuotientGroup.mk' (pCore 2 H))

/-- The source factor, with the required two-residual taken before embedding in G. -/
def factor (H : Subgroup G) (d : ℕ)
    (D : Subgroup (pCore d (XiQuotient H))) : Subgroup G :=
  ((pResidual 2 (factorPreimage H d D)).map (factorPreimage H d D).subtype).map H.subtype

omit [Finite G] in
theorem factor_le (H : Subgroup G) (d : ℕ)
    (D : Subgroup (pCore d (XiQuotient H))) : factor H d D ≤ H := map_subtype_le _

theorem factor_twoPerfect (H : Subgroup G) (d : ℕ)
    (D : Subgroup (pCore d (XiQuotient H))) : IsPPerfect 2 (factor H d D) := by
  let e := equivMapOfInjective
    ((pResidual 2 (factorPreimage H d D)).map (factorPreimage H d D).subtype)
    H.subtype H.subtype_injective
  exact (isPPerfect_embedded_pResidual 2 (factorPreimage H d D)).of_surjective
    e.toMonoidHom e.surjective

omit [Finite G] in
theorem factor_normal (H : Subgroup G) {d : ℕ}
    {D : Subgroup (pCore d (XiQuotient H))} (hD : IsSupercriticalPSubgroup d D) :
    ((factor H d D).subgroupOf H).Normal := by
  let : D.Characteristic := hD.characteristic
  let : (factorPreimage H d D).Normal := inferInstanceAs
    (((D.map (pCore d (XiQuotient H)).subtype).comap
      (QuotientGroup.mk' (pCore 2 H))).Normal)
  change ((((pResidual 2 (factorPreimage H d D)).map
    (factorPreimage H d D).subtype).map H.subtype).subgroupOf H).Normal
  rw [subgroupOf, comap_map_eq_self_of_injective H.subtype_injective]
  infer_instance

/-- Taking the two-residual preserves the entire odd quotient image. -/
theorem factor_image (H : Subgroup G) {d : ℕ} [Fact d.Prime] (ho : Odd d)
    (D : Subgroup (pCore d (XiQuotient H))) :
    ((pResidual 2 (factorPreimage H d D)).map (factorPreimage H d D).subtype).map
      (QuotientGroup.mk' (pCore 2 H)) = D.map (pCore d (XiQuotient H)).subtype := by
  rw [map_embedded_pResidual]
  have he : (factorPreimage H d D).map (QuotientGroup.mk' (pCore 2 H)) =
      D.map (pCore d (XiQuotient H)).subtype :=
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  rw [he]
  have hp : IsPGroup d (D.map (pCore d (XiQuotient H)).subtype) :=
    ((pCore_isPGroup (p := d)).to_subgroup D).map _
  have hr : pResidual 2 (D.map (pCore d (XiQuotient H)).subtype) = ⊤ := by
    apply top_unique
    intro x _
    apply mem_pResidual_of_orderOf_coprime
    exact (hp.orderOf_coprime (Nat.coprime_two_right.mpr ho) x).symm
  rw [hr,← MonoidHom.range_eq_map,range_subtype]

/-- The literal quotient of the two-perfect lift is the chosen supercritical factor. -/
def factorQuotientEquiv (H : Subgroup G) {d : ℕ} [Fact d.Prime] (ho : Odd d)
    (D : Subgroup (pCore d (XiQuotient H))) : XiQuotient (factor H d D) ≃* D := by
  let P := factorPreimage H d D
  let E := D.map (pCore d (XiQuotient H)).subtype
  let q := QuotientGroup.mk' (pCore 2 H)
  have hEp : IsPGroup d E := ((pCore_isPGroup (p := d)).to_subgroup D).map _
  let Y := (pResidual 2 P).map P.subtype
  have hYq : Y.map q = E := factor_image H ho D
  let g : Y →* XiQuotient H := q.comp Y.subtype
  have hg : g.range = E := by rw [MonoidHom.range_comp,range_subtype]; exact hYq
  have hk : IsPGroup 2 g.ker := by
    rw [← MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ Y.subtype_injective
  have hzero : pCore 2 g.range = ⊥ := by
    rw [hg]
    exact disjoint_top.mp (pCore_isPGroup.disjoint_of_coprime
      (hEp.to_subgroup ⊤) (Nat.coprime_two_left.mpr ho))
  have he : g.ker = pCore 2 Y := by
    have hh := g.rangeRestrict.comap_pCore_of_ker_isPGroup (p := 2)
      g.rangeRestrict_surjective
      (hk.of_equiv (MulEquiv.subgroupCongr (MonoidHom.ker_rangeRestrict g)).symm)
    rwa [hzero,MonoidHom.comap_bot,MonoidHom.ker_rangeRestrict] at hh
  let e : Y ≃* factor H d D := equivMapOfInjective Y H.subtype H.subtype_injective
  exact (QuotientGroup.congr _ _ e.symm (pCore_map_iso 2 e.symm)).trans
    ((QuotientGroup.quotientMulEquivOfEq he.symm).trans
      ((QuotientGroup.quotientKerEquivRange g).trans
        ((MulEquiv.subgroupCongr hg).trans
          (equivMapOfInjective D _ (pCore d (XiQuotient H)).subtype_injective).symm)))

omit [Finite G] in
/-- If the lift escapes a subgroup containing O₂(H), its odd factor is nontrivial. -/
theorem factor_ne_bot_of_outside {H M : Subgroup G} {d : ℕ}
    {D : Subgroup (pCore d (XiQuotient H))}
    (hcore : H.pCoreIn 2 ≤ M) (hout : ¬ factor H d D ≤ M) : D ≠ ⊥ := by
  intro he
  apply hout
  subst D
  have hP : factorPreimage H d (⊥ : Subgroup (pCore d (XiQuotient H))) = pCore 2 H := by
    simp only [factorPreimage,Subgroup.map_bot,MonoidHom.comap_bot,QuotientGroup.ker_mk']
  exact ((map_mono (f := H.subtype) (map_subtype_le _)).trans
    (map_mono (f := H.subtype) hP.le)).trans hcore

/-- All clauses of the odd source alternative, for the actual escaping lift. -/
theorem factor_oddShape {H M : Subgroup G} {d : ℕ} [Fact d.Prime] (ho : Odd d)
    {D : Subgroup (pCore d (XiQuotient H))} (hD : IsSupercriticalPSubgroup d D)
    (hcore : H.pCoreIn 2 ≤ M) (hout : ¬ factor H d D ≤ M) : OddShape (factor H d D) := by
  let e := factorQuotientEquiv H ho D
  let : Nontrivial D := (Subgroup.nontrivial_iff_ne_bot D).mpr
    (factor_ne_bot_of_outside hcore hout)
  have hexp : Monoid.exponent D = d :=
    ((Fact.out : d.Prime).eq_one_or_self_of_dvd _ hD.exponent_dvd_p).resolve_left
      (fun h => not_subsingleton D (Monoid.exp_eq_one_iff.mp h))
  let : Group.IsNilpotent D := hD.isNilpotent
  refine ⟨factor_twoPerfect H d D,d,Fact.out,ho,
    ((pCore_isPGroup (p := d)).to_subgroup D).of_equiv e.symm,?_,?_⟩
  · exact (Monoid.exponent_eq_of_mulEquiv e).trans hexp
  · exact (Group.nilpotencyClass_le_of_surjective e.symm.toMonoidHom e.symm.surjective).trans
      hD.nilpotencyClass_le_two

/-- The theta lift supplies the original witness, including relative normality
and movement of the actual Ω₁Z(T). Existence of an outside factor is separate. -/
theorem witness_of_factor_outside {T : Sylow 2 G} {L H : Subgroup G}
    {d : ℕ} [Fact d.Prime] (ho : Odd d)
    {D : Subgroup (pCore d (XiQuotient H))} (hD : IsSupercriticalPSubgroup d D)
    (hcore : H.pCoreIn 2 ≤ normalizer (L : Set G))
    (hcent : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤
      normalizer (L : Set G))
    (hout : ¬ factor H d D ≤ normalizer (L : Set G)) :
    Witness T L H (factor H d D) := by
  refine ⟨factor_le H d D,factor_normal H hD,hout,?_,
    Or.inl (factor_oddShape ho hD hcore hout)⟩
  intro he
  rw [commutator_comm] at he
  exact hout ((commutator_eq_bot_iff_le_centralizer.mp he).trans hcent)

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape.Theta

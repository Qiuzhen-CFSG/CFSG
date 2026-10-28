module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowModelsTransport
public import Theory.Representation.BinarySevenCode.WeightTwoResidual
public import Theory.SpecificGroups.Alternating.SevenFiveCover
public import Theory.SpecificGroups.AlternatingFiveCore
/-!
# The literal A₅ quotient of the weight-two point residual

The original projection L → A₇ identifies the point centralizer with the
preimage of its word stabilizer, and maps its perfect residual onto the
pointwise fixer of the two support letters. After quotienting by O₂(L),
this residual has a central kernel of odd order. The proved cyclic-Sylow
transfer argument removes that kernel because the odd-prime ranks of A₅
are at most one. Thus the original restricted projection has a two-group
kernel and gives the actual quotient C_L(e(2))∞/O₂(C_L(e(2))∞) ≅ A₅.

The source consumer applies the resulting quotient to the original
three-residual inclusion. The two support
coordinates also prove disjointness of the exact factors in 12.3.7(2).
This quotient is the faithful input needed for the remaining Thompson
generation and omega fixed-space equality.
No ambient central-cover triviality, arbitrary model, or source callback
is assumed. Final 12.3.7 assembly remains qt-d-1237-thompson-omega, and its
ambient centralizer consumer is qt-d-1236-1238-point-centralizers.

Source: Aschbacher--Smith, Lemma 12.3.7(2), printed p.809, using I.1.2.
-/
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode
universe u


variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}
namespace Setup.NaturalCoordinates
variable (E : S.NaturalCoordinates)

theorem point_centralizer_subgroupOf_eq_comap (v : V) :
    (L ⊓ centralizer ({(v : G)} : Set G)).subgroupOf L =
      (WeightTwoGeometry.stabilizer (E.coordinates v).toAdd).comap S.projection := by
  ext l
  change ((l : G) ∈ L ∧ (l : G) ∈ centralizer ({(v : G)} : Set G)) ↔ _
  rw [and_iff_right l.property, mem_comap, WeightTwoGeometry.mem_stabilizer]
  rw [← E.equivariant]
  constructor
  · intro h
    congr 2
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp h)
  · intro h
    have he := E.coordinates.injective (Multiplicative.toAdd.injective h)
    exact mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he))

theorem point_residual_image (v : V) (hv : weight (E.coordinates v).toAdd.val = 2) :
    ((SylowNormalizer.pointResidual L (v : G)).subgroupOf L).map S.projection =
      WeightTwoGeometry.five (E.coordinates v).toAdd := by
  let C := L ⊓ centralizer ({(v : G)} : Set G)
  have hCL : C ≤ L := inf_le_left
  let e : C ≃* C.subgroupOf L := (subgroupOfEquivOfLe hCL).symm
  have hm := map_solvableResidual_eq e.toMonoidHom e.surjective
  have htrans : ((SylowNormalizer.pointResidual L (v : G)).subgroupOf L) =
      (solvableResidual (C.subgroupOf L)).map (C.subgroupOf L).subtype := by
    apply map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le ((SylowNormalizer.pointResidual_le L (v : G)).trans inf_le_left), ← hm, map_map, map_map]
    rfl
  rw [htrans, E.point_centralizer_subgroupOf_eq_comap,
    map_solvableResidual_comap S.projection S.projection_surjective,
    WeightTwoGeometry.residual_stabilizer_eq_five _ hv]

/-- No odd central-cover kernel remains on the actual weight-two residual. -/
theorem point_residual_projection_kernel_isTwoGroup
    (v : V) (hv : weight (E.coordinates v).toAdd.val = 2) :
    IsPGroup 2 (S.projection.comp (inclusion
      ((SylowNormalizer.pointResidual_le L (v : G)).trans inf_le_left))).ker := by
  let K := SylowNormalizer.pointResidual L (v : G)
  let B := K.subgroupOf L
  have hKL : K ≤ L := (SylowNormalizer.pointResidual_le L (v : G)).trans inf_le_left
  let e : K ≃* B := (subgroupOfEquivOfLe hKL).symm
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let Q := L ⧸ pCore 2 L
  let π : L →* Q := QuotientGroup.mk' (pCore 2 L)
  have hk : pCore 2 L ≤ S.projection.ker := by
    intro l hl
    change S.quotient (QuotientGroup.mk' _ l) = 1
    apply S.quotient.map_eq_one_iff.mpr
    exact (QuotientGroup.eq_one_iff l).mpr (le_centralPreimage _ hl)
  let q : Q →* alternatingGroup (Fin 7) := QuotientGroup.lift _ S.projection hk
  have hqπ : q.comp π = S.projection := rfl
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨l,rfl⟩ := S.projection_surjective a
    exact ⟨π l,rfl⟩
  have hcentral : q.ker ≤ center Q := by
    intro x hx
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) x
    have he : S.projection l = 1 := hx
    have hl : l ∈ centralPreimage (pCore 2 L) := by
      apply (QuotientGroup.eq_one_iff l).mp
      exact S.quotient.map_eq_one_iff.mp he
    exact hl
  let : IsQuasisimple Q := S.hypothesis.quasisimple
  let c : PerfectCentralCovering.Cover Q (alternatingGroup (Fin 7)) :=
    ⟨q,hq,inferInstance,hcentral⟩
  let D := B.map π
  let : Group.IsPerfect D := Group.IsPerfect.map π
  let F := WeightTwoGeometry.five (E.coordinates v).toAdd
  have hD : D.map q = F := by
    rw [map_map,hqπ]
    exact E.point_residual_image v hv
  have hinj : Function.Injective (q.subgroupMap D) :=
    c.injective_on_perfect_subgroup (pCore_quotient_pCore_eq_bot 2) D (by
      intro p hp ho
      change primeRank p (D.map q) ≤ 1
      rw [hD,primeRank_equiv p (WeightTwoGeometry.fiveEquiv _ hv),
        GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 5 p hp (by
          intro he
          rw [he] at ho
          norm_num at ho)]
      have hthree : 3 ≤ p := by
        have htwo := hp.two_le
        have hne : p ≠ 2 := by intro he; rw [he] at ho; norm_num at ho
        omega
      exact (Nat.div_le_div_left hthree (by decide)).trans (by decide : 5 / 3 ≤ 1))
  let f := S.projection.comp (inclusion hKL)
  let j : f.ker →* pCore 2 L :=
    ((inclusion hKL).comp f.ker.subtype).codRestrict _ (fun x => by
      apply (QuotientGroup.eq_one_iff _).mp
      have hxD : π (inclusion hKL x.val) ∈ D :=
        mem_map_of_mem π (show inclusion hKL x.val ∈ B from x.val.property)
      have hh : (q.subgroupMap D) ⟨π (inclusion hKL x.val),hxD⟩ = 1 := by
        apply Subtype.ext
        exact x.property
      exact congrArg Subtype.val (hinj (hh.trans (map_one _).symm)))
  exact pCore_isPGroup.of_injective j (by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun a : pCore 2 L => ((a : L) : G)) hxy)

/-- The projection is restricted to its actual pointwise-two-fixer image. -/
def pointResidualProjection (v : V) (hv : weight (E.coordinates v).toAdd.val = 2) :
    SylowNormalizer.pointResidual L (v : G) →*
      WeightTwoGeometry.five (E.coordinates v).toAdd :=
  (S.projection.comp (inclusion ((SylowNormalizer.pointResidual_le L (v : G)).trans
    inf_le_left))).codRestrict _ (fun x => by
      exact (E.point_residual_image v hv).le (mem_map_of_mem S.projection
        (show (inclusion ((SylowNormalizer.pointResidual_le L (v : G)).trans
          inf_le_left)) x ∈ (SylowNormalizer.pointResidual L (v : G)).subgroupOf L
            from x.property)))

theorem pointResidualProjection_surjective (v : V)
    (hv : weight (E.coordinates v).toAdd.val = 2) :
    Function.Surjective (E.pointResidualProjection v hv) := by
  intro a
  obtain ⟨l,hl,he⟩ := (E.point_residual_image v hv).ge a.property
  exact ⟨⟨l,hl⟩,Subtype.ext he⟩

theorem pointResidualProjection_kernel_isTwoGroup (v : V)
    (hv : weight (E.coordinates v).toAdd.val = 2) :
    IsPGroup 2 (E.pointResidualProjection v hv).ker := by
  have he : (E.pointResidualProjection v hv).ker =
      (S.projection.comp (inclusion ((SylowNormalizer.pointResidual_le L (v : G)).trans
        inf_le_left))).ker := by
    ext x
    exact Subtype.ext_iff
  rw [he]
  exact E.point_residual_projection_kernel_isTwoGroup v hv

/-- The actual point residual has the simple A₅ two-core quotient, even
when the ambient L/O₂(L) is a central cover of A₇. -/
def pointResidualCoreEquiv (v : V) (hv : weight (E.coordinates v).toAdd.val = 2) :
    ((SylowNormalizer.pointResidual L (v : G)) ⧸
      pCore 2 (SylowNormalizer.pointResidual L (v : G))) ≃* alternatingGroup (Fin 5) := by
  let e := WeightTwoGeometry.fiveEquiv (E.coordinates v).toAdd hv
  let f := e.toMonoidHom.comp (E.pointResidualProjection v hv)
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact E.pointResidualProjection_kernel_isTwoGroup v hv
  exact (f.pCoreQuotientEquiv (e.surjective.comp (E.pointResidualProjection_surjective v hv)) hk).trans
    ((QuotientGroup.quotientMulEquivOfEq alternatingGroup.five_twoCore_eq_bot).trans
      QuotientGroup.quotientBot)

/-- Every displacement by the point residual vanishes on the two support letters. -/
theorem point_residual_commutator_support_zero (v : V)
    (hv : weight (E.coordinates v).toAdd.val = 2)
    (x : V) (hx : (x : G) ∈ ⁅V,SylowNormalizer.pointResidual L (v : G)⁆) :
    ∀ i ∈ WeightTwoGeometry.support (E.coordinates v).toAdd,
      (E.coordinates x).toAdd.val i = 0 := by
  let K := SylowNormalizer.pointResidual L (v : G)
  have hKL : K ≤ L := (SylowNormalizer.pointResidual_le L (v : G)).trans inf_le_left
  intro i hi
  let eval : V →* Multiplicative (ZMod 2) :=
    (AddMonoidHom.toMultiplicative
      ((Pi.evalAddMonoidHom (fun _ : Fin 7 => ZMod 2) i).comp evenWords.subtype.toAddMonoidHom)).comp
        E.coordinates.toMonoidHom
  let N := eval.ker.map V.subtype
  have hVN : ⁅V,K⁆ ≤ N := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro k hk y hy
    have hp : S.projection ⟨k,hKL hk⟩ ∈ WeightTwoGeometry.five (E.coordinates v).toAdd :=
      (E.point_residual_image v hv).le (mem_map_of_mem S.projection hk)
    have hpi : (S.projection ⟨k,hKL hk⟩).val.symm i = i := by
      have hh := hp ⟨i,hi⟩
      change (S.projection ⟨k,hKL hk⟩).val i = i at hh
      exact (Equiv.symm_apply_eq _).mpr hh.symm
    let y' : V := ⟨y,hy⟩
    let c : V := V.normalizerMonoidHom ⟨k,S.chosen.normalizes (hKL hk)⟩ y' * y'⁻¹
    refine ⟨c,?_,rfl⟩
    change (E.coordinates c).toAdd.val i = 0
    have he := E.equivariant ⟨k,hKL hk⟩ y'
    dsimp only [c]
    rw [map_mul,map_inv,toAdd_mul,toAdd_inv]
    change ((E.coordinates (V.normalizerMonoidHom _ y')).toAdd +
      -(E.coordinates y').toAdd).val i = 0
    rw [he]
    change (E.coordinates y').toAdd.val ((S.projection ⟨k,hKL hk⟩).val.symm i) +
      -(E.coordinates y').toAdd.val i = 0
    rw [hpi,add_neg_cancel]
  obtain ⟨y,hy,he⟩ := hVN hx
  have hey : y = x := Subtype.ext he
  subst y
  exact hy

theorem point_residual_commutator_factors_disjoint (v : V)
    (hv : weight (E.coordinates v).toAdd.val = 2) :
    Disjoint ⁅V,SylowNormalizer.pointResidual L (v : G)⁆
      (omegaCenterIn (T : Subgroup G) ⊓
        centralizer (SylowNormalizer.pointResidual L (v : G) : Set G)) := by
  let K := SylowNormalizer.pointResidual L (v : G)
  have hKL : K ≤ L := (SylowNormalizer.pointResidual_le L (v : G)).trans inf_le_left
  have hWV : ⁅V,K⁆ ≤ V := le_normalizer_iff_commutator_le_left.mp (hKL.trans S.chosen.normalizes)
  apply disjoint_iff.mpr
  apply bot_unique
  intro x hx
  let x' : V := ⟨x,hWV hx.1⟩
  have hz := E.point_residual_commutator_support_zero v hv x' hx.1
  have hf : ∀ a ∈ WeightTwoGeometry.five (E.coordinates v).toAdd,
      evenRepresentation a.val (E.coordinates x').toAdd = (E.coordinates x').toAdd := by
    intro a ha
    obtain ⟨k,hk,hka⟩ := (E.point_residual_image v hv).ge ha
    rw [← hka,← E.equivariant]
    congr 2
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hx.2.2 k hk)
  have he := WeightTwoGeometry.fixed_eq_zero_of_support_zero _ _ hv hz hf
  exact mem_bot.mpr (congrArg Subtype.val (E.coordinates.injective
    (Multiplicative.toAdd.injective (he.trans (congrArg Multiplicative.toAdd
      (map_one E.coordinates)).symm))))

end Setup.NaturalCoordinates
namespace SylowNormalizer.Points
variable {E : S.NaturalCoordinates} (P : Points E)

/-- Apply the literal two-core recognition to the original source residual. -/
def fiveCoreEquiv : (P.five ⧸ pCore 2 P.five) ≃* alternatingGroup (Fin 5) :=
  E.pointResidualCoreEquiv P.two P.two_weight

/-- The actual A₅ quotient discharges the existing ambient three-residual
inclusion input, without a source callback. -/
theorem five_le_pointThreeResidual : P.five ≤ pointThreeResidual (P.two : G) :=
  P.five_le_three_of_quotient P.fiveCoreEquiv

/-- Disjointness of the exact two factors requested in source 12.3.7(2). -/
theorem five_core_omega_factors_disjoint :
    Disjoint ⁅V,P.five⁆
      (omegaCenterIn (T : Subgroup G) ⊓ centralizer (P.five : Set G)) :=
  E.point_residual_commutator_factors_disjoint P.two P.two_weight

end SylowNormalizer.Points
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

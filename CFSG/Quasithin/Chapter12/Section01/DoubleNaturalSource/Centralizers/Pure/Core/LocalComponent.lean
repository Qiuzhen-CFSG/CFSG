module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Core.Components
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality

/-!
# The actual pure-point residual in the local C-component family

The literal O²(C_L(w)) maps onto the H.9 pure stabilizer with a two-group
kernel. Its quotient by O₂ is therefore quasisimple, and its 2-perfectness
makes it a C-component of C_M(w). Relative Sylow control and the central
point w discharge the other two clauses of Definition 1.2.3.

The genuine 1.2.4 now gives the unique normal C-component of C_G(w)
containing that residual once the original marked ambient Sylow holds.
In dimension five the permitted positive globalW input proves that premise.
Identifying this component with the ordinary component of 1.1.5 and excluding
its model remain with `qt-d-double-natural-pure-fusion`.
Source: Aschbacher--Smith, 12.1.6, printed p.791, using H.9.1 and 1.2.4.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  {B : DoubledBranch T L V n}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
namespace SourceModel
variable (S : B.SourceModel)

include S in
private theorem pureResidual_quotient_quasisimple
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0) :
    IsQuasisimple (B.pointResidual w ⧸ pCore 2 (B.pointResidual w)) := by
  let u : S.setup.natural := ⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩
  let X := B.pointResidual w
  let f : X →* S.setup.stabilizer (Additive.ofMul w) :=
    (S.pureLocalAction w).comp (inclusion
      (le_inf (B.pointResidual_le_normalizer w) ((B.pointResidual_le w).trans inf_le_right)))
  have hf : Function.Surjective f := by
    intro a
    have ha : a.val ∈ S.setup.residual (Additive.ofMul w) :=
      (S.setup.pure_stabilizer_eq_residual u hw).1 ▸ a.property
    rw [← S.pointResidual_image w] at ha
    obtain ⟨l,hl,he⟩ := ha
    exact ⟨⟨l,mem_map_of_mem _ hl⟩,Subtype.ext he⟩
  have hk : IsPGroup 2 f.ker := by
    let j : X →* L := inclusion ((B.pointResidual_le w).trans inf_le_left)
    have hj : f.ker ≤ (pCore 2 L).comap j := by
      intro x hx
      change j x ∈ pCore 2 L
      rw [← B.componentToActionQuotient_ker]
      exact congrArg Subtype.val (show f x = 1 from hx)
    exact (pCore_isPGroup.comap_of_injective j
      (inclusion_injective ((B.pointResidual_le w).trans inf_le_left))).to_le hj
  let := S.setup.finite_group
  let e := S.setup.purePointEquiv u hw
  let : Group.IsPerfect (BinaryNaturalDual.VectorStabilizers.Pure.pointStabilizer
      (S.setup.naturalCoordinates u)) :=
    BinaryNaturalDual.VectorStabilizers.Pure.point_isPerfect
      (by have := S.setup.degree; omega) (S.setup.naturalCoordinates_ne_zero u hw)
  let : Group.IsPerfect (S.setup.stabilizer (Additive.ofMul w)) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let Q := S.setup.stabilizer (Additive.ofMul w) ⧸ pCore 2 (S.setup.stabilizer (Additive.ofMul w))
  obtain ⟨eq⟩ := S.setup.pure_quotient_projective u hw
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin (n-1)) (ZMod 2)) :=
    Atlas.psl_simple_high_rank (F := ZMod 2) (n-1) (by have := S.setup.degree; omega)
  let : IsSimpleGroup Q := eq.isSimpleGroup
  let : Group.IsPerfect Q := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hc : center Q = ⊥ := by
    rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with hc | hc
    · exact hc
    · exact (Group.IsPerfect.not_isMulCommutative Q (center_eq_top_iff.mp hc)).elim
  let : IsQuasisimple Q := {simple := ((QuotientGroup.quotientMulEquivOfEq hc).trans
    QuotientGroup.quotientBot).isSimpleGroup}
  exact IsQuasisimple.of_mulEquiv (f.pCoreQuotientEquiv hf hk).symm

include S in
/-- The literal residual is a C-component in the original normalizer point centralizer. -/
theorem pureResidual_local_component
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0) :
    ((B.pointResidual w).subgroupOf (B.localPointCentralizer w)).IsCComponent := by
  have hX : B.pointResidual w ≤ B.localPointCentralizer w :=
    le_inf (B.pointResidual_le_normalizer w) ((B.pointResidual_le w).trans inf_le_right)
  let e := subgroupOfEquivOfLe hX
  have hXp : IsPPerfect 2 (B.pointResidual w) :=
    (isPPerfect_embedded_pResidual 2 (L ⊓ B.pointCentralizer w)).of_surjective
      (MulEquiv.subgroupCongr (B.pointResidual_eq w).symm).toMonoidHom
      (MulEquiv.subgroupCongr (B.pointResidual_eq w).symm).surjective
  let := S.pureResidual_quotient_quasisimple w hw hp
  let : IsQuasisimple ((B.pointResidual w).subgroupOf (B.localPointCentralizer w) ⧸
      pCore 2 ((B.pointResidual w).subgroupOf (B.localPointCentralizer w))) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  exact isCComponent_of_isPPerfect_of_quasisimple_core_quotient
    ((normal_subgroupOf_iff_le_normalizer hX).mpr
      (B.localPointCentralizer_normalizes_residual w)).isSubnormal
    (hXp.of_surjective e.symm.toMonoidHom e.symm.surjective)

end SourceModel
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch

namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  {B : DoubledBranch T L V n}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
  (S : B.SourceModel)

include S in
/-- The original residual satisfies all three clauses of Definition 1.2.3. -/
theorem pureResidual_mem_local_family
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hwT : (w : G) ∈ (T : Subgroup G)) (hp : (B.coordinates w).toAdd.2 = 0)
    (hs : Chapter1.IsSylowIn 2 (B.pointSylow w) (B.localPointCentralizer w)) :
    B.pointResidual w ∈ Chapter1.L G (B.pointSylow w) := by
  have hX : B.pointResidual w ≤ B.localPointCentralizer w :=
    le_inf (B.pointResidual_le_normalizer w) ((B.pointResidual_le w).trans inf_le_right)
  have hS : B.pointSylow w ≤ B.localPointCentralizer w :=
    inf_le_inf hTM le_rfl
  have hJ : B.pointResidual w ⊔ B.pointSylow w ≤ B.localPointCentralizer w := sup_le hX hS
  refine ⟨(S.pureResidual_local_component w hw hp).subgroupOf_of_le le_sup_left hJ,
    hs.restrict le_sup_right hJ, ?_⟩
  have hw2 : orderOf (w : G) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) (w : G) w.property)
    (fun he => hw (Subtype.ext he))
  have hpc : IsPGroup 2 (zpowers (w : G)) := IsPGroup.of_card (n := 1)
    (by simpa only [Nat.card_zpowers,pow_one] using hw2)
  have hwJ : (w : G) ∈ B.pointResidual w ⊔ B.pointSylow w :=
    (show B.pointSylow w ≤ B.pointResidual w ⊔ B.pointSylow w from le_sup_right)
      ⟨hwT,mem_centralizer_singleton_iff.mpr rfl⟩
  have hn : B.pointCentralizer w ≤ normalizer (zpowers (w : G) : Set G) := by
    have hc : centralizer (zpowers (w : G) : Set G) = B.pointCentralizer w := by
      rw [zpowers_eq_closure,centralizer_closure]
      rfl
    exact hc ▸ Subgroup.centralizer_le_normalizer _
  have hc := le_pCoreIn_of_normalizes hpc (zpowers_le.mpr hwJ)
    ((hJ.trans inf_le_right).trans hn)
  intro he
  have hh := hc (mem_zpowers (w : G))
  rw [he,mem_bot] at hh
  exact hw (Subtype.ext hh)

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original marked residual is in the literal local family, before assuming
that the marked Sylow is Sylow in the full point centralizer. -/
theorem doubleNatural_pure_local_family_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      B.pointResidual w ∈ Chapter1.L G (B.pointSylow w) ∧
        B.pointSylow w ≤ normalizer (B.pointResidual w : Set G) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix
  have hs := D.doubleNatural_relative_pure_sylow_of_many h hmany B S w hw hp hfix
  exact ⟨S.pureResidual_mem_local_family D.sylow_normalizes_component w hw
    ((D.doubledOrbit_E322 h).le_sylow w.property) hp hs,
    (inf_le_inf D.sylow_normalizes_component le_rfl).trans
      (B.localPointCentralizer_normalizes_residual w)⟩

/-- The genuine 1.2.4 produces the unique normal C-component containing the
literal pure-point residual. Its only ambient Sylow premise is the original mark. -/
theorem doubleNatural_pure_containing_component_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, S.MarkedAmbientSylow D.sylow_normalizes_component →
      ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ∃! K : Subgroup (B.pointCentralizer w), K.IsCComponent ∧
        (B.pointResidual w).subgroupOf (B.pointCentralizer w) ≤ K ∧ K.Normal := by
  let := D.doubledOrbit_elementary h
  intro S hs w hw hp hfix
  have hH : B.pointResidual w ≤ B.pointCentralizer w := (B.pointResidual_le w).trans inf_le_right
  obtain ⟨hL,hn⟩ := D.doubleNatural_pure_local_family_of_many h hmany B S w hw hp hfix
  obtain ⟨P₀,hP⟩ := hs w hw hp hfix
  let P : Sylow 2 (B.pointCentralizer w) := P₀
  have he := S.marked_centralizer_eq D.sylow_normalizes_component w hw hp hfix
  have hPm : (P : Subgroup _).map (B.pointCentralizer w).subtype = B.pointSylow w :=
    hP.trans he.symm
  have hPr : (B.pointSylow w).subgroupOf (B.pointCentralizer w) = P := by
    rw [← hPm]
    exact comap_map_eq_self_of_injective (B.pointCentralizer w).subtype_injective _
  have hLP : (B.pointResidual w).subgroupOf (B.pointCentralizer w) ∈
      Chapter1.L (B.pointCentralizer w) P := by
    rw [← hPr]
    exact (Chapter1.mem_LIn_iff_subgroupOf inf_le_right hH).mp ⟨hH,hL⟩
  have hPn : (P : Subgroup _) ≤ normalizer
      ((B.pointResidual w).subgroupOf (B.pointCentralizer w) : Set (B.pointCentralizer w)) := by
    rw [← hPr,← subgroupOf_normalizer_eq hH]
    exact comap_mono hn
  have hw2 : orderOf (w : G) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) (w : G) w.property)
    (fun he => hw (Subtype.ext he))
  have hsq : IsSQTK KnownSimple.IsKnownSimple (B.pointCentralizer w) :=
    h.simpleQTKE.twoLocal_sqtk (isTwoLocal_involution_centralizer hw2)
  have hq : IsSQTK KnownSimple.IsKnownSimple
      (B.pointCentralizer w ⧸ pCore 2 (B.pointCentralizer w)) := by
    refine ⟨?_,hsq.isKGroup.quotient _⟩
    intro p hprime hodd
    let : Fact p.Prime := ⟨hprime⟩
    exact (primeRank_quotient_le_of_isTwoGroup p hodd _ pCore_isPGroup).trans
      (hsq.stronglyQuasithin p hprime hodd)
  exact Chapter1.Section02.lemma_1_2_4_containment_normality_source hq P hLP hPn

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- In dimension five the permitted positive globalW input discharges the
ambient Sylow premise of the original 1.2.4 application. -/
theorem doubleNatural_five_pure_containing_component_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 5)
    (hW : 0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ∃! K : Subgroup (B.pointCentralizer w), K.IsCComponent ∧
        (B.pointResidual w).subgroupOf (B.pointCentralizer w) ≤ K ∧ K.Normal := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix
  have hs : S.MarkedAmbientSylow D.sylow_normalizes_component := by
    intro v hv hpv hfixv
    exact (D.doubleNatural_five_marked_pure_sylow_of_many h hmany B hW S v hv hpv hfixv).2
  exact D.doubleNatural_pure_containing_component_of_many h hmany B S hs w hw hp hfix

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

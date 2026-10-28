module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCrossing
public import Theory.Representation.SL3.PointRadicalDualDisplacement

/-!
# Crossing geometry for the remaining secondary-core enlargement

For A≤Q with [L,A]≤U, the literal doubled-dual image of A is fixed by
L and hence by the point radical. Point-local displacements belong to
the image of K₂∩Q, since Q normalizes K₂. Those displacements contain
the entire point-radical fixed space. As U≤K₂, lifting through the
original map Q→Q/U gives A≤K₂.

Apply this to the crossed natural center U^(t⁻¹), using the original
full-module identity [U^(t⁻¹),L]=W≤U. Thus the elementary overgroup
U U^(t⁻¹)>U lies in O₂(K_Z)∩K₂∩Q, through the actual selected component
and its two subtype embeddings. The final application constructs the
marked MS data from the existing whole-core alternatives.

In particular this crossing witness does not establish the remaining
strict inequality K₂<O₂(K_Z)K₂ in original 4.3.14(3). That inequality
and the resulting marked-input contradiction remain open here. No
SecondarySourceData, terminal quotient model or enlargement premise is
used in these results.

Source: Aschbacher--Smith, original 4.3.9--14, printed pp.616--618;
C.1.34(3), printed pp.136--137, for the natural and doubled-dual modules.
The displacement calculation uses PointRadicalDualDisplacement.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open Matrix.PSL3.LinearThree Representation.SL3ParabolicNatural
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ} {d : MSData c n}

/-- A subgroup of Q fixed modulo U by the original line local lies in K₂. -/
theorem RootCoordinates.core_line_displacement_le_secondary (m : RootCoordinates d)
    (hn : 1 < n) (D : Chapter12.Section02.ChosenModule T L V)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier)
    (A : Subgroup G) (hAQ : A ≤ Q c) (hcomm : ⁅L,A⁆ ≤ U c) :
    A ≤ secondary c := by
  obtain ⟨p,hp,hk,he,_⟩ := d.exists_elementary_dual_lifts
  let B := (((secondary c ⊓ Q c).subgroupOf (Q c)).map p).toAddSubgroup'
  have hRN : R₂ c ≤ normalizer (secondary c : Set G) :=
    (R₂ c).le_normalizer.trans ((m.radical_normalizer_source hn D).trans inf_le_right)
  have hB (g : Matrix.SpecialLinearGroup (Fin 3) d.field.Carrier)
      (hg : g ∈ pointLocalSL d.field.Carrier) (v) :
      (((Representation.specialLinearNatural 3).dual.prod
        (Representation.specialLinearNatural 3).dual) g v - v) ∈ B := by
    obtain ⟨k,hkg⟩ := m.secondaryProjection_surjective hn ⟨g,hg⟩
    have hkg' := congrArg Subtype.val hkg
    rw [m.secondaryProjection_apply] at hkg'
    obtain ⟨q,hq⟩ := hp (Multiplicative.ofAdd v)
    let k' : K c := ⟨k,secondary_le_original k.property⟩
    let q' : Q c := ⟨(k:G)*(q:G)*(k:G)⁻¹,
      (mem_normalizer_iff.mp (d.doubleDual.2.1 k'.property) q).mp q.property⟩
    have hz : ((q' * q⁻¹ : Q c) : G) ∈ secondary c :=
      le_normalizer_iff_commutator_le_left.mp ((core_le_radical c).trans hRN)
        (commutator_mem_commutator k.property q.property)
    refine ⟨q' * q⁻¹,⟨hz,(q' * q⁻¹).property⟩,?_⟩
    change p (q' * q⁻¹) = Multiplicative.ofAdd _
    apply Multiplicative.toAdd.injective
    rw [map_mul,map_inv,toAdd_mul,toAdd_inv,he k' q q' rfl,hkg',hq]
    simp only [toAdd_ofAdd,sub_eq_add_neg]
  intro a ha
  let q : Q c := ⟨a,hAQ ha⟩
  have hv (g : pointRadicalSL d.field.Carrier) :
      (((Representation.specialLinearNatural 3).dual.prod
        (Representation.specialLinearNatural 3).dual) g.val.val (p q).toAdd) = (p q).toAdd := by
    have hg : g.val.val ∈ lineLocalSL d.field.Carrier := by
      have hpoint := (mem_pointLocalSL_iff d.field.Carrier g.val.val).mp g.val.property
      have hrad := (mem_pointRadicalSL_iff d.field.Carrier g.val).mp g.property
      exact (mem_lineLocalSL_iff _ _).mpr ⟨hpoint.2.2,hrad.2.2.1,hrad.2.2.2⟩
    obtain ⟨l,hl,hlg⟩ := hL.ge hg
    let q' : Q c := ⟨(l:G)*a*(l:G)⁻¹,
      (mem_normalizer_iff.mp (d.doubleDual.2.1 l.property) a).mp (hAQ ha)⟩
    have hz : q' * q⁻¹ ∈ p.ker := by
      rw [hk]
      exact hcomm (commutator_mem_commutator hl ha)
    have hpq : p q' = p q := by
      have hh : p (q' * q⁻¹) = 1 := hz
      rw [map_mul,map_inv] at hh
      exact mul_inv_eq_one.mp hh
    have hh := he l q q' rfl
    rw [hpq,hlg] at hh
    exact hh.symm
  have hqB := doubledDual_pointRadical_fixed_mem B hB (p q).toAdd hv
  obtain ⟨b,hb,hbq⟩ := hqB
  change p b = p q at hbq
  have hz : b⁻¹*q ∈ p.ker := by
    change p (b⁻¹*q) = 1
    rw [map_mul,map_inv,hbq,inv_mul_cancel]
  have hzK : ((b⁻¹*q : Q c) : G) ∈ secondary c :=
    m.center_le_secondary hn (by
      have hh : b⁻¹*q ∈ (U c).subgroupOf (Q c) := hk ▸ hz
      exact hh)
  have hh := (secondary c).mul_mem hb.1 hzK
  simpa only [Subgroup.coe_mul,Subgroup.coe_inv,Subgroup.subtype_apply,mul_inv_cancel_left] using hh

/-- The original crossed center lies in K₂, with no component-core premise. -/
theorem MSData.crossed_center_le_secondary (d : MSData c n) (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier)
    (hSL : ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier) :
    (U c).map (MulAut.conj c.t⁻¹).toMonoidHom ≤ secondary c := by
  obtain ⟨m⟩ := d.rootCoordinates_of_marked_parabolic hL hSL
  apply m.core_line_displacement_le_secondary hn D hL _ (d.crossed_center_le_core hn D hL)
  rw [commutator_comm,d.crossed_center_fullModule D,←d.fullModule]
  exact le_normalizer_iff_commutator_le_left.mp (c.le_component.trans d.natural.2.1)

/-- The actual elementary crossing overgroup grows beyond U inside both
K₂ and the selected component core. Its growth does not witness escape
from K₂. All three intersections are in the original ambient group. -/
theorem MSData.sourceComponent_crossed_center_join (d : MSData c n) (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier)
    (hSL : ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier) :
    let B := d.sourceComponent hn D h hL hSL
    let A := U c ⊔ (U c).map (MulAut.conj c.t⁻¹).toMonoidHom
    IsElementaryAbelian 2 A ∧ U c < A ∧
      A ≤ (B.map (rootNormalizer c).subtype).pCoreIn 2 ⊓ secondary c ⊓ Q c := by
  obtain ⟨m⟩ := d.rootCoordinates_of_marked_parabolic hL hSL
  obtain ⟨hA,hUA,hAQ⟩ := d.crossed_center_elementary_growth hn D hL
  have hP := (d.sourceComponent_core_layer hn D h hL hSL).2.1
  have hK := sup_le (m.center_le_secondary hn) (d.crossed_center_le_secondary hn D hL hSL)
  exact ⟨hA,hUA,le_inf (le_inf (hAQ.trans inf_le_left |>.trans hP) hK)
    (hAQ.trans inf_le_right)⟩

open scoped MatrixGroups
/-- Consume the original whole-core alternatives with their actual MS selection.
The resulting elementary overgroup remains inside K₂ even though it is
larger than U and lies in O₂(K_Z). Classification is still an explicit input. -/
theorem source_component_crossed_center_join_of_alternatives
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : ¬ ChapterC.IsBlock c.K)
    (n : ℕ) (hn : 1 < n)
    (F : ChapterB.QuasisimpleSource.BinaryField) (hdegree : F.degree = n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F.Carrier))
    (P : Subgroup G) (hP : Chapter1.IsSylowIn 2 P (K c ⊔ c.I.pCoreIn 2))
    (hm : MSModuleAlternatives (K c) (c.I.pCoreIn 2) P n F.Carrier e) :
    let A := U c ⊔ (U c).map (MulAut.conj c.t⁻¹).toMonoidHom
    ∃ B : Subgroup (rootNormalizer c), B.IsCComponent ∧ B.Normal ∧
      IsQuasisimple (B ⧸ pCore 2 B) ∧ secondary c < B.map (rootNormalizer c).subtype ∧
      IsElementaryAbelian 2 A ∧ U c < A ∧
      A ≤ (B.map (rootNormalizer c).subtype).pCoreIn 2 ⊓ secondary c ⊓ Q c := by
  obtain ⟨d,_,hL,hSL⟩ := DoubledMarking.source_msData_of_alternatives D hf hb n hn
    F hdegree e P hP hm
  obtain ⟨hB,hBn,hsec,_⟩ := d.sourceComponent_spec hn D h hL hSL
  exact ⟨d.sourceComponent hn D h hL hSL,hB,hBn,
    d.sourceComponent_quasisimple hn D h hL hSL,hsec,
    d.sourceComponent_crossed_center_join hn D h hL hSL⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock

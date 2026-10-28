module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.AlternatingSeven.PointCentralizer
public import Theory.SpecificGroups.AlternatingSix.TwoKernelResidual

/-!
# Excluding the ordinary constrained A₇ block

The actual intersection L ∩ C_G(V₁) maps onto the six-letter alternating
point stabilizer with two-group kernel. Its solvable residual is therefore
a C-component of C_G(V₁), with literal A₆ two-core quotient. The rank-two
normalizer theorem makes it contain every cubic residual normalizing V₁.
The conjugate original cubic residual moves V₁, giving the contradiction.

The proof retains both exchanged plane rows and has no model-action,
partition, residual, or block-exclusion callback. Source: Aschbacher--Smith
15.1.25(5), printed p.1102, using A.3.18.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The quotient of the actual centralizer intersection is the actual A₆
point stabilizer, with its two-kernel retained. -/
theorem ExchangedSource.constrained_a7_intersection_quotient
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M) (h : PreparedChosenModule T M V)
    (a : d.ConstrainedA7Alternative) :
    Nonempty (((d.L ⊓ centralizer (d.nineFixedPlane : Set G) : Subgroup G) ⧸
      pCore 2 (d.L ⊓ centralizer (d.nineFixedPlane : Set G) : Subgroup G)) ≃*
        alternatingGroup (Fin 6)) := by
  obtain ⟨q,i,hpoint⟩ := s.constrained_a7_point_centralizer hG hTM h a
  let C := centralizer (d.nineFixedPlane : Set G)
  let H := d.L ⊓ C
  let f := q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 d.L))
  let P := MulAction.stabilizer (alternatingGroup (Fin 7)) i
  have hmem (l : d.L) : (l : G) ∈ C ↔ f l ∈ P := by
    exact SetLike.ext_iff.mp hpoint l
  let g : H →* P := {
    toFun x := ⟨f ⟨x,x.property.1⟩,(hmem _).mp x.property.2⟩
    map_one' := Subtype.ext (map_one f)
    map_mul' := fun x y => Subtype.ext (map_mul f ⟨x,x.property.1⟩ ⟨y,y.property.1⟩) }
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨l,hl⟩ := (q.surjective.comp (QuotientGroup.mk'_surjective _)) y.val
    have hl' : f l = y.val := hl
    have hc : (l : G) ∈ C := (hmem l).mpr (hl'.symm ▸ y.property)
    exact ⟨⟨l,l.property,hc⟩,Subtype.ext hl⟩
  have hker : g.ker = (pCore 2 d.L).comap (inclusion (show H ≤ d.L from inf_le_left)) := by
    ext x
    change g x = 1 ↔ _
    rw [Subtype.ext_iff]
    change q (QuotientGroup.mk' (pCore 2 d.L) ⟨x,x.property.1⟩) = 1 ↔ _
    rw [q.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff (inclusion (show H ≤ d.L from inf_le_left) x)
  have hk : IsPGroup 2 g.ker := by
    rw [hker]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
  let eP : P ≃* alternatingGroup (Fin 6) := AlternatingSix.SmallIndex.pointEquiv i
  let f6 := eP.toMonoidHom.comp g
  have hf6 := eP.surjective.comp hg
  have hk6 : IsPGroup 2 f6.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ eP.injective]
    exact hk
  have hcore : f6.ker = pCore 2 H := by
    have hh := f6.comap_pCore_of_ker_isPGroup hf6 hk6
    simpa only [AlternatingSix.TwoKernelResidual.twoCore_eq_bot,MonoidHom.comap_bot] using hh
  exact ⟨QuotientGroup.liftEquiv _ hf6 hcore.symm⟩


end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Subgroup ChapterC Theory.SpecificGroups.BinaryComponentResidual
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The original A₇ alternative is impossible: its point-stabilizer residual
centralizes V₁, while the conjugate cubic residual moves V₁. Both exchanged
plane sizes are retained, and all partition and cover-action premises are
proved from the literal alternative. -/
theorem ExchangedSource.no_constrained_a7
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M) (h : PreparedChosenModule T M V) :
    ¬ d.ConstrainedA7Alternative := by
  intro a
  let C := centralizer (d.nineFixedPlane : Set G)
  let H := d.L ⊓ C
  let K := (solvableResidual H).map H.subtype
  obtain ⟨eH⟩ := s.constrained_a7_intersection_quotient hG hTM h a
  have hL := (s.constrained_a7_residual_and_movement hG h a.block).1
  have hLn : d.G1 ≤ normalizer (d.L : Set G) := by
    rw [hL]
    exact d.G1.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (primeToResidual 3 _))
  have hCn : C ≤ normalizer (d.L : Set G) :=
    (centralizer_le s.marked_le_fixed).trans hLn
  have hn : (H.subgroupOf C).Normal := normal_subgroupOf_of_le_normalizer
    ((le_inf hCn C.le_normalizer).trans inf_normalizer_le_normalizer_inf)
  obtain ⟨hK,⟨eK⟩⟩ := AlternatingSix.TwoKernelResidual.residual_component H C inf_le_right hn eH
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv eK.symm
  have hf := Facts.of_equiv eK alternatingSix
  obtain ⟨t,ht,htS⟩ := s.exchange_exists
  let f := (MulAut.conj t).toMonoidHom
  let A := d.nineCubic.map f
  have hex := (s.exchanges t ht htS).2
  have hWne : d.nineFixedPlane ≠ ⊥ := by
    intro he
    rcases s.sizes with hs | hs <;> have hc := hs.2.2.1 <;> rw [he,card_bot] at hc <;> omega
  have hAn : A ≤ normalizer (d.nineFixedPlane : Set G) := by
    have hnY : d.nineCubic ≤ normalizer (d.nineMovingPlane : Set G) :=
      le_normalizer_iff_commutator_le_left.mpr s.cubic_moving.le
    have hh := map_mono (f := f) hnY
    rw [map_normalizer_eq_of_bijective _ (MulAut.conj t).bijective,hex] at hh
    exact hh
  have hAid : (primeToResidual 3 A).map A.subtype = A := by
    rw [←map_embedded_primeToResidual_of_hom 3 d.nineCubic f,s.cubic_idempotent]
  have hAmove : ⁅d.nineFixedPlane,A⁆ ≠ ⊥ := by
    have hh := congrArg (map f) s.cubic_moving
    rw [map_commutator,hex] at hh
    exact fun hz => hWne (hh.symm.trans hz)
  let := h.elementary
  have hWtwo : IsPGroup 2 d.nineFixedPlane :=
    (IsElementaryAbelian.isPGroup 2 V).to_le inf_le_left
  have hrN : primeRank 3 (normalizer (d.nineFixedPlane : Set G)) ≤ 2 :=
    (hG.twoLocal_sqtk ⟨d.nineFixedPlane,hWne,hWtwo,rfl⟩).stronglyQuasithin
      3 Nat.prime_three (by decide)
  exact hK.not_centralizes_of_cubic_movement le_rfl hf.1 hf.2.1 hf.2.2
    hrN hAn hAid hAmove ((map_subtype_le _).trans inf_le_right)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

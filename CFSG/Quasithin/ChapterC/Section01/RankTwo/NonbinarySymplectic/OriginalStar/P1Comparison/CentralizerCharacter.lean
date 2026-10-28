module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison.IntersectionCoordinates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison.RadicalCoordinates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison.SpanAction
public import Theory.GroupAction.QuotientCommutatorPairing
public import Theory.GroupTheory.Commutator.RectangularPairing
public import Theory.Representation.SL2NaturalOffenders.ScalarRows
public import Theory.GroupTheory.CommutatorPreimage.Membership
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison.NaturalCommutator

/-!
# The original relative centralizer as the kernel of a scalar character

Commutators pair the original span with the point-core preimage, with values
in the intersection modulo the critical line. Natural coordinates identify the
latter quotient and the radical modulo the span with the same SL₂ two-space.
Levi conjugation therefore makes every commutator row an equivariant additive
endomorphism. The natural SL₂ centralizer theorem makes each row scalar.

Evaluating at the first basis vector extracts a homomorphism to the additive
field. Its restriction to the whole natural kernel is the original opposite
coordinate, and its kernel is exactly the relative centralizer used in MS93
(3.7), printed p.877. No cardinality of the relative centralizer or splitting
of the original extension is assumed.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement IsMulCommutative
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.ParabolicOppositeSections
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison
variable {F G : Type*} [Field F] [Group G] [Finite G] [CharP F 2]
variable {κ : G →* Sp F} {A B : Subgroup G} (s : MarkedPair κ A B)

/-- The actual mixed commutators give a multiplicative family of middle-coordinate rows. -/
theorem exists_middle_commutator_pairing :
    ∃ b : (A ⊔ B : Subgroup G) →*
      ((pointRadicalAmbient.comap κ) →* Multiplicative (Fin 2→F)),
      ∀ x q, b x q=intersectionMiddle s
        ⟨⁅(x:G),(q:G)⁆,pointCore_span_commutator_le_intersection s
          (commutator_mem_commutator x.property q.property)⟩ := by
  let I := A ⊓ B
  let R := ⁅A,B⁆
  let : IsMulCommutative I := IsMulCommutative.of_comm (fun x y => Subtype.ext
    ((mem_centralizer_iff.mp (span_centralizes_intersection s
      ((le_sup_left : A ≤ A ⊔ B) x.property.1)) y y.property).symm))
  let : (R.subgroupOf I).Normal := inferInstance
  let m : (I ⧸ R.subgroupOf I) →* Multiplicative (Fin 2→F) :=
    QuotientGroup.lift (R.subgroupOf I) (intersectionMiddle s)
      (by rw [intersectionMiddle_kernel s])
  let p := centralQuotientCommutatorPairing (A ⊔ B) (pointRadicalAmbient.comap κ) I R
    (inf_le_left.trans le_sup_left) (span_centralizes_intersection s)
    (pointCore_span_commutator_le_intersection s) (intersection_pointCore_commutator s)
  let b : (A ⊔ B : Subgroup G) →*
      ((pointRadicalAmbient.comap κ) →* Multiplicative (Fin 2→F)) := {
    toFun x := m.comp (p x)
    map_one' := by ext q; simp
    map_mul' := by intro x y; ext q; simp }
  refine ⟨b,?_⟩
  intro x q
  change m (p x q)=_
  rw [centralQuotientCommutatorPairing_apply]
  exact QuotientGroup.lift_mk' _ _ _

/-- Each row descends through the actual radical-coordinate map. -/
theorem exists_radical_commutator_rows :
    ∃ d : (A ⊔ B : Subgroup G) →*
      (Multiplicative (Fin 2→F) →* Multiplicative (Fin 2→F)),
      ∀ x q, d x (radicalCoordinates κ q)=intersectionMiddle s
        ⟨⁅(x:G),(q:G)⁆,pointCore_span_commutator_le_intersection s
          (commutator_mem_commutator x.property q.property)⟩ := by
  obtain ⟨b,hb⟩ := exists_middle_commutator_pairing s
  have hk : ∀ x, (radicalCoordinates κ).ker ≤ (b x).ker := by
    intro x q hq
    rw [radicalCoordinates_kernel s] at hq
    change b x q=1
    rw [hb]
    apply (intersectionMiddle_kernel s).ge
    exact span_commutator_le_critical s (commutator_mem_commutator x.property hq)
  obtain ⟨d,hd⟩ := MonoidHom.exists_descended_rectangular_pairing
    (MonoidHom.id (A ⊔ B : Subgroup G)) (radicalCoordinates κ)
    Function.surjective_id (radicalCoordinates_onto s) b
    (by intro x hx; change x=1 at hx; rw [hx,map_one]) hk
  exact ⟨d,fun x q => (hd x q).trans (hb x q)⟩


omit [Finite G] [CharP F 2] in
private theorem pointCore_levi_conjugate_mem
    (l : Matrix.SpecialLinearGroup (Fin 2) F) (g : G) (hg : κ g=(pointLevi l).val)
    (q : pointRadicalAmbient.comap κ) :
    g*q*g⁻¹ ∈ pointRadicalAmbient.comap κ := by
  obtain ⟨r,hr,he⟩ := q.property
  refine ⟨pointLevi l*r*(pointLevi l)⁻¹,
    (inferInstance : (pointRadical (F := F)).Normal).conj_mem r hr (pointLevi l),?_⟩
  change (pointLevi l).val*r.val*(pointLevi l).val⁻¹=κ (g*q*g⁻¹)
  rw [map_mul,map_mul,map_inv,hg,←he]
  rfl

/-- The literal point Levi intertwines every descended commutator row. -/
theorem radical_commutator_rows_equivariant
    (d : (A ⊔ B : Subgroup G) →*
      (Multiplicative (Fin 2→F) →* Multiplicative (Fin 2→F)))
    (hd : ∀ x q, d x (radicalCoordinates κ q)=intersectionMiddle s
      ⟨⁅(x:G),(q:G)⁆,pointCore_span_commutator_le_intersection s
        (commutator_mem_commutator x.property q.property)⟩) :
    ∀ x (l : Matrix.SpecialLinearGroup (Fin 2) F) (v : Fin 2→F),
      (d x (Multiplicative.ofAdd (l.val.mulVec v))).toAdd =
        l.val.mulVec (d x (Multiplicative.ofAdd v)).toAdd := by
  have hI : ∀ x : (A ⊔ B : Subgroup G), x.val ∈ A ⊓ B → d x=1 := by
    intro x hx
    apply MonoidHom.ext
    intro v
    obtain ⟨q,rfl⟩ := radicalCoordinates_onto s v
    change d x (radicalCoordinates κ q)=1
    rw [hd]
    apply (intersectionMiddle_kernel s).ge
    exact intersection_pointCore_commutator s (commutator_mem_commutator hx q.property)
  intro x l v
  obtain ⟨g,hg⟩ := s.onto (pointLevi l).val
  have hgP : κ g ∈ stabilizer (point F) := by rw [hg]; exact pointLocal_le (pointLevi l).property
  let x' : (A ⊔ B : Subgroup G) :=
    ⟨g*x*g⁻¹,(mem_normalizer_iff.mp (span_normalized s hgP) x).mp x.property⟩
  have hdx : d x'=d x := by
    have hh := hI (x'/x) (levi_span_fixed_mod_intersection s l g hg x x' rfl)
    rw [map_div] at hh
    exact div_eq_one.mp hh
  obtain ⟨q,hq⟩ := radicalCoordinates_onto s (Multiplicative.ofAdd v)
  let q' : pointRadicalAmbient.comap κ :=
    ⟨g*q*g⁻¹,pointCore_levi_conjugate_mem l g hg q⟩
  have hq' : radicalCoordinates κ q'=Multiplicative.ofAdd (l.val.mulVec v) := by
    rw [radicalCoordinates_levi_conjugation g l hg q q' rfl,hq]
    rfl
  have hh := intersectionMiddle_levi_conjugation s l g hg
    ⟨⁅(x:G),(q:G)⁆,pointCore_span_commutator_le_intersection s
      (commutator_mem_commutator x.property q.property)⟩
    ⟨⁅(x':G),(q':G)⁆,pointCore_span_commutator_le_intersection s
      (commutator_mem_commutator x'.property q'.property)⟩ (by
      change ⁅g*(x:G)*g⁻¹,g*(q:G)*g⁻¹⁆=g*⁅(x:G),(q:G)⁆*g⁻¹
      simp only [commutatorElement_def]
      group)
  rw [←hd,←hd,hdx,hq',hq] at hh
  exact hh


/-- The relative centralizer is the kernel of a scalar character extending the natural cofixed coordinate. -/
theorem exists_relativeCentralizer_character :
    ∃ φ : (A ⊔ B : Subgroup G) →* Multiplicative F,
      (∀ a : A, φ ⟨a, (le_sup_left : A ≤ A ⊔ B) a.property⟩=s.naturalLine a) ∧
      φ.ker=(commutatorPreimage (A ⊔ B) (pointRadicalAmbient.comap κ) ⁅A,B⁆).subgroupOf (A ⊔ B) := by
  obtain ⟨d,hd⟩ := exists_radical_commutator_rows s
  obtain ⟨φ,hφ⟩ := Representation.SL2NaturalOffenders.exists_scalar_rows d
    (radical_commutator_rows_equivariant s d hd)
  have hscalar (x : (A ⊔ B : Subgroup G)) (q : pointRadicalAmbient.comap κ) :
      intersectionMiddle s ⟨⁅(x:G),(q:G)⁆,pointCore_span_commutator_le_intersection s
        (commutator_mem_commutator x.property q.property)⟩ =
        Multiplicative.ofAdd ((φ x).toAdd • (radicalCoordinates κ q).toAdd) := by
    rw [←hd]
    exact hφ x (radicalCoordinates κ q).toAdd
  refine ⟨φ,?_,?_⟩
  · intro a
    obtain ⟨q,hq⟩ := radicalCoordinates_onto s (Multiplicative.ofAdd ![1,0])
    have hh := (hscalar ⟨a,(le_sup_left : A ≤ A ⊔ B) a.property⟩ q).symm.trans
      (natural_commutator_middle s a q)
    rw [hq] at hh
    apply Multiplicative.toAdd.injective
    simpa only [toAdd_ofAdd,Pi.smul_apply,smul_eq_mul,Matrix.cons_val_zero,mul_one] using
      congrArg (fun v : Multiplicative (Fin 2→F) => v.toAdd 0) hh
  · ext x
    have hn : A ⊔ B ≤ normalizer (⁅A,B⁆ : Subgroup G) :=
      sup_le (normalizer_commutator_ge_left A B) (normalizer_commutator_ge_right A B)
    change φ x=1 ↔ x.val ∈ commutatorPreimage (A ⊔ B) (pointRadicalAmbient.comap κ) ⁅A,B⁆
    rw [mem_commutatorPreimage_iff _ _ _ hn,and_iff_right x.property]
    constructor
    · intro hx q hq
      have hm := hscalar x ⟨q,hq⟩
      rw [hx] at hm
      have hz : intersectionMiddle s ⟨⁅(x:G),q⁆,pointCore_span_commutator_le_intersection s
          (commutator_mem_commutator x.property hq)⟩=1 := by
        simpa only [toAdd_one,zero_smul,ofAdd_zero] using hm
      exact (intersectionMiddle_kernel s).le hz
    · intro hx
      obtain ⟨q,hq⟩ := radicalCoordinates_onto s (Multiplicative.ofAdd ![1,0])
      have hm := hscalar x q
      have hz : intersectionMiddle s ⟨⁅(x:G),(q:G)⁆,pointCore_span_commutator_le_intersection s
          (commutator_mem_commutator x.property q.property)⟩=1 :=
        (intersectionMiddle_kernel s).ge (hx q q.property)
      rw [hz,hq] at hm
      apply Multiplicative.toAdd.injective
      simpa only [toAdd_ofAdd,toAdd_one,Pi.zero_apply,Pi.smul_apply,smul_eq_mul,
        Matrix.cons_val_zero,mul_one] using
        (congrArg (fun v : Multiplicative (Fin 2→F) => v.toAdd 0) hm).symm

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison

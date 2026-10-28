module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Symplectic.OriginalOrbits
public import Theory.SpecificGroups.SymplecticSix.FanoClasses
/-!
# The four involution classes of the original generated group

The constructed Fano-core coordinates preserve the actual symplectic
representation. Image size and alternation show that E-conjugacy on
O₂(H₀) is exactly H₀-conjugacy. The four orbits of lengths 7, 7, 21, 28
therefore give Suzuki types b₁, a₂, c₂, b₃. The invariant-Lagrangian
representative theorem proves that every involution of E belongs to
exactly one of these four classes. Two distinct elements of the first
family multiply into the third family through the literal core map. The
original nonidentity fixed-line generator is identified inside the first
family, using its actual marked transvection.

The final existence theorem constructs the coordinates from MarkedC3;
no module marking or class assertion is an additional premise. This
completes the intrinsic four-class calculation of the solvable source
branch. Selecting the original case (ii) from genuine 13.4.7 remains
separate, with earlier-source discharge at qt-d-1341-fixed-core-source.
Source: Aschbacher–Smith 13.4.9, printed pp.906–907, and H.5.3(3–4).
-/

@[expose] public noncomputable section

namespace Quasithin.I5.C3Recognition.SymplecticMark
open Subgroup Matrix Theory.SpecificGroups.SymplecticSix
open BinaryLinearThree.FanoTransvection BinaryLinearThree.FanoLocalStructure
variable {G : Type*} [Group G] {S : DSystem .C3 G}
variable (m : SymplecticMark S)
variable (b : BinaryLinearThree.Vector ≃ₗ[ZMod 2] m.planeSpace S.basePlane)
variable (P : Sylow 2 G) (hP : (P : Subgroup G) = S.T)

include P hP in
/-- The four plane-core orbits remain distinct in the whole recognized group. -/
theorem fanoLift_isConj_iff (a c : BinaryLinearThree.Core) :
    IsConj (m.fanoLift b (Multiplicative.ofAdd a)) (m.fanoLift b (Multiplicative.ofAdd c)) ↔
      c ∈ orbit a := by
  constructor
  · intro h
    have hh := m.hom.map_isConj h
    simp only [m.fanoLift_marking] at hh
    have he := orbit_eq_of_shear_isConj (m.fanoEmbedding b) (m.fanoEmbedding_isotropic b)
      (m.fanoEmbedding_injective b) a c hh
    rw [he]
    exact ⟨1,by rw [map_one]; rfl⟩
  · intro h
    obtain ⟨g,hg⟩ := (m.fanoLift_orbit_iff b P hP a c).mpr h
    exact isConj_iff.mpr ⟨g.val,hg⟩

end Quasithin.I5.C3Recognition.SymplecticMark

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Subgroup Theory.GroupTheory Quasithin.I5 Quasithin.I5.C3Recognition
open Chapter12.Section02 SolvableCentralizerC3 BinaryLinearThree.FanoLocalStructure
open BinaryLinearThree.FanoTransvection Theory.SpecificGroups.SymplecticSix
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
variable (D : ChosenModule T L V) (z : G) (H₀ : Subgroup G) (C : MarkedC3 T L z H₀)
variable (m : SymplecticMark C.system)
variable (b : BinaryLinearThree.Vector ≃ₗ[ZMod 2] m.planeSpace C.system.basePlane)

/-- E-conjugacy on the literal ambient core is exactly its marked Fano orbit. -/
theorem original_fano_generated_conjugate_iff (a c : BinaryLinearThree.Core) :
    (∃ g ∈ generated (normalizer (L : Set G)) z H₀,
      MulAut.conj g (originalFanoEquiv D z H₀ C m b (Multiplicative.ofAdd a)).val =
        (originalFanoEquiv D z H₀ C m b (Multiplicative.ofAdd c)).val) ↔ c ∈ orbit a := by
  let E := generated (normalizer (L : Set G)) z H₀
  have hTE : (T : Subgroup G) ≤ E :=
    D.sylow_normalizes_component.trans (first_le_generated _ _ _)
  rw [←m.fanoLift_isConj_iff b (T.subtype hTE) C.chamber.symm,isConj_iff]
  simp only [originalFanoEquiv_apply]
  constructor
  · rintro ⟨g,hg,he⟩
    exact ⟨⟨g,hg⟩,Subtype.ext he⟩
  · rintro ⟨g,he⟩
    exact ⟨g.val,g.property,congrArg Subtype.val he⟩

include D C m b in
/-- No two of the four H₀-orbits are fused by E. -/
theorem original_core_generated_fusion (a c : H₀.pCoreIn 2) :
    (∃ g ∈ generated (normalizer (L : Set G)) z H₀, MulAut.conj g a.val = c.val) ↔
      ∃ g ∈ H₀, MulAut.conj g a.val = c.val := by
  obtain ⟨x,rfl⟩ := (originalFanoEquiv D z H₀ C m b).surjective a
  obtain ⟨y,rfl⟩ := (originalFanoEquiv D z H₀ C m b).surjective c
  exact (original_fano_generated_conjugate_iff D z H₀ C m b x.toAdd y.toAdd).trans
    (original_fano_orbit_iff D z H₀ C m b x.toAdd y.toAdd).symm

/-- The intrinsic symplectic invariant of an element of the original two-core. -/
noncomputable def originalCoreSignature (a : H₀.pCoreIn 2) : ℕ × Bool :=
  involutionSignature (m.hom ⟨a.val, ((pCoreIn_le 2 H₀).trans
    (show H₀ ≤ generated (normalizer (L : Set G)) z H₀ from le_sup_right)) a.property⟩)

theorem originalCoreSignature_fano (a : BinaryLinearThree.Core) :
    originalCoreSignature z H₀ C m (originalFanoEquiv D z H₀ C m b (Multiplicative.ofAdd a)) =
      tensorSignature a := by
  unfold originalCoreSignature
  rw [originalFanoEquiv_marking]
  exact shear_signature _ _ (m.fanoEmbedding_injective b) a

/-- The four source types b₁, a₂, c₂, b₃ are determined by displacement
image sizes 2,4,4,8 and alternation false,true,false,false. -/
theorem originalFanoFamily_signature_iff (a : H₀.pCoreIn 2) :
    (a.val ∈ originalFanoFamily D z H₀ C m b pointComplements ↔
      originalCoreSignature z H₀ C m a = (2, false)) ∧
    (a.val ∈ originalFanoFamily D z H₀ C m b lineComplements ↔
      originalCoreSignature z H₀ C m a = (4, true)) ∧
    (a.val ∈ originalFanoFamily D z H₀ C m b weightTwo ↔
      originalCoreSignature z H₀ C m a = (4, false)) ∧
    (a.val ∈ originalFanoFamily D z H₀ C m b basisComplements ↔
      originalCoreSignature z H₀ C m a = (8, false)) := by
  obtain ⟨x,rfl⟩ := (originalFanoEquiv D z H₀ C m b).surjective a
  have hm (A : Set BinaryLinearThree.Core) :
      (originalFanoEquiv D z H₀ C m b x).val ∈ originalFanoFamily D z H₀ C m b A ↔
        x.toAdd ∈ A := by
    constructor
    · rintro ⟨c,hc,he⟩
      have hh := congrArg Multiplicative.toAdd
        ((originalFanoEquiv D z H₀ C m b).injective (Subtype.ext he))
      exact hh ▸ hc
    · intro hx
      exact ⟨x.toAdd,hx,rfl⟩
  have hs := originalCoreSignature_fano D z H₀ C m b x.toAdd
  change originalCoreSignature z H₀ C m (originalFanoEquiv D z H₀ C m b x) =
    tensorSignature x.toAdd at hs
  simp only [hm,hs]
  exact four_families_signature_iff x.toAdd

/-- The intersection with W of each E-class is its actual H₀-orbit. -/
theorem original_generated_class_intersection (a : H₀.pCoreIn 2) :
    {c : G | c ∈ H₀.pCoreIn 2 ∧ ∃ g ∈ generated (normalizer (L : Set G)) z H₀,
      MulAut.conj g a.val = c} =
    originalFanoFamily D z H₀ C m b
      (orbit ((originalFanoEquiv D z H₀ C m b).symm a).toAdd) := by
  obtain ⟨x,rfl⟩ := (originalFanoEquiv D z H₀ C m b).surjective a
  rw [MulEquiv.symm_apply_apply,←originalFanoFamily_orbit D z H₀ C m b x.toAdd]
  ext c
  constructor
  · rintro ⟨hc,hg⟩
    exact (original_core_generated_fusion D z H₀ C m b _ ⟨c,hc⟩).mp hg
  · intro hg
    obtain ⟨g,hgH,rfl⟩ := hg
    have hn : H₀ ≤ normalizer (H₀.pCoreIn 2 : Set G) :=
      H₀.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H₀ (pCore 2 H₀))
    exact ⟨(mem_normalizer_iff.mp (hn hgH) _).mp
      (originalFanoEquiv D z H₀ C m b x).property,⟨g,(show H₀ ≤ generated (normalizer (L : Set G)) z H₀ from le_sup_right) hgH,rfl⟩⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable

namespace Quasithin.I5.C3Recognition.SymplecticMark
open Subgroup Matrix Theory.SpecificGroups.SymplecticSix
open BinaryLinearThree.FanoTransvection BinaryLinearThree.FanoLocalStructure
variable {G : Type*} [Group G] {S : DSystem .C3 G}
variable (m : SymplecticMark S)
variable (b : BinaryLinearThree.Vector ≃ₗ[ZMod 2] m.planeSpace S.basePlane)
variable (P : Sylow 2 G) (hP : (P : Subgroup G) = S.T)

theorem fanoLift_fourRepresentatives_involution (i : Fin 4) :
    m.fanoLift b (Multiplicative.ofAdd (fourRepresentatives i)) ≠ 1 ∧
      m.fanoLift b (Multiplicative.ofAdd (fourRepresentatives i)) ^ 2 = 1 := by
  constructor
  · intro h
    exact fourRepresentatives_ne_zero i (congrArg Multiplicative.toAdd
      (m.fanoLift_injective b (h.trans (map_one _).symm)))
  · rw [pow_two,←map_mul]
    have he : Multiplicative.ofAdd (fourRepresentatives i) * Multiplicative.ofAdd (fourRepresentatives i) = 1 :=
      congrArg Multiplicative.ofAdd (ZModModule.add_self (fourRepresentatives i))
    rw [he,map_one]

/-- These four marked elements are pairwise nonconjugate in the whole C₃ group. -/
theorem fanoLift_fourRepresentatives_isConj_iff (i j : Fin 4) :
    IsConj (m.fanoLift b (Multiplicative.ofAdd (fourRepresentatives i)))
      (m.fanoLift b (Multiplicative.ofAdd (fourRepresentatives j))) ↔ i = j := by
  constructor
  · intro h
    have he := involutionSignature_eq_of_isConj (m.hom.map_isConj h)
    simp only [m.fanoLift_marking,shear_signature _ _ (m.fanoEmbedding_injective b)] at he
    exact fourRepresentatives_signature_injective he
  · rintro rfl
    exact IsConj.refl _

include P hP in
/-- Every involution of the recognized group has exactly one of the four marked types. -/
theorem exists_unique_fano_involution_class (a : G) (ha : a ^ 2 = 1) (ha1 : a ≠ 1) :
    ∃! i : Fin 4, IsConj a (m.fanoLift b (Multiplicative.ofAdd (fourRepresentatives i))) := by
  obtain ⟨c,hc⟩ := m.square_one_representative P hP a ha
  obtain ⟨x,hx⟩ := (m.planeFanoEquiv b P hP).surjective ⟨MulAut.conj c a,hc⟩
  have hxv : m.fanoLift b x = MulAut.conj c a := congrArg Subtype.val hx
  have hx0 : x.toAdd ≠ 0 := by
    intro hz
    have hx1 : x = 1 := congrArg Multiplicative.ofAdd hz
    rw [hx1,map_one] at hxv
    exact ha1 ((MulAut.conj c).injective (hxv.symm.trans (map_one _).symm))
  obtain ⟨i,hi⟩ := exists_fourRepresentatives_orbit x.toAdd hx0
  have hax : IsConj a (m.fanoLift b x) := isConj_iff.mpr ⟨c,hxv.symm⟩
  have hia := (m.fanoLift_isConj_iff b P hP (fourRepresentatives i) x.toAdd).mpr hi
  have hai := hax.trans hia.symm
  refine ⟨i,hai,?_⟩
  intro j hj
  exact (m.fanoLift_fourRepresentatives_isConj_iff b j i).mp (hj.symm.trans hai)

end Quasithin.I5.C3Recognition.SymplecticMark

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Subgroup Theory.GroupTheory Quasithin.I5 Quasithin.I5.C3Recognition
open Chapter12.Section02 SolvableCentralizerC3 BinaryLinearThree.FanoLocalStructure
open BinaryLinearThree.FanoTransvection Theory.SpecificGroups.SymplecticSix
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
variable (D : ChosenModule T L V) (z : G) (H₀ : Subgroup G) (C : MarkedC3 T L z H₀)
variable (m : SymplecticMark C.system)
variable (b : BinaryLinearThree.Vector ≃ₗ[ZMod 2] m.planeSpace C.system.basePlane)

/-- The four literal core representatives give exactly the involution classes of E. -/
theorem original_four_involution_classes
    (a : G) (haE : a ∈ generated (normalizer (L : Set G)) z H₀)
    (ha : a ^ 2 = 1) (ha1 : a ≠ 1) :
    ∃! i : Fin 4, ∃ g ∈ generated (normalizer (L : Set G)) z H₀,
      MulAut.conj g a = (originalFanoEquiv D z H₀ C m b
        (Multiplicative.ofAdd (fourRepresentatives i))).val := by
  let E := generated (normalizer (L : Set G)) z H₀
  have hTE : (T : Subgroup G) ≤ E :=
    D.sylow_normalizes_component.trans (first_le_generated _ _ _)
  let aE : E := ⟨a,haE⟩
  have haE2 : aE ^ 2 = 1 := Subtype.ext ha
  have haE1 : aE ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  have he (i : Fin 4) : IsConj aE (m.fanoLift b (Multiplicative.ofAdd (fourRepresentatives i))) ↔
      ∃ g ∈ E, MulAut.conj g a = (originalFanoEquiv D z H₀ C m b
        (Multiplicative.ofAdd (fourRepresentatives i))).val := by
    rw [isConj_iff]
    constructor
    · rintro ⟨g,hg⟩
      exact ⟨g.val,g.property,congrArg Subtype.val hg⟩
    · rintro ⟨g,hg,he⟩
      exact ⟨⟨g,hg⟩,Subtype.ext he⟩
  simpa only [he] using m.exists_unique_fano_involution_class b
    (T.subtype hTE) C.chamber.symm aE haE2 haE1

/-- Two distinct elements of β₁ multiply into the literal γ₂ family. -/
theorem original_pointFamily_product_weightTwo {a c : G}
    (ha : a ∈ originalFanoFamily D z H₀ C m b pointComplements)
    (hc : c ∈ originalFanoFamily D z H₀ C m b pointComplements) (hac : a ≠ c) :
    a * c ∈ originalFanoFamily D z H₀ C m b weightTwo := by
  obtain ⟨_,⟨p,rfl⟩,rfl⟩ := ha
  obtain ⟨_,⟨q,rfl⟩,rfl⟩ := hc
  have hpq : p ≠ q := fun h => hac (h ▸ rfl)
  refine ⟨BinaryLinearThree.FanoDecomposition.pointSpike p + BinaryLinearThree.FanoDecomposition.pointSpike q,
    (mem_weightTwo_iff _).mpr ⟨p,q,hpq,rfl⟩,?_⟩
  exact congrArg Subtype.val ((originalFanoEquiv D z H₀ C m b).map_mul _ _)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Subgroup Theory.GroupTheory Quasithin.I5 Quasithin.I5.C3Recognition
open Chapter12.Section02 SolvableCentralizerC3 BinaryLinearThree.FanoLocalStructure
open BinaryLinearThree.FanoTransvection Theory.SpecificGroups.SymplecticSix
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
variable (D : ChosenModule T L V) (z : G) (H₀ : Subgroup G) (C : MarkedC3 T L z H₀)
variable (m : SymplecticMark C.system)
variable (b : BinaryLinearThree.Vector ≃ₗ[ZMod 2] m.planeSpace C.system.basePlane)

theorem original_four_representatives_involutions (i : Fin 4) :
    let a := (originalFanoEquiv D z H₀ C m b (Multiplicative.ofAdd (fourRepresentatives i))).val
    a ≠ 1 ∧ a ^ 2 = 1 := by
  obtain ⟨hn,hp⟩ := m.fanoLift_fourRepresentatives_involution b i
  exact ⟨fun h => hn (Subtype.ext h),congrArg Subtype.val hp⟩

include D C in
/-- Construct four marked, pairwise distinct involution classes in the actual
E, using only the original marked chamber to supply the module coordinates. -/
theorem exists_original_four_involution_classes :
    ∃ r : Fin 4 → H₀.pCoreIn 2,
      (∀ i, (r i).val ≠ 1 ∧ (r i).val ^ 2 = 1) ∧
      (∀ a ∈ generated (normalizer (L : Set G)) z H₀, a ^ 2 = 1 → a ≠ 1 →
        ∃! i : Fin 4, ∃ g ∈ generated (normalizer (L : Set G)) z H₀,
          MulAut.conj g a = (r i).val) := by
  obtain ⟨m,b,_⟩ := exists_original_fano_orbit_marking D z H₀ C
  exact ⟨fun i => originalFanoEquiv D z H₀ C m b (Multiplicative.ofAdd (fourRepresentatives i)),
    original_four_representatives_involutions D z H₀ C m b,
    original_four_involution_classes D z H₀ C m b⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Subgroup Theory.GroupTheory Quasithin.I5 Quasithin.I5.C3Recognition
open Chapter12.Section02 SolvableCentralizerC3 BinaryLinearThree.FanoLocalStructure
open BinaryLinearThree.FanoTransvection
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual fixed-line generator is in β₁, not merely in an unmarked
abstract transvection class. -/
theorem fixed_line_mem_original_pointFamily
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : G) (H₀ : Subgroup G) (C : MarkedC3 T L z H₀)
    (mark : SymplecticMark C.system)
    (b : BinaryLinearThree.Vector ≃ₗ[ZMod 2] mark.planeSpace C.system.basePlane)
    {d : G} (hd : d ∈ V ⊓ centralizer (L : Set G)) (hd1 : d ≠ 1) :
    d ∈ originalFanoFamily D z H₀ C mark b pointComplements := by
  let E := generated (normalizer (L : Set G)) z H₀
  have hdM : d ∈ normalizer (L : Set G) := D.sylow_normalizes_component (D.le_sylow hd.1)
  let aE : E := ⟨d,(first_le_generated _ _ _) hdM⟩
  have ha0 : aE ∈ C.system.family 0 := C.first.symm ▸ hdM
  let a₀ : C.system.family 0 := ⟨aE,ha0⟩
  have hbase : C.system.Inc C.system.basePoint C.system.basePlane := ⟨1,rfl,rfl⟩
  obtain ⟨v,hv⟩ := b.surjective ⟨mark.point C.system.basePoint,mark.point_mem_planeSpace hbase⟩
  have hv' : mark.fanoEmbedding b v = mark.point C.system.basePoint := congrArg Subtype.val hv
  have hv0 : v ≠ 0 := by
    intro he
    rw [he,map_zero] at hv'
    exact mark.point_nonzero _ hv'.symm
  let p : BinaryLinearThree.Point := ⟨v,hv0⟩
  refine ⟨BinaryLinearThree.FanoDecomposition.pointSpike p,⟨p,rfl⟩,?_⟩
  change (mark.fanoLift b (Multiplicative.ofAdd (BinaryLinearThree.FanoDecomposition.pointSpike p))).val = d
  change _ = aE.val
  apply congrArg (fun x : E => x.val)
  apply mark.hom_injective
  rw [mark.fanoLift_marking,shear_pointSpike]
  change Matrix.PSp4Three.transvection (mark.fanoEmbedding b v) 1 = mark.hom aE
  rw [hv']
  exact (fixed_line_transvection h structural D m z H₀ C mark a₀ hd hd1).symm

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable

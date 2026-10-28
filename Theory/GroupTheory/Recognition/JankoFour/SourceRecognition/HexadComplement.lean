module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.FullCubicInvolutions
public import Theory.Mathieu.M22.UniversalMultiplier.TwoPrimary.HexadLifting
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.PlaneOverlaps
public import Mathlib.GroupTheory.Complement
public import Theory.GroupTheory.PerfectCentralSupplement

/-!
# A marker-free subgroup above the original hexad A₆ section

For the literal C_H(X), quotient by the specified cubic X and retain its
map to the native M₂₂. The kernel is central of order two, so the existing
M₂₂ covering theorem lifts the specified native hexad A₆ section. Its full
inverse image in C_H(X) has order 1080 and contains X. The coprime orders
three and two make it disjoint from the original marker line. Together
with that line it is exactly the preimage of the same A₆ section.
When the full cubic centralizer is perfect, transfer at the prime-to-three
index 2464 forces the scalar into its derived subgroup. The A₆ image then
makes the constructed subgroup perfect. It is exactly the derived subgroup
of the full A₆ preimage, so this construction is canonical there.

The original cubic projection places this subgroup inside the actual
point–plane overlap. MathieuJ4RecognitionApplication.HexadComplement
constructs that overlap and applies the result with no additional premise.
The invariant complement in the extraspecial core and the extension across
the outer involution remain necessary for the full Todd complement.

Source: Aschbacher–Segev, The uniqueness of groups of type J₄,
Invent. Math. 105 (1991), (4.8), printed p.599, DOI 10.1007/BF01232280.
The native A₆ lifting theorem and its source are in
Theory.Mathieu.M22.UniversalMultiplier.TwoPrimary.HexadLifting.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative Pointwise
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open LocalGeometry Sporadic.Mathieu LocalGeometry.LocalSubgroups
variable {G : Type*} [Group G] [Finite G] {z : G}
variable (h : IsTypeJ4 z) (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
  (X : Sylow 3 (CubicLift.subgroup e))

theorem fullCubic_hexadSection {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    ∃ s : alternatingGroup (Fin 6) →* (fullCubicCentralizer e X ⧸ fullCubicScalar e X),
      (fullCubicDoubleProjection h e X).comp s =
        (MulAction.stabilizer M22 B).subtype.comp (m22HexadSection hB) := by
  have hp : IsPGroup 2 (fullCubicDoubleProjection h e X).ker :=
    IsPGroup.of_card (n := 1) (by rw [fullCubicDoubleProjection_kernel_card h e X]; norm_num)
  exact M22UniversalMultiplier.exists_hexadSection_lift (fullCubicDoubleProjection h e X)
    (fullCubicDoubleProjection_surjective h e X)
    (fullCubicDoubleProjection_kernel_central h e X) hp hB

private theorem card_preimage_of_surjective {A B : Type*} [Group A] [Group B]
    [Finite A] (f : A →* B) (hf : Function.Surjective f) (U : Subgroup B) :
    Nat.card (U.comap f) = Nat.card f.ker * Nat.card U := by
  let g : U.comap f →* U := (f.comp (U.comap f).subtype).codRestrict U (fun x => x.property)
  have hg : Function.Surjective g := by
    intro u
    obtain ⟨x,hx⟩ := hf u.val
    exact ⟨⟨x,by change f x ∈ U; rw [hx]; exact u.property⟩,Subtype.ext hx⟩
  have hk : g.ker = f.ker.subgroupOf (U.comap f) := by
    ext x
    change g x=1 ↔ f x.val=1
    exact Subtype.ext_iff
  have hle : f.ker ≤ U.comap f := by
    intro x hx
    change f x ∈ U
    rw [hx]
    exact U.one_mem
  have hh := g.ker.card_mul_index
  rw [index_ker,MonoidHom.range_eq_top.mpr hg,card_top,hk,
    Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv] at hh
  exact hh.symm

/-- An actual subgroup of order 1080 over the specified native A₆ section,
containing the original cubic and disjoint from the original marker line. -/
theorem fullCubic_hexad_complement {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    ∃ A : Subgroup (fullCubicCentralizer e X),
      Nat.card A = 1080 ∧ fullCubicScalar e X ≤ A ∧
      Disjoint (fullCubicProjection h e X).ker A ∧
      A.map (fullCubicSimpleProjection h e X) =
        ((MulAction.stabilizer M22 B).subtype.comp (m22HexadSection hB)).range ∧
      (fullCubicProjection h e X).ker ⊔ A =
        (((MulAction.stabilizer M22 B).subtype.comp (m22HexadSection hB)).range).comap
          (fullCubicSimpleProjection h e X) := by
  obtain ⟨s,hs⟩ := fullCubic_hexadSection h e X hB
  let q := QuotientGroup.mk' (fullCubicScalar e X)
  let f := fullCubicDoubleProjection h e X
  let j := (MulAction.stabilizer M22 B).subtype.comp (m22HexadSection hB)
  have hj : Function.Injective j :=
    (MulAction.stabilizer M22 B).subtype_injective.comp (m22HexadSection_injective hB)
  have hfs (a) : f (s a) = j a := DFunLike.congr_fun hs a
  have hsi : Function.Injective s := by
    intro a b he
    apply hj
    rw [←hfs a,←hfs b,he]
  have hsc : Nat.card s.range = Nat.card (alternatingGroup (Fin 6)) :=
    (Nat.card_congr (Equiv.ofInjective s hsi)).symm
  have hjc : Nat.card j.range = Nat.card (alternatingGroup (Fin 6)) :=
    (Nat.card_congr (Equiv.ofInjective j hj)).symm
  let A := s.range.comap q
  have hAr : A.map q = s.range := map_comap_eq_self (by
    rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
    exact le_top)
  have hAc : Nat.card A=1080 := by
    rw [card_preimage_of_surjective q (QuotientGroup.mk'_surjective _) s.range,
      QuotientGroup.ker_mk',fullCubicScalar_card h e X,
      hsc,nat_card_alternatingGroup]
    norm_num
  have hscalar : fullCubicScalar e X ≤ A := by
    intro x hx
    change q x ∈ s.range
    have he : q x=1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [he]
    exact s.range.one_mem
  have hdis : Disjoint (fullCubicProjection h e X).ker A := by
    apply disjoint_def.mpr
    intro x hxK hxA
    obtain ⟨a,ha⟩ := hxA
    have hfx : f (q x)=1 := by
      change fullCubicSimpleProjection h e X x=1
      change (innerProjection e) ((cubicCentralizerProjection h e X)
        (fullCubicProjection h e X x))=1
      rw [show fullCubicProjection h e X x=1 from hxK,map_one,map_one]
    have ha1 : a=1 := hj (by rw [←hfs a,ha,hfx,map_one])
    have hqx : q x=1 := by rw [←ha,ha1,map_one]
    have hxS : x ∈ fullCubicScalar e X := (QuotientGroup.eq_one_iff x).mp hqx
    have h2 := pow_card_eq_one' (x := (⟨x,hxK⟩ : (fullCubicProjection h e X).ker))
    rw [fullCubicProjection_kernel_card h e X] at h2
    have h3 := pow_card_eq_one' (x := (⟨x,hxS⟩ : fullCubicScalar e X))
    rw [fullCubicScalar_card h e X] at h3
    have hx2 : x^2=1 := congrArg Subtype.val h2
    have hx3 : x^3=1 := congrArg Subtype.val h3
    rw [pow_succ,hx2,one_mul] at hx3
    exact hx3
  have him : A.map (fullCubicSimpleProjection h e X) = j.range := by
    change A.map (f.comp q)=j.range
    rw [←map_map,hAr,←MonoidHom.range_comp,hs]
  let D := j.range.comap (fullCubicSimpleProjection h e X)
  have hAD : A ≤ D := (map_le_iff_le_comap).mp him.le
  have hKD : (fullCubicProjection h e X).ker ≤ D := by
    intro x hx
    change fullCubicSimpleProjection h e X x ∈ j.range
    have he : fullCubicSimpleProjection h e X x=1 := by
      change (innerProjection e) ((cubicCentralizerProjection h e X)
        (fullCubicProjection h e X x))=1
      rw [show fullCubicProjection h e X x=1 from hx,map_one,map_one]
    rw [he]
    exact j.range.one_mem
  have hDc : Nat.card D=2160 := by
    rw [card_preimage_of_surjective _ (fullCubicSimpleProjection_surjective h e X),
      fullCubicSimpleProjection_ker,fullCubicCentralizer_center_card h e X,
      hjc,nat_card_alternatingGroup]
    norm_num
  have hcomp : ((fullCubicProjection h e X).ker.subgroupOf D).IsComplement' (A.subgroupOf D) := by
    apply isComplement'_of_card_mul_and_disjoint
    · rw [Nat.card_congr (subgroupOfEquivOfLe hKD).toEquiv,
        Nat.card_congr (subgroupOfEquivOfLe hAD).toEquiv,
        fullCubicProjection_kernel_card h e X,hAc,hDc]
    · apply disjoint_def.mpr
      intro x hx hy
      exact Subtype.ext (disjoint_def.mp hdis hx hy)
  have hgen := congrArg (map D.subtype) hcomp.sup_eq_top
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hKD,map_subgroupOf_eq_of_le hAD,
    ←MonoidHom.range_eq_map,range_subtype] at hgen
  exact ⟨A,hAc,hscalar,hdis,him,hgen⟩


private theorem hexad_inner_mem {B : Finset (Fin 22)} (a : MulAction.stabilizer M22 B) :
    MulAut.conj a.val ∈ designStabilizer B := by
  let g : m22DesignAut := ⟨a.val.val,M22_le_hexadDesignAut a.val.property⟩
  refine ⟨g,a.property,?_⟩
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  exact m22DesignAutToAut_apply_perm g x

/-- The constructed subgroup lies in the original point-plane overlap,
using the same native hexad and the same full cubic projection. -/
theorem fullCubic_hexad_subgroup_le_overlap {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (M : Subgroup G)
    (hM : M.subgroupOf (centralizer z) = (designStabilizer B).comap (CubicLift.projection e))
    (A : Subgroup (fullCubicCentralizer e X))
    (hA : A.map (fullCubicSimpleProjection h e X) =
      ((MulAction.stabilizer M22 B).subtype.comp (m22HexadSection hB)).range) :
    A.map (fullCubicCentralizer e X).subtype ≤ M.subgroupOf (centralizer z) := by
  rintro c ⟨a,ha,rfl⟩
  rw [hM]
  change CubicLift.projection e a.val ∈ designStabilizer B
  change e.projection (QuotientGroup.mk' (core z) a.val) ∈ designStabilizer B
  rw [←fullCubicSimpleProjection_conj h e X a]
  obtain ⟨b,hb⟩ := hA.le (mem_map_of_mem (fullCubicSimpleProjection h e X) ha)
  rw [←hb]
  exact hexad_inner_mem (m22HexadSection hB b)

/-- Every literal hexad overlap contains the constructed order-1080
subgroup; it does not contain the marker involution. -/
theorem fullCubic_hexad_overlap_complement {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (M : Subgroup G)
    (hM : M.subgroupOf (centralizer z) = (designStabilizer B).comap (CubicLift.projection e)) :
    ∃ A : Subgroup (fullCubicCentralizer e X),
      Nat.card A = 1080 ∧ fullCubicScalar e X ≤ A ∧
      Disjoint (fullCubicProjection h e X).ker A ∧
      A.map (fullCubicSimpleProjection h e X) =
        ((MulAction.stabilizer M22 B).subtype.comp (m22HexadSection hB)).range ∧
      (fullCubicProjection h e X).ker ⊔ A =
        (((MulAction.stabilizer M22 B).subtype.comp (m22HexadSection hB)).range).comap
          (fullCubicSimpleProjection h e X) ∧
      A.map (fullCubicCentralizer e X).subtype ≤ M.subgroupOf (centralizer z) := by
  obtain ⟨A,hAc,hscalar,hdis,him,hgen⟩ := fullCubic_hexad_complement h e X hB
  exact ⟨A,hAc,hscalar,hdis,him,hgen,fullCubic_hexad_subgroup_le_overlap h e X hB M hM A him⟩


/-- Transfer in the original perfect cubic centralizer forces the cubic
into the derived subgroup of its order-1080 hexad subgroup. -/
theorem fullCubic_hexad_subgroup_perfect
    [Group.IsPerfect (fullCubicCentralizer e X)]
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (A : Subgroup (fullCubicCentralizer e X))
    (hAc : Nat.card A=1080) (hscalar : fullCubicScalar e X ≤ A)
    (him : A.map (fullCubicSimpleProjection h e X) =
      ((MulAction.stabilizer M22 B).subtype.comp (m22HexadSection hB)).range) :
    Group.IsPerfect A := by
  let j := (MulAction.stabilizer M22 B).subtype.comp (m22HexadSection hB)
  have hj : Function.Injective j :=
    (MulAction.stabilizer M22 B).subtype_injective.comp (m22HexadSection_injective hB)
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect j.range := Group.IsPerfect.range j
  let q : A →* j.range := ((fullCubicSimpleProjection h e X).comp A.subtype).codRestrict _
    (fun a => him.le (mem_map_of_mem _ a.property))
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨x,hx,he⟩ := him.ge a.property
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  have hjc : Nat.card j.range=360 := by
    have hc : Nat.card j.range=Nat.card (alternatingGroup (Fin 6)) :=
      (Nat.card_congr (Equiv.ofInjective j hj)).symm
    rw [hc,nat_card_alternatingGroup]
    norm_num
  have hkc : Nat.card q.ker=3 := by
    have hh := q.ker.card_mul_index
    rw [index_ker,MonoidHom.range_eq_top.mpr hq,card_top,hjc,hAc] at hh
    omega
  have hle : (fullCubicScalar e X).subgroupOf A ≤ q.ker := by
    intro x hx
    apply Subtype.ext
    change fullCubicSimpleProjection h e X x.val=1
    rw [←MonoidHom.mem_ker,fullCubicSimpleProjection_ker]
    exact fullCubicScalar_central e X hx
  have hker : q.ker=(fullCubicScalar e X).subgroupOf A :=
    (eq_of_le_of_card_ge hle (by
      rw [hkc,Nat.card_congr (subgroupOfEquivOfLe hscalar).toEquiv,fullCubicScalar_card h e X])).symm
  have hi : A.index=2464 := by
    have hh := A.card_mul_index
    rw [hAc,fullCubicCentralizer_card h e X] at hh
    omega
  have hcomm : fullCubicScalar e X ≤ ⁅A,A⁆ :=
    central_pSubgroup_le_commutator A (fullCubicScalar e X) hscalar
      (fullCubicScalar_central e X)
      (IsPGroup.of_card (n := 1) (by rw [fullCubicScalar_card h e X]; norm_num))
      (by rw [hi]; decide : ¬3 ∣ A.index)
  have hkcomm : q.ker ≤ _root_.commutator A := by
    rw [hker]
    intro x hx
    have hh := hcomm hx
    rw [←map_subtype_commutator] at hh
    obtain ⟨y,hy,he⟩ := hh
    exact (Subtype.ext he : y=x) ▸ hy
  exact ⟨(sup_eq_right.mpr hkcomm).symm.trans
    (CentralExtension.ker_sup_commutator_eq_top_of_surjective q hq)⟩


/-- The complement is the derived subgroup of the literal A₆ preimage.
In particular it is canonical inside this preimage. -/
theorem fullCubic_hexad_subgroup_derived
    [Group.IsPerfect (fullCubicCentralizer e X)]
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (A : Subgroup (fullCubicCentralizer e X))
    (hAc : Nat.card A=1080) (hscalar : fullCubicScalar e X ≤ A)
    (him : A.map (fullCubicSimpleProjection h e X) =
      ((MulAction.stabilizer M22 B).subtype.comp (m22HexadSection hB)).range)
    (hgen : (fullCubicProjection h e X).ker ⊔ A =
      (((MulAction.stabilizer M22 B).subtype.comp (m22HexadSection hB)).range).comap
        (fullCubicSimpleProjection h e X)) :
    (_root_.commutator
      ((((MulAction.stabilizer M22 B).subtype.comp (m22HexadSection hB)).range).comap
        (fullCubicSimpleProjection h e X))).map
      ((((MulAction.stabilizer M22 B).subtype.comp (m22HexadSection hB)).range).comap
        (fullCubicSimpleProjection h e X)).subtype = A := by
  let D := (((MulAction.stabilizer M22 B).subtype.comp (m22HexadSection hB)).range).comap
    (fullCubicSimpleProjection h e X)
  let Z := (fullCubicProjection h e X).ker
  have hAD : A ≤ D := le_sup_right.trans_eq hgen
  have hZD : Z ≤ D := le_sup_left.trans_eq hgen
  have hZC : Z ≤ center (fullCubicCentralizer e X) := fullCubicProjection_kernel_central h e X
  have hn : D ≤ normalizer (A : Set (fullCubicCentralizer e X)) := by
    change (((MulAction.stabilizer M22 B).subtype.comp (m22HexadSection hB)).range).comap
      (fullCubicSimpleProjection h e X) ≤ _
    rw [←hgen]
    exact sup_le (hZC.trans (center_le_normalizer _)) A.le_normalizer
  let : (A.subgroupOf D).Normal := (normal_subgroupOf_iff_le_normalizer hAD).mpr hn
  have hs : A.subgroupOf D ⊔ center D = ⊤ := by
    have hz : Z.subgroupOf D ≤ center D := by
      intro x hx
      exact mem_center_iff.mpr (fun y => Subtype.ext (mem_center_iff.mp (hZC hx) y.val))
    have hg : Z.subgroupOf D ⊔ A.subgroupOf D = ⊤ := by
      rw [←subgroupOf_sup hZD hAD,hgen,subgroupOf_self]
    apply top_unique
    rw [←hg]
    exact sup_le (hz.trans le_sup_right) le_sup_left
  let := fullCubic_hexad_subgroup_perfect h e X hB A hAc hscalar him
  apply le_antisymm
  · have hc := Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hs
      (inferInstance : IsMulCommutative (center D))
    have hm := map_mono (f := D.subtype) hc
    rw [map_subgroupOf_eq_of_le hAD] at hm
    exact hm
  · rw [map_subtype_commutator,←commutator_eq_self (H := A)]
    exact commutator_mono hAD hAD


end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition

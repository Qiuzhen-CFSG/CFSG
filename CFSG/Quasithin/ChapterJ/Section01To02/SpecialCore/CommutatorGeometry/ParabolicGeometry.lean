module

public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.CommutatorGeometry.Propagation
public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.Basic
public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.CommutatorGeometry.ParabolicGeometry.Natural
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.CoreEquality.ParabolicImage
public import Theory.Representation.PSL3Two.SteinbergStructure.PointRadicalFixedSpace
public import Theory.GroupTheory.PCoreImage


/-!
# Natural parabolics and the Steinberg geometry of J.2.3

The faithful natural Ru1 action supplies the Sylow normalizers used by the
commutator propagation theorem. For the geometry, the image of U in the actual
Steinberg coordinates has order four and is invariant under the point parabolic
coming from the same Ru1 marking. The model's uniqueness theorem identifies it
with the point-radical fixed plane; its transporter theorem gives U ∩ Uˡ = V.

The preceding J.2.2 equality R₁ = O₂(L ∩ H) remains an explicit input. The
restricted quotient marking has two-group kernel, so that equality identifies
the actual image of R₁ with the radical of the same conjugate point parabolic.
This proves the fixed-subgroup equality in the literal quotient S/V. A separate
preimage theorem verifies the action through ambient commutators, without the
core-equality input. Only relative normality of V in S is used.

No full-commutator seed enters either geometry proof. The natural-parabolic
adapter is re-exported with its application to the existing propagation theorem.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
J.2.3(8,9), printed p.433 (PDF p.444), and the natural-parabolic step in (6).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterJ.SpecialCore.CommutatorGeometry
noncomputable section
variable {G : Type*} [Group G] [Finite G]
open BinaryLinearThree.SteinbergStructure.PointRadicalFixedSpace

private theorem coordinate_mul_inv_eq_one {A M : Type*} [Group A] [AddCommGroup M]
    (f : A →* Multiplicative M) (s t : A) :
    f (s*t⁻¹) = 1 ↔ (f s).toAdd = (f t).toAdd := by
  rw [map_mul,map_inv,mul_inv_eq_one]
  exact Multiplicative.toAdd.injective.eq_iff.symm

private theorem card_coordinate_domain {A M : Type*} [Group A] [AddCommGroup M]
    (f : A →* Multiplicative M) : Nat.card A = Nat.card f.range * Nat.card f.ker := by
  have hc := card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at hc
  exact hc

/-- U/V in the literal Steinberg coordinates. -/
def uSpace (d : LocalSetup G) : Submodule (ZMod 2) BinaryLinearThree.Steinberg :=
  AddSubgroup.toZModSubmodule 2
    ((d.toTypeRuSetup.U.subgroupOf d.toTypeRuSetup.S).map d.ru1.steinberg.coordinates).toAddSubgroup'

private theorem mem_uSpace (d : LocalSetup G) (s : d.toTypeRuSetup.S) :
    (d.ru1.steinberg.coordinates s).toAdd ∈ uSpace d ↔ (s : G) ∈ d.toTypeRuSetup.U := by
  change d.ru1.steinberg.coordinates s ∈
    (d.toTypeRuSetup.U.subgroupOf d.toTypeRuSetup.S).map d.ru1.steinberg.coordinates ↔ _
  constructor
  · rintro ⟨t,ht,he⟩
    have hv : ((s * t⁻¹ : d.toTypeRuSetup.S) : G) ∈ d.V :=
      (d.ru1.steinberg.coordinates_eq_one_iff _).mp
        ((coordinate_mul_inv_eq_one d.ru1.steinberg.coordinates s t).mpr
          (congrArg Multiplicative.toAdd he.symm))
    have hu := d.toTypeRuSetup.U.mul_mem ((le_conjugateSpan _ _) hv) ht
    simpa using hu
  · intro hs
    exact mem_map.mpr ⟨s,hs,rfl⟩

private theorem card_uSpace (d : LocalSetup G) : Nat.card (uSpace d) = 4 := by
  let f : d.toTypeRuSetup.U →* Multiplicative BinaryLinearThree.Steinberg :=
    d.ru1.steinberg.coordinates.comp (inclusion d.U_le_S)
  have hk : f.ker = d.V.subgroupOf d.toTypeRuSetup.U := by
    ext u
    exact d.ru1.steinberg.coordinates_eq_one_iff ⟨u,d.U_le_S u.property⟩
  let I : Subgroup (Multiplicative BinaryLinearThree.Steinberg) :=
    (d.toTypeRuSetup.U.subgroupOf d.toTypeRuSetup.S).map d.ru1.steinberg.coordinates
  have hi : f.range = I := by
    ext v
    constructor
    · rintro ⟨u,rfl⟩
      exact mem_map.mpr ⟨⟨u,d.U_le_S u.property⟩,u.property,rfl⟩
    · rintro ⟨u,hu,rfl⟩
      exact ⟨⟨u,hu⟩,rfl⟩
  have hker : Nat.card f.ker = 8 := by
    rw [hk]
    exact (Nat.card_congr (subgroupOfEquivOfLe
      (le_conjugateSpan d.toTypeRuSetup.H d.V)).toEquiv).trans d.ru1.card_V
  have himage : Nat.card (f.range : Subgroup (Multiplicative BinaryLinearThree.Steinberg)) =
      Nat.card (uSpace d) := by
    rw [hi]
    rfl
  have hc := card_coordinate_domain f
  rw [hker,himage,d.ru2.card_U d.card_Z] at hc
  omega

private theorem uSpace_stable (d : LocalSetup G) (a : BinaryLinearThree.Group)
    (ha : a ∈ d.parabolicMap.range) (v : BinaryLinearThree.Steinberg) (hv : v ∈ uSpace d) :
    BinaryLinearThree.S a v ∈ uSpace d := by
  obtain ⟨l,rfl⟩ := ha
  have hv' : Multiplicative.ofAdd v ∈
      (d.toTypeRuSetup.U.subgroupOf d.toTypeRuSetup.S).map d.ru1.steinberg.coordinates := hv
  obtain ⟨s,hs,hsv⟩ := hv'
  have hsv' : (d.ru1.steinberg.coordinates s).toAdd = v := congrArg Multiplicative.toAdd hsv
  rw [← hsv']
  let t : d.toTypeRuSetup.S := ⟨l*s*(l:G)⁻¹,
    (mem_normalizer_iff.mp (d.ru1.steinberg.normalized l.property.1) s).mp s.property⟩
  have ht : (t:G) ∈ d.toTypeRuSetup.U :=
    (mem_normalizer_iff.mp (d.ru2.natural.normalized l.property.2) s).mp hs
  have he : (d.ru1.steinberg.coordinates t).toAdd =
      BinaryLinearThree.S (d.parabolicMap l) (d.ru1.steinberg.coordinates s).toAdd :=
    d.ru1.steinberg.equivariant ⟨l,l.property.1⟩ s
  rw [← he]
  exact (mem_uSpace d t).mpr ht

/-- The image of U is the fixed plane for the radical of its actual point parabolic. -/
theorem uSpace_eq_point_fixed (d : LocalSetup G) (g : BinaryLinearThree.Group)
    (hg : d.parabolicMap.range =
      Matrix.PSL3Two.pointParabolicSL.map (MulAut.conj g).toMonoidHom) :
    uSpace d = fixedSpace BinaryLinearThree.S
      (Matrix.PSL3Two.MarkedAutomorphisms.pointV.map (MulAut.conj g).toMonoidHom) := by
  apply conjugate_eq_fixed_of_card_four g (uSpace d) (card_uSpace d)
  intro a ha v hv
  exact uSpace_stable d a (hg.symm ▸ ha) v hv

private theorem mem_H_of_quotient_mem (d : LocalSetup G) (l : d.L)
    (hl : d.ru1.quotientMap l ∈ d.parabolicMap.range) : (l:G) ∈ d.toTypeRuSetup.H := by
  obtain ⟨a,ha⟩ := hl
  let aL : d.L := ⟨a,a.property.1⟩
  have hk : l * aL⁻¹ ∈ d.ru1.quotientMap.ker := by
    change d.ru1.quotientMap (l*aL⁻¹) = 1
    rw [map_mul,map_inv]
    change d.ru1.quotientMap l * (d.parabolicMap a)⁻¹ = 1
    rw [ha,mul_inv_cancel]
  rw [d.ru1.quotient_kernel] at hk
  have h := d.toTypeRuSetup.H.mul_mem (d.S_le_H hk) a.property.2
  simpa [aL] using h

/-- J.2.3(9), in the source's direct ambient conjugation coordinates. -/
theorem U_inf_conjugate (d : LocalSetup G) (l : G) (hl : l ∈ d.L)
    (hnot : l ∉ d.toTypeRuSetup.H) :
    d.toTypeRuSetup.U ⊓ d.toTypeRuSetup.U.map (MulAut.conj l).toMonoidHom = d.V := by
  obtain ⟨g,hg⟩ := d.parabolic_image
  have he := uSpace_eq_point_fixed d g hg
  apply le_antisymm
  · rintro x ⟨hx, y,hy,hxy⟩
    by_contra hxV
    let sy : d.toTypeRuSetup.S := ⟨y,d.U_le_S hy⟩
    let sx : d.toTypeRuSetup.S := ⟨x,d.U_le_S hx⟩
    have heq : (d.ru1.steinberg.coordinates sx).toAdd =
        BinaryLinearThree.S (d.ru1.quotientMap ⟨l,hl⟩) (d.ru1.steinberg.coordinates sy).toAdd := by
      let sz : d.toTypeRuSetup.S := ⟨l * sy * l⁻¹,
        (mem_normalizer_iff.mp (d.ru1.steinberg.normalized hl) sy).mp sy.property⟩
      have hact : (d.ru1.steinberg.coordinates sz).toAdd =
          BinaryLinearThree.S (d.ru1.quotientMap ⟨l,hl⟩) (d.ru1.steinberg.coordinates sy).toAdd :=
        d.ru1.steinberg.equivariant ⟨l,hl⟩ sy
      have hsz : sz = sx := Subtype.ext hxy
      exact (congrArg (fun t => (d.ru1.steinberg.coordinates t).toAdd) hsz).symm.trans hact
    have hn : (d.ru1.steinberg.coordinates sy).toAdd ≠ 0 := by
      intro hz
      apply hxV
      apply (d.ru1.steinberg.coordinates_eq_one_iff sx).mp
      change (d.ru1.steinberg.coordinates sx).toAdd = 0
      rw [heq,hz,map_zero]
    have htrans := conjugate_transporter g (d.ru1.quotientMap ⟨l,hl⟩)
      (d.ru1.steinberg.coordinates sy).toAdd (d.ru1.steinberg.coordinates sx).toAdd
      (he ▸ (mem_uSpace d sy).mpr hy) hn
      (he ▸ (mem_uSpace d sx).mpr hx) heq.symm
    exact hnot (mem_H_of_quotient_mem d ⟨l,hl⟩ (hg.symm ▸ htrans))
  · apply le_inf (le_conjugateSpan _ _)
    have hn := mem_normalizer_iff_map_conj_eq.mp (d.ru1.natural.normalized hl)
    rw [← hn]
    exact map_mono (le_conjugateSpan _ _)

/-- R₁ is mapped to the radical of the same marked point parabolic.
The only additional premise is the preceding J.2.2(1) core equality. -/
theorem R₁_image (d : LocalSetup G)
    (hcore : d.toTypeRuSetup.R₁ = d.parabolic.pCoreIn 2)
    (g : BinaryLinearThree.Group)
    (hg : d.parabolicMap.range =
      Matrix.PSL3Two.pointParabolicSL.map (MulAut.conj g).toMonoidHom) :
    (d.toTypeRuSetup.R₁.subgroupOf d.parabolic).map d.parabolicMap =
      Matrix.PSL3Two.MarkedAutomorphisms.pointV.map (MulAut.conj g).toMonoidHom := by
  have hk : IsPGroup 2 d.parabolicMap.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict,d.parabolicMap_kernel]
    exact (isPGroup_pCoreIn 2 d.L).comap_subtype
  have hp := d.parabolicMap.rangeRestrict.comap_pCore_of_ker_isPGroup
    d.parabolicMap.rangeRestrict_surjective hk
  have hm : (pCore 2 d.parabolic).map d.parabolicMap.rangeRestrict =
      pCore 2 d.parabolicMap.range := by
    rw [← hp,map_comap_eq_self]
    rw [MonoidHom.range_eq_top_of_surjective _ d.parabolicMap.rangeRestrict_surjective]
    exact le_top
  have hmap : (pCore 2 d.parabolic).map d.parabolicMap = d.parabolicMap.range.pCoreIn 2 := by
    rw [pCoreIn, ← hm, map_map]
    rfl
  have he : d.toTypeRuSetup.R₁.subgroupOf d.parabolic = pCore 2 d.parabolic := by
    rw [hcore]
    exact comap_map_eq_self_of_injective d.parabolic.subtype_injective _
  rw [he,hmap,hg]
  have hconj := map_pCoreIn_of_ker_isPGroup (p := 2) (MulAut.conj g).toMonoidHom
    (by rw [(MulAut.conj g).toMonoidHom.ker_eq_bot_iff.mpr (MulAut.conj g).injective]; exact IsPGroup.of_bot)
    Matrix.PSL3Two.pointParabolicSL
  rw [Matrix.PSL3Two.MarkedProduct.pointParabolic_core] at hconj
  exact hconj.symm

omit [Finite G] in
private theorem commutator_mem_iff_fixed {L V : Subgroup G} (r : RuOne L V)
    (a : L) (s : L.pCoreIn 2) :
    ⁅(a:G),(s:G)⁆ ∈ V ↔ BinaryLinearThree.S (r.quotientMap a)
      (r.steinberg.coordinates s).toAdd = (r.steinberg.coordinates s).toAdd := by
  let t : L.pCoreIn 2 := ⟨a*s*(a:G)⁻¹,
    (mem_normalizer_iff.mp (r.steinberg.normalized a.property) s).mp s.property⟩
  have hc := (coordinate_mul_inv_eq_one r.steinberg.coordinates t s).symm.trans
    (r.steinberg.coordinates_eq_one_iff (t*s⁻¹))
  have hcomm : ((t*s⁻¹ : L.pCoreIn 2) : G) = ⁅(a:G),(s:G)⁆ := rfl
  rw [hcomm] at hc
  rw [← hc]
  rw [show (r.steinberg.coordinates t).toAdd =
    BinaryLinearThree.S (r.quotientMap a) (r.steinberg.coordinates s).toAdd from
      r.steinberg.equivariant a s]

/-- J.2.3(8), as the exact ambient preimage of the fixed subgroup in S/V. -/
theorem mem_U_iff_commutators (d : LocalSetup G)
    (hcore : d.toTypeRuSetup.R₁ = d.parabolic.pCoreIn 2) (s : d.toTypeRuSetup.S) :
    (s:G) ∈ d.toTypeRuSetup.U ↔
      ∀ a ∈ d.toTypeRuSetup.R₁, ⁅a,(s:G)⁆ ∈ d.V := by
  obtain ⟨g,hg⟩ := d.parabolic_image
  have hRle : d.toTypeRuSetup.R₁ ≤ d.parabolic := by
    rw [hcore]
    exact pCoreIn_le 2 d.parabolic
  rw [← mem_uSpace, uSpace_eq_point_fixed d g hg, ← R₁_image d hcore g hg]
  constructor
  · intro hs a ha
    rw [commutator_mem_iff_fixed d.ru1 ⟨a,(hRle ha).1⟩ s]
    exact hs ⟨d.parabolicMap ⟨a,hRle ha⟩, mem_map.mpr ⟨⟨a,hRle ha⟩,ha,rfl⟩⟩
  · intro hs a
    obtain ⟨b,hb,he⟩ := a.property
    change BinaryLinearThree.S (a : BinaryLinearThree.Group)
      (d.ru1.steinberg.coordinates s).toAdd = (d.ru1.steinberg.coordinates s).toAdd
    rw [← he]
    exact (commutator_mem_iff_fixed d.ru1 ⟨b,b.property.1⟩ s).mp (hs b hb)

/-- The subgroup of S/V fixed under the conjugation action of R₁.
The action is transported by the specified common Ru1 marking. -/
def quotientFixed (d : LocalSetup G)
    [(d.V.subgroupOf d.toTypeRuSetup.S).Normal] :
    Subgroup (d.toTypeRuSetup.S ⧸ d.V.subgroupOf d.toTypeRuSetup.S) :=
  ((fixedSpace BinaryLinearThree.S
    ((d.toTypeRuSetup.R₁.subgroupOf d.parabolic).map d.parabolicMap)).toAddSubgroup.toSubgroup).comap
      d.ru1.steinberg.quotientEquiv.toMonoidHom

/-- The fixed subgroup uses the actual quotient conjugation: its preimage is
exactly the elements whose R₁-commutators lie in V. No parabolic core equality
is needed to identify this action. -/
theorem mem_quotientFixed_mk_iff (d : LocalSetup G)
    [(d.V.subgroupOf d.toTypeRuSetup.S).Normal] (s : d.toTypeRuSetup.S) :
    QuotientGroup.mk' (d.V.subgroupOf d.toTypeRuSetup.S) s ∈ quotientFixed d ↔
      ∀ a ∈ d.toTypeRuSetup.R₁, ⁅a,(s:G)⁆ ∈ d.V := by
  have hRle : d.toTypeRuSetup.R₁ ≤ d.parabolic :=
    (pCoreIn_le 2 d.toTypeRuSetup.L₁).trans (map_subtype_le _)
  change (d.ru1.steinberg.quotientEquiv
    (QuotientGroup.mk' (d.V.subgroupOf d.toTypeRuSetup.S) s)).toAdd ∈
    fixedSpace BinaryLinearThree.S
      ((d.toTypeRuSetup.R₁.subgroupOf d.parabolic).map d.parabolicMap) ↔ _
  rw [Representation.BinaryConjugationSection.quotientEquiv_mk]
  constructor
  · intro hs a ha
    rw [commutator_mem_iff_fixed d.ru1 ⟨a,(hRle ha).1⟩ s]
    exact hs ⟨d.parabolicMap ⟨a,hRle ha⟩, mem_map.mpr ⟨⟨a,hRle ha⟩,ha,rfl⟩⟩
  · intro hs a
    obtain ⟨b,hb,he⟩ := a.property
    change BinaryLinearThree.S (a : BinaryLinearThree.Group)
      (d.ru1.steinberg.coordinates s).toAdd = (d.ru1.steinberg.coordinates s).toAdd
    rw [← he]
    exact (commutator_mem_iff_fixed d.ru1 ⟨b,b.property.1⟩ s).mp (hs b hb)

/-- The literal quotient fixed subgroup in J.2.3(8) is the image of U/V. -/
theorem quotientFixed_eq (d : LocalSetup G)
    [(d.V.subgroupOf d.toTypeRuSetup.S).Normal]
    (hcore : d.toTypeRuSetup.R₁ = d.parabolic.pCoreIn 2) :
    quotientFixed d = (d.toTypeRuSetup.U.subgroupOf d.toTypeRuSetup.S).map
      (QuotientGroup.mk' (d.V.subgroupOf d.toTypeRuSetup.S)) := by
  ext q
  obtain ⟨s,rfl⟩ := QuotientGroup.mk'_surjective (d.V.subgroupOf d.toTypeRuSetup.S) q
  rw [mem_quotientFixed_mk_iff, ← mem_U_iff_commutators d hcore]
  constructor
  · intro hs
    exact mem_map.mpr ⟨s,hs,rfl⟩
  · rintro ⟨t,ht,he⟩
    have hv := QuotientGroup.eq_iff_div_mem.mp he
    have hu := d.toTypeRuSetup.U.mul_mem
      (d.toTypeRuSetup.U.inv_mem ((le_conjugateSpan _ _) hv)) ht
    rw [map_div,div_eq_mul_inv] at hu
    have hu' : (((t : G) * (s : G)⁻¹)⁻¹ * (t : G)) ∈ d.toTypeRuSetup.U := hu
    simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one] using hu'

/-- Both source geometry clauses, retaining precisely the preceding core equality. -/
theorem source_eight_nine (d : LocalSetup G)
    (hcore : d.toTypeRuSetup.R₁ = d.parabolic.pCoreIn 2) :
    let := d.ru1.steinberg.kernel_normal
    quotientFixed d = (d.toTypeRuSetup.U.subgroupOf d.toTypeRuSetup.S).map
      (QuotientGroup.mk' (d.V.subgroupOf d.toTypeRuSetup.S)) ∧
    (∀ s : d.toTypeRuSetup.S, (s:G) ∈ d.toTypeRuSetup.U ↔
      ∀ a ∈ d.toTypeRuSetup.R₁, ⁅a,(s:G)⁆ ∈ d.V) ∧
    ∀ l ∈ d.L, l ∉ d.toTypeRuSetup.H →
      d.toTypeRuSetup.U ⊓ d.toTypeRuSetup.U.map (MulAut.conj l).toMonoidHom = d.V := by
  let := d.ru1.steinberg.kernel_normal
  exact ⟨quotientFixed_eq d hcore, mem_U_iff_commutators d hcore, U_inf_conjugate d⟩
end
end CFSG.Quasithin.ChapterJ.SpecialCore.CommutatorGeometry

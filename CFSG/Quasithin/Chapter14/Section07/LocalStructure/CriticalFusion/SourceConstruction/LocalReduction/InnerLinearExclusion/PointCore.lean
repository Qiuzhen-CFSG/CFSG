module
public import CFSG.Quasithin.ChapterI.Section04To05.C3Recognition.Source
public import Theory.SpecificGroups.SymplecticSix.FixedRadical

/-!
# The elementary point core of the literal C₃ system

Use the original I.5 symplectic point marking, including its equivariance
and collinearity. The three points of each line have vector sum zero.
Consequently an element of the actual point two-core fixes the marked
point and displaces each vector of its orthogonal hyperplane into that
point. Preservation of the alternating form makes this shear square to
one on the whole six-space. Faithfulness then makes the original point
two-core elementary abelian, with no assumption about parabolic markings
or the image of that core under an abstract group isomorphism.

This is the local fact used in the final contradiction of original
14.7.11. Source: Aschbacher–Smith, refs/quasithin.pdf, printed p.1046,
using the marked recognition in I.5.15, printed p.424.
-/

public noncomputable section
open Subgroup Matrix Quasithin.I5
open Theory.SpecificGroups.SymplecticSix Theory.SpecificGroups.SymplecticSix.TwoLocalCover
open Quasithin.I5.C3Recognition
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion
variable {X : Type*} [Group X] {S : DSystem .C3 X}
local notation "B" => form (ZMod 2)
local notation "W" => Vector (ZMod 2)

private theorem binary_add_self (v : W) : v + v = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (v i)

private theorem line_third_vector (m : SymplecticMark S)
    {x y z : S.Point} {l : S.Line}
    (hx : S.Inc x l) (hy : S.Inc y l) (hz : S.Inc z l)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hall : ∀ t, S.Inc t l → t = x ∨ t = y ∨ t = z) :
    m.point x + m.point y = m.point z := by
  have ho : Theory.LinearAlgebra.BinaryPolarGeometry.OneOrAll S.Collinear x y z := by
    intro t
    have hab : S.Collinear t x → S.Collinear t y → S.Collinear t z := fun ha hb => S.line_all_collinear_of_two S.source_local_polar_facts hx hy hxy ha hb z hz
    have hac : S.Collinear t x → S.Collinear t z → S.Collinear t y := fun ha hc => S.line_all_collinear_of_two S.source_local_polar_facts hx hz hxz ha hc y hy
    have hbc : S.Collinear t y → S.Collinear t z → S.Collinear t x := fun hb hc => S.line_all_collinear_of_two S.source_local_polar_facts hy hz hyz hb hc x hx
    have hany : S.Collinear t x ∨ S.Collinear t y ∨ S.Collinear t z := by
      obtain ⟨u,hu,htu⟩ := S.line_has_collinear_point S.source_local_polar_facts t l
      rcases hall u hu with rfl | rfl | rfl
      · exact Or.inl htu
      · exact Or.inr (Or.inl htu)
      · exact Or.inr (Or.inr htu)
    tauto
  apply sub_eq_zero.mp
  apply form_nondegenerate.2
  intro v
  by_cases hv : v = 0
  · subst v; simp
  obtain ⟨t,ht⟩ := m.point_bijective.surjective ⟨v,hv⟩
  have ht' : m.point t = v := congrArg Subtype.val ht
  rw [←ht',map_sub,map_add]
  have hh := ho t
  simp only [←m.orthogonal] at hh
  generalize B (m.point t) (m.point x) = a at hh ⊢
  generalize B (m.point t) (m.point y) = b at hh ⊢
  generalize B (m.point t) (m.point z) = c at hh ⊢
  have split (r : ZMod 2) : r = 0 ∨ r = 1 := by
    have hr := ZMod.val_lt r
    have hr' : r.val = 0 ∨ r.val = 1 := by omega
    rcases hr' with he | he
    · left; simpa only [he,Nat.cast_zero] using (ZMod.natCast_zmod_val r).symm
    · right; simpa only [he,Nat.cast_one] using (ZMod.natCast_zmod_val r).symm
  rcases split a with rfl | rfl <;> rcases split b with rfl | rfl <;>
    rcases split c with rfl | rfl <;> simp_all [CharTwo.add_self_eq_zero]

private theorem core_displacement (m : SymplecticMark S)
    (a : S.family 0) (ha : a ∈ pCore 2 (S.family 0))
    (v : W) (hv : B (m.point S.basePoint) v = 0) :
    (m.hom a.val) • v + v = 0 ∨ (m.hom a.val) • v + v = m.point S.basePoint := by
  have hbase : a.val • S.basePoint = S.basePoint := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [S.stabilizer_basePoint]
    exact a.property
  have hq : a.val ∈ S.Q 0 := mem_map.mpr ⟨a,ha,rfl⟩
  by_cases hv0 : v = 0
  · subst v
    left
    exact by simp only [←toLinear_apply,map_zero,add_zero]
  obtain ⟨x,hx⟩ := m.point_bijective.surjective ⟨v,hv0⟩
  have hx' : m.point x = v := congrArg Subtype.val hx
  subst v
  rw [Theory.SpecificGroups.SymplecticSix.smul_eq_mulVec,m.equivariant]
  by_cases hbx : S.basePoint = x
  · subst x
    left
    rw [hbase,binary_add_self]
  obtain ⟨l,hbl,hxl⟩ := (m.orthogonal _ _).mp hv
  have hal : a.val • l = l := S.core_fixes_incident_coset 0 1 (by decide) hq hbl
  have haxl : S.Inc (a.val • x) l := by simpa only [hal] using hxl.smul S a.val
  obtain ⟨z,hzl,hbz,hxz,hall⟩ := S.exists_third_line_point hbl hxl hbx
  have hz := line_third_vector m hbl hxl hzl hbx hbz hxz hall
  rcases hall (a.val • x) haxl with he | he | he
  · have : x = S.basePoint := (MulAction.injective a.val) (he.trans hbase.symm)
    exact (hbx this.symm).elim
  · left; rw [he,binary_add_self]
  · right; rw [he,←hz,add_assoc,binary_add_self,add_zero]

private theorem shear_square (g : W ≃ₗ[ZMod 2] W) (w : W)
    (hw : g w = w) (hg : ∀ x y, B (g x) (g y) = B x y)
    (hd : ∀ v, B w v = 0 → g v + v = 0 ∨ g v + v = w) :
    ∀ v, g (g v) = v := by
  intro v
  have hvd : B w (g v + v) = 0 := by
    have hh := hg w v
    rw [hw] at hh
    rw [map_add,hh,CharTwo.add_self_eq_zero]
  have hzero : g (g v + v) + (g v + v) = 0 := by
    rcases hd (g v + v) hvd with hz | hz
    · exact hz
    by_cases hv : B w v = 0
    · rcases hd v hv with he | he
      · rw [he,map_zero,add_zero]
      · rw [he,hw,binary_add_self]
    · have hb : B v w ≠ 0 := fun hh => hv (form_alternating.eq_iff.mp hh)
      have hform := hg v (g v + v)
      have hz' : g (g v + v) = w + (g v + v) := by
        have hh := congrArg (fun z : W => z + (g v + v)) hz
        rw [add_assoc, binary_add_self (g v + v), add_zero] at hh
        exact hh
      rw [hz'] at hform
      have hgvw : B (g v) w = B v w := by simpa only [hw] using hg v w
      have hsym : B (g v) v = B v (g v) := by
        have hh := form_alternating.neg_eq (g v) v
        simpa only [CharTwo.neg_eq] using hh
      simp only [map_add,hgvw,form_alternating.self_eq_zero,
        hsym,zero_add,add_zero] at hform
      exact (hb (add_eq_right.mp hform)).elim
  have he : g (g v) + v = 0 := by
    simpa only [map_add,add_assoc,←add_assoc (g v) (g v) v,binary_add_self,zero_add] using hzero
  have hh := congrArg (fun z : W => z + v) he
  simpa only [add_assoc,binary_add_self,add_zero,zero_add] using hh

/-- The literal point two-core in a C₃ system is elementary abelian.
The marked symplectic action fixes each incident line, so its displacement
on the point's orthogonal hyperplane lies in that point. Preservation of
the alternating form makes every such shear an involution. -/
theorem c3_point_core_elementary (S : DSystem .C3 X) :
    IsElementaryAbelian 2 (pCore 2 (S.family 0)) := by
  let d := S.source_local_polar_facts
  obtain ⟨m⟩ := exists_symplecticMark S
    ⟨S.c3_points_card d,S.faithful_points,S.c3_exists_noncollinear,
      S.source_one_or_all_triples d⟩
  have hp (a : pCore 2 (S.family 0)) : a ^ 2 = 1 := by
    let g := toLinear (m.hom a.val.val)
    have hw : g (m.point S.basePoint) = m.point S.basePoint := by
      change (m.hom a.val.val).val *ᵥ m.point S.basePoint = m.point S.basePoint
      exact (m.fixes_basePoint_iff a.val.val).mpr a.val.property
    have hsq := shear_square g (m.point S.basePoint) hw
      (preserves_form (m.hom a.val.val)) (core_displacement m a.val a.property)
    apply Subtype.ext
    apply Subtype.ext
    apply m.hom_injective
    apply Subtype.ext
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    change (m.hom (a.val.val ^ 2)).val *ᵥ v = (m.hom 1).val *ᵥ v
    rw [map_pow,map_one]
    change (m.hom a.val.val ^ 2) • v = (1 : Sp (ZMod 2)) • v
    simpa only [g,toLinear_apply,pow_two,mul_smul,one_smul] using hsq v
  have hi (a : pCore 2 (S.family 0)) : a⁻¹ = a :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hp a)
  refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩
           exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hp }
  calc
    a * b = (a * b)⁻¹ := (hi _).symm
    _ = b * a := by rw [_root_.mul_inv_rev,hi,hi]

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion

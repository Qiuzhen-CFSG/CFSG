module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearLocalKernel.Parabolics
public import Theory.GroupTheory.PCoreImageRestriction
public import Theory.GroupTheory.PCoreImage
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore

/-!
# Cubic Cartan actors on the two symplectic parabolic quotients

The point action is conjugation by the middle SL₂ block, whose center is
trivial. The plane action is conjugation by the full upper-left GL₂ block;
its scalar kernel is retained. For a cubic Borel element these kernels are,
respectively, equality of the two determinant characters and the second
character equal to the square of the first. The calculation uses the full
intrinsic two-core of each local factor, with a transport theorem for actual
subgroup images through maps with two-group kernel.

Source: Aschbacher--Smith, the terminal Sp₄/Sp₄ comparison in 11.1.2,
printed p.764. These action identities are used by Sp4Cartan to compare the
literal original and reselected cubic subgroups.
-/

open Subgroup Matrix
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open CFSG.Quasithin.Chapter11.ChosenNaturalSource
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.TerminalOrientation
public noncomputable section

private theorem core_kernel_iff_projection {G H : Type*} [Group G] [Group H]
    (B : Subgroup G) (p : B →* H) (hp : p.ker = pCore 2 B)
    {x : G} (hx : x ∈ normalizer (B : Set G)) :
    x ∈ Closure.coreQuotientCentralizer B ↔
      ∀ b : B, p (B.normalizerMonoidHom ⟨x,hx⟩ b) = p b := by
  have he (a b : B) : p a = p b ↔
      QuotientGroup.mk' (pCore 2 B) a = QuotientGroup.mk' (pCore 2 B) b := by
    change p a = p b ↔ QuotientGroup.mk a = QuotientGroup.mk b
    rw [QuotientGroup.eq_iff_div_mem,←hp,MonoidHom.mem_ker,map_div,div_eq_mul_inv,mul_inv_eq_one]
  constructor
  · rintro ⟨g,hg,rfl⟩ b
    apply (he _ _).mpr
    have hh := congrArg (fun a : MulAut (B ⧸ pCore 2 B) =>
      a (QuotientGroup.mk' (pCore 2 B) b)) (MonoidHom.mem_ker.mp hg)
    rw [Closure.coreQuotientAction_apply_mk] at hh
    have hg' : (⟨(normalizer (B : Set G)).subtype g,hx⟩ : normalizer (B : Set G)) = g :=
      Subtype.ext rfl
    rw [hg']
    exact hh
  · intro h
    refine ⟨⟨x,hx⟩,MonoidHom.mem_ker.mpr ?_,rfl⟩
    apply MulEquiv.ext
    intro z
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) z
    rw [Closure.coreQuotientAction_apply_mk]
    exact (he _ _).mp (h b)

open scoped commutatorElement
private theorem core_kernel_iff_commutators {G : Type*} [Group G]
    (B : Subgroup G) {x : G} (hn : x ∈ normalizer (B : Set G)) :
    x ∈ Closure.coreQuotientCentralizer B ↔
      ∀ b ∈ B, ⁅x,b⁆ ∈ B.pCoreIn 2 := by
  constructor
  · rintro ⟨a,ha,rfl⟩ b hb
    let k : B := ⟨b,hb⟩
    have he := congrArg (fun f : MulAut (B ⧸ pCore 2 B) =>
      f (QuotientGroup.mk' (pCore 2 B) k)) (MonoidHom.mem_ker.mp ha)
    rw [Closure.coreQuotientAction_apply_mk] at he
    have hh : B.normalizerMonoidHom a k * k⁻¹ ∈ pCore 2 B :=
      (QuotientGroup.eq_one_iff (N := pCore 2 B) _).mp (by
        change QuotientGroup.mk' (pCore 2 B) (B.normalizerMonoidHom a k * k⁻¹) = 1
        rw [map_mul,map_inv,he,MulAut.one_apply,mul_inv_cancel])
    exact ⟨B.normalizerMonoidHom a k * k⁻¹,hh,rfl⟩
  · intro hc
    refine ⟨⟨x,hn⟩,MonoidHom.mem_ker.mpr ?_,rfl⟩
    apply MulEquiv.ext
    intro z
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) z
    rw [Closure.coreQuotientAction_apply_mk]
    apply QuotientGroup.eq_iff_div_mem.mpr
    obtain ⟨r,hr,he⟩ := hc b b.property
    have he' : r = B.normalizerMonoidHom ⟨x,hn⟩ b / b := by
      apply Subtype.ext
      simpa only [subtype_apply,div_eq_mul_inv,coe_mul,coe_inv,
        normalizerMonoidHom_apply_apply_coe,commutatorElement_def] using he
    exact he' ▸ hr

/-- Quotient kernels transport through a map with two-group kernel,
for the actual subgroup and its actual image. -/
theorem core_kernel_map_iff {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (q : G →* H) (hq : IsPGroup 2 q.ker) (B : Subgroup G)
    {x : G} (hx : x ∈ normalizer (B : Set G)) :
    q x ∈ Closure.coreQuotientCentralizer (B.map q) ↔
      x ∈ Closure.coreQuotientCentralizer B := by
  have hn := B.le_normalizer_map q (mem_map_of_mem q hx)
  rw [core_kernel_iff_commutators _ hn,core_kernel_iff_commutators _ hx]
  constructor
  · intro hc b hb
    have hmem : ⁅x,b⁆ ∈ B := B.mul_mem ((mem_normalizer_iff.mp hx b).mp hb) (B.inv_mem hb)
    apply (inf_comap_pCoreIn_eq_of_ker_isPGroup 2 q B hq).le
    refine ⟨hmem,?_⟩
    change q ⁅x,b⁆ ∈ (B.map q).pCoreIn 2
    rw [map_commutatorElement]
    exact hc (q b) (mem_map_of_mem q hb)
  · intro hc
    rintro _ ⟨b,hb,rfl⟩
    have hh := mem_map_of_mem q (hc b hb)
    rwa [map_pCoreIn_of_ker_isPGroup q hq B,map_commutatorElement] at hh

namespace Sp4Model
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
private theorem sl2_center_trivial (a : SpecialLinearGroup (Fin 2) F)
    (ha : a ∈ center (SpecialLinearGroup (Fin 2) F)) : a = 1 := by
  let e : SpecialLinearGroup (Fin 2) F ≃* ProjectiveSpecialLinearGroup (Fin 2) F :=
    Atlas.RankOneFieldAutomorphisms.slEquivPSL
  apply e.map_eq_one_iff.mp
  exact Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot.le ((centerCongr e) ⟨a,ha⟩).property

/-- The literal point quotient action is trivial exactly when its middle
SL₂ block is the identity. The full intrinsic two-core is retained. -/
theorem point_kernel_iff (hF : Nat.card F = 4) (b : borel (F := F)) :
    b.val ∈ Closure.coreQuotientCentralizer (pointLocal (F := F)) ↔
      pointParabolicQuotient ⟨b.val,b.property.1⟩ = 1 := by
  have hn : b.val ∈ normalizer (pointLocal (F := F) : Set (Sp F)) := by
    rw [pointLocal_normalizer (n := 2) (by simpa using hF) (by decide)]
    exact b.property.1
  rw [core_kernel_iff_projection pointLocal pointQuotient
    (by rw [pointLocal_core_eq (n := 2) (by simpa using hF) (by decide)]; rfl) hn]
  have he (l : pointLocal (F := F)) :
      pointQuotient (pointLocal.normalizerMonoidHom ⟨b.val,hn⟩ l) =
      pointParabolicQuotient ⟨b.val,b.property.1⟩ * pointQuotient l *
        (pointParabolicQuotient ⟨b.val,b.property.1⟩)⁻¹ :=
    pointQuotient_conjugate ⟨b.val,b.property.1⟩ l _
  constructor
  · intro h
    apply sl2_center_trivial
    apply mem_center_iff.mpr
    intro a
    obtain ⟨l,rfl⟩ := pointQuotient_surjective a
    have hh := h l
    rw [he] at hh
    exact ((mul_inv_eq_iff_eq_mul).mp hh).symm
  · intro h l
    rw [he,h,one_mul,inv_one,mul_one]

omit [Finite F] in
private theorem point_block_one_iff_characters (b : borel (F := F))
    (hb : b^3 = 1) :
    pointParabolicQuotient ⟨b.val,b.property.1⟩ = 1 ↔
      (borelCharacters b).1 = (borelCharacters b).2 := by
  let q := pointParabolicQuotient ⟨b.val,b.property.1⟩
  let a := (borelCharacters b).1
  let d := (borelCharacters b).2
  have hb0 := (mem_borel_iff b.val).mp b.property
  have ha : b.val.val (.inl 0) (.inl 0) = (a:F) :=
    (determinantCharacter_point_coe ⟨b.val,b.property.1⟩).symm
  have hd : (a:F) * q.val 0 0 = (d:F) := by
    have hh := Plane.upperLeft_det (⟨b.val,b.property.2⟩ : planeParabolic)
    rw [det_fin_two] at hh
    change b.val.val (.inl 0) (.inl 0) * b.val.val (.inl 1) (.inl 1) -
      b.val.val (.inl 0) (.inl 1) * b.val.val (.inl 1) (.inl 0) = (d:F) at hh
    rw [ha,hb0.1,mul_zero,sub_zero] at hh
    exact hh
  constructor
  · intro h
    change q = 1 at h
    rw [h] at hd
    apply Units.ext
    simpa using hd
  · intro h
    have h00 : q.val 0 0 = 1 := by
      have had : a = d := h
      rw [←had] at hd
      exact (mul_eq_left₀ a.ne_zero).mp hd
    have h10 : q.val 1 0 = 0 := hb0.2 1 1
    have h11 : q.val 1 1 = 1 := by
      simpa only [det_fin_two,h00,h10,one_mul,mul_zero,sub_zero] using q.property
    have h2 : q^2 = 1 := by
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [pow_two,mul_apply,Fin.sum_univ_two,h00,h10,h11,CharTwo.add_self_eq_zero]
    have h3 : q^3 = 1 := by
      let p : borel (F := F) →* SpecialLinearGroup (Fin 2) F :=
        pointParabolicQuotient.comp (inclusion inf_le_left)
      change p b ^ 3 = 1
      rw [←map_pow,hb,map_one]
    have hh := h3
    rw [pow_succ,h2,one_mul] at hh
    exact hh

/-- For a cubic actor in the actual Borel, the point quotient kernel is
exactly the equality of the two determinant characters. -/
theorem cubic_point_kernel_iff_characters (hF : Nat.card F = 4)
    (b : borel (F := F)) (hb : b^3 = 1) :
    b.val ∈ Closure.coreQuotientCentralizer (pointLocal (F := F)) ↔
      (borelCharacters b).1 = (borelCharacters b).2 :=
  (point_kernel_iff hF b).trans (point_block_one_iff_characters b hb)

/-- The plane quotient kernel consists exactly of scalar upper-left
blocks. Scalars are kept in the full GL₂ action. -/
theorem plane_kernel_iff_scalar (hF : Nat.card F = 4) (b : borel (F := F)) :
    b.val ∈ Closure.coreQuotientCentralizer (planeLocal (F := F)) ↔
      ∃ a : F, Plane.upperLeft ⟨b.val,b.property.2⟩ = scalar (Fin 2) a := by
  have hn : b.val ∈ normalizer (planeLocal (F := F) : Set (Sp F)) := by
    rw [planeLocal_normalizer (n := 2) (by simpa using hF) (by decide)]
    exact b.property.2
  rw [core_kernel_iff_projection planeLocal Plane.quotientMap
    (by rw [planeLocal_core_eq (n := 2) (by simpa using hF) (by decide)]; rfl) hn]
  let g : planeParabolic (F := F) := ⟨b.val,b.property.2⟩
  let B := Plane.upperLeft g
  have hright : Plane.upperLeft g⁻¹ * B = 1 := by
    change Plane.upperLeft g⁻¹ * Plane.upperLeft g = 1
    rw [←map_mul,inv_mul_cancel,map_one]
  have hleft : B * Plane.upperLeft g⁻¹ = 1 := by
    change Plane.upperLeft g * Plane.upperLeft g⁻¹ = 1
    rw [←map_mul,mul_inv_cancel,map_one]
  have he (l : planeLocal (F := F)) :
      (Plane.quotientMap (planeLocal.normalizerMonoidHom ⟨b.val,hn⟩ l)).val =
      B * (Plane.quotientMap l).val * Plane.upperLeft g⁻¹ :=
    planeQuotient_conjugate g l _
  constructor
  · intro h
    have hc (A : SpecialLinearGroup (Fin 2) F) : Commute A.val B := by
      obtain ⟨l,rfl⟩ := Plane.quotientMap_surjective A
      have hh := congrArg Subtype.val (h l)
      rw [he] at hh
      calc
        (Plane.quotientMap l).val * B = (B * (Plane.quotientMap l).val * Plane.upperLeft g⁻¹) * B :=
          congrArg (fun z => z * B) hh.symm
        _ = B * (Plane.quotientMap l).val := by rw [mul_assoc, mul_assoc,hright,mul_one]
    obtain ⟨a,ha⟩ := mem_range_scalar_of_commute_transvectionStruct
      (fun t => hc t.toSpecialLinearGroup)
    exact ⟨a,ha.symm⟩
  · rintro ⟨a,ha⟩ l
    apply Subtype.ext
    rw [he]
    have hc : Commute B (Plane.quotientMap l).val := by
      rw [show B = scalar (Fin 2) a from ha]
      exact scalar_commute a (Commute.all a) _
    rw [hc.eq,mul_assoc,hleft,mul_one]

omit [Finite F] in
private theorem plane_scalar_iff_characters (b : borel (F := F)) (hb : b^3 = 1) :
    (∃ a : F, Plane.upperLeft ⟨b.val,b.property.2⟩ = scalar (Fin 2) a) ↔
      (borelCharacters b).2 = (borelCharacters b).1 ^ 2 := by
  let B := Plane.upperLeft (⟨b.val,b.property.2⟩ : planeParabolic)
  let a := (borelCharacters b).1
  have ha : B 0 0 = (a:F) :=
    (determinantCharacter_point_coe ⟨b.val,b.property.1⟩).symm
  have h10 : B 1 0 = 0 := (mem_borel_iff b.val).mp b.property |>.1
  have hd : (a:F) * B 1 1 = ((borelCharacters b).2 : F) := by
    have hh := Plane.upperLeft_det (⟨b.val,b.property.2⟩ : planeParabolic)
    change B.det = _ at hh
    change B.det = ((borelCharacters b).2 : F) at hh
    simpa only [det_fin_two,ha,h10,mul_zero,sub_zero] using hh
  constructor
  · rintro ⟨s,hs⟩
    have he : s = (a:F) := by
      have hh := congrArg (fun z : Matrix (Fin 2) (Fin 2) F => z 0 0) hs
      change B 0 0 = _ at hh
      simpa [ha] using hh.symm
    apply Units.ext
    rw [←hd]
    have h11 : B 1 1 = s := by rw [show B = scalar (Fin 2) s from hs]; simp
    simp only [h11,he,pow_two]; rfl
  · intro h
    have h11 : B 1 1 = (a:F) := by
      rw [h,Units.val_pow_eq_pow_val,pow_two] at hd
      exact mul_left_cancel₀ a.ne_zero hd
    have h3 : B^3 = 1 := by
      let p : borel (F := F) →* Matrix (Fin 2) (Fin 2) F :=
        Plane.upperLeft.comp (inclusion inf_le_right)
      change p b ^ 3 = 1
      rw [←map_pow,hb,map_one]
    have hh := congrArg (fun z : Matrix (Fin 2) (Fin 2) F => z 0 1) h3
    have h01 : B 0 1 = 0 := by
      have hz : (a:F) * ((a:F) * B 0 1) = 0 := by
        rw [show (3:ℕ) = 2+1 from rfl,pow_succ,pow_two] at hh
        simp only [one_apply,Fin.zero_ne_one,if_false] at hh
        simp only [mul_apply,Fin.sum_univ_two,ha,h10,h11,mul_zero,add_zero,
          mul_comm (B 0 1) (a:F),CharTwo.add_self_eq_zero,zero_mul,mul_assoc] at hh
        exact hh
      exact (mul_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left a.ne_zero)).resolve_left a.ne_zero
    refine ⟨a,?_⟩
    change B = scalar (Fin 2) (a:F)
    ext i j
    fin_cases i <;> fin_cases j
    · exact ha
    · exact h01
    · exact h10
    · exact h11

/-- On cubic actors, the actual plane quotient kernel is the second
character equal to the square of the first. -/
theorem cubic_plane_kernel_iff_characters (hF : Nat.card F = 4)
    (b : borel (F := F)) (hb : b^3 = 1) :
    b.val ∈ Closure.coreQuotientCentralizer (planeLocal (F := F)) ↔
      (borelCharacters b).2 = (borelCharacters b).1 ^ 2 :=
  (plane_kernel_iff_scalar hF b).trans (plane_scalar_iff_characters b hb)

end Sp4Model
end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.TerminalOrientation

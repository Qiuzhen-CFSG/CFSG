module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.SpecificGroups.SymplecticFour.NaturalScalarCubic
public import Theory.GroupTheory.PCoreImage
public import Theory.SpecificGroups.SymplecticFour.PlaneNaturalQuotient
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ExceptionalRestrictions.Conjugation
public import CFSG.Quasithin.ChapterI.Section02.ModuleCovers.SymplecticFour.Roots
public import Theory.SpecificGroups.SymplecticFour.PlaneDisplacements

/-!
# Natural symplectic block geometry over every nonbinary field

The point exclusion, plane quotient and root commutator arguments work over
any field of order 2^n with n > 1. The local-core identifications and the
I.2.3 root-cover calculation are the only field-size inputs. This extension
retains the whole fixed layer and the literal quotient map, so the crossed
module argument in original 4.3.7 can be applied before the C.1.32 field
restriction. The field-four interfaces are preserved in their original files.

Source: Aschbacher--Smith I.2.3(3), C.4.1(2) and 4.3.7,
printed pp.413,151--153,615--616.
-/
public section
noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open Theory.SpecificGroups.SymplecticFour
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.SymplecticNonbinary
open CFSG.Quasithin.ChapterC.ExceptionalRestrictions
variable {X : Type*} [Group X] [Finite X] {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- A moved subgroup fixed by the local core excludes the point marking. -/
theorem symplectic_not_point_of_moved_core_fixed
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    {rho : Sp F →* MulAut (Multiplicative (Vector F))}
    (m : BlockModuleModel X rho)
    (hrho : ∀ g v, (rho g v).toAdd = g.val.mulVec v.toAdd)
    (A W : Subgroup X) (hWU : W ≤ blockU X) (hne : W ≠ ⊥)
    (hcomm : ⁅W,A⁆ = W)
    (hfix : W ≤ centralizer (A.pCoreIn 2 : Set X)) :
    A.map (m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))) ≠
      pointLocal := by
  intro hA
  let p := m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  let q := m.moduleIso.toMonoidHom.comp (QuotientGroup.mk' (blockFixed X))
  have hp : p.ker = pCore 2 X := by
    rw [MonoidHom.ker_comp_of_injective _ _ m.quotientIso.injective,QuotientGroup.ker_mk']
  have hk : q.ker = blockFixed X := by
    rw [MonoidHom.ker_comp_of_injective _ _ m.moduleIso.injective,QuotientGroup.ker_mk']
  have hcore : (A.pCoreIn 2).map p = pointRadicalAmbient := by
    rw [map_pCoreIn_of_ker_isPGroup p (hp ▸ pCore_isPGroup), hA]
    change (pCore 2 (pointLocal (F := F))).map pointLocal.subtype = _
    rw [pointLocal_core_eq hF hn]
  have hq (a : X) (u : blockU X) :
      (q (blockConjugate X a u)).toAdd = (p a).val.mulVec (q u).toAdd := by
    change (m.moduleIso (QuotientGroup.mk' _ (blockConjugate X a u))).toAdd = _
    rw [m.intertwining,hrho]
    rfl
  have hpoint (w : blockU X) (hw : w.val ∈ W) : (q w).toAdd ∈ point F := by
    apply NaturalScalarCubic.point_radical_fixed
    intro r hr
    rw [←hcore] at hr
    obtain ⟨a,ha,rfl⟩ := hr
    rw [smul_eq_mulVec,←hq]
    congr 2
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hfix hw a ha)
  have hfixed (a : X) (ha : a ∈ A) (w : blockU X) (hw : w.val ∈ W) :
      q (blockConjugate X a w) = q w := by
    apply Multiplicative.toAdd.injective
    rw [hq,←smul_eq_mulVec]
    have hpA : p a ∈ pointLocal (F := F) := hA ▸ mem_map_of_mem p ha
    obtain ⟨t,ht⟩ := Submodule.mem_span_singleton.mp (hpoint w hw)
    rw [←ht]
    change toLinear (p a) (t • e 0) = t • e 0
    rw [map_smul]
    exact congrArg (t • ·) ((mem_pointLocal_iff_fixed (p a)).mp hpA)
  have hc : ⁅A,W⁆ ≤ center X := by
    apply commutator_le.mpr
    intro a ha w hw
    let u : blockU X := ⟨w,hWU hw⟩
    have hz : blockConjugate X a u * u⁻¹ ∈ q.ker := by
      rw [MonoidHom.mem_ker,map_mul,map_inv,hfixed a ha u hw,mul_inv_cancel]
    rw [hk] at hz
    exact hz
  rw [commutator_comm,hcomm] at hc
  have hz : ⁅W,A⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr (by
    intro w hw a _
    exact mem_center_iff.mp (hc hw) a)
  exact hne (hcomm.symm.trans hz)

variable {X : Type*} [Group X] [Finite X] {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The full local image in the original central quotient is the natural plane. -/
theorem symplectic_plane_image
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    {rho : Sp F →* MulAut (Multiplicative (Vector F))}
    (m : BlockModuleModel X rho)
    (hrho : ∀ g v, (rho g v).toAdd = g.val.mulVec v.toAdd)
    (A W : Subgroup X) (hWU : W ≤ blockU X) (hne : W ≠ ⊥)
    (hcomm : ⁅W,A⁆ = W)
    (hfix : W ≤ centralizer (A.pCoreIn 2 : Set X))
    (hA : A.map (m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))) =
      planeLocal) :
    ((W.subgroupOf (blockU X)).map
      (m.moduleIso.toMonoidHom.comp (QuotientGroup.mk' (blockFixed X)))).toAddSubgroup' =
        (plane F).toAddSubgroup := by
  let p := m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  let q := m.moduleIso.toMonoidHom.comp (QuotientGroup.mk' (blockFixed X))
  let Q := (W.subgroupOf (blockU X)).map q
  have hp : p.ker = pCore 2 X := by
    rw [MonoidHom.ker_comp_of_injective _ _ m.quotientIso.injective,QuotientGroup.ker_mk']
  have hk : q.ker = blockFixed X := by
    rw [MonoidHom.ker_comp_of_injective _ _ m.moduleIso.injective,QuotientGroup.ker_mk']
  have hcore : (A.pCoreIn 2).map p = planeRadicalAmbient := by
    rw [map_pCoreIn_of_ker_isPGroup p (hp ▸ pCore_isPGroup), hA]
    change (pCore 2 (planeLocal (F := F))).map planeLocal.subtype = _
    rw [planeLocal_core_eq hF hn]
  have hq (a : X) (u : blockU X) :
      (q (blockConjugate X a u)).toAdd = (p a).val.mulVec (q u).toAdd := by
    change (m.moduleIso (QuotientGroup.mk' _ (blockConjugate X a u))).toAdd = _
    rw [m.intertwining,hrho]
    rfl
  have hWn : A ≤ normalizer (W : Set X) := by
    rw [le_normalizer_iff_commutator_le_right,commutator_comm,hcomm]
  have hQ : ∀ g ∈ planeLocal, ∀ v ∈ Q.toAddSubgroup', g.val.mulVec v ∈ Q.toAddSubgroup' := by
    rw [←hA]
    rintro g ⟨a,ha,rfl⟩ v ⟨u,hu,huv⟩
    refine ⟨blockConjugate X a u,?_,?_⟩
    · exact (mem_normalizer_iff.mp (hWn ha) (u : X)).mp hu
    · apply Multiplicative.toAdd.injective
      rw [hq,huv]
      rfl
  have hQne : Q.toAddSubgroup' ≠ ⊥ := by
    intro he
    have hWZ : W ≤ center X := by
      intro w hw
      let u : blockU X := ⟨w,hWU hw⟩
      have hmem : (q u).toAdd ∈ Q.toAddSubgroup' := ⟨u,hw,rfl⟩
      rw [he] at hmem
      have hu : u ∈ q.ker := hmem
      rw [hk] at hu
      exact hu
    have hc : ⁅W,A⁆ = ⊥ := by
      apply commutator_eq_bot_iff_le_centralizer.mpr
      intro w hw a _
      exact mem_center_iff.mp (hWZ hw) a
    exact hne (hcomm.symm.trans hc)
  apply PlaneNatural.invariant_additive_eq_plane Q.toAddSubgroup' hQne _ hQ
  rintro v ⟨w,hw,rfl⟩
  apply NaturalScalarCubic.plane_radical_fixed
  intro r hr
  rw [←hcore] at hr
  obtain ⟨a,ha,rfl⟩ := hr
  change (p a).val.mulVec (q w).toAdd = (q w).toAdd
  rw [←hq]
  congr 2
  apply Subtype.ext
  exact mul_inv_eq_iff_eq_mul.mpr (hfix hw a ha)

/-- Natural quotient coordinates with the complete central layer retained in the kernel. -/
theorem symplectic_natural_quotient
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    {rho : Sp F →* MulAut (Multiplicative (Vector F))}
    (m : BlockModuleModel X rho)
    (hrho : ∀ g v, (rho g v).toAdd = g.val.mulVec v.toAdd)
    (A W : Subgroup X) (hWU : W ≤ blockU X) (hne : W ≠ ⊥)
    (hcomm : ⁅W,A⁆ = W)
    (hfix : W ≤ centralizer (A.pCoreIn 2 : Set X))
    (hA : A.map (m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))) =
      planeLocal) :
    ∃ f : blockU X →* Multiplicative (Fin 2 → F), Function.Surjective f ∧
      f.ker = (W ⊔ (blockU X ⊓ center X)).subgroupOf (blockU X) ∧
      ∀ (a : X) (ha : a ∈ A) (u : blockU X),
        f (blockConjugate X a u) = Multiplicative.ofAdd
          ((Plane.quotientMap ⟨m.quotientIso (QuotientGroup.mk' (pCore 2 X) a),
            hA ▸ mem_map_of_mem _ ha⟩).val.mulVec (f u).toAdd) := by
  let q := m.moduleIso.toMonoidHom.comp (QuotientGroup.mk' (blockFixed X))
  let f := PlaneNatural.quotient.toAddMonoidHom.toMultiplicative.comp q
  have hsurj : Function.Surjective q :=
    m.moduleIso.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = blockFixed X := by
    rw [MonoidHom.ker_comp_of_injective _ _ m.moduleIso.injective,QuotientGroup.ker_mk']
  have himage := symplectic_plane_image hF hn m hrho A W hWU hne hcomm hfix hA
  let Q := (W.subgroupOf (blockU X)).map q
  have hpre : (Q.comap q).map (blockU X).subtype = W ⊔ (blockU X ⊓ center X) := by
    rw [Subgroup.comap_map_eq,Subgroup.map_sup,hk,
      map_subgroupOf_eq_of_le hWU,blockFixed_map]
  refine ⟨f,?_,?_,?_⟩
  · intro v
    obtain ⟨w,hw⟩ := PlaneNatural.quotient_surjective v.toAdd
    obtain ⟨u,hu⟩ := hsurj (Multiplicative.ofAdd w)
    exact ⟨u,by change Multiplicative.ofAdd (PlaneNatural.quotient (q u).toAdd) = v; rw [hu]; exact congrArg Multiplicative.ofAdd hw⟩
  · ext u
    change f u = 1 ↔ u.val ∈ W ⊔ (blockU X ⊓ center X)
    rw [←hpre]
    change f u = 1 ↔ (blockU X).subtype u ∈ (Q.comap q).map (blockU X).subtype
    rw [mem_map_iff_mem (blockU X).subtype_injective]
    change PlaneNatural.quotient (q u).toAdd = 0 ↔ (q u).toAdd ∈ Q.toAddSubgroup'
    rw [PlaneNatural.quotient_eq_zero,himage]
    rfl
  · intro a ha u
    apply Multiplicative.toAdd.injective
    change PlaneNatural.quotient
      (m.moduleIso (QuotientGroup.mk' (blockFixed X) (blockConjugate X a u))).toAdd = _
    rw [m.intertwining,hrho]
    exact PlaneNatural.quotient_action
      ⟨m.quotientIso (QuotientGroup.mk' (pCore 2 X) a),hA ▸ mem_map_of_mem _ ha⟩
      (q u).toAdd


namespace SymplecticRootModule
variable {X : Type*} [Group X] [Finite X] {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
private theorem root_zero_mem_radical (t : F) :
    Representation.OneCohomology.SymplecticFour.rootElement 0 t ∈ planeRadicalAmbient := by
  let B : Plane.symmetricMatrices F := ⟨!![t,0;0,0], by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl⟩
  have he : (Plane.shear B).val =
      Representation.OneCohomology.SymplecticFour.rootElement 0 t := by
    apply Subtype.ext
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;> rfl
  rw [←he]
  exact mem_map_of_mem planeLocal.subtype (show Plane.shear B ∈ Plane.radical from Plane.quotientMap_shear B)

/-- The global fixed layer is generated by displacements from the actual local core. -/
theorem fixed_le_core_commutator
    (h : IsShort X) {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    {rho : Sp F →* MulAut (Multiplicative (Vector F))}
    (m : BlockModuleModel X rho)
    (hrho : ∀ g v, (rho g v).toAdd = g.val.mulVec v.toAdd)
    (A : Subgroup X)
    (hA : A.map (m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))) = planeLocal) :
    blockU X ⊓ center X ≤ ⁅blockU X,A.pCoreIn 2⁆ := by
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hn
  let := h.elementary
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let d : (X ⧸ pCore 2 X) ≃* SymplecticFourOrthogonalCover.L (K := F) := {
    toFun x := ⟨m.quotientIso x, by
      rw [SymplecticFour.LargeField.commutator_eq_top hlarge]
      trivial⟩
    invFun g := m.quotientIso.symm g.val
    left_inv x := m.quotientIso.symm_apply_apply x
    right_inv g := Subtype.ext (m.quotientIso.apply_symm_apply g.val)
    map_mul' x y := Subtype.ext (m.quotientIso.map_mul x y) }
  let σ : Representation (ZMod 2) (SymplecticFourOrthogonalCover.L (K := F))
      (Additive (blockU X)) := (uRepresentation h).comp d.symm.toMonoidHom
  let q := m.moduleIso.toMonoidHom.comp (QuotientGroup.mk' (blockFixed X))
  let p : σ.IntertwiningMap (SymplecticFourOrthogonalCover.binaryNatural (K := F)) :=
    q.toAdditiveLeft.toZModLinearMap 2 |>.intertwiningMap_of_isIntertwiningMap _ _ (by
      intro g u
      obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective (pCore 2 X) (d.symm g)
      change (q (uAut h (d.symm g) u.toMul)).toAdd = _
      rw [←hx]
      change (m.moduleIso (QuotientGroup.mk' _ (blockConjugate X x u.toMul))).toAdd = _
      rw [m.intertwining,hrho]
      have he : m.quotientIso (QuotientGroup.mk' (pCore 2 X) x) = g.val := by
        rw [hx]
        exact m.quotientIso.apply_symm_apply g.val
      rw [he]
      rfl)
  have hp : IsCover p := by
    refine ⟨?_,?_,?_⟩
    · intro v
      obtain ⟨u,hu⟩ := (m.moduleIso.surjective.comp (QuotientGroup.mk'_surjective _))
        (Multiplicative.ofAdd v)
      exact ⟨Additive.ofMul u,hu⟩
    · intro u hu g
      have hz : u.toMul ∈ blockFixed X := by
        apply (QuotientGroup.eq_one_iff _).mp
        apply m.moduleIso.injective
        exact hu.trans (map_one m.moduleIso).symm
      exact (uRepresentation_fixed h u).mpr hz (d.symm g)
    · apply top_unique
      rw [←uRepresentation_moved h]
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨g,u⟩,rfl⟩
      have he : σ (d g) u = uRepresentation h g u := by
        change uRepresentation h (d.symm (d g)) u = _
        rw [d.symm_apply_apply]
      change uRepresentation h g u - u ∈ Coinvariants.ker σ
      rw [←he]
      exact Coinvariants.sub_mem_ker (d g) u
  have hgeo := ChapterI.ModuleCovers.SymplecticFour.arbitrary_cover_root_geometry
    hlarge p hp
  let π := m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hπ : π.ker = pCore 2 X := by
    rw [MonoidHom.ker_comp_of_injective _ _ m.quotientIso.injective,QuotientGroup.ker_mk']
  have hcore : (A.pCoreIn 2).map π = planeRadicalAmbient := by
    rw [map_pCoreIn_of_ker_isPGroup π (hπ ▸ pCore_isPGroup),hA]
    change (pCore 2 (planeLocal (F := F))).map planeLocal.subtype = _
    rw [planeLocal_core_eq hF hn]
  let B := ⁅blockU X,A.pCoreIn 2⁆
  let S : Submodule (ZMod 2) (Additive (blockU X)) :=
    AddSubgroup.toZModSubmodule 2 (B.subgroupOf (blockU X)).toAddSubgroup
  have hmove : Coinvariants.ker
      (σ.comp (SymplecticFourOrthogonalCover.Roots.group (K := F)).subtype) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,u⟩,rfl⟩
    obtain ⟨t,ht⟩ := (SymplecticFourOrthogonalCover.Roots.mem_group hlarge g.val).mp g.property
    have hgm : g.val.val ∈ planeRadicalAmbient := by
      rw [←ht]
      exact root_zero_mem_radical t
    rw [←hcore] at hgm
    obtain ⟨a,ha,hea⟩ := hgm
    have hd : d.symm g.val = QuotientGroup.mk' (pCore 2 X) a := by
      apply m.quotientIso.injective
      change m.quotientIso (m.quotientIso.symm g.val.val) = π a
      rw [m.quotientIso.apply_symm_apply,hea]
    change ((uRepresentation h (d.symm g.val) u - u).toMul : X) ∈ B
    change ((uRepresentation h (d.symm g.val) u).toMul : X) / (u.toMul : X) ∈ B
    rw [div_eq_mul_inv,hd,uRepresentation_apply]
    exact (commutator_comm (A.pCoreIn 2) (blockU X)).le
      (commutator_mem_commutator ha u.toMul.property)
  intro z hz
  let u : Additive (blockU X) := Additive.ofMul ⟨z,hz.1⟩
  have hu : u ∈ fixed σ := by
    intro g
    exact (uRepresentation_fixed h u).mpr hz.2 (d.symm g)
  have hu' := hgeo.1 hu
  rw [hgeo.2.1] at hu'
  exact hmove hu'

/-- The plane residual generates the whole block layer by commutators. -/
theorem commutator_eq
    (h : IsShort X) {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    {rho : Sp F →* MulAut (Multiplicative (Vector F))}
    (m : BlockModuleModel X rho)
    (hrho : ∀ g v, (rho g v).toAdd = g.val.mulVec v.toAdd)
    (A : Subgroup X)
    (hA : A.map (m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))) = planeLocal) :
    ⁅blockU X,A⁆ = blockU X := by
  let p := m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  let q := m.moduleIso.toMonoidHom.comp (QuotientGroup.mk' (blockFixed X))
  let B := ⁅blockU X,A⁆
  let Q := ((B.subgroupOf (blockU X)).map q).toAddSubgroup'
  have hQ : Q = ⊤ := by
    apply PlaneNatural.displacements_span
    intro g v
    have hg : g.val ∈ A.map p := hA.symm ▸ g.property
    obtain ⟨a,ha,hea⟩ := hg
    obtain ⟨u,hu⟩ := (m.moduleIso.surjective.comp (QuotientGroup.mk'_surjective _))
      (Multiplicative.ofAdd v)
    refine ⟨blockConjugate X a u * u⁻¹,?_,?_⟩
    · change a * u.val * a⁻¹ * u.val⁻¹ ∈ B
      exact (commutator_comm A (blockU X)).le (commutator_mem_commutator ha u.property)
    · change q (blockConjugate X a u * u⁻¹) = Multiplicative.ofAdd (g.val.val.mulVec v - v)
      change q u = Multiplicative.ofAdd v at hu
      apply Multiplicative.toAdd.injective
      rw [map_mul,map_inv]
      change (m.moduleIso (QuotientGroup.mk' _ (blockConjugate X a u))).toAdd + -(q u).toAdd = _
      rw [m.intertwining,hrho]
      change (p a).val.mulVec (q u).toAdd + -(q u).toAdd = _
      rw [hea,hu]
      exact (sub_eq_add_neg _ _).symm
  have hZ : blockU X ⊓ center X ≤ B :=
    (fixed_le_core_commutator h hF hn m hrho A hA).trans
      (commutator_mono le_rfl (pCoreIn_le 2 A))
  apply le_antisymm (commutator_le_left _ _)
  intro x hx
  let u : blockU X := ⟨x,hx⟩
  have hu : (q u).toAdd ∈ Q := hQ ▸ AddSubgroup.mem_top _
  obtain ⟨v,hv,hev⟩ := hu
  change q v = q u at hev
  have hz : u * v⁻¹ ∈ blockFixed X := by
    apply (QuotientGroup.eq_one_iff _).mp
    apply m.moduleIso.injective
    change q (u*v⁻¹) = m.moduleIso 1
    rw [map_one,map_mul,map_inv,hev,mul_inv_cancel]
  have hmem := (B.mul_mem (hZ ⟨(u*v⁻¹).property,hz⟩) hv)
  change x * v.val⁻¹ * v.val ∈ B at hmem
  simpa only [inv_mul_cancel_right] using hmem

end SymplecticRootModule

end CFSG.Quasithin.ChapterC.SymplecticNonbinary

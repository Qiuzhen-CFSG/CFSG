module

public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.Models
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification.Transitivity
public import Theory.AtlasPort.LinearGroups.G2.DistinguishedPlane

/-!
# The three-line pencil in the binary G₂ models

At the first singular point, annihilation by its basis vector confines every
incident zero-product line to the first three octonion coordinates. The three
possible binary directions give exactly three lines. Their span embeds in
both the trace-zero Weyl module and its natural quotient and has dimension
three. Point transitivity transports the calculation to every singular point.

The final applications use the literal subgroups of `U/(V₁ ∩ U)`. They prove
clause (3) of Aschbacher–Smith 14.7.55 once the earlier source marking of
`V₂/V₁` is supplied. They do not assume pencil size or span rank. The marking,
actor centralizers, offender classification and residual action remain
separate obligations in the assembly of 14.7.55.

Source: combined manuscript (1 March 2004), printed p.1066, PDF p.1083.
The existing octonion realization is from the attributed ATLAS port; see
LICENSES/ATLAS.txt. No additional ATLAS source is copied here.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil
open Atlas.G2 Atlas.SplitOctonion Atlas.G2.Natural
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification

private def direction (i : Fin 3) : Carrier (ZMod 2) :=
  ![0, (![1,0,1] : Fin 3 → ZMod 2) i, (![0,1,1] : Fin 3 → ZMod 2) i,0,0,0,0,0]

private theorem direction_ne_zero (i : Fin 3) : direction i ≠ 0 := by
  intro h
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  fin_cases i <;> simp [direction] at h1 h2

private def plane (i : Fin 3) : Submodule (ZMod 2) (Carrier (ZMod 2)) :=
  Submodule.span (ZMod 2) {basisVector 0, direction i}

private theorem plane_isLine (i : Fin 3) : IsZeroProductLine (plane i) := by
  constructor
  · have hi : LinearIndependent (ZMod 2)
        (![basisVector 0, direction i] : Fin 2 → Carrier (ZMod 2)) := by
      rw [linearIndependent_fin2]
      refine ⟨direction_ne_zero i, ?_⟩
      intro a h
      have he := congrFun h 0
      simp [direction, basisVector] at he
    have hr : Set.range (![basisVector 0, direction i] : Fin 2 → Carrier (ZMod 2)) =
        {basisVector 0, direction i} := by
      ext x
      simp [or_comm]
    have he := finrank_span_eq_card hi
    change Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
      (Set.range (![basisVector 0, direction i] : Fin 2 → Carrier (ZMod 2)))) = 2 at he
    rw [hr] at he
    exact he
  · intro x hx y hy
    obtain ⟨a,b,rfl⟩ := Submodule.mem_span_pair.mp hx
    obtain ⟨c,d,rfl⟩ := Submodule.mem_span_pair.mp hy
    ext j
    fin_cases j <;> simp [Atlas.SplitOctonion.mul, basisVector, direction]
    ring_nf
    simp only [show (2 : ZMod 2) = 0 by decide, mul_zero]

private def baseLine (i : Fin 3) : ZeroProductLine (ZMod 2) := ⟨plane i, plane_isLine i⟩

private theorem baseLine_incident (i : Fin 3) : pointOnLine firstPoint (baseLine i) := by
  rw [firstPoint_on_line_iff]
  exact Submodule.subset_span (by simp)

private theorem baseLine_injective : Function.Injective baseLine := by
  intro i j h
  have hd : direction i ∈ plane j := by
    have hi : direction i ∈ (baseLine i).val := Submodule.subset_span (by simp)
    rwa [h] at hi
  obtain ⟨a,b,he⟩ := Submodule.mem_span_pair.mp hd
  have h1 := congrFun he 1
  have h2 := congrFun he 2
  fin_cases i <;> fin_cases j <;> simp_all [direction, basisVector]

private theorem line_le_plane (L : ZeroProductLine (ZMod 2)) (hL : pointOnLine firstPoint L) :
    L.val ≤ distinguishedPlane := by
  intro x hx
  have h0 := (firstPoint_on_line_iff L).mp hL
  have hl := (inLowerPlane_iff_annihilator x).mpr
    ⟨L.property.2 _ h0 _ hx, L.property.2 _ hx _ h0⟩
  rcases hl with ⟨h3,h4,h5,h6,h7⟩
  intro i hi
  fin_cases i <;> simp_all

private theorem baseLine_exhausts (L : ZeroProductLine (ZMod 2))
    (hL : pointOnLine firstPoint L) : ∃ i, baseLine i = L := by
  have h0 := (firstPoint_on_line_iff L).mp hL
  have hnot : ¬ L.val ≤ Submodule.span (ZMod 2) {basisVector 0} := by
    intro h
    have hf := Submodule.finrank_mono h
    rw [L.property.1, finrank_span_singleton first_basis_ne_zero] at hf
    omega
  have hex : ∃ x ∈ L.val, x ∉ Submodule.span (ZMod 2) {basisVector 0} := by
    by_contra! hn
    exact hnot hn
  obtain ⟨x,hx,hout⟩ := hex
  have hd := line_le_plane L hL hx
  have he := distinguishedPlane_coordinates hd
  have hne : x 1 ≠ 0 ∨ x 2 ≠ 0 := by
    by_contra! h
    apply hout
    apply Submodule.mem_span_singleton.mpr
    refine ⟨x 0, ?_⟩
    rw [he]
    ext j
    fin_cases j <;> simp [basisVector, h.1,h.2]
  have hb : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have hi : ∃ i : Fin 3, direction i = x - (x 0) • basisVector 0 := by
    rcases hb (x 1) with h1 | h1 <;> rcases hb (x 2) with h2 | h2
    · rcases hne with hn | hn <;> contradiction
    · refine ⟨1, ?_⟩
      rw [he]
      ext j
      fin_cases j <;> simp [direction,basisVector,h1,h2]
    · refine ⟨0, ?_⟩
      rw [he]
      ext j
      fin_cases j <;> simp [direction,basisVector,h1,h2]
    · refine ⟨2, ?_⟩
      rw [he]
      ext j
      fin_cases j <;> simp [direction,basisVector,h1,h2]
  obtain ⟨i,hi⟩ := hi
  refine ⟨i, Subtype.ext ?_⟩
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    rintro y (rfl | rfl)
    · exact h0
    · rw [hi]
      exact L.val.sub_mem hx (L.val.smul_mem _ h0)
  · exact (plane_isLine i).1.trans L.property.1.symm

private def basePencilEquiv : Fin 3 ≃ {L : ZeroProductLine (ZMod 2) // pointOnLine firstPoint L} :=
  Equiv.ofBijective (fun i => ⟨baseLine i, baseLine_incident i⟩) ⟨by
    intro i j h
    exact baseLine_injective (congrArg Subtype.val h), by
    rintro ⟨L,hL⟩
    obtain ⟨i,hi⟩ := baseLine_exhausts L hL
    exact ⟨i, Subtype.ext hi⟩⟩

/-- The three doubly singular lines through a binary singular point. -/
theorem pencil_card (p : SingularPoints (ZMod 2)) :
    Nat.card {L : ZeroProductLine (ZMod 2) // pointOnLine p L} = 3 := by
  obtain ⟨g,hg⟩ := exists_smul_firstPoint p
  let e : {L : ZeroProductLine (ZMod 2) // pointOnLine p L} ≃
      {L : ZeroProductLine (ZMod 2) // pointOnLine firstPoint L} :=
    { toFun := fun L => ⟨g • L.val, by rw [← hg]; exact (pointOnLine_smul_iff g p L.val).mpr L.property⟩
      invFun := fun L => ⟨g⁻¹ • L.val, by
        have h := (pointOnLine_smul_iff g⁻¹ firstPoint L.val).mpr L.property
        simpa only [← hg, inv_smul_smul] using h⟩
      left_inv := fun L => Subtype.ext (inv_smul_smul g L.val)
      right_inv := fun L => Subtype.ext (smul_inv_smul g L.val) }
  rw [Nat.card_congr e, ← Nat.card_congr basePencilEquiv]
  simp


variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- The span of the doubly singular lines through the marked point. -/
def pencilSpan (f : SingularMap W) (p : SingularPoints (ZMod 2)) : Submodule (ZMod 2) W :=
  ⨆ L : {L : ZeroProductLine (ZMod 2) // pointOnLine p L}, f.line L.val

private def lowerLift : (Fin 3 → ZMod 2) →ₗ[ZMod 2] TraceZero (ZMod 2) where
  toFun x := ⟨![x 0,x 1,x 2,0,0,0,0,0], by simp [trace]⟩
  map_add' x y := by ext j; fin_cases j <;> simp
  map_smul' a x := by ext j; fin_cases j <;> simp

private theorem lowerLift_norm (x : Fin 3 → ZMod 2) :
    Atlas.SplitOctonion.norm (lowerLift x).val = 0 := by
  simp [lowerLift, Atlas.SplitOctonion.norm]

private theorem lowerLift_comp_injective (f : SingularMap W) :
    Function.Injective (f.linear.comp lowerLift) := by
  intro x y h
  have he := f.separates (lowerLift x) (lowerLift y) (lowerLift_norm x) (lowerLift_norm y) h
  have hc := congrArg Subtype.val he
  ext j
  fin_cases j
  all_goals first | exact congrFun hc 0 | exact congrFun hc 1 | exact congrFun hc 2

private theorem base_span_range (f : SingularMap W) :
    pencilSpan f firstPoint = LinearMap.range (f.linear.comp lowerLift) := by
  apply le_antisymm
  · apply iSup_le
    rintro ⟨L,hL⟩ y ⟨x,hx,rfl⟩
    have hd := line_le_plane L hL hx
    refine ⟨![x.val 0,x.val 1,x.val 2], ?_⟩
    apply congrArg f.linear
    exact Subtype.ext (distinguishedPlane_coordinates hd).symm
  · have h0 : f.linear (lowerLift ![1,0,0]) ∈ pencilSpan f firstPoint := by
      apply (le_iSup (fun L : {L : ZeroProductLine (ZMod 2) // pointOnLine firstPoint L} =>
        f.line L.val) ⟨baseLine 0,baseLine_incident 0⟩)
      refine ⟨lowerLift ![1,0,0], ?_, rfl⟩
      change ![(1 : ZMod 2),0,0,0,0,0,0,0] ∈ plane 0
      have he : (![(1 : ZMod 2),0,0,0,0,0,0,0] : Carrier (ZMod 2)) = basisVector 0 := by
        ext j; fin_cases j <;> simp [basisVector]
      rw [he]
      exact Submodule.subset_span (by simp)
    have h1 : f.linear (lowerLift ![0,1,0]) ∈ pencilSpan f firstPoint := by
      apply (le_iSup (fun L : {L : ZeroProductLine (ZMod 2) // pointOnLine firstPoint L} =>
        f.line L.val) ⟨baseLine 0,baseLine_incident 0⟩)
      refine ⟨lowerLift ![0,1,0], ?_, rfl⟩
      exact Submodule.subset_span (by change direction 0 ∈ {basisVector 0,direction 0}; simp)
    have h2 : f.linear (lowerLift ![0,0,1]) ∈ pencilSpan f firstPoint := by
      apply (le_iSup (fun L : {L : ZeroProductLine (ZMod 2) // pointOnLine firstPoint L} =>
        f.line L.val) ⟨baseLine 1,baseLine_incident 1⟩)
      refine ⟨lowerLift ![0,0,1], ?_, rfl⟩
      exact Submodule.subset_span (by change direction 1 ∈ {basisVector 0,direction 1}; simp)
    rintro y ⟨x,rfl⟩
    change f.linear (lowerLift x) ∈ _
    have he : lowerLift x = x 0 • lowerLift ![1,0,0] +
        x 1 • lowerLift ![0,1,0] + x 2 • lowerLift ![0,0,1] := by
      ext j; fin_cases j <;> simp [lowerLift]
    rw [he, map_add, map_add, map_smul, map_smul, map_smul]
    exact (pencilSpan f firstPoint).add_mem
      ((pencilSpan f firstPoint).add_mem ((pencilSpan f firstPoint).smul_mem _ h0)
        ((pencilSpan f firstPoint).smul_mem _ h1)) ((pencilSpan f firstPoint).smul_mem _ h2)

/-- At the first point the pencil span is precisely the image of the first
three octonion coordinates. This supplies coordinates for actor calculations. -/
theorem pencilSpan_firstPoint (f : SingularMap W) :
    pencilSpan f firstPoint = f.image distinguishedPlane := by
  rw [base_span_range]
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    refine ⟨lowerLift x, ?_, rfl⟩
    change (lowerLift x).val ∈ distinguishedPlane
    intro i hi
    fin_cases i <;> simp_all [lowerLift]
  · rintro ⟨x,hx,rfl⟩
    refine ⟨![x.val 0,x.val 1,x.val 2], ?_⟩
    apply congrArg f.linear
    exact Subtype.ext (distinguishedPlane_coordinates hx).symm

private def actorEquiv (ρ : Representation (ZMod 2) (Model (ZMod 2)) W)
    (g : Model (ZMod 2)) : W ≃ₗ[ZMod 2] W where
  toLinearMap := ρ g
  invFun := ρ g⁻¹
  left_inv x := by change (ρ g⁻¹ * ρ g) x = x; rw [← map_mul, inv_mul_cancel, map_one]; rfl
  right_inv x := by change (ρ g * ρ g⁻¹) x = x; rw [← map_mul, mul_inv_cancel, map_one]; rfl

/-- The pencil span respects the actual G₂ action. -/
theorem pencilSpan_equivariant (f : SingularMap W)
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) W) (hf : f.Equivariant ρ)
    (g : Model (ZMod 2)) (p : SingularPoints (ZMod 2)) :
    (pencilSpan f p).map (ρ g) = pencilSpan f (g • p) := by
  unfold pencilSpan
  rw [Submodule.map_iSup]
  apply le_antisymm
  · apply iSup_le
    rintro ⟨L,hL⟩
    rw [← f.line_equivariant ρ hf g L]
    exact le_iSup (fun L : {L : ZeroProductLine (ZMod 2) // pointOnLine (g • p) L} =>
      f.line L.val) ⟨g • L, (pointOnLine_smul_iff g p L).mpr hL⟩
  · apply iSup_le
    rintro ⟨L,hL⟩
    have hi : pointOnLine p (g⁻¹ • L) := by
      have h := (pointOnLine_smul_iff g⁻¹ (g • p) L).mpr hL
      simpa only [inv_smul_smul] using h
    have he : f.line L = (f.line (g⁻¹ • L)).map (ρ g) := by
      rw [← f.line_equivariant ρ hf g, smul_inv_smul]
    rw [he]
    exact le_iSup (fun L : {L : ZeroProductLine (ZMod 2) // pointOnLine p L} =>
      (f.line L.val).map (ρ g)) ⟨g⁻¹ • L,hi⟩

/-- The three-line pencil spans dimension three in either actual module model. -/
theorem pencilSpan_finrank (f : SingularMap W)
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) W) (hf : f.Equivariant ρ)
    (p : SingularPoints (ZMod 2)) : Module.finrank (ZMod 2) (pencilSpan f p) = 3 := by
  obtain ⟨g,hg⟩ := exists_smul_firstPoint p
  have he : (pencilSpan f p).map (actorEquiv ρ g).toLinearMap = pencilSpan f firstPoint := by
    rw [show (actorEquiv ρ g).toLinearMap = ρ g from rfl, pencilSpan_equivariant f ρ hf, hg]
  rw [← (actorEquiv ρ g).finrank_map_eq, he, base_span_range,
    LinearMap.finrank_range_of_inj (lowerLift_comp_injective f)]
  simp


variable {Q : Type*} [Group Q]

/-- The source pencil consists of actual line subgroups containing the marked point. -/
def quotientPencil (geom : QuotientGeometry Q) (P : Subgroup Q) : Set (Subgroup Q) :=
  {L | L ∈ Set.range geom.line ∧ P ≤ L}

private def quotientPencilEquiv (geom : QuotientGeometry Q) (p : SingularPoints (ZMod 2)) :
    {L : ZeroProductLine (ZMod 2) // pointOnLine p L} ≃ quotientPencil geom (geom.point p) :=
  Equiv.ofBijective (fun L => ⟨geom.line L.val, ⟨⟨L.val,rfl⟩, (geom.incidence p L.val).mp L.property⟩⟩)
    ⟨by
      intro L M h
      exact Subtype.ext (geom.line.injective (congrArg Subtype.val h)), by
      rintro ⟨_,⟨⟨L,rfl⟩,hL⟩⟩
      exact ⟨⟨L,(geom.incidence p L).mpr hL⟩,rfl⟩⟩

/-- Three actual quotient lines contain any marked singular point. -/
theorem quotientPencil_card (geom : QuotientGeometry Q) (p : SingularPoints (ZMod 2)) :
    Nat.card (quotientPencil geom (geom.point p)) = 3 := by
  rw [← Nat.card_congr (quotientPencilEquiv geom p)]
  exact pencil_card p

private def binarySubmodule (S : Subgroup (Multiplicative W)) : Submodule (ZMod 2) W where
  carrier := {w | Multiplicative.ofAdd w ∈ S}
  zero_mem' := S.one_mem
  add_mem' := S.mul_mem
  smul_mem' a w hw := by
    have hb : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    rcases hb a with rfl | rfl
    · rw [zero_smul]
      exact S.one_mem
    · simpa only [one_smul] using hw

private theorem subgroup_iSup (ι : Type*) (P : ι → Submodule (ZMod 2) W) :
    (⨆ i, P i).toAddSubgroup.toSubgroup = ⨆ i, (P i).toAddSubgroup.toSubgroup := by
  apply le_antisymm
  · change (⨆ i, P i) ≤ binarySubmodule (⨆ i, (P i).toAddSubgroup.toSubgroup)
    exact iSup_le fun i => le_iSup (fun i => (P i).toAddSubgroup.toSubgroup) i
  · exact iSup_le fun i => le_iSup P i

/-- The subgroup generated by the actual line pencil. -/
def quotientPencilSpan (geom : QuotientGeometry Q) (P : Subgroup Q) : Subgroup Q :=
  ⨆ L : quotientPencil geom P, L.val

/-- The literal quotient span agrees with the transported module span. -/
theorem quotientPencilSpan_eq (f : SingularMap W)
    (e : Multiplicative W ≃* Q) (p : SingularPoints (ZMod 2)) :
    quotientPencilSpan (transportGeometry f.geometry e)
      ((transportGeometry f.geometry e).point p) =
      (pencilSpan f p).toAddSubgroup.toSubgroup.map e.toMonoidHom := by
  rw [pencilSpan, subgroup_iSup, Subgroup.map_iSup]
  apply le_antisymm
  · apply iSup_le
    rintro ⟨_,⟨⟨L,rfl⟩,hL⟩⟩
    have hi := ((transportGeometry f.geometry e).incidence p L).mpr hL
    exact le_iSup (fun L : {L : ZeroProductLine (ZMod 2) // pointOnLine p L} =>
      ((f.line L.val).toAddSubgroup.toSubgroup).map e.toMonoidHom) ⟨L,hi⟩
  · apply iSup_le
    rintro ⟨L,hL⟩
    exact le_iSup (fun L : quotientPencil (transportGeometry f.geometry e)
      ((transportGeometry f.geometry e).point p) => L.val)
      ⟨(transportGeometry f.geometry e).line L,
        ⟨⟨L,rfl⟩,((transportGeometry f.geometry e).incidence p L).mp hL⟩⟩

/-- Rank three in multiplicative notation: the literal pencil span has order eight. -/
theorem quotientPencilSpan_card (f : SingularMap W)
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) W) (hf : f.Equivariant ρ)
    (e : Multiplicative W ≃* Q) (p : SingularPoints (ZMod 2)) :
    Nat.card (quotientPencilSpan (transportGeometry f.geometry e)
      ((transportGeometry f.geometry e).point p)) = 8 := by
  rw [quotientPencilSpan_eq, Subgroup.card_map_of_injective e.injective]
  change Nat.card (pencilSpan f p) = 8
  have : Module.Finite (ZMod 2) (pencilSpan f p) :=
    Module.finite_of_finrank_eq_succ (pencilSpan_finrank f ρ hf p)
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), pencilSpan_finrank f ρ hf p]
  simp

/-- Clause (3) for a marked subgroup in the literal natural quotient `U/V₁`.
The earlier marking must identify `V₂/V₁` with a singular point. -/
theorem natural_source_pencil (U V₁ V₂ : Subgroup Q) [(V₁.subgroupOf U).Normal]
    (e : Multiplicative (Space (ZMod 2)) ≃* U ⧸ V₁.subgroupOf U)
    (p : SingularPoints (ZMod 2))
    (hmark : (V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)) =
      (naturalQuotientGeometry (V₁.subgroupOf U) e).point p) :
    Nat.card (quotientPencil (naturalQuotientGeometry (V₁.subgroupOf U) e)
      ((V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)))) = 3 ∧
    Nat.card (quotientPencilSpan (naturalQuotientGeometry (V₁.subgroupOf U) e)
      ((V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)))) = 8 := by
  rw [hmark]
  exact ⟨quotientPencil_card _ p,
    quotientPencilSpan_card naturalMap (action (ZMod 2)) naturalMap_equivariant e p⟩

/-- The same literal quotient application for the trace-zero Weyl module. -/
theorem weyl_source_pencil (U V₁ V₂ : Subgroup Q) [(V₁.subgroupOf U).Normal]
    (e : Multiplicative (TraceZero (ZMod 2)) ≃* U ⧸ V₁.subgroupOf U)
    (p : SingularPoints (ZMod 2))
    (hmark : (V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)) =
      (weylQuotientGeometry (V₁.subgroupOf U) e).point p) :
    Nat.card (quotientPencil (weylQuotientGeometry (V₁.subgroupOf U) e)
      ((V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)))) = 3 ∧
    Nat.card (quotientPencilSpan (weylQuotientGeometry (V₁.subgroupOf U) e)
      ((V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)))) = 8 := by
  rw [hmark]
  exact ⟨quotientPencil_card _ p,
    quotientPencilSpan_card weylMap (traceZeroAction (ZMod 2)) weylMap_equivariant e p⟩
end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil

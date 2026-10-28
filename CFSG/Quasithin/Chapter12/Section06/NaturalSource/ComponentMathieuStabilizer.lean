module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentMathieuCommutator
public import Theory.Mathieu.M22.InnerCentralizer
public import Theory.Representation.BinaryConjugationSection.SolvableStabilizer
/-!
# The original nonsingular point in the Mathieu commutator

The marked V-action is an inner involution on the selected cubic Mathieu
component. The native involution centralizer calculation proves that its
V-star centralizer is solvable. F.9's exact centralizer preimage lifts this
to N_K(V), and the earlier TI input identifies K ∩ M inside that normalizer.
The genuine nonsingular-centralizer containment then makes C_K(w) solvable.

The quotient-vector stabilizer is handled by a commutator homomorphism
into the central point V₁, rather than by assuming that every coset fixer
centralizes w. The whole component commutator and its checked James-module
equivalence transport this stabilizer to the actual model. A dimension
argument constructs a nonsingular w in the original V₅, and the final
application constructs the literal U_H/V₁ action and coordinate map.

The nonsolvability of this model point stabilizer, the M₂₂ exclusion,
12.6.26 and the universal natural reduction remain open. The earlier TI
and nonsingular-centralizer inputs are explicit; the latter remains with
qt-d-12634-central. No source theorem is inferred from the conditional result.

Source: Aschbacher–Smith, proof of 12.6.26, printed p.832, using 12.2.6,
12.6.2 and H.12.1(5),(7), printed pp.393–394.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open Representation BinaryNaturalDual.VectorStabilizers
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1)
  (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
  (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
  (hm : Chapter1.Section02.LocalModels.IsM22Cover (Nonabelian.Setup.star H c.K))
include hz hTV hTz hbound hH hn a hm in
/-- The literal centralizer of V-star inside the selected Mathieu component is solvable. -/
theorem SourceHypothesis.original_mathieuCover_module_centralizer_solvable :
    Group.IsSolvable (Nonabelian.Setup.star H c.K ⊓
      centralizer (Nonabelian.Setup.star H V : Set (Nonabelian.Setup.Hstar H)) : Subgroup _) := by
  let B := Nonabelian.Setup.star H c.K
  let A := (V.subgroupOf c.localActor).map a.action
  obtain ⟨α,hα⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 (by rw [show Nat.card A = 2 from a.module_card])
  have hαo : orderOf (α : MulAut B) = 2 := (Subgroup.orderOf_coe α).trans hα
  obtain ⟨b,hb⟩ := S.original_cubicCover_module_inner D hZ z hz hTV hTz hbound hH hn c a
    (Or.inr hm) α.property
  obtain ⟨_,_,⟨e⟩⟩ := hm
  let : Group.IsSolvable (centralizer ({b} : Set B)) :=
    Sporadic.Mathieu.centralizer_isSolvable_of_inner_involution e b (hb ▸ hαo)
  let C := B ⊓ centralizer (Nonabelian.Setup.star H V : Set (Nonabelian.Setup.Hstar H))
  have hfix (x : C) : (⟨x.val,x.property.1⟩ : B) ∈ centralizer ({b} : Set B) := by
    obtain ⟨v,hv,hvα⟩ := α.property
    let qv := QuotientGroup.mk' (pCore 2 H) (inclusion a.local_le v)
    have hqv : qv ∈ Nonabelian.Setup.star H V := mem_map_of_mem _ hv
    have he := a.conjugation v (⟨x.val,x.property.1⟩ : B)
    rw [hvα,←hb] at he
    have hc : qv*x.val = x.val*qv := x.property.2 qv hqv
    change (b*(⟨x.val,x.property.1⟩ : B)*b⁻¹).val = qv*x.val*qv⁻¹ at he
    rw [hc,mul_inv_cancel_right] at he
    apply mem_centralizer_singleton_iff.mpr
    have hh : b*(⟨x.val,x.property.1⟩ : B)*b⁻¹ = ⟨x.val,x.property.1⟩ := Subtype.ext he
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  let f : C →* centralizer ({b} : Set B) := {
    toFun x := ⟨⟨x.val,x.property.1⟩,hfix x⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun v : centralizer ({b} : Set B) => v.val.val) h
  exact Group.isSolvable_of_isSolvable_injective hf

include hz hTV hTz hbound hH hn a hm in
/-- Lift through the original two-core quotient to prove solvability of N_K(V). -/
theorem SourceHypothesis.original_mathieuCover_normalizer_solvable :
    Group.IsSolvable (c.K ⊓ normalizer (V : Set G) : Subgroup G) := by
  let E := D.fullSetup hZ T z
  let q := QuotientGroup.mk' (pCore 2 H)
  let B := Nonabelian.Setup.star H c.K
  let C := B ⊓ centralizer (Nonabelian.Setup.star H V : Set (Nonabelian.Setup.Hstar H))
  let : Group.IsSolvable C := S.original_mathieuCover_module_centralizer_solvable
    D hZ z hz hTV hTz hbound hH hn c a hm
  let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable q.ker := by rw [QuotientGroup.ker_mk']; infer_instance
  let : Group.IsSolvable (C.comap q) := isSolvable_comap_of_solvable_ker q C
  have he := (S.original_nonabelian_geometry D hZ z hz hTV hTz hbound hH hn).2.2.2.2
  let P := c.K ⊓ normalizer (V : Set G)
  let f : P →* C.comap q := {
    toFun x := ⟨⟨x.val,c.le_H x.property.1⟩,by
      constructor
      · exact mem_map_of_mem _ x.property.1
      · change (⟨x.val,c.le_H x.property.1⟩ : H) ∈
          (centralizer (Nonabelian.Setup.star H V : Set (Nonabelian.Setup.Hstar H))).comap q
        rw [he]
        exact x.property.2⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun v : C.comap q => v.val.val) h
  exact Group.isSolvable_of_isSolvable_injective hf

include hz hTV hTz hbound hH hn a hm in
/-- The original K ∩ M and its literal star image are solvable, using the earlier TI input. -/
theorem SourceHypothesis.original_mathieuCover_intersection_solvable
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V) :
    Group.IsSolvable (c.K ⊓ M L : Subgroup G) ∧
      Group.IsSolvable (Nonabelian.Setup.star H (c.K ⊓ M L)) := by
  let : Group.IsSolvable (c.K ⊓ normalizer (V : Set G) : Subgroup G) :=
    S.original_mathieuCover_normalizer_solvable D hZ z hz hTV hTz hbound hH hn c a hm
  have hle : c.K ⊓ M L ≤ c.K ⊓ normalizer (V : Set G) := by
    intro x hx
    refine ⟨hx.1,Mv_le_module_normalizer_of_TI hTI z hz ⟨hx.2,?_⟩⟩
    have hh := hH.2.1 (c.le_H hx.1)
    rwa [(D.fullSetup hZ T z).Gz_eq] at hh
  let : Group.IsSolvable (c.K ⊓ M L : Subgroup G) :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hle)
  constructor
  · infer_instance
  · let e : ((c.K ⊓ M L : Subgroup G).subgroupOf H) ≃* (c.K ⊓ M L : Subgroup G) :=
      subgroupOfEquivOfLe (inf_le_left.trans c.le_H)
    let : Group.IsSolvable ((c.K ⊓ M L : Subgroup G).subgroupOf H) :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact Group.isSolvable_of_surjective
      ((QuotientGroup.mk' (pCore 2 H)).subgroupMap_surjective _)

include hz hTV hTz hbound hH hn a hm in
/-- The actual component stabilizer of a nonsingular quotient vector is solvable;
the central coordinate kernel is retained in the lift. -/
theorem SourceHypothesis.original_mathieuCover_point_stabilizer_solvable
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (Nonabelian.Setup.Hstar H) W)
    (κ : BinaryConjugationSection H ((D.fullSetup hZ T z).UH H)
      ((D.fullSetup hZ T z).V₁) (σ.comp (QuotientGroup.mk' (pCore 2 H))))
    (w : V) (hw : D.Nonsingular w) (hwU : w.val ∈ (D.fullSetup hZ T z).UH H) :
    Group.IsSolvable (representationStabilizer (σ.comp (Nonabelian.Setup.star H c.K).subtype)
      (κ.coordinates ⟨w.val,hwU⟩).toAdd) := by
  let E := D.fullSetup hZ T z
  let q := QuotientGroup.mk' (pCore 2 H)
  let B := Nonabelian.Setup.star H c.K
  let : Group.IsSolvable (c.K ⊓ M L : Subgroup G) :=
    (S.original_mathieuCover_intersection_solvable D hZ z hz hTV hTz hbound hH hn c a hm hTI).1
  let C := (centralizer ({w.val} : Set G)).subgroupOf c.K
  let f : C →* (c.K ⊓ M L : Subgroup G) := {
    toFun x := ⟨x.val.val,⟨x.val.property,hns w hw x.property⟩⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun v : (c.K ⊓ M L : Subgroup G) => v.val) h
  let : Group.IsSolvable C := Group.isSolvable_of_isSolvable_injective hf
  let : Group.IsSolvable E.V₁ := by
    change Group.IsSolvable (zpowers z.val)
    infer_instance
  let τ := (σ.comp q).comp (inclusion c.le_H)
  let v := (κ.coordinates ⟨w.val,hwU⟩).toAdd
  let : Group.IsSolvable (representationStabilizer τ v) :=
    κ.stabilizer_isSolvable_of_central_kernel hH.2.1 c.K c.le_H ⟨w.val,hwU⟩
  let j : c.K →* B := (q.comp (inclusion c.le_H)).codRestrict B
    (fun k => mem_map_of_mem q k.property)
  have hj : Function.Surjective j := by
    rintro ⟨b,u,hu,rfl⟩
    exact ⟨⟨u.val,hu⟩,rfl⟩
  let P := representationStabilizer (σ.comp B.subtype) v
  let g : representationStabilizer τ v →* P := {
    toFun x := ⟨j x.val,x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hg : Function.Surjective g := by
    intro b
    obtain ⟨k,hk⟩ := hj b.val
    refine ⟨⟨k,?_⟩,Subtype.ext hk⟩
    change σ (j k).val v = v
    rw [hk]
    exact b.property
  exact Group.isSolvable_of_surjective hg


include hz hTV hTz hbound hH hn a hm in
/-- Transport the same original nonsingular point through the whole component
commutator and its actual James-module equivalence. -/
theorem SourceHypothesis.original_mathieuCover_model_point_stabilizer
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (σ : Representation (ZMod 2) (Nonabelian.Setup.Hstar H) W)
    (hσ : Function.Injective σ)
    (κ : BinaryConjugationSection H ((D.fullSetup hZ T z).UH H)
      ((D.fullSetup hZ T z).V₁) (σ.comp (QuotientGroup.mk' (pCore 2 H))))
    (w : V) (hw : D.Nonsingular w) (hw5 : w.val ∈ (D.fullSetup hZ T z).V₅) :
    ∃ C : Subrepresentation σ,
      C.toSubmodule = Coinvariants.ker (σ.comp (Nonabelian.Setup.star H c.K).subtype) ∧
      ∃ (ec : Nonabelian.Setup.star H c.K ≃* Sporadic.Mathieu.M22TripleCover)
        (em : Equiv (C.toRepresentation.comp (Nonabelian.Setup.star H c.K).subtype)
          (Sporadic.Mathieu.M22TripleCover.representationOfEquiv ec))
        (u : C.toSubmodule),
        u.val = (κ.coordinates ⟨w.val,(le_conjugateSpanBy _ _) hw5⟩).toAdd ∧
        em u ≠ 0 ∧ Group.IsSolvable (representationStabilizer
          Sporadic.Mathieu.M22TripleCover.binaryRepresentation (em u)) := by
  classical
  let E := D.fullSetup hZ T z
  let B := Nonabelian.Setup.star H c.K
  have hwU : w.val ∈ E.UH H := (le_conjugateSpanBy _ _) hw5
  let v := (κ.coordinates ⟨w.val,hwU⟩).toAdd
  have hv0 : v ≠ 0 := by
    intro he
    have hw1 : w.val ∈ E.V₁ := (κ.coordinates_eq_one_iff ⟨w.val,hwU⟩).mp he
    have ho : orderOf z.val = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian _ z.property) (fun he => hz (Subtype.ext he))
    change w.val ∈ zpowers z.val at hw1
    rw [mem_zpowers_iff_mem_range_orderOf,ho] at hw1
    obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hw1
    have hn2 : n < 2 := Finset.mem_range.mp hn
    interval_cases n
    · exact nonsingular_ne_one D hw (Subtype.ext (by simpa using he.symm))
    · have hwz : w = z := Subtype.ext (by simpa using he.symm)
      exact S.original_point_singular D hZ z hz hTz (hwz ▸ hw)
  obtain ⟨C,hC,_,_,_,_,⟨ec,⟨em⟩⟩,t,ht,hto,_,_,hVC,_⟩ :=
    S.original_mathieuCover_commutator_of_binary_section D hZ z hz hTV hTz hbound hH hn c a hm σ hσ κ
  have hvC : v ∈ C.toSubmodule :=
    hVC ((κ.mem_imageSpace_iff E.V₅ v).mpr ⟨⟨w.val,hwU⟩,hw5,rfl⟩)
  let u : C.toSubmodule := ⟨v,hvC⟩
  have hu0 : em u ≠ 0 := by
    intro he
    exact hv0 (congrArg Subtype.val (em.toLinearEquiv.map_eq_zero_iff.mp he))
  let P := representationStabilizer (σ.comp B.subtype) v
  let : Group.IsSolvable P := S.original_mathieuCover_point_stabilizer_solvable
    D hZ z hz hTV hTz hbound hH hn c a hm hTI hns σ κ w hw hwU
  let Q := representationStabilizer Sporadic.Mathieu.M22TripleCover.binaryRepresentation (em u)
  let f : Q →* P := {
    toFun g := ⟨ec.symm g.val,by
      have he := LinearMap.congr_fun (em.isIntertwining' (ec.symm g.val)) u
      change em ((C.toRepresentation.comp B.subtype) (ec.symm g.val) u) =
        Sporadic.Mathieu.M22TripleCover.binaryRepresentation (ec (ec.symm g.val)) (em u) at he
      rw [ec.apply_symm_apply] at he
      have hh : (C.toRepresentation.comp B.subtype) (ec.symm g.val) u = u :=
        em.toLinearEquiv.injective (he.trans g.property)
      exact congrArg Subtype.val hh⟩
    map_one' := Subtype.ext (map_one ec.symm)
    map_mul' _ _ := Subtype.ext (map_mul ec.symm _ _) }
  have hf : Function.Injective f := by
    intro g k he
    apply Subtype.ext
    apply ec.symm.injective
    exact congrArg (fun x : P => x.val) he
  exact ⟨C,hC,ec,em,u,rfl,hu0,Group.isSolvable_of_isSolvable_injective hf⟩


/-- The original five-dimensional perpendicular contains a nonsingular point. -/
theorem SourceHypothesis.original_perpendicular_has_nonsingular :
    ∃ w : V, w.val ∈ (D.fullSetup hZ T z).V₅ ∧ D.Nonsingular w := by
  classical
  let f := BinaryPermutation.TerminalOrthogonal.Eight.form.polarBilin (D.fullCoordinates hZ z).toAdd
  have hex : ∃ v ∈ f.ker, BinaryPermutation.TerminalOrthogonal.Eight.form v ≠ 0 := by
    by_contra! hh
    have hd := BinaryPermutation.EightGeometry.finrank_singular_le f.ker hh
    have hr := f.finrank_range_add_finrank_ker
    have hb : Module.finrank (ZMod 2) f.range ≤ 1 := by
      simpa only [Module.finrank_self] using Submodule.finrank_le f.range
    rw [BinaryPermutation.TerminalOrthogonal.Eight.finrank_natural] at hr
    omega
  obtain ⟨v,hv,hq⟩ := hex
  let w : V := (D.fullCoordinates hZ).symm (Multiplicative.ofAdd v)
  have he : (D.fullCoordinates hZ w).toAdd = v := (D.fullCoordinates hZ).apply_symm_apply _
  refine ⟨w,?_,?_⟩
  · apply ((D.fullSetup hZ T z).mem_V₅_iff w).mpr
    change BinaryPermutation.TerminalOrthogonal.Eight.form.polarBilin (D.fullCoordinates hZ z).toAdd
      (D.fullCoordinates hZ w).toAdd = 0
    rw [he]
    exact hv
  · apply (D.fullCoordinates_nonsingular_iff hZ w).mp
    rwa [he]

include hz hTV hTz hbound hH hn a hm in
/-- Construct the literal U_H/V₁ action and a nonzero James-module point with
solvable stabilizer, preserving its original nonsingular representative. -/
theorem SourceHypothesis.original_mathieuCover_nonsingular_point
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) :
    let h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
    let _ : ((D.fullSetup hZ T z).V₁.subgroupOf ((D.fullSetup hZ T z).UH H)).Normal :=
      h.point_normal_in_UH
    let _ : IsElementaryAbelian 2 ((D.fullSetup hZ T z).UH H ⧸
        (D.fullSetup hZ T z).V₁.subgroupOf ((D.fullSetup hZ T z).UH H)) :=
      h.point_quotient_elementary
    ∃ (σ : Representation (ZMod 2) (Nonabelian.Setup.Hstar H)
        (Additive ((D.fullSetup hZ T z).UH H ⧸
          (D.fullSetup hZ T z).V₁.subgroupOf ((D.fullSetup hZ T z).UH H))))
      (κ : BinaryConjugationSection H ((D.fullSetup hZ T z).UH H)
        ((D.fullSetup hZ T z).V₁) (σ.comp (QuotientGroup.mk' (pCore 2 H)))),
      Function.Injective σ ∧
      (∀ u : (D.fullSetup hZ T z).UH H, (κ.coordinates u).toAdd =
        Additive.ofMul (QuotientGroup.mk' ((D.fullSetup hZ T z).V₁.subgroupOf
          ((D.fullSetup hZ T z).UH H)) u)) ∧
    ∃ (w : V) (hw5 : w.val ∈ (D.fullSetup hZ T z).V₅), D.Nonsingular w ∧
      ∃ C : Subrepresentation σ,
        C.toSubmodule = Coinvariants.ker (σ.comp (Nonabelian.Setup.star H c.K).subtype) ∧
        ∃ (ec : Nonabelian.Setup.star H c.K ≃* Sporadic.Mathieu.M22TripleCover)
          (em : Equiv (C.toRepresentation.comp (Nonabelian.Setup.star H c.K).subtype)
            (Sporadic.Mathieu.M22TripleCover.representationOfEquiv ec))
          (u : C.toSubmodule),
          u.val = (κ.coordinates ⟨w.val,(le_conjugateSpanBy _ _) hw5⟩).toAdd ∧
          em u ≠ 0 ∧ Group.IsSolvable (representationStabilizer
            Sporadic.Mathieu.M22TripleCover.binaryRepresentation (em u)) := by
  let h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  let := h.point_normal_in_UH
  let := h.point_quotient_elementary
  obtain ⟨σ,κ,hσ,hcoordinates⟩ := h.faithful_point_quotient
  obtain ⟨w,hw5,hw⟩ := S.original_perpendicular_has_nonsingular D hZ z
  exact ⟨σ,κ,hσ,hcoordinates,w,hw5,hw,
    S.original_mathieuCover_model_point_stabilizer D hZ z hz hTV hTz hbound hH hn c a hm
      hTI hns σ hσ κ w hw hw5⟩
end CFSG.Quasithin.Chapter12.Section06

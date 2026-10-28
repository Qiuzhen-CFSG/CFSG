module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryTwo.NativeFive
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryTwo.CommonCover
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourExtension.BinaryOrders
public import Theory.GroupAction.RankTwoCosetCover.PathTransport
/-!
# Five-path transitivity in the binary unitary graph extension

The graph extension has the same two-type coset graph as the projective
unitary-four graph after adjoining its common outer involution.  We construct
that correspondence directly on cosets: every extended coset has a unique
ordinary first-coordinate representative, because the outer factor belongs to
both marked endpoint subgroups.  Incidence, the ordinary projective action,
and nonbacktracking walks are transported literally.  The resulting
five-path transitivity uses the ordinary model calculation and the full
semidirect-product action through its `inl` subgroup.

This is a model source fact for F.4.24.  It proves a path-transitivity input,
not the later quadrangle recognition or completion-marking equivalence.
-/
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo.ExtensionFive
open Theory.GroupTheory
open Theory.SpecificGroups.ClassicalUnitary
open Subgroup.CosetGeometry
open Subgroup.CosetGeometry.RankTwo
open SimpleGraph
open SimpleGraph.BasedWalk
open SimpleGraph.PathTransitivePolygon
open CFSG.Quasithin.ChapterF.GreenBook.LieModels
local notation "h1" => (Nat.le_refl 1)
local notation "P" => GreenBook.LieModels.UnitaryFour.ProjectiveGroup 1 h1
local notation "E" => GreenBook.LieModels.UnitaryFour.Extension.ProjectiveExtension 1 h1
abbrev AP (i : Bool) : Subgroup P := if i then GreenBook.LieModels.UnitaryFour.planeParabolic 1 h1 else GreenBook.LieModels.UnitaryFour.pointParabolic 1 h1
abbrev AE (i : Bool) : Subgroup E := if i then GreenBook.LieModels.UnitaryFour.Extension.plane 1 h1 else GreenBook.LieModels.UnitaryFour.Extension.point 1 h1
local notation "inl" => (SemidirectProduct.inl : P →* E)

lemma mem_AE_inl (i : Bool) (a : P) : inl a ∈ AE i ↔ a ∈ AP i := by
  cases i
  · change inl a ∈ GreenBook.LieModels.UnitaryFour.Extension.point 1 h1 ↔ _
    rw [GreenBook.LieModels.UnitaryFour.Extension.mem_point]
    rfl
  · change inl a ∈ GreenBook.LieModels.UnitaryFour.Extension.plane 1 h1 ↔ _
    rw [GreenBook.LieModels.UnitaryFour.Extension.mem_plane]
    rfl

lemma mem_AE_inr (i : Bool) (c : UnitaryFourOuter.C2) :
    (SemidirectProduct.inr c : E) ∈ AE i := by
  cases i
  · apply (GreenBook.LieModels.UnitaryFour.Extension.mem_point 1 h1 _).mpr
    exact (GreenBook.LieModels.UnitaryFour.pointParabolic 1 h1).one_mem
  · apply (GreenBook.LieModels.UnitaryFour.Extension.mem_plane 1 h1 _).mpr
    exact (GreenBook.LieModels.UnitaryFour.planeParabolic 1 h1).one_mem

noncomputable def cosetMap (i : Bool) : P ⧸ AP i → E ⧸ AE i :=
  Quotient.map inl (by
    intro a b hab
    apply QuotientGroup.leftRel_apply.mpr
    rw [← map_inv, ← map_mul]
    exact (mem_AE_inl i (a⁻¹ * b)).mpr (QuotientGroup.leftRel_apply.mp hab))

noncomputable def vertexMap (v : Subgroup.CosetGeometry.Vertex AP) : Subgroup.CosetGeometry.Vertex AE :=
  ⟨v.type, cosetMap v.type v.coset⟩

lemma vertexMap_mk (i : Bool) (a : P) :
    vertexMap (mkVertex AP i a) = mkVertex AE i (inl a) := rfl

lemma cosetMap_injective (i : Bool) : Function.Injective (cosetMap i) := by
  intro a b hab
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  apply QuotientGroup.eq.mpr
  change (inl x : E ⧸ AE i) = inl y at hab
  have hh : (inl x : E)⁻¹ * inl y ∈ AE i := (QuotientGroup.eq.mp hab)
  rw [← map_inv, ← map_mul] at hh
  exact (mem_AE_inl i (x⁻¹ * y)).mp hh

lemma vertexMap_injective : Function.Injective vertexMap := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  have hij : i = j := congrArg Vertex.type h
  subst j
  change (⟨i, cosetMap i a⟩ : Subgroup.CosetGeometry.Vertex AE) = ⟨i, cosetMap i b⟩ at h
  have hcos : cosetMap i a = cosetMap i b := by
    injection h with hcos
  exact congrArg (fun q => (⟨i, q⟩ : Subgroup.CosetGeometry.Vertex AP))
    (cosetMap_injective i hcos)

lemma vertexMap_surjective : Function.Surjective vertexMap := by
  rintro ⟨i, q⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rcases x with ⟨xl, xr⟩
  let v : Subgroup.CosetGeometry.Vertex AP := mkVertex AP i xl
  refine ⟨v, ?_⟩
  change (⟨i, cosetMap i (xl : P ⧸ AP i)⟩ : Subgroup.CosetGeometry.Vertex AE) = ⟨i, (⟨xl, xr⟩ : E)⟩
  apply congrArg (fun q => (⟨i, q⟩ : Subgroup.CosetGeometry.Vertex AE))
  apply QuotientGroup.eq.mpr
  have hrel : (SemidirectProduct.inl xl : E)⁻¹ * (⟨xl, xr⟩ : E) =
      SemidirectProduct.inr xr := by
    calc
      (SemidirectProduct.inl xl : E)⁻¹ * (⟨xl, xr⟩ : E) =
          (SemidirectProduct.inl xl : E)⁻¹ * (inl xl * SemidirectProduct.inr xr) := by
            congr 1
            exact SemidirectProduct.mk_eq_inl_mul_inr xr xl
      _ = SemidirectProduct.inr xr :=
        inv_mul_cancel_left (SemidirectProduct.inl xl : E) (SemidirectProduct.inr xr)
  rw [hrel]
  exact mem_AE_inr i xr

noncomputable def vertexEquiv : Subgroup.CosetGeometry.Vertex AP ≃ Subgroup.CosetGeometry.Vertex AE :=
  Equiv.ofBijective vertexMap ⟨vertexMap_injective, vertexMap_surjective⟩

lemma vertexMap_smul (a : P) (v : Subgroup.CosetGeometry.Vertex AP) :
    vertexMap (a • v) = inl a • vertexMap v := by
  rcases v with ⟨i, q⟩
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
  change vertexMap (mkVertex AP i (a * b)) = inl a • vertexMap (mkVertex AP i b)
  rw [vertexMap_mk, vertexMap_mk, smul_mkVertex]
  exact congrArg (fun x => mkVertex AE i x) (map_mul inl a b)

lemma vertexMap_adj_iff (v w : Subgroup.CosetGeometry.Vertex AP) :
    (graph AP).Adj v w ↔ (graph AE).Adj (vertexMap v) (vertexMap w) := by
  rcases v with ⟨i, q⟩
  rcases w with ⟨j, r⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective r
  change (graph AP).Adj (mkVertex AP i a) (mkVertex AP j b) ↔
    (graph AE).Adj (mkVertex AE i (inl a)) (mkVertex AE j (inl b))
  simp only [incidenceGraph_adj]
  constructor
  · rintro ⟨hij, ⟨z, hz1, hz2⟩⟩
    refine ⟨hij, ⟨inl z, ?_, ?_⟩⟩
    · exact congrArg (cosetMap i) hz1
    · exact congrArg (cosetMap j) hz2
  · rintro ⟨hij, ⟨z, hz1, hz2⟩⟩
    rcases z with ⟨zl, zr⟩
    refine ⟨hij, ⟨zl, ?_, ?_⟩⟩
    · apply QuotientGroup.eq.mpr
      have hm : (⟨zl, zr⟩ : E)⁻¹ * inl a ∈ AE i := QuotientGroup.eq.mp hz1
      have hm' : (SemidirectProduct.inr zr : E) * ((⟨zl, zr⟩ : E)⁻¹ * inl a) ∈ AE i :=
        (AE i).mul_mem (mem_AE_inr i zr) hm
      have hleft : (SemidirectProduct.inr zr : E) *
          ((⟨zl, zr⟩ : E)⁻¹ * inl a) = inl (zl⁻¹ * a) := by
        rw [SemidirectProduct.mk_eq_inl_mul_inr, mul_inv_rev]
        rw [← mul_assoc, mul_inv_cancel_left, ← map_inv, ← map_mul]
      rw [hleft] at hm'
      exact (mem_AE_inl i _).mp hm'
    · apply QuotientGroup.eq.mpr
      have hm : (⟨zl, zr⟩ : E)⁻¹ * inl b ∈ AE j := QuotientGroup.eq.mp hz2
      have hm' : (SemidirectProduct.inr zr : E) * ((⟨zl, zr⟩ : E)⁻¹ * inl b) ∈ AE j :=
        (AE j).mul_mem (mem_AE_inr j zr) hm
      have hleft : (SemidirectProduct.inr zr : E) *
          ((⟨zl, zr⟩ : E)⁻¹ * inl b) = inl (zl⁻¹ * b) := by
        rw [SemidirectProduct.mk_eq_inl_mul_inr, mul_inv_rev]
        rw [← mul_assoc, mul_inv_cancel_left, ← map_inv, ← map_mul]
      rw [hleft] at hm'
      exact (mem_AE_inl j _).mp hm'

noncomputable def graphIso : graph AP ≃g graph AE where
  toFun := vertexMap
  invFun := vertexEquiv.symm
  left_inv := vertexEquiv.left_inv
  right_inv := vertexEquiv.right_inv
  map_rel_iff' := by
    intro v w
    exact (vertexMap_adj_iff v w).symm


lemma projective_five_path_transitive (i : Bool) :
    RootPathTransitive (graph AP) P (Subgroup.CosetGeometry.RankTwo.base AP i) 5 := by
  have hnative := NativeFive.five_path_transitive i
  have hc : RootPathTransitive (graph NativeFive.completion.family)
      NativeFive.MG (Subgroup.CosetGeometry.RankTwo.base NativeFive.completion.family i) 5 := by
    rw [NativeFive.completion_family]
    exact hnative
  have hm := (Completion.rootPathTransitive_iff_model NativeFive.completion i 5).mp hc
  have hfamily : SourceCompletion.UnitaryTwo.modelCompletion.family = AP := by
    funext j
    cases j
    · change (SourceCompletion.UnitaryTwo.modelCompletion.left.range) = _
      exact RankTwoAmalgam.FaithfulCompletion.ofSubgroups_left_range _ _ _ _ _ _
    · change (SourceCompletion.UnitaryTwo.modelCompletion.right.range) = _
      exact RankTwoAmalgam.FaithfulCompletion.ofSubgroups_right_range _ _ _ _ _ _
  exact hfamily ▸ hm

lemma extension_five_path_transitive (i : Bool) :
    RootPathTransitive (graph AE) E (Subgroup.CosetGeometry.RankTwo.base AE i) 5 := by
  have hp := projective_five_path_transitive i
  intro p q hpn hqn
  have hbase : graphIso (Subgroup.CosetGeometry.RankTwo.base AP i) = Subgroup.CosetGeometry.RankTwo.base AE i := by
    change vertexMap (mkVertex AP i 1) = Subgroup.CosetGeometry.RankTwo.base AE i
    rfl
  have hbase' : graphIso.symm (Subgroup.CosetGeometry.RankTwo.base AE i) = Subgroup.CosetGeometry.RankTwo.base AP i := by
    apply graphIso.injective
    rw [graphIso.apply_symm_apply, hbase]
  let p' : BasedWalk (graph AP) 5 (Subgroup.CosetGeometry.RankTwo.base AP i) :=
    BasedWalk.rebase hbase' (p.map graphIso.symm.toHom)
  let q' : BasedWalk (graph AP) 5 (Subgroup.CosetGeometry.RankTwo.base AP i) :=
    BasedWalk.rebase hbase' (q.map graphIso.symm.toHom)
  have hp' : p'.Nonbacktracking := by
    exact (BasedWalk.nonbacktracking_rebase _ _).mpr
      ((BasedWalk.nonbacktracking_map_iff graphIso.symm.toHom
        (fun x => (graphIso.symm.mapNeighborSet x).injective) p).mpr hpn)
  have hq' : q'.Nonbacktracking := by
    exact (BasedWalk.nonbacktracking_rebase _ _).mpr
      ((BasedWalk.nonbacktracking_map_iff graphIso.symm.toHom
        (fun x => (graphIso.symm.mapNeighborSet x).injective) q).mpr hqn)
  obtain ⟨a, ha, hab⟩ := hp p' q' hp' hq'
  have hroot : (inl a : E) • Subgroup.CosetGeometry.RankTwo.base AE i = Subgroup.CosetGeometry.RankTwo.base AE i := by
    change (inl a : E) • vertexMap (Subgroup.CosetGeometry.RankTwo.base AP i) =
      vertexMap (Subgroup.CosetGeometry.RankTwo.base AP i)
    rw [← vertexMap_smul, ha]
  refine ⟨inl a, hroot, ?_⟩
  have hpv : p'.vertices = p.vertices.map graphIso.symm :=
    (BasedWalk.vertices_rebase hbase' _).trans (BasedWalk.vertices_map graphIso.symm.toHom p)
  have hqv : q'.vertices = q.vertices.map graphIso.symm :=
    (BasedWalk.vertices_rebase hbase' _).trans (BasedWalk.vertices_map graphIso.symm.toHom q)
  have hl := congrArg (List.map (fun x => graphIso x)) hab
  rw [hpv, hqv] at hl
  simp only [List.map_map, Function.comp_def, graphIso.apply_symm_apply] at hl
  have hcomp (x : Subgroup.CosetGeometry.Vertex AE) :
      graphIso (a • graphIso.symm x) = (inl a : E) • x := by
    change vertexMap (a • graphIso.symm x) = (inl a : E) • x
    rw [vertexMap_smul]
    exact congrArg ((inl a : E) • ·) (graphIso.apply_symm_apply x)
  have hleft : List.map (fun x => graphIso (a • graphIso.symm x)) p.vertices =
      List.map (fun x => (inl a : E) • x) p.vertices :=
    List.map_congr_left (fun x _ => hcomp x)
  exact hleft.symm.trans hl


private theorem transport_family_eq {G : Type*} [Group G]
    {F D : Bool → Subgroup G} (h : F = D) (i : Bool) (n : ℕ)
    (ht : RootPathTransitive (graph D) G (Subgroup.CosetGeometry.RankTwo.base D i) n) :
    RootPathTransitive (graph F) G (Subgroup.CosetGeometry.RankTwo.base F i) n := by
  cases h
  exact ht

/-- The extension path calculation feeds every faithful extended completion.
The common-cover theorem then transports it from the projective model to the
completion supplied by F.4.31. -/
lemma completion_extension_five_path_transitive {G : Type*} [Group G]
    (c : SourceCompletion.UnitaryTwo.Extension.Completion G) (i : Bool) :
    RootPathTransitive c.graph G (Subgroup.CosetGeometry.RankTwo.base c.family i) 5 := by
  have hm := extension_five_path_transitive i
  have hfamily : SourceCompletion.UnitaryTwo.Extension.modelCompletion.family = AE := by
    funext j
    cases j
    · change SourceCompletion.UnitaryTwo.Extension.modelCompletion.left.range = _
      exact RankTwoAmalgam.FaithfulCompletion.ofSubgroups_left_range _ _ _ _ _ _
    · change SourceCompletion.UnitaryTwo.Extension.modelCompletion.right.range = _
      exact RankTwoAmalgam.FaithfulCompletion.ofSubgroups_right_range _ _ _ _ _ _
  have hmodel : RootPathTransitive
      SourceCompletion.UnitaryTwo.Extension.modelCompletion.graph
      E (Subgroup.CosetGeometry.RankTwo.base SourceCompletion.UnitaryTwo.Extension.modelCompletion.family i) 5 := by
    exact transport_family_eq hfamily i 5 hm
  exact (SourceCompletion.UnitaryTwo.Extension.Completion.rootPathTransitive_iff_model c i 5).mpr hmodel

end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo.ExtensionFive

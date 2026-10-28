module
public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Geometry
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore

/-!
# The short-local rank-one quotient

The action on the standard null plane is a concrete matrix homomorphism.
Positive roots act as upper transvections in the sixth coordinate and the
short Weyl element acts as the rank-one Weyl matrix, proving surjectivity
onto SL₂. An element acting trivially fixes the first vector, hence lies
in the Borel by the geometric overlap calculation. Its Borel coordinates
then show that it belongs to exactly the five-root radical.

The intrinsic two-core equality follows from its already proved ambient
image. The first isomorphism theorem and the trivial scalar center of SL₂
in characteristic two give the actual quotient equivalence with PSL₂.
No simplicity assumption excludes the binary parameter.

Source: Aschbacher--Smith, F.1.12(I)(3), printed pp. 262--264.
Root coordinates and the Borel normal form use the licensed ATLAS port
(LICENSES/ATLAS.txt; LICENSES/ATLAS-CITATION.cff).
-/

@[expose] public section
open Atlas.SplitOctonion Atlas.G2 Atlas.G2.Explicit
open scoped MatrixGroups
namespace Atlas.G2.LieParabolicSetup
variable {F : Type*} [Field F]

private theorem plane_decomposition {x : Carrier F} (hx : x ∈ shortPlane) :
    x = x 0 • basisVector 0 + x 1 • basisVector 1 := by
  rw [shortPlane_coordinates hx]
  funext i
  fin_cases i <;> simp [basisVector]

private theorem short_basis_decomposition (g : shortPlaneStabilizer (F := F)) (j : Fin 2) :
    g.val.val (basisVector (j.castLE (by decide : 2 ≤ 8))) =
      g.val.val (basisVector (j.castLE (by decide : 2 ≤ 8))) 0 • basisVector 0 +
      g.val.val (basisVector (j.castLE (by decide : 2 ≤ 8))) 1 • basisVector 1 := by
  apply plane_decomposition
  exact g.property.1 _ (basis_mem_shortPlane _ j.isLt)

/-- The action of the geometric short parabolic on its standard null plane. -/
def shortRepresentation : shortPlaneStabilizer (F := F) →* Matrix (Fin 2) (Fin 2) F where
  toFun g i j := g.val.val (basisVector (j.castLE (by decide : 2 ≤ 8)))
    (i.castLE (by decide : 2 ≤ 8))
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [basisVector]
  map_mul' g h := by
    ext i j
    change g.val.val (h.val.val (basisVector (j.castLE (by decide : 2 ≤ 8))))
      (i.castLE (by decide : 2 ≤ 8)) =
      ∑ k : Fin 2, g.val.val (basisVector (k.castLE (by decide : 2 ≤ 8)))
        (i.castLE (by decide : 2 ≤ 8)) *
        h.val.val (basisVector (j.castLE (by decide : 2 ≤ 8)))
          (k.castLE (by decide : 2 ≤ 8))
    rw [short_basis_decomposition h j, map_add, map_smul, map_smul]
    simp [Fin.sum_univ_two, basisVector, mul_comm]

/-- The determinant character of the actual plane action. -/
def shortDet : shortPlaneStabilizer (F := F) →* F :=
  Matrix.detMonoidHom.comp shortRepresentation

/-- The subgroup of the geometric parabolic acting with determinant one. -/
def shortSpecial : Subgroup (Model F) := shortDet.ker.map shortPlaneStabilizer.subtype

private theorem mem_shortSpecial {g : Model F} (hg : g ∈ shortPlaneStabilizer) :
    g ∈ shortSpecial ↔ (shortRepresentation ⟨g,hg⟩).det = 1 := by
  constructor
  · rintro ⟨h, hh, he⟩
    have he' : h = ⟨g,hg⟩ := Subtype.ext he
    subst h
    exact hh
  · intro h
    exact ⟨⟨g,hg⟩,h,rfl⟩

private theorem shortRepresentation_unipotent (t : Fin 6 → F) :
    shortRepresentation ⟨unipotentProduct t,
      unipotent_le_shortPlaneStabilizer (unipotentProduct_mem t)⟩ = !![1,-t 5;0,1] := by
  ext i j
  change (unipotentProduct t).val (basisVector (j.castLE (by decide : 2 ≤ 8)))
    (i.castLE (by decide : 2 ≤ 8)) = _
  fin_cases i <;> fin_cases j <;>
    simp [basisVector,unipotentProduct,rootA,rootB,rootC,rootD,rootE,rootF,
      rootAEquiv,rootBEquiv,rootCEquiv,rootDEquiv,rootEEquiv,rootFEquiv,
      rootALinear,rootBLinear,rootCLinear,rootDLinear,rootELinear,rootFLinear,
      rootAApply,rootBApply,rootCApply,rootDApply,rootEApply,rootFApply]

variable [CharP F 2]

private theorem local₁_le_shortSpecial : local₁ (F := F) ≤ shortSpecial := by
  apply sup_le
  · intro g hg
    rw [unipotent_eq_range] at hg
    obtain ⟨t,rfl⟩ := hg
    apply (mem_shortSpecial (unipotent_le_shortPlaneStabilizer (unipotentProduct_mem t))).mpr
    rw [shortRepresentation_unipotent]
    simp
  · apply (Subgroup.closure_le _).mpr
    rintro g (rfl : g = weylS)
    apply (mem_shortSpecial weylS_mem_shortPlaneStabilizer).mpr
    rw [Matrix.det_fin_two]
    change weylS.val (basisVector 0) 0 * weylS.val (basisVector 1) 1 -
      weylS.val (basisVector 1) 0 * weylS.val (basisVector 0) 1 = (1 : F)
    simp [basisVector,weylS,weylSEquiv,weylSLinear,weylSApply,CharTwo.neg_eq]

omit [CharP F 2] in
private theorem local₁_le_shortPlane : local₁ (F := F) ≤ shortPlaneStabilizer :=
  sup_le unipotent_le_shortPlaneStabilizer
    ((Subgroup.closure_le _).mpr (by simpa using weylS_mem_shortPlaneStabilizer (F := F)))

/-- The concrete short-local quotient map, read from the first two coordinates. -/
def shortSLHom : local₁ (F := F) →* SL(2,F) where
  toFun g := ⟨shortRepresentation ⟨g.val,by exact local₁_le_shortPlane g.property⟩,
    by exact (mem_shortSpecial _).mp (local₁_le_shortSpecial g.property)⟩
  map_one' := Subtype.ext shortRepresentation.map_one
  map_mul' g h := by
    apply Subtype.ext
    exact shortRepresentation.map_mul
      ⟨g.val,local₁_le_shortPlane g.property⟩ ⟨h.val,local₁_le_shortPlane h.property⟩

/-- Each positive-root product maps to the upper transvection in its sixth coordinate. -/
@[simp] theorem shortSLHom_unipotent (t : Fin 6 → F) :
    shortSLHom ⟨unipotentProduct t,unipotent_le_local₁ (unipotentProduct_mem t)⟩ = upperSL (t 5) := by
  apply Subtype.ext
  change shortRepresentation ⟨unipotentProduct t, _⟩ = (upperSL (t 5)).val
  rw [shortRepresentation_unipotent]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperSL,Matrix.SpecialLinearGroup.transvection_coe,CharTwo.neg_eq]

@[simp] theorem shortSLHom_rootF (a : F) :
    shortSLHom ⟨rootF a,unipotent_le_local₁ (Subgroup.subset_closure (by simp))⟩ = upperSL a := by
  simpa [unipotentProduct] using shortSLHom_unipotent (F := F) ![0,0,0,0,0,a]

@[simp] theorem shortSLHom_weylS :
    shortSLHom ⟨weylS,Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))⟩ = rankOneJ (F := F) := by
  apply Subtype.ext
  ext i j
  change (weylS : Model F).val (basisVector (j.castLE (by decide : 2 ≤ 8)))
    (i.castLE (by decide : 2 ≤ 8)) = _
  fin_cases i <;> fin_cases j <;>
    simp [rankOneJ,basisVector,weylS,weylSEquiv,
      weylSLinear,weylSApply,CharTwo.neg_eq]

theorem shortSLHom_surjective : Function.Surjective (shortSLHom (F := F)) := by
  intro M
  have hu (a : F) : upperSL a ∈ (shortSLHom (F := F)).range :=
    ⟨⟨rootF a,unipotent_le_local₁ (Subgroup.subset_closure (by simp))⟩,shortSLHom_rootF a⟩
  have hj : rankOneJ (F := F) ∈ shortSLHom.range :=
    ⟨⟨weylS,Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))⟩,shortSLHom_weylS⟩
  apply Matrix.SL2.transvection_induction (fun M => M ∈ (shortSLHom (F := F)).range) ?_ ?_ M
  · intro i j hij a
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hu a
    · change lowerSL a ∈ shortSLHom.range
      rw [lowerSL_conjugate]
      exact shortSLHom.range.mul_mem (shortSLHom.range.mul_mem hj (hu _))
        (shortSLHom.range.inv_mem hj)
    · exact (hij rfl).elim
  · exact fun _ _ => shortSLHom.range.mul_mem

omit [CharP F 2] in
private theorem shortRepresentation_torus (l m : Fˣ) :
    shortRepresentation ⟨torus l m,torus_le_shortPlaneStabilizer ⟨(l,m),rfl⟩⟩ =
      !![(l : F),0;0,(m : F)] := by
  ext i j
  change (torus l m).val (basisVector (j.castLE (by decide : 2 ≤ 8)))
    (i.castLE (by decide : 2 ≤ 8)) = _
  fin_cases i <;> fin_cases j <;>
    simp [torus,torusEquiv,torusLinear,torusWeights,basisVector]

omit [CharP F 2] in
private theorem radical_of_trivial_plane (g : shortPlaneStabilizer (F := F))
    (hg : shortRepresentation g = 1) : g.val ∈ radical₁ := by
  have hf : g.val.val (basisVector 0) = basisVector 0 := by
    have he := short_basis_decomposition g 0
    have h0 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) hg
    have h1 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 0) hg
    change g.val.val (basisVector 0) 0 = 1 at h0
    change g.val.val (basisVector 0) 1 = 0 at h1
    change g.val.val (basisVector 0) =
      g.val.val (basisVector 0) 0 • basisVector 0 + g.val.val (basisVector 0) 1 • basisVector 1 at he
    simpa only [h0,h1,one_smul,zero_smul,add_zero] using he
  have hp : g.val ∈ parabolic₂ := fixingFirstVector_le_parabolic hf
  have hb : g.val ∈ borel := shortPlaneStabilizer_inf_parabolic₂.le ⟨g.property,hp⟩
  obtain ⟨⟨⟨u,hu⟩,⟨v,hv⟩⟩,he⟩ := (borelProductEquiv (K := F)).surjective ⟨g.val,hb⟩
  have he' : u*v = g.val := congrArg Subtype.val he
  rw [unipotent_eq_range] at hu
  obtain ⟨t,rfl⟩ := hu
  obtain ⟨⟨l,m⟩,rfl⟩ := hv
  change unipotentProduct t * torus l m = g.val at he'
  have hh : (⟨unipotentProduct t,unipotent_le_shortPlaneStabilizer (unipotentProduct_mem t)⟩ :
      shortPlaneStabilizer (F := F)) *
      ⟨torus l m,torus_le_shortPlaneStabilizer ⟨(l,m),rfl⟩⟩ = g := Subtype.ext he'
  rw [← hh,map_mul,shortRepresentation_unipotent,shortRepresentation_torus] at hg
  have h0 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) hg
  have h1 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 1) hg
  have h5 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) hg
  have hl : l = 1 := Units.ext (by simpa [Matrix.mul_apply,Fin.sum_univ_two] using h0)
  have hm : m = 1 := Units.ext (by simpa [Matrix.mul_apply,Fin.sum_univ_two] using h1)
  have ht : t 5 = 0 := by simpa [Matrix.mul_apply,Fin.sum_univ_two,hm] using h5
  rw [hl,hm] at he'
  simp only [show torus (1 : Fˣ) 1 = 1 from (torusHom (K := F)).map_one,mul_one] at he'
  exact ⟨t,ht,he'⟩

/-- The kernel is precisely the five-root radical, with normality inside the local group. -/
theorem shortSLHom_ker : (shortSLHom (F := F)).ker = radical₁.subgroupOf local₁ := by
  ext g
  change shortSLHom g = 1 ↔ g.val ∈ radical₁
  constructor
  · intro h
    exact radical_of_trivial_plane ⟨g.val,local₁_le_shortPlane g.property⟩
      (congrArg Subtype.val h)
  · rintro ⟨t,ht,he⟩
    have hg : g = ⟨unipotentProduct t,unipotent_le_local₁ (unipotentProduct_mem t)⟩ :=
      Subtype.ext he.symm
    rw [hg,shortSLHom_unipotent,ht]
    apply Subtype.ext
    simp [upperSL]

/-- The first local group is the determinant-one subgroup of the geometric parabolic. -/
theorem local₁_eq_shortSpecial : local₁ (F := F) = shortSpecial := by
  apply le_antisymm local₁_le_shortSpecial
  rintro g ⟨p,hp,rfl⟩
  let M : SL(2,F) := ⟨shortRepresentation p,hp⟩
  obtain ⟨h,hh⟩ := shortSLHom_surjective M
  let h' : shortPlaneStabilizer (F := F) := ⟨h.val,local₁_le_shortPlane h.property⟩
  have he : shortRepresentation h' = shortRepresentation p := congrArg Subtype.val hh
  have hz : shortRepresentation (p*h'⁻¹) = 1 := by
    rw [map_mul,← he,← map_mul,mul_inv_cancel,map_one]
  have hr := radical_of_trivial_plane (p*h'⁻¹) hz
  have ht := local₁.mul_mem (radical₁_le_local₁ hr) h.property
  change p.val * h.val⁻¹ * h.val ∈ local₁ at ht
  change p.val ∈ local₁
  simpa only [inv_mul_cancel_right] using ht

/-- The intrinsic core equality, rather than only its ambient image. -/
theorem local₁_intrinsic_pCore [Finite F] :
    pCore 2 (local₁ (F := F)) = radical₁.subgroupOf local₁ := by
  apply Subgroup.map_injective (local₁ (F := F)).subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le radical₁_le_local₁]
  exact local₁_pCore

noncomputable def local₁CoreEquivRadical [Finite F] :
    pCore 2 (local₁ (F := F)) ≃* radical₁ (F := F) :=
  (MulEquiv.subgroupCongr local₁_intrinsic_pCore).trans
    (Subgroup.subgroupOfEquivOfLe radical₁_le_local₁)

theorem card_local₁_pCore [Finite F] :
    Nat.card (pCore 2 (local₁ (F := F))) = Nat.card F ^ 5 := by
  rw [Nat.card_congr local₁CoreEquivRadical.toEquiv,card_radical₁]

noncomputable def local₁RadicalQuotientEquivSL :
    local₁ (F := F) ⧸ radical₁.subgroupOf local₁ ≃* SL(2,F) :=
  (QuotientGroup.quotientMulEquivOfEq shortSLHom_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective shortSLHom shortSLHom_surjective)

/-- The actual local quotient by its two-core, valid also in the full binary group. -/
noncomputable def local₁CoreQuotientEquivPSL [Finite F] :
    local₁ (F := F) ⧸ pCore 2 (local₁ (F := F)) ≃* PSL(2,F) :=
  (QuotientGroup.quotientMulEquivOfEq local₁_intrinsic_pCore).trans
    (local₁RadicalQuotientEquivSL.trans RankOneFieldAutomorphisms.slEquivPSL)

@[simp] theorem local₁CoreQuotientEquivPSL_mk [Finite F] (g : local₁ (F := F)) :
    local₁CoreQuotientEquivPSL (QuotientGroup.mk g) = QuotientGroup.mk (shortSLHom g) := rfl

end Atlas.G2.LieParabolicSetup

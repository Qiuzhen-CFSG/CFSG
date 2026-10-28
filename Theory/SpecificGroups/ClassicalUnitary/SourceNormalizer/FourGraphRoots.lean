module
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourGraphCenter
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourLongMark

/-!
# The long-root line in the graph-fixed characteristic plane

In the original unitary matrix coordinates, the fixed Sylow central plane
has Hermitian parameters [[s,t],[t,0]]. Its intersection with the center
of the original point residual is exactly t=0. The reverse inclusion is
checked against the full vector stabilizer; the forward inclusion uses
one opposite root in that stabilizer. Thus this intersection is the
q-element long-root group, with every parameter retained.

Source: Aschbacher–Smith F.4.37(4), printed p.293 (`refs/quasithin.pdf`).
-/

@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourGraph
open SymplecticFour SymplecticFour.CentralRootGeometry UnitaryFourFlag
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "K" => FixedBy.subfield F σ
local notation "U" => SU F (form F σ hσ)
local notation "L" => UnitaryFourPointLocal.localSU F (form F σ hσ)

omit [Finite F] in
theorem embedded_theta_matrix (s t : K) :
    (embedding F σ hσ (theta s t).val).val.val =
      !![1,0,(t:F),(s:F); 0,1,0,(t:F); 0,0,1,0; 0,0,0,1] := by
  ext i j
  rw [embedding_apply]
  change ((element 0 s t 0).val.val (coordinates i) (coordinates j) : F) = _
  rw [element_matrix]
  fin_cases i <;> fin_cases j <;> simp [coordinates,Matrix.fromBlocks]

private def oppositeRoot : U := embedding F σ hσ (rootElement 3 (1 : K))

omit [Finite F] in
private theorem oppositeRoot_matrix : (oppositeRoot F σ hσ).val.val =
    !![1,0,0,0; 0,1,0,0; 0,1,1,0; 0,0,0,1] := by
  ext i j
  change (embedding F σ hσ (rootElement 3 (1:K))).val.val i j = _
  rw [embedding_apply]
  fin_cases i <;> fin_cases j <;>
    simp [rootElement,rootMatrix,coordinates,Matrix.fromBlocks,Matrix.single]

omit [Finite F] in
private theorem oppositeRoot_mem : oppositeRoot F σ hσ ∈ L := by
  rw [UnitaryFourPointLocal.mem_localSU]
  simp [oppositeRoot_matrix]

omit [Finite F] in
/-- The full original point residual cuts out exactly the diagonal root
line in the fixed characteristic plane. -/
theorem embedded_theta_mem_point_center_iff (s t : K) :
    embedding F σ hσ (theta s t).val ∈ (center L).map (L).subtype ↔ t=0 := by
  constructor
  · rintro ⟨z,hz,he⟩
    have hcomm := mem_center_iff.mp hz ⟨oppositeRoot F σ hσ,oppositeRoot_mem F σ hσ⟩
    have hh' := congrArg (L).subtype hcomm
    change oppositeRoot F σ hσ * z.val = z.val * oppositeRoot F σ hσ at hh'
    change z.val = embedding F σ hσ (theta s t).val at he
    rw [he] at hh'
    have hh := congrArg (fun a : U => a.val.val 0 1) hh'
    change ((oppositeRoot F σ hσ).val.val * (embedding F σ hσ (theta s t).val).val.val) 0 1 =
      ((embedding F σ hσ (theta s t).val).val.val * (oppositeRoot F σ hσ).val.val) 0 1 at hh
    rw [embedded_theta_matrix,oppositeRoot_matrix] at hh
    have ht : (t:F)=0 := by
      simpa [Matrix.mul_apply,Fin.sum_univ_succ] using hh.symm
    exact Subtype.ext ht
  · rintro rfl
    have hz : embedding F σ hσ (theta s 0).val ∈ L := by
      rw [UnitaryFourPointLocal.mem_localSU]
      simp [embedded_theta_matrix]
    refine ⟨⟨_,hz⟩,mem_center_iff.mpr ?_,rfl⟩
    intro g
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    have hg := (UnitaryFourPointLocal.mem_localSU F _ g.val).mp g.property
    have hl := UnitaryFourPointLocal.last_row F σ hσ g.val g.property
    change g.val.val.val * (embedding F σ hσ (theta s 0).val).val.val =
      (embedding F σ hσ (theta s 0).val).val.val * g.val.val.val
    rw [embedded_theta_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_succ,hg.1,hg.2.1,hg.2.2.1,hg.2.2.2,
        hl.2.1,hl.2.2.1,hl.2.2.2,add_comm]

/-- The whole characteristic root plane, embedded in the original SU₄. -/
def rootPlaneHom : (Multiplicative K × Multiplicative K) →* U :=
  (embedding F σ hσ).comp CentralRootGeometry.parameter

/-- The long-root line in that same plane, with all fixed-field parameters. -/
def longRootHom : Multiplicative K →* U :=
  (rootPlaneHom F σ hσ).comp (MonoidHom.inl _ _)

omit [Finite F] in
theorem rootPlaneHom_apply (s t : K) :
    rootPlaneHom F σ hσ (Multiplicative.ofAdd s,Multiplicative.ofAdd t) =
      embedding F σ hσ (theta s t).val := rfl

omit [Finite F] in
theorem longRootHom_injective : Function.Injective (longRootHom F σ hσ) :=
  (embedding_injective F σ hσ).comp
    (CentralRootGeometry.parameter_injective.comp (fun _ _ he => congrArg Prod.fst he))

omit [Finite F] in
/-- Exact native long-root intersection needed in F.4.37, with no collapse
of the central graph factor or projective quotient. -/
theorem rootPlane_inf_point_center :
    (rootPlaneHom F σ hσ).range ⊓ (center L).map (L).subtype =
      (longRootHom F σ hσ).range := by
  ext x
  constructor
  · rintro ⟨⟨⟨s,t⟩,rfl⟩,hx⟩
    have ht : t.toAdd=0 := (embedded_theta_mem_point_center_iff F σ hσ s.toAdd t.toAdd).mp hx
    refine ⟨s,?_⟩
    change embedding F σ hσ (theta s.toAdd 0).val =
      embedding F σ hσ (theta s.toAdd t.toAdd).val
    rw [ht]
  · rintro ⟨s,rfl⟩
    exact ⟨⟨(s,1),rfl⟩,(embedded_theta_mem_point_center_iff F σ hσ s.toAdd 0).mpr rfl⟩

omit [Finite F] in
theorem rootPlane_inf_point_center_card :
    Nat.card ((rootPlaneHom F σ hσ).range ⊓ (center L).map (L).subtype : Subgroup U) =
      Nat.card K := by
  rw [rootPlane_inf_point_center,
    ←Nat.card_congr (MonoidHom.ofInjective (longRootHom_injective F σ hσ)).toEquiv]
  exact Nat.card_congr (Multiplicative.toAdd : Multiplicative K ≃ K)

/-- The root plane is exactly the first-factor image of the characteristic
center–derived subgroup of the full fixed Sylow U×C₂. -/
theorem rootPlane_eq_fixed_derived_image {m : ℕ}
    (hK : Nat.card K=2^m) (hm : 1<m) :
    (center ((unipotent (F := K)) × UnitaryFourOuter.C2) ⊓
      _root_.commutator ((unipotent (F := K)) × UnitaryFourOuter.C2)).map
      ((embedding F σ hσ).comp ((unipotent (F := K)).subtype.comp
        (MonoidHom.fst _ _))) = (rootPlaneHom F σ hσ).range := by
  rw [fixed_product_center_derived hK hm]
  ext x
  constructor
  · rintro ⟨⟨u,c⟩,⟨hu,_⟩,rfl⟩
    rw [←theta_range] at hu
    obtain ⟨a,rfl⟩ := hu
    exact ⟨a,rfl⟩
  · rintro ⟨a,rfl⟩
    exact ⟨(thetaHom a,1),⟨theta_mem_center _ _,mem_bot.mpr rfl⟩,rfl⟩

end Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourGraph

module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ModuleApplications.CriticalActorBounds
public import Theory.Representation.RankOne.QuadraticRecognition.UnitaryMovingTorus
public import Theory.Representation.RankOne.QuadraticRecognition.UnitaryElementBounds

/-!
# The moving torus on the original critical module

The original action and marking L/O₂(L) give the literal quotient
Z/(Z∩Z(L)), the image of B and the original elements t and l. In the
contrary small-index case of DGS (5.10)(b), the torus element l is fixed-free
on the central quotient of the fixed-generated SL₂ block. Both denominator
subspaces are retained, and actor quadraticity and fixed-space generation
are descended through the original vector projection in the proof.

This supplies the moving-torus reduction for the critical modules used in
DGS Chapter 8, (8.2), (8.3), (8.6) and (8.7). The graph owners still supply
the original module, faithful marking, actor placement and Sylow generation.
The further numerical contradiction remains part of (5.10)(b) assembly.

Source: DGS85, Groups and Graphs, pp.111–112 and 130–143.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open BenderSuzuki.MatrixGroups BenderSuzuki.External
open HermitianForm.BorelTorus.EvenCenterAction HermitianForm.EvenInner
open Representation.SU3.CubicDegree.InnerActors.ThreeRoots
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.DGS85.ModuleApplications
variable {L F : Type*} [Group L] [Finite L] [Field F] [Finite F] [CharP F 2]

/-- DGS (5.10)(b) on the original critical quotient. The map of `t` is the
specified nonidentity element of the original image actor. -/
theorem critical_su3_root_element_field_index
    (J : HermitianForm 3 F) (hJ : J.form=!![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 2≤n) (hcard : Nat.card F=(2^n)^2)
    (hconj : ∀ x, J.conj x=x^(2^n))
    (Z : Subgroup L) [IsElementaryAbelian 2 Z]
    (e : (L ⧸ pCore 2 L) ≃* J.specialSubgroup)
    (ρ : Representation (ZMod 2) J.specialSubgroup (Additive Z))
    (hact : ∀ (l : L) (v : Additive Z),
      ((ρ (e (QuotientGroup.mk' (pCore 2 L) l)) v).toMul : L)=l*(v.toMul:L)*l⁻¹)
    (hf : Function.Injective (globalFixedQuotient ρ))
    (B : Subgroup L)
    (hB : B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))≤central J hJ)
    (hBc : 4≤Nat.card (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (hquad : IsQuadratic ρ (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (t : L) (ht : t∈B) (ht1 : e (QuotientGroup.mk' (pCore 2 L) t)≠1) :
    centralPart Z=fixedSpace ρ ⊤ ∧
      2^(2*n)≤Nat.card ((Additive Z ⧸ fixedSpace ρ ⊤) ⧸
        fixedSpace (globalFixedQuotient ρ)
          (zpowers (e (QuotientGroup.mk' (pCore 2 L) t)))) := by
  let : Finite (Additive Z ⧸ (globalFixedSubrepresentation ρ).toSubmodule) :=
    Finite.of_surjective _ (globalFixedSubrepresentation ρ).toSubmodule.mkQ_surjective
  let φ := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let A := B.map φ
  let σ := globalFixedQuotient ρ
  have hq : IsQuadratic σ A :=
    quadratic_of_equivariant_surjection ρ σ (fixedSpace ρ ⊤).mkQ
      (fixedSpace ρ ⊤).mkQ_surjective (fun g v => (globalFixedQuotient_mk ρ g v).symm) A hquad
  exact ⟨centralPart_eq_fixedSpace_model Z e ρ hact,
    su3_root_element_field_index J hJ hn hcard hconj σ hf A hB hBc hq
      (φ t) ⟨t,ht,rfl⟩ ht1⟩

/-- The projective-unitary form of DGS (5.10)(b), retaining the original
actor and element images through `L/O₂(L)`. -/
theorem critical_psu3_root_element_field_index
    (J : HermitianForm 3 F) (hJ : J.form=!![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 2≤n) (hcard : Nat.card F=(2^n)^2)
    (hconj : ∀ x, J.conj x=x^(2^n))
    (Z : Subgroup L) [IsElementaryAbelian 2 Z]
    (e : (L ⧸ pCore 2 L) ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (ρ : Representation (ZMod 2) (ProjectiveSpecialUnitaryMatrixGroup J) (Additive Z))
    (hact : ∀ (l : L) (v : Additive Z),
      ((ρ (e (QuotientGroup.mk' (pCore 2 L) l)) v).toMul : L)=l*(v.toMul:L)*l⁻¹)
    (hf : Function.Injective (globalFixedQuotient ρ))
    (B : Subgroup L)
    (hB : B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))≤centralImage J hJ)
    (hBc : 4≤Nat.card (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (hquad : IsQuadratic ρ (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (t : L) (ht : t∈B) (ht1 : e (QuotientGroup.mk' (pCore 2 L) t)≠1) :
    centralPart Z=fixedSpace ρ ⊤ ∧
      2^(2*n)≤Nat.card ((Additive Z ⧸ fixedSpace ρ ⊤) ⧸
        fixedSpace (globalFixedQuotient ρ)
          (zpowers (e (QuotientGroup.mk' (pCore 2 L) t)))) := by
  let : Finite (Additive Z ⧸ (globalFixedSubrepresentation ρ).toSubmodule) :=
    Finite.of_surjective _ (globalFixedSubrepresentation ρ).toSubmodule.mkQ_surjective
  let φ := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let A := B.map φ
  let σ := globalFixedQuotient ρ
  have hq : IsQuadratic σ A :=
    quadratic_of_equivariant_surjection ρ σ (fixedSpace ρ ⊤).mkQ
      (fixedSpace ρ ⊤).mkQ_surjective (fun g v => (globalFixedQuotient_mk ρ g v).symm) A hquad
  exact ⟨centralPart_eq_fixedSpace_model Z e ρ hact,
    psu3_root_element_field_index J hJ hn hcard hconj σ hf A hB hBc hq
      (φ t) ⟨t,ht,rfl⟩ ht1⟩

/-- The special moving-torus reduction retains both central denominators
and the original actor and torus-element images. -/
theorem critical_su3_small_element_full_torus_fixed_free
    (J : HermitianForm 3 F) (hJ : J.form=!![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 2≤n) (hcard : Nat.card F=(2^n)^2)
    (hconj : ∀ x, J.conj x=x^(2^n))
    (Z : Subgroup L) [IsElementaryAbelian 2 Z]
    (e : (L ⧸ pCore 2 L) ≃* J.specialSubgroup)
    (ρ : Representation (ZMod 2) J.specialSubgroup (Additive Z))
    (hact : ∀ (l : L) (v : Additive Z),
      ((ρ (e (QuotientGroup.mk' (pCore 2 L) l)) v).toMul : L)=l*(v.toMul:L)*l⁻¹)
    (hf : Function.Injective (globalFixedQuotient ρ))
    (B : Subgroup L)
    (hB : B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))≤central J hJ)
    (hBc : 4≤Nat.card (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (S : Sylow 2 J.specialSubgroup)
    (hBS : B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))≤S)
    (hgen : GeneratedByFixedSpace ρ S)
    (hquad : IsQuadratic ρ (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (t : L) (ht : t∈B) (ht1 : e (QuotientGroup.mk' (pCore 2 L) t)≠1)
    (hsmall : fixedCodim (globalFixedQuotient ρ)
      (zpowers (e (QuotientGroup.mk' (pCore 2 L) t)))<2*n)
    (k : normOne J) (l : L)
    (hl : e (QuotientGroup.mk' (pCore 2 L) l)=hermitianTorusSU J hJ k.val)
    (hk : e (QuotientGroup.mk' (pCore 2 L) l)≠1) :
    centralPart Z=fixedSpace ρ ⊤ ∧
      let σ := globalFixedQuotient ρ
      let A := B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))
      let j := block J hJ
      let W := fixedGeneratedSubrepresentation (σ.comp j) (A.comap j)
      GeneratedByFixedSpace σ A ∧ IsQuadratic σ A ∧
      ∀ v∈W.toSubmodule,
        σ (e (QuotientGroup.mk' (pCore 2 L) l)) v-v∈fixedSpace (σ.comp j) ⊤ →
        v∈fixedSpace (σ.comp j) ⊤ := by
  let : Finite (Additive Z ⧸ (globalFixedSubrepresentation ρ).toSubmodule) :=
    Finite.of_surjective _ (globalFixedSubrepresentation ρ).toSubmodule.mkQ_surjective
  let φ := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let A := B.map φ
  let σ := globalFixedQuotient ρ
  have hgenA : GeneratedByFixedSpace ρ A := by
    apply top_unique
    rw [←show (⨆ g, (fixedSpace ρ S).map (ρ g))=⊤ from hgen]
    apply iSup_mono
    intro g
    exact Submodule.map_mono (ρ.invariants_comp_subtype_antitone hBS)
  have hgenQ := globalFixedQuotient_generated Z ρ A hgenA
  have hq : IsQuadratic σ A :=
    quadratic_of_equivariant_surjection ρ σ (fixedSpace ρ ⊤).mkQ
      (fixedSpace ρ ⊤).mkQ_surjective (fun g v => (globalFixedQuotient_mk ρ g v).symm) A hquad
  refine ⟨centralPart_eq_fixedSpace_model Z e ρ hact,hgenQ,hq,?_⟩
  rw [hl]
  exact su3_small_element_full_torus_fixed_free J hJ hn hcard hconj σ hf A hB hBc hq hgenQ
    (φ t) ⟨t,ht,rfl⟩ ht1 hsmall k (hl ▸ hk)

/-- The projective moving-torus reduction retains both central denominators
and the original actor and torus-element images. -/
theorem critical_psu3_small_element_torus_fixed_free
    (J : HermitianForm 3 F) (hJ : J.form=!![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 2≤n) (hcard : Nat.card F=(2^n)^2)
    (hconj : ∀ x, J.conj x=x^(2^n))
    (Z : Subgroup L) [IsElementaryAbelian 2 Z]
    (e : (L ⧸ pCore 2 L) ≃* (ProjectiveSpecialUnitaryMatrixGroup J))
    (ρ : Representation (ZMod 2) (ProjectiveSpecialUnitaryMatrixGroup J) (Additive Z))
    (hact : ∀ (l : L) (v : Additive Z),
      ((ρ (e (QuotientGroup.mk' (pCore 2 L) l)) v).toMul : L)=l*(v.toMul:L)*l⁻¹)
    (hf : Function.Injective (globalFixedQuotient ρ))
    (B : Subgroup L)
    (hB : B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))≤centralImage J hJ)
    (hBc : 4≤Nat.card (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (hBS : B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))≤S)
    (hgen : GeneratedByFixedSpace ρ S)
    (hquad : IsQuadratic ρ (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (t : L) (ht : t∈B) (ht1 : e (QuotientGroup.mk' (pCore 2 L) t)≠1)
    (hsmall : fixedCodim (globalFixedQuotient ρ)
      (zpowers (e (QuotientGroup.mk' (pCore 2 L) t)))<2*n)
    (k : normOne J) (l : L)
    (hl : e (QuotientGroup.mk' (pCore 2 L) l)=normOneMap J hJ k)
    (hk : e (QuotientGroup.mk' (pCore 2 L) l)≠1) :
    centralPart Z=fixedSpace ρ ⊤ ∧
      let σ := globalFixedQuotient ρ
      let A := B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))
      let j := J.specialToProjective.comp (block J hJ)
      let W := fixedGeneratedSubrepresentation (σ.comp j) (A.comap j)
      GeneratedByFixedSpace σ A ∧ IsQuadratic σ A ∧
      ∀ v∈W.toSubmodule,
        σ (e (QuotientGroup.mk' (pCore 2 L) l)) v-v∈fixedSpace (σ.comp j) ⊤ →
        v∈fixedSpace (σ.comp j) ⊤ := by
  let : Finite (Additive Z ⧸ (globalFixedSubrepresentation ρ).toSubmodule) :=
    Finite.of_surjective _ (globalFixedSubrepresentation ρ).toSubmodule.mkQ_surjective
  let φ := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let A := B.map φ
  let σ := globalFixedQuotient ρ
  have hgenA : GeneratedByFixedSpace ρ A := by
    apply top_unique
    rw [←show (⨆ g, (fixedSpace ρ S).map (ρ g))=⊤ from hgen]
    apply iSup_mono
    intro g
    exact Submodule.map_mono (ρ.invariants_comp_subtype_antitone hBS)
  have hgenQ := globalFixedQuotient_generated Z ρ A hgenA
  have hq : IsQuadratic σ A :=
    quadratic_of_equivariant_surjection ρ σ (fixedSpace ρ ⊤).mkQ
      (fixedSpace ρ ⊤).mkQ_surjective (fun g v => (globalFixedQuotient_mk ρ g v).symm) A hquad
  refine ⟨centralPart_eq_fixedSpace_model Z e ρ hact,hgenQ,hq,?_⟩
  rw [hl]
  exact psu3_small_element_torus_fixed_free J hJ hn hcard hconj σ
    ⟨φ t,fun he => ht1 (hf (he.trans σ.map_one.symm))⟩ A hB hBc hq hgenQ
    (φ t) ⟨t,ht,rfl⟩ ht1 hsmall k (hl ▸ hk)

end CFSG.Quasithin.DGS85.ModuleApplications

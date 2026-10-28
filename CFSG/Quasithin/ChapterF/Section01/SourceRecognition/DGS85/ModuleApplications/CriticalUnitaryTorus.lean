module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ModuleApplications.CriticalActorBounds
public import Theory.Representation.RankOne.QuadraticRecognition.UnitaryTorus

/-!
# The unitary torus estimate on the original DGS critical quotient

These applications retain the map L → L/O₂(L) → SU₃ or PSU₃, the image of
the original subgroup B, and the specified original elements t and l. The
conjugation equation identifies the vector denominator with Z ∩ Z(L), so the
module remains the literal Z/(Z∩Z(L)). Three-conjugate generation supplies
its actor field-square bound. In the first torus branch it also gives the
individual-element estimate used in DGS Chapter 8, including (8.2), (8.3),
(8.6), and (8.7).

The original Sylow fixed-space generation implies generation by the actor
fixed space and descends to this quotient. The original quadratic action and
torus displacement identity descend through the same vector projection.
The graph argument still supplies Z, the model marking, quotient
faithfulness, normalized actor placement and the actual torus case. The
moving-torus branch is not asserted here. In the special cover the
root-generation step retains the necessary nontrivial-cube condition.

Source: DGS85, Groups and Graphs, (5.4)(f) and (5.10)(b), pp.107,111–112,
and its critical-module uses in Chapter 8, pp.130–143.
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

/-- The field-square bound on the original critical quotient and actor image. -/
theorem critical_su3_root_actor_field_index
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
    : centralPart Z=fixedSpace ρ ⊤ ∧
      2^(2*n)≤Nat.card ((Additive Z ⧸ fixedSpace ρ ⊤) ⧸
        fixedSpace (globalFixedQuotient ρ)
          (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) := by
  let : Finite (Additive Z ⧸ (globalFixedSubrepresentation ρ).toSubmodule) :=
    Finite.of_surjective _ (globalFixedSubrepresentation ρ).toSubmodule.mkQ_surjective
  let A := B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))
  have hA : A≠⊥ := by
    intro he
    have hh : 4≤Nat.card A := hBc
    rw [he,card_bot] at hh
    omega
  obtain ⟨a,ha,ha1⟩ := A.bot_or_exists_ne_one.resolve_left hA
  exact ⟨centralPart_eq_fixedSpace_model Z e ρ hact,
    su3_root_actor_field_index J hJ hn hcard hconj (globalFixedQuotient ρ)
      ⟨a,fun he => ha1 (hf (he.trans (globalFixedQuotient ρ).map_one.symm))⟩ A hB hBc⟩

/-- The first torus branch of DGS (5.10)(b) on Z/(Z∩Z(L)). The original
 Sylow fixed-space generation and displacement identity descend explicitly. -/
theorem critical_su3_element_index_of_torus_centralizes_displacements
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
    (k : normOne J) (l : L)
    (hl : e (QuotientGroup.mk' (pCore 2 L) l)=hermitianTorusSU J hJ k.val)
    (hk : k^3≠1)
    (hmove : ∀ a∈B, ∀ v : Additive Z,
      ρ (e (QuotientGroup.mk' (pCore 2 L) l))
          (ρ (e (QuotientGroup.mk' (pCore 2 L) a)) v-v)=
        ρ (e (QuotientGroup.mk' (pCore 2 L) a)) v-v) :
    centralPart Z=fixedSpace ρ ⊤ ∧
      let σ := globalFixedQuotient ρ
      let A := B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))
      GeneratedByFixedSpace σ A ∧
      2^(2*n)≤Nat.card ((Additive Z ⧸ fixedSpace ρ ⊤) ⧸
        fixedSpace σ (zpowers (e (QuotientGroup.mk' (pCore 2 L) t)))) := by
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
  have htor : ∀ a∈A, ∀ v, ρ (hermitianTorusSU J hJ k.val) (ρ a v-v)=ρ a v-v := by
    rintro _ ⟨a,ha,rfl⟩ v
    simpa only [φ,MonoidHom.comp_apply,MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe,hl]
      using hmove a ha v
  have htorQ : ∀ a∈A, ∀ v, σ (hermitianTorusSU J hJ k.val) (σ a v-v)=σ a v-v := by
    intro a ha v
    induction v using Submodule.Quotient.induction_on with
    | _ v =>
      exact congrArg (globalFixedSubrepresentation ρ).toSubmodule.mkQ (htor a ha v)
  refine ⟨centralPart_eq_fixedSpace_model Z e ρ hact,hgenQ,?_⟩
  exact su3_element_field_index_of_torus_centralizes_displacements J hJ hn hcard hconj σ
    ⟨φ t,fun he => ht1 (hf (he.trans σ.map_one.symm))⟩ A hB hBc hq hgenQ
    (φ t) ⟨t,ht,rfl⟩ ht1 k hk htorQ

/-- The field-square bound on the original critical quotient and actor image. -/
theorem critical_psu3_root_actor_field_index
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
    : centralPart Z=fixedSpace ρ ⊤ ∧
      2^(2*n)≤Nat.card ((Additive Z ⧸ fixedSpace ρ ⊤) ⧸
        fixedSpace (globalFixedQuotient ρ)
          (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) := by
  let : Finite (Additive Z ⧸ (globalFixedSubrepresentation ρ).toSubmodule) :=
    Finite.of_surjective _ (globalFixedSubrepresentation ρ).toSubmodule.mkQ_surjective
  let A := B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))
  have hA : A≠⊥ := by
    intro he
    have hh : 4≤Nat.card A := hBc
    rw [he,card_bot] at hh
    omega
  obtain ⟨a,ha,ha1⟩ := A.bot_or_exists_ne_one.resolve_left hA
  exact ⟨centralPart_eq_fixedSpace_model Z e ρ hact,
    psu3_root_actor_field_index J hJ hn hcard hconj (globalFixedQuotient ρ)
      ⟨a,fun he => ha1 (hf (he.trans (globalFixedQuotient ρ).map_one.symm))⟩ A hB hBc⟩

/-- The first torus branch of DGS (5.10)(b) on Z/(Z∩Z(L)). The original
 Sylow fixed-space generation and displacement identity descend explicitly. -/
theorem critical_psu3_element_index_of_torus_centralizes_displacements
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
    (k : normOne J) (l : L)
    (hl : e (QuotientGroup.mk' (pCore 2 L) l)=normOneMap J hJ k)
    (hk : e (QuotientGroup.mk' (pCore 2 L) l)≠1)
    (hmove : ∀ a∈B, ∀ v : Additive Z,
      ρ (e (QuotientGroup.mk' (pCore 2 L) l))
          (ρ (e (QuotientGroup.mk' (pCore 2 L) a)) v-v)=
        ρ (e (QuotientGroup.mk' (pCore 2 L) a)) v-v) :
    centralPart Z=fixedSpace ρ ⊤ ∧
      let σ := globalFixedQuotient ρ
      let A := B.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))
      GeneratedByFixedSpace σ A ∧
      2^(2*n)≤Nat.card ((Additive Z ⧸ fixedSpace ρ ⊤) ⧸
        fixedSpace σ (zpowers (e (QuotientGroup.mk' (pCore 2 L) t)))) := by
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
  have htor : ∀ a∈A, ∀ v, ρ (normOneMap J hJ k) (ρ a v-v)=ρ a v-v := by
    rintro _ ⟨a,ha,rfl⟩ v
    simpa only [φ,MonoidHom.comp_apply,MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe,hl]
      using hmove a ha v
  have htorQ : ∀ a∈A, ∀ v, σ (normOneMap J hJ k) (σ a v-v)=σ a v-v := by
    intro a ha v
    induction v using Submodule.Quotient.induction_on with
    | _ v =>
      exact congrArg (globalFixedSubrepresentation ρ).toSubmodule.mkQ (htor a ha v)
  refine ⟨centralPart_eq_fixedSpace_model Z e ρ hact,hgenQ,?_⟩
  exact psu3_element_field_index_of_torus_centralizes_displacements J hJ hn hcard hconj σ
    ⟨φ t,fun he => ht1 (hf (he.trans σ.map_one.symm))⟩ A hB hBc hq hgenQ
    (φ t) ⟨t,ht,rfl⟩ ht1 k (by rwa [←hl]) htorQ

end CFSG.Quasithin.DGS85.ModuleApplications

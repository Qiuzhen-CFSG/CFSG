module
public import Theory.Representation.HermitianTensorThree.PointSection.ParabolicMovement
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourPointTransvections

/-!
# The chosen module lies in the full point-residual core

The original centralizer residual maps onto the complete point parabolic.
Its full movement on the Hermitian nine-space therefore gives [V,L_z]=V.
Since the abelian V normalizes C_L(z) and its characteristic residual, this
commutator lies in L_z. Normality and the two-group property then place V
inside the whole O₂(L_z), without assuming that containment in advance.

Source: Aschbacher–Smith 8.2.11(2–4), printed p.722, refs/quasithin.pdf.
The Chapter 12 extension applies this to the literal chosen orbit and its
actual residual map, retaining all covering kernels. The natural and A₅
quotient actions and the subsequent ambient contradiction remain separate.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE
set_option backward.isDefEq.respectTransparency false
variable {G : Type*} [Group G] [Finite G]

/-- The native projective point parabolic has exactly the marked binary image. -/
theorem native_point_parabolic_image :
    (Matrix.PSL3.RootPlaneGeometry.parabolic Matrix.PSL3Four.F true).map
      ((binaryImage 1).subtype.comp nativeBinaryEquiv.toMonoidHom) =
        ParabolicTorus.pointParabolicImage 1 := by
  apply le_antisymm
  · rintro _ ⟨a,ha,rfl⟩
    obtain ⟨b,hb⟩ := (nativeBinaryEquiv a).property
    refine ⟨b,?_,hb⟩
    apply (Matrix.PSL3.LinearThree.mem_pointParabolicSL_iff _ _).mpr
    apply (PointSection.fixes_pointVector_iff b).mp
    rw [hb]
    exact (native_point_parabolic_iff a).mp ha
  · rintro _ ⟨b,hb,rfl⟩
    let a : binaryImage 1 := ⟨binaryActionHom 1 b,⟨b,rfl⟩⟩
    refine ⟨nativeBinaryEquiv.symm a,?_,congrArg Subtype.val (nativeBinaryEquiv.apply_symm_apply a)⟩
    apply (native_point_parabolic_iff _).mpr
    rw [nativeBinaryEquiv.apply_symm_apply]
    exact (PointSection.fixes_pointVector_iff b).mpr
      ((Matrix.PSL3.LinearThree.mem_pointParabolicSL_iff _ _).mp hb)

omit [Finite G] in
/-- Full parabolic movement transports to the literal ambient commutator. -/
theorem marked_point_parabolic_commutator
    (V R : Subgroup G) [IsElementaryAbelian 2 V]
    (hRN : R ≤ normalizer (V : Set G))
    (e : Additive V ≃ₗ[ZMod 2] Space 1)
    (q : R →* (Space 1 ≃ₗ[ZMod 2] Space 1))
    (he : ∀ x v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion hRN x)) v) = q x (e v))
    (hq : q.range = ParabolicTorus.pointParabolicImage 1) : ⁅V,R⁆ = V := by
  let f := V.normalizerMonoidHom.rangeRestrict.comp (inclusion hRN)
  let ρ := (automizerRepresentation V).comp f
  let σ := UnipotentRadicals.ambientAction 1
  have hact (x : R) (v : V) :
      ρ x (Additive.ofMul v) = Additive.ofMul
        (⟨(x : G)*(v : G)*(x : G)⁻¹,le_normalizer_iff.mp hRN x x.property v v.property⟩ : V) := rfl
  have hcomm := commutator_image_eq ρ V V R hRN le_rfl (MonoidHom.id R)
    (MonoidHom.id V) (fun x v => hact x v) ⊤ (by ext v; simp [binarySubgroup])
  have hC : (⁅V,R⁆).subgroupOf V = binarySubgroup (subspaceCommutator ρ ⊤ (⊤ : Subgroup R)) := by
    simpa only [map_id,(MonoidHom.id R).range_eq_top_of_surjective (fun x => ⟨x,rfl⟩)] using hcomm
  have he' (x : R) (w : Space 1) : ρ x (e.symm w) = e.symm (σ (q x) w) := by
    apply e.injective
    exact (he x (e.symm w)).trans (by simp only [e.apply_symm_apply]; rfl)
  have hm := subspaceCommutator_map_embedding ρ σ q e.symm.toLinearMap he'
    (⊤ : Subgroup R) (⊤ : Submodule (ZMod 2) (Space 1))
  have hM : subspaceCommutator ρ ⊤ (⊤ : Subgroup R) = ⊤ := by
    dsimp only [σ] at hm
    simpa only [Submodule.map_top,LinearEquiv.range,←MonoidHom.range_eq_map,hq,
      PointSection.point_parabolic_commutator] using hm
  apply le_antisymm (le_normalizer_iff_commutator_le_left.mp hRN)
  intro v hv
  change (⟨v,hv⟩ : V) ∈ (⁅V,R⁆).subgroupOf V
  rw [hC,hM]
  change Additive.ofMul (⟨v,hv⟩ : V) ∈ (⊤ : Submodule (ZMod 2) (Additive V))
  exact Submodule.mem_top

/-- The original residual moves all of V, and therefore contains V in its
full two-core. No containment of V in the residual is assumed. -/
theorem marked_point_residual_contains_module
    (V L : Subgroup G) [IsElementaryAbelian 2 V]
    (hVL : V ≤ L) (hLN : L ≤ normalizer (V : Set G))
    (e : Additive V ≃ₗ[ZMod 2] Space 1) (q : L →* binaryImage 1)
    (he : ∀ (l : L) v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) v) = (q l).val (e v))
    (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (z : V) (hz : e (Additive.ofMul z) = PointSection.pointVector) :
    ⁅V,Centralizer.localResidual L z⁆ = V ∧ V ≤ Centralizer.localTwoCore L z := by
  let f := nativeBinaryEquiv.symm.toMonoidHom.comp q
  have hf : Function.Surjective f := nativeBinaryEquiv.symm.surjective.comp hq
  have hfk : IsPGroup 2 f.ker := by
    rwa [MonoidHom.ker_comp_of_injective _ _ nativeBinaryEquiv.symm.injective]
  have hP := marked_point_centralizer_preimage V L hLN e q he z hz
  have hRimage := (point_residual_images L (z : G) f hf hfk hP).1
  let R := Centralizer.localResidual L z
  have hRL : R ≤ L := (Centralizer.localResidual_le L z).trans inf_le_left
  let r := (binaryImage 1).subtype.comp (q.comp (inclusion hRL))
  have hRange : r.range = ParabolicTorus.pointParabolicImage 1 := by
    have hm := congrArg (Subgroup.map ((binaryImage 1).subtype.comp nativeBinaryEquiv.toMonoidHom)) hRimage
    rw [map_map,native_point_parabolic_image] at hm
    have heq : ((binaryImage 1).subtype.comp nativeBinaryEquiv.toMonoidHom).comp f =
        (binaryImage 1).subtype.comp q := by
      apply MonoidHom.ext
      intro l
      exact congrArg Subtype.val (nativeBinaryEquiv.apply_symm_apply (q l))
    rw [heq] at hm
    have hi : (inclusion hRL).range = R.subgroupOf L := by
      ext l
      constructor
      · rintro ⟨x,rfl⟩; exact x.property
      · intro hl; exact ⟨⟨l,hl⟩,Subtype.ext rfl⟩
    change (((binaryImage 1).subtype.comp q).comp (inclusion hRL)).range = _
    rw [MonoidHom.range_comp,hi]
    exact hm
  have hfull := marked_point_parabolic_commutator V R (hRL.trans hLN) e r
    (fun x v => he (inclusion hRL x) v) hRange
  have hVP : V ≤ L ⊓ centralizer ({(z : G)} : Set G) := by
    apply le_inf hVL
    intro v hv
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mul_comm' (⟨v,hv⟩ : V) z)
  have hVN : V ≤ normalizer (R : Set G) :=
    (hVP.trans (L ⊓ centralizer ({(z : G)} : Set G)).le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))
  have hVR : V ≤ R := hfull.ge.trans (le_normalizer_iff_commutator_le_right.mp hVN)
  exact ⟨hfull,le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V) hVR (hRL.trans hLN)⟩

end CFSG.Quasithin.Chapter8.Section02.HermitianSource

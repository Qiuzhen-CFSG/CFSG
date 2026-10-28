module
public import CFSG.Quasithin.Chapter13.Section09.CentralizerGrowth.Nine
public import Theory.SpecificGroups.SymmetricFourWreath.OrthogonalB

/-!
# The full original normalizer action is O₄⁺(2)

The nine-point z-orbit is exactly the nonzero singular locus of the concrete
form on the original B. Conjugation therefore preserves this quadratic form.
The pointwise-centralizer calculation gives literal kernel B, and the orbit
and stabilizer orders give image order72. Hence the actual action is onto
the full isometry group, with its marked linear action retained.

Source: Aschbacher–Smith 13.9.5, printed pp.970–971 (PDF pp.987–988).
The only contrary hypothesis is C_G(z)=T; no action model, fusion result,
or classification conclusion is assumed.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath SymmetricFourWreath.InvolutionClasses
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {d : Configuration G} (m : Marking d)

noncomputable def BModelEquiv : SymmetricFourWreath.B ≃* m.B :=
  m.imageEquiv SymmetricFourWreath.B

noncomputable def BLinearCoordinates : Additive m.B ≃ₗ[ZMod 2] BinaryFourPlus.V :=
  ({ m.BModelEquiv.symm.toAdditive with
    map_smul' := by
      intro c x
      rcases (by decide : ∀c:ZMod 2,c=0 ∨ c=1) c with rfl|rfl
      · simp only [RingHom.id_apply,zero_smul]
        exact m.BModelEquiv.symm.toAdditive.map_zero
      · simp only [RingHom.id_apply,one_smul] } :
      Additive m.B ≃ₗ[ZMod 2] Additive SymmetricFourWreath.B).trans OrthogonalB.linearCoordinates

omit [Finite G] in
theorem BLinearCoordinates_image (x:SymmetricFourWreath.B) :
    m.BLinearCoordinates (Additive.ofMul (m.BModelEquiv x))=
      OrthogonalB.linearCoordinates (Additive.ofMul x) := by
  change OrthogonalB.linearCoordinates
    (Additive.ofMul (m.BModelEquiv.symm (m.BModelEquiv x)))=_
  rw [MulEquiv.symm_apply_apply]

theorem B_singular_iff_conjugate_z
    {𝒦 : GroupClass} (hG:IsSimpleQTKE 𝒦 G)
    (hC : centralizer ({m.z}:Set G)=(d.T:Subgroup G)) (x:m.B) :
    BinaryFourPlus.q (m.BLinearCoordinates (Additive.ofMul x))=0 ↔ x=1 ∨ IsConj m.z (x:G) := by
  obtain ⟨a,rfl⟩ := m.BModelEquiv.surjective x
  rw [m.BLinearCoordinates_image,OrthogonalB.singular_iff]
  have he : (m.BModelEquiv a:G)=m.embedding a := rfl
  rw [he,m.conjugate_z_local_classes_iff_of_centralizer_eq hG hC _
    (m.image_le_local SymmetricFourWreath.B (mem_map_of_mem m.embedding a.property))]
  rw [m.embedding_mem_localInvolutionClass,m.embedding_mem_localInvolutionClass,
    m.embedding_mem_localInvolutionClass]
  have h1 : m.BModelEquiv a=1 ↔ a=1 :=
    m.BModelEquiv.map_eq_one_iff
  rw [h1]

noncomputable def normalizerLinearAction : normalizer (m.B:Set G) →*
    (BinaryFourPlus.V ≃ₗ[ZMod 2] BinaryFourPlus.V) where
  toFun g := m.BLinearCoordinates.symm.trans
    (({ (m.B.normalizerMonoidHom g).toAdditive with
       map_smul' := by
         intro c x
         rcases (by decide : ∀c:ZMod 2,c=0 ∨ c=1) c with rfl|rfl <;> simp } :
         Additive m.B ≃ₗ[ZMod 2] Additive m.B).trans m.BLinearCoordinates)
  map_one' := by
    apply LinearEquiv.ext
    intro v
    change m.BLinearCoordinates (Additive.ofMul (m.B.normalizerMonoidHom 1
      ((m.BLinearCoordinates.symm v).toMul)))=v
    rw [map_one]
    exact m.BLinearCoordinates.apply_symm_apply v
  map_mul' g h := by
    apply LinearEquiv.ext
    intro v
    change m.BLinearCoordinates (Additive.ofMul (m.B.normalizerMonoidHom (g*h)
      ((m.BLinearCoordinates.symm v).toMul)))=
      m.BLinearCoordinates (Additive.ofMul (m.B.normalizerMonoidHom g
        ((m.BLinearCoordinates.symm
          (m.BLinearCoordinates (Additive.ofMul (m.B.normalizerMonoidHom h
            ((m.BLinearCoordinates.symm v).toMul))))).toMul)))
    rw [m.BLinearCoordinates.symm_apply_apply,map_mul]
    rfl

omit [Finite G] in
theorem normalizerLinearAction_apply (g:normalizer (m.B:Set G)) (x:m.B) :
    m.normalizerLinearAction g (m.BLinearCoordinates (Additive.ofMul x))=
      m.BLinearCoordinates (Additive.ofMul (m.B.normalizerMonoidHom g x)) := by
  change m.BLinearCoordinates (Additive.ofMul (m.B.normalizerMonoidHom g
    ((m.BLinearCoordinates.symm (m.BLinearCoordinates (Additive.ofMul x))).toMul)))=_
  rw [m.BLinearCoordinates.symm_apply_apply]
  rfl
theorem normalizerLinearAction_preserves
    {𝒦 : GroupClass} (hG:IsSimpleQTKE 𝒦 G)
    (hC : centralizer ({m.z}:Set G)=(d.T:Subgroup G))
    (g:normalizer (m.B:Set G)) (v:BinaryFourPlus.V) :
    BinaryFourPlus.q (m.normalizerLinearAction g v)=BinaryFourPlus.q v := by
  let x:m.B := (m.BLinearCoordinates.symm v).toMul
  have hv : m.BLinearCoordinates (Additive.ofMul x)=v := m.BLinearCoordinates.apply_symm_apply v
  rw [←hv,m.normalizerLinearAction_apply]
  apply (by decide : ∀a b:ZMod 2,(a=0 ↔ b=0)→a=b)
  rw [m.B_singular_iff_conjugate_z hG hC,m.B_singular_iff_conjugate_z hG hC]
  have hx : IsConj (x:G) (m.B.normalizerMonoidHom g x:G) := isConj_iff.mpr ⟨g,rfl⟩
  rw [(m.B.normalizerMonoidHom g).map_eq_one_iff]
  exact or_congr Iff.rfl ⟨fun h=>h.trans hx.symm,fun h=>h.trans hx⟩

noncomputable def normalizerIsometryAction
    {𝒦 : GroupClass} (hG:IsSimpleQTKE 𝒦 G)
    (hC : centralizer ({m.z}:Set G)=(d.T:Subgroup G)) :
    normalizer (m.B:Set G) →* BinaryFourPlus.q.isometrySubgroup :=
  m.normalizerLinearAction.codRestrict _
    (fun g=>(QuadraticMap.mem_isometrySubgroup _ _).mpr (m.normalizerLinearAction_preserves hG hC g))

omit [Finite G] in
theorem normalizerLinearAction_ker :
    m.normalizerLinearAction.ker=m.B.normalizerMonoidHom.ker := by
  ext g
  rw [MonoidHom.mem_ker,MonoidHom.mem_ker]
  constructor
  · intro he
    apply MulEquiv.ext
    intro x
    have hf := congrArg (fun a:BinaryFourPlus.V≃ₗ[ZMod 2]BinaryFourPlus.V =>
      a (m.BLinearCoordinates (Additive.ofMul x))) he
    rw [m.normalizerLinearAction_apply] at hf
    exact congrArg Additive.toMul (m.BLinearCoordinates.injective hf)
  · intro he
    apply LinearEquiv.ext
    intro v
    let x:m.B := (m.BLinearCoordinates.symm v).toMul
    have hv : m.BLinearCoordinates (Additive.ofMul x)=v := m.BLinearCoordinates.apply_symm_apply v
    rw [←hv,m.normalizerLinearAction_apply,he]
    rfl

theorem centralizer_B_of_centralizer_eq
    {𝒦 : GroupClass} (hG:IsSimpleQTKE 𝒦 G)
    (hC : centralizer ({m.z}:Set G)=(d.T:Subgroup G)) : centralizer (m.B:Set G)=m.B := by
  apply le_antisymm
  · intro g hg
    apply (m.conjugate_z_pointwise_centralizer_of_centralizer_eq hG hC).le
    refine ⟨?_,?_⟩
    · have hz : g∈centralizer ({m.z}:Set G) := mem_centralizer_singleton_iff.mpr
        ((mem_centralizer_iff.mp hg m.z m.z_mem_B).symm)
      exact hC ▸ hz
    · exact centralizer_le (by intro x hx;exact hx.1) hg
  · intro g hg x hx
    exact congrArg Subtype.val
      ((IsElementaryAbelian.toIsMulCommutative (p:=2) (G:=m.B)).is_comm.comm
        (⟨x,hx⟩:m.B) ⟨g,hg⟩)

theorem normalizerIsometryAction_ker
    {𝒦 : GroupClass} (hG:IsSimpleQTKE 𝒦 G)
    (hC : centralizer ({m.z}:Set G)=(d.T:Subgroup G)) :
    (m.normalizerIsometryAction hG hC).ker=m.B.subgroupOf (normalizer (m.B:Set G)) := by
  have he : (m.normalizerIsometryAction hG hC).ker=m.normalizerLinearAction.ker := by
    ext g
    rw [MonoidHom.mem_ker,MonoidHom.mem_ker,Subtype.ext_iff]
    rfl
  rw [he,m.normalizerLinearAction_ker,normalizerMonoidHom_ker,m.centralizer_B_of_centralizer_eq hG hC]

theorem normalizerIsometryAction_surjective
    {𝒦 : GroupClass} (hG:IsSimpleQTKE 𝒦 G)
    (hC : centralizer ({m.z}:Set G)=(d.T:Subgroup G)) :
    Function.Surjective (m.normalizerIsometryAction hG hC) := by
  let : Finite BinaryFourPlus.q.isometrySubgroup :=
    Finite.of_equiv BinaryFourPlus.Wreath BinaryFourPlus.isometryEquivWreath.symm.toEquiv
  let ρ := m.normalizerIsometryAction hG hC
  have hk : Nat.card ρ.ker=16 := by
    rw [m.normalizerIsometryAction_ker hG hC,
      Nat.card_congr (subgroupOfEquivOfLe m.B.le_normalizer).toEquiv]
    exact m.card_elementaryGroup false false
  have hN : Nat.card (normalizer (m.B:Set G))=1152 := by
    rw [m.normalizer_card_of_centralizer_eq hC,(m.normalizerOrbit_nine_of_centralizer_eq hG hC).1]
  have hr : Nat.card ρ.range=72 := by
    have he := ρ.ker.card_mul_index
    rw [Subgroup.index_ker,hk,hN] at he
    omega
  exact MonoidHom.range_eq_top.mp (ρ.range.eq_top_of_card_eq
    (hr.trans BinaryFourPlus.card_isometrySubgroup.symm))

end CFSG.Quasithin.Chapter13.Section09.Marking

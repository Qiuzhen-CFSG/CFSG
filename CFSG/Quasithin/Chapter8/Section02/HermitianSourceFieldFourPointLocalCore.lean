module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourPointCrossing
public import Theory.GroupTheory.PCoreQuotientJoinAction
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# The full point-local core and the original closure image

Conjugation on the marked L/O₂(L) has exactly O₂(LT) as its kernel.
The native PSL₃ local calculation therefore lifts to
O₂(L_z T) = O₂(L_z) O₂(LT), with the original Sylow and full cores.

The selected-plane crossing and the irreducible dual interval then give
E O₂(LT) = O₂(L_z) O₂(LT). Since O₂(LT) is elementary and E is central
in O₂(C_G(z)) modulo ⟨z⟩, the intersection of the two full cores commutes
with O₂(L_z) modulo that same central line. The denominator O₂(LT) is
retained. The fixed-space identity on V nevertheless gives
V ∩ O₂(C_G(z)) = V ∩ E = V_z. These facts alone do not identify EV with O₂(L_z).

Source: Aschbacher–Smith 8.2.11(4) and 8.2.12, printed p.722,
refs/quasithin.pdf. The Chapter 12 consumer supplies all new premises for
the original half-field tensor. The fixed-subgroup bound on the whole
indecomposable LT core and the extraspecial closure remain subsequent steps.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
variable {G : Type*} [Group G] [Finite G]
set_option backward.isDefEq.respectTransparency false

theorem point_local_core_product
    (L : Subgroup G) (T : Sylow 2 G) (z : G)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (f : L →* Matrix.PSL3Four.PSL) (hf : Function.Surjective f)
    (hk : f.ker = pCore 2 L)
    (hP : Matrix.PSL3Four.ElementaryParabolic.liftedParabolic f true =
      (centralizer ({z} : Set G)).subgroupOf L) :
    (Centralizer.localResidual L z ⊔ (T : Subgroup G)).pCoreIn 2 =
      (Centralizer.localResidual L z).pCoreIn 2 ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let J := L ⊔ (T : Subgroup G)
  let R := Centralizer.localResidual L z
  have hRL : R ≤ L := (Centralizer.localResidual_le L z).trans inf_le_left
  have hRJ : R ≤ J := hRL.trans le_sup_left
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (point_commutator_normalizes L ⊥ (T : Subgroup G) z hTL
      (by rw [normalizer_eq_top]; exact le_top) hTz).1
  let e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Four.PSL :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have he (l : L) : e (QuotientGroup.mk' (pCore 2 L) l) = f l := rfl
  have hcenter : center (L ⧸ pCore 2 L) = ⊥ := by
    apply bot_unique
    intro x hx
    have hx' := (centerCongr e ⟨x,hx⟩).property
    change e x ∈ center Matrix.PSL3Four.PSL at hx'
    have hconj : MulAut.conj (e x) = 1 := by
      ext y
      change e x*y*(e x)⁻¹=y
      rw [←mem_center_iff.mp hx' y,mul_inv_cancel_right]
    have htriv : e x = 1 :=
      Matrix.PSL3.ExtensionBorel.inner_injective Matrix.PSL3Four.F
        (hconj.trans (map_one MulAut.conj).symm)
    exact e.injective (htriv.trans e.map_one.symm)
  let a : J →* MulAut Matrix.PSL3Four.PSL :=
    (MulAut.congr e).toMonoidHom.comp (pCoreJoinAction 2 hTL)
  have hak : a.ker = pCore 2 J := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.congr e).injective,
      pCoreJoinAction_kernel 2 hTL T.isPGroup' hcenter]
  have hap : IsPGroup 2 a.ker := hak ▸ pCore_isPGroup
  have hai (l : L) : a (inclusion (show L ≤ J from le_sup_left) l) = MulAut.conj (f l) := by
    change MulAut.congr e (pCoreJoinAction 2 hTL (inclusion le_sup_left l)) = _
    rw [pCoreJoinAction_on_component]
    ext x
    obtain ⟨u,rfl⟩ := e.surjective x
    change e (QuotientGroup.mk' (pCore 2 L) l * e.symm (e u) *
      (QuotientGroup.mk' (pCore 2 L) l)⁻¹) = _
    simp only [e.symm_apply_apply,map_mul,map_inv,he,MulAut.conj_apply]
  let im := fun A : Subgroup G => (A.subgroupOf J).map a
  have him (A : Subgroup G) (hAL : A ≤ L) :
      im A = ((A.subgroupOf L).map f).map MulAut.conj := by
    ext b
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨f ⟨x,hAL hx⟩,⟨⟨x,hAL hx⟩,hx,rfl⟩,(hai ⟨x,hAL hx⟩).symm⟩
    · rintro ⟨_,⟨l,hl,rfl⟩,rfl⟩
      exact ⟨inclusion le_sup_left l,hl,hai l⟩
  have hRim : im R =
      (Matrix.PSL3.LinearThree.OuterExtensions.localFactor Matrix.PSL3Four.F true).map MulAut.conj := by
    rw [him R hRL,(point_residual_images L z f hf (hk ▸ pCore_isPGroup) hP).1,
      Matrix.PSL3Four.ElementaryParabolic.native_parabolic_eq_local]
  have hnorm : im (T : Subgroup G) ≤ normalizer (im R : Set _) :=
    (map_mono ((comap_mono hTR).trans (R.le_normalizer_comap _))).trans (le_normalizer_map _)
  rw [hRim] at hnorm
  have hpres (b : MulAut Matrix.PSL3Four.PSL) (hb : b ∈ im (T : Subgroup G)) :
      (Matrix.PSL3.LinearThree.OuterExtensions.localFactor Matrix.PSL3Four.F true).map b.toMonoidHom =
        Matrix.PSL3.LinearThree.OuterExtensions.localFactor Matrix.PSL3Four.F true := by
    have hb' := mem_normalizer_iff_map_conj_eq.mp (hnorm hb)
    have heq : (MulAut.conj b : MulAut Matrix.PSL3Four.PSL →* _).comp MulAut.conj =
        MulAut.conj.comp b.toMonoidHom := by
      ext x y
      simp
    rw [map_map,heq,←map_map] at hb'
    exact map_injective (Matrix.PSL3.ExtensionBorel.inner_injective Matrix.PSL3Four.F) hb'
  have hc := Matrix.PSL3.LinearThree.OuterExtensions.AmbientLocalCores.local_join_core_in_aut
    Matrix.PSL3Four.F (f := 2) (by decide) (by rw [Matrix.PSL3Four.card_F]; norm_num)
    true (im (T : Subgroup G)) hpres
  have himcore (A : Subgroup G) (hAJ : A ≤ J) : im (A.pCoreIn 2) = (im A).pCoreIn 2 := by
    dsimp only [im]
    rw [←pCoreIn_subgroupOf 2 A J hAJ,map_pCoreIn_of_ker_isPGroup a hap]
  have himjoin : im (R ⊔ (T : Subgroup G)) = im R ⊔ im (T : Subgroup G) := by
    dsimp only [im]
    rw [subgroupOf_sup hRJ le_sup_right,Subgroup.map_sup]
  have hsame : im ((R ⊔ (T : Subgroup G)).pCoreIn 2) = im (R.pCoreIn 2) := by
    rw [himcore _ (sup_le hRJ le_sup_right),himjoin,himcore R hRJ,hRim,hc]
  apply le_antisymm
  · intro x hx
    have hxJ : x ∈ J := (pCoreIn_le 2 _).trans (sup_le hRJ le_sup_right) hx
    have hximage : a ⟨x,hxJ⟩ ∈ im (R.pCoreIn 2) := hsame ▸ mem_map_of_mem a hx
    obtain ⟨y,hy,heq⟩ := hximage
    have hxy : (⟨x,hxJ⟩ : J) * y⁻¹ ∈ pCore 2 J := by
      rw [←hak]
      change a ((⟨x,hxJ⟩ : J)*y⁻¹)=1
      rw [map_mul,map_inv,heq,mul_inv_cancel]
    have hxy' : x*(y : G)⁻¹ ∈ J.pCoreIn 2 := mem_map_of_mem J.subtype hxy
    have hp := (R.pCoreIn 2 ⊔ J.pCoreIn 2).mul_mem (mem_sup_right hxy') (mem_sup_left hy)
    change x*(y : G)⁻¹*(y : G) ∈ _ at hp
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using hp
  · apply sup_le
    · exact pCoreIn_mono_of_normalizes le_sup_left (sup_le R.le_normalizer hTR)
    · have hQT : J.pCoreIn 2 ≤ (T : Subgroup G) := by
        simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
          (show (T : Subgroup G) ≤ J from le_sup_right)] using
          pCoreIn_le_sylow J (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right))
      intro x hx
      exact inf_pCoreIn_le_of_le 2 (sup_le hRJ le_sup_right) ⟨mem_sup_right (hQT hx),hx⟩

omit [Finite G] in
/-- The actual crossing and dual interval fill the local core modulo the full LT core. -/
theorem point_closure_join_core
    (L V : Subgroup G) (T : Sylow 2 G) (z : G)
    (hVX : V ≤ Centralizer.localTwoCore L z)
    (hVQ : V ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hE : (Centralizer.sourceClosure L V z).map (centralizer ({z} : Set G)).subtype ≤
      Centralizer.localTwoCore L z ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hout : ¬ (Centralizer.sourceClosure L V z).map (centralizer ({z} : Set G)).subtype ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hirr : ∀ Y : Subgroup G, V ≤ Y → Y ≤ Centralizer.localTwoCore L z →
      Centralizer.localResidual L z ≤ normalizer (Y : Set G) →
      Y = V ∨ Y = Centralizer.localTwoCore L z) :
    (Centralizer.sourceClosure L V z).map (centralizer ({z} : Set G)).subtype ⊔
      (L ⊔ (T : Subgroup G)).pCoreIn 2 =
      Centralizer.localTwoCore L z ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let C := centralizer ({z} : Set G)
  let J := L ⊔ (T : Subgroup G)
  let R := Centralizer.localResidual L z
  let X := Centralizer.localTwoCore L z
  let Q := J.pCoreIn 2
  let E := (Centralizer.sourceClosure L V z).map C.subtype
  let Y := X ⊓ (E ⊔ Q)
  have hRJ : R ≤ J := ((Centralizer.localResidual_le L z).trans inf_le_left).trans le_sup_left
  have hXJ : X ≤ J := (Centralizer.localTwoCore_le L z).trans hRJ
  have hQJ : Q ≤ J := pCoreIn_le 2 J
  have hEJ : E ≤ J := hE.trans (sup_le hXJ hQJ)
  have hRE : R ≤ normalizer (E : Set G) := by
    have hh := (Centralizer.sourceClosure L V z).le_normalizer_map C.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
    exact ((Centralizer.localResidual_le L z).trans inf_le_right).trans hh
  have hRQ : R ≤ normalizer (Q : Set G) := hRJ.trans
    (J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))
  have hRY : R ≤ normalizer (Y : Set G) :=
    (le_inf (R.le_normalizer.trans (normalizer_le_normalizer_characteristic_image R (pCore 2 R)))
      ((le_inf hRE hRQ).trans (normalizer_inf_normalizer_le_normalizer_sup E Q))).trans
      inf_normalizer_le_normalizer_inf
  have hVY : V ≤ Y := le_inf hVX (hVQ.trans le_sup_right)
  have hXY : X ≤ E ⊔ Q := by
    rcases hirr Y hVY inf_le_left hRY with he | he
    · exfalso
      apply hout
      intro x hx
      have hxJ := hEJ hx
      have hxjoin : (⟨x,hxJ⟩ : J) ∈ X.subgroupOf J ⊔ Q.subgroupOf J := by
        rw [←subgroupOf_sup hXJ hQJ]
        exact hE hx
      let : (Q.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
        (J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))
      obtain ⟨a,ha,b,hb,hab⟩ := mem_sup_of_normal_right.mp hxjoin
      have hab' : (a : G)*(b : G)=x := congrArg J.subtype hab
      have haY : (a : G) ∈ Y := by
        refine ⟨ha,?_⟩
        have haeq : (a : G)=x*(b : G)⁻¹ := by rw [←hab']; group
        rw [haeq]
        exact (E ⊔ Q).mul_mem (mem_sup_left hx) (mem_sup_right (Q.inv_mem hb))
      have haQ := hVQ (he ▸ haY)
      rw [←hab']
      exact Q.mul_mem haQ hb
    · exact he.ge.trans inf_le_right
  exact le_antisymm (sup_le hE le_sup_right) (sup_le hXY le_sup_right)

omit [Finite G] in
/-- The two full cores intersect in the point-radical fixed subgroup modulo
the original central line. No indecomposable-extension bound is assumed here. -/
theorem point_core_intersection_commutator
    (L V : Subgroup G) (T : Sylow 2 G) (z : G)
    (hTC : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hQ : IsElementaryAbelian 2 ((L ⊔ (T : Subgroup G)).pCoreIn 2))
    (hEQ : ⁅Centralizer.sourceClosure L V z,pCore 2 (centralizer ({z} : Set G))⁆ ≤
      (zpowers z).subgroupOf (centralizer ({z} : Set G)))
    (hjoin : (Centralizer.sourceClosure L V z).map (centralizer ({z} : Set G)).subtype ⊔
      (L ⊔ (T : Subgroup G)).pCoreIn 2 =
      Centralizer.localTwoCore L z ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ (centralizer ({z} : Set G)).pCoreIn 2,
      Centralizer.localTwoCore L z⁆ ≤ zpowers z := by
  let C := centralizer ({z} : Set G)
  let J := L ⊔ (T : Subgroup G)
  let Q := J.pCoreIn 2
  let E := (Centralizer.sourceClosure L V z).map C.subtype
  let Z := zpowers z
  have hZC : Z ≤ C := zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
  have hCZ : C ≤ normalizer (Z : Set G) := by
    apply le_trans ?_ (centralizer_le_normalizer (Z : Set G))
    rw [show Z = zpowers z from rfl,zpowers_eq_closure,centralizer_closure]
  have hQC : Q ≤ C := by
    have hQT : Q ≤ (T : Subgroup G) := by
      simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
        (show (T : Subgroup G) ≤ J from le_sup_right)] using
        pCoreIn_le_sylow J (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right))
    exact hQT.trans hTC
  have hEQ' : ⁅E,C.pCoreIn 2⁆ ≤ Z := by
    have hh := map_mono (f := C.subtype) hEQ
    rw [map_commutator,map_subgroupOf_eq_of_le hZC] at hh
    exact hh
  let := hQ
  have hQQ : ⁅Q,Q⁆ = ⊥ := commutator_self_eq_bot_iff.mpr inferInstance
  have hb : ⁅E ⊔ Q,Q ⊓ C.pCoreIn 2⁆ ≤ Z :=
    commutator_sup_le_of_relative_normal C E Q (Q ⊓ C.pCoreIn 2) Z hCZ
      (map_subtype_le _) hQC ((commutator_mono le_rfl inf_le_right).trans hEQ')
      ((commutator_mono le_rfl inf_le_left).trans (hQQ.le.trans bot_le))
  rw [commutator_comm]
  exact (commutator_mono (le_sup_left.trans hjoin.ge) le_rfl).trans hb

omit [Finite G] in
/-- The retained denominator already determines the intersection of the original
module with both the full centralizer core and the actual normal closure. -/
theorem point_module_core_intersections
    (L V : Subgroup G) [IsElementaryAbelian 2 V] (T : Sylow 2 G) (z : V)
    (hLN : L ≤ normalizer (V : Set G))
    (hVQ : V ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hE : (Centralizer.sourceClosure L V z).map (centralizer ({(z : G)} : Set G)).subtype ≤
      (centralizer ({(z : G)} : Set G)).pCoreIn 2)
    (hc : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓
      (centralizer ({(z : G)} : Set G)).pCoreIn 2,Centralizer.localTwoCore L z⁆ ≤ zpowers (z : G))
    (hfix : ∀ v : V, (∀ x : Centralizer.localTwoCore L z,
      ⁅(x : G),(v : G)⁆ ∈ zpowers (z : G)) ↔
        v.val ∈ Centralizer.commutatorSpace L V z) :
    V ⊓ (centralizer ({(z : G)} : Set G)).pCoreIn 2 = Centralizer.commutatorSpace L V z ∧
      V ⊓ (Centralizer.sourceClosure L V z).map (centralizer ({(z : G)} : Set G)).subtype =
        Centralizer.commutatorSpace L V z := by
  have hWE := Centralizer.commutatorSpace_le_sourceClosure L V z z.property hLN
  have hWV := Centralizer.commutatorSpace_le L V z hLN
  have hcap : V ⊓ (centralizer ({(z : G)} : Set G)).pCoreIn 2 ≤
      Centralizer.commutatorSpace L V z := by
    intro v hv
    apply (hfix ⟨v,hv.1⟩).mp
    intro x
    rw [commutator_comm] at hc
    exact hc (commutator_mem_commutator x.property ⟨hVQ hv.1,hv.2⟩)
  exact ⟨le_antisymm hcap (le_inf hWV (hWE.trans hE)),
    le_antisymm ((inf_le_inf_left V hE).trans hcap) (le_inf hWV hWE)⟩

end CFSG.Quasithin.Chapter8.Section02.HermitianSource

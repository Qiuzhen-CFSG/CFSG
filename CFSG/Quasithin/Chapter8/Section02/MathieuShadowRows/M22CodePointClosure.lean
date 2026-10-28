module
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodePointPairing
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodePointCover
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodePointLocalCore
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodePointQuotient
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourPointLocalCore
/-!
# The full M22 point closure and its literal residual image

The native hexad section and commutator pairing place the relative closure
inside the centralizer core. The selected crossing and full point-local
core product identify its image modulo the original LT core. Perfect
residual action and Sylow averaging control the fixed subgroup on that
entire core, giving E=O₂(C_G(z)), EV=O₂(L_z), and E∩V=V_z.

The actual projection into C_G(z)/O₂(C_G(z)) consequently has two-core
of order 32 and full A₆ quotient. All covering kernels and original maps
are retained. The source consumer supplies the earlier block conditions,
the selected crossing, and the native point-local core product.

Source: Aschbacher--Smith 8.2.11--13, printed pp.722--723,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
open ChapterE Centralizer
variable {G : Type*} [Group G] [Finite G]
set_option backward.isDefEq.respectTransparency false

/-- The original point closure is the full centralizer core, and adjoining
the original module gives the full point-residual core. -/
theorem m22_point_closure_core
    (L V : Subgroup G) [IsElementaryAbelian 2 V] (T : Sylow 2 G) (z : V)
    (hchar : centralizer (pCore 2 (centralizer ({(z : G)} : Set G)) :
      Set (centralizer ({(z : G)} : Set G))) ≤
        pCore 2 (centralizer ({(z : G)} : Set G)))
    (hVL : V ≤ L) (hLN : L ≤ normalizer (V : Set G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hVT : V ≤ T)
    (hTC : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hz2 : orderOf (z : G) = 2)
    (hVQ : V ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hQC : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ centralizer (V : Set G))
    (hQ : IsElementaryAbelian 2 ((L ⊔ (T : Subgroup G)).pCoreIn 2))
    (hcomm : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,L⁆ ≤ V)
    (hTCL : (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (e : Additive V ≃ₗ[ZMod 2] M22Code)
    (c : (L ⊓ centralizer ({(z : G)} : Set G) : Subgroup G) →* MulAction.stabilizer M22 B)
    (hc : Function.Surjective c)
    (hck : c.ker = V.subgroupOf (L ⊓ centralizer ({(z : G)} : Set G)))
    (hz : e (Additive.ofMul z) = m22HexadVector hB)
    (he : ∀ r v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion (inf_le_left.trans hLN) r)) v) =
        m22CodeRepresentation (c r).val (e v))
    (hker : (centralizer (V : Set G)).subgroupOf (localTwoCore L z) =
      V.subgroupOf (localTwoCore L z))
    (hlocal : (localResidual L z ⊔ (T : Subgroup G)).pCoreIn 2 =
      localTwoCore L z ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hout : ¬ (sourceClosure L V z).map (centralizer ({(z : G)} : Set G)).subtype ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    sourceClosure L V z = pCore 2 (centralizer ({(z : G)} : Set G)) ∧
      (sourceClosure L V z).map (centralizer ({(z : G)} : Set G)).subtype ⊔ V =
        localTwoCore L z ∧
      V ⊓ (sourceClosure L V z).map (centralizer ({(z : G)} : Set G)).subtype =
        commutatorSpace L V z ∧
      (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ (centralizer ({(z : G)} : Set G)).pCoreIn 2 =
        commutatorSpace L V z ∧ Nat.card (commutatorSpace L V z) = 32 ∧
      Nat.card (pCore 2 (Chapter7.NormalizedSource.MathieuSextet.pointResidualImage L (z : G))) = 32 ∧
      Nonempty ((Chapter7.NormalizedSource.MathieuSextet.pointResidualImage L (z : G) ⧸
        pCore 2 (Chapter7.NormalizedSource.MathieuSextet.pointResidualImage L (z : G))) ≃*
          alternatingGroup (Fin 6)) := by
  let C := centralizer ({(z : G)} : Set G)
  let R := localResidual L z
  let X := localTwoCore L z
  let W := commutatorSpace L V z
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let E := (sourceClosure L V z).map C.subtype
  let i := inclusion (localResidual_le L z)
  let f := c.comp i
  have hcp : IsPGroup 2 c.ker := hck ▸ (IsElementaryAbelian.isPGroup 2 V).comap_subtype
  obtain ⟨hf,hfk⟩ := m22_point_full_residual_cover L z hB c hc hcp
  obtain ⟨hRC,hVX,_⟩ := m22_point_full_centralizer L V z hVL hLN hB e c hc hck hz he
  have hfe : ∀ r v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion
        (((localResidual_le L z).trans inf_le_left).trans hLN) r)) v) =
        m22CodeRepresentation (f r).val (e v) := fun r v => he (i r) v
  obtain ⟨hWcard,hZW,hirr,_⟩ := m22_point_hexad_section L V z hLN hB e f hf hfk hz hfe
  obtain ⟨hpair,hfix,hfixed⟩ := m22_point_hexad_pairing L V z hLN hB e f hf hfk hz hfe
  have hRL : R ≤ L := (localResidual_le L z).trans inf_le_left
  have hRz : R ≤ C := (localResidual_le L z).trans inf_le_right
  have hRW : R ≤ normalizer (W : Set G) :=
    (HermitianSource.point_commutator_normalizes L V R z
      (hRL.trans L.le_normalizer) (hRL.trans hLN) hRz).2
  obtain ⟨hTR,hTW⟩ := HermitianSource.point_commutator_normalizes L V (T : Subgroup G) z hTL hTV hTC
  obtain ⟨hcore,hclass,_⟩ := sourceClosure_core_of_irreducible_section L V T z
    hchar hLN hVT hTC hZW (sup_le hRW hTW) hirr
  have hCcoreT : C.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ C from hTC)] using
      pCoreIn_le_sylow C (T.subtype hTC)
  have hCcoreLocal : C.pCoreIn 2 ≤ (R ⊔ (T : Subgroup G)).pCoreIn 2 := by
    intro x hx
    exact inf_pCoreIn_le_of_le 2 (sup_le hRz hTC)
      ⟨mem_sup_right (hCcoreT hx),hx⟩
  have hbound : C.pCoreIn 2 ≤ X ⊔ Q := hCcoreLocal.trans hlocal.le
  have hEmap : E ≤ C.pCoreIn 2 := map_mono hcore
  have hz1 : (z : G) ≠ 1 := by intro hz1; simp [hz1] at hz2
  have hdual := sourcePoint_dual_interval L V z hz1
    ChapterH.Section13To16.M22Local.Hexad.NativePairing.Section hpair hker hZW.le hRW hirr
  have hjoin := HermitianSource.point_closure_join_core L V T z hVX hVQ
    (hEmap.trans hbound) hout hdual
  have hccomm := HermitianSource.point_core_intersection_commutator L V T z hTC hQ hclass hjoin
  have hwhole (a : G) (ha : a ∈ Q) (hfa : ∀ x : X, ⁅(x : G),a⁆ ∈ zpowers (z : G)) : a ∈ W := by
    have hav : a ∈ V := sourcePoint_full_core_second_fixed L V T z hLN hTL hVT hVQ
      hQC hcomm hTCL hz2 (by intro t ht; exact mem_centralizer_singleton_iff.mp (hTC ht))
      hRC ChapterH.Section13To16.M22Local.Hexad.NativePairing.Section hpair hker hfix a ha hfa
    exact (hfixed ⟨a,hav⟩).mp hfa
  obtain ⟨hcap,hEcore⟩ := sourcePoint_core_intersection_of_fixed_bound L V T z hLN hTC hVQ
    hcore (hbound.trans hjoin.ge) hccomm hwhole
  have hEeq : E = C.pCoreIn 2 := congrArg (Subgroup.map C.subtype) hEcore
  have hnact : ¬ W ≤ centralizer (R : Set G) := by
    intro ha
    apply hZW.not_ge
    exact (le_inf (commutatorSpace_le L V z hLN)
      (ha.trans (centralizer_le (localTwoCore_le L z)))).trans hfix.le
  have hEV := sourcePoint_closure_join_module L V T z hz2 hLN hTR hVQ hQC hVX hRW hirr
    hnact ChapterH.Section13To16.M22Local.Hexad.NativePairing.Section hpair hker hfix hZW.le
    hEeq ((commutator_mono le_rfl hcore).trans hclass) hjoin (by
      change Q ⊓ E = W
      rw [hEeq]
      exact hcap)
  have hVE := (HermitianSource.point_module_core_intersections L V T z hLN hVQ
    hEmap hccomm hfixed).2
  have hVC : V ≤ C := by
    intro v hv
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm' (⟨v,hv⟩ : V) z))
  have hVc : Nat.card V = 1024 := by
    change Nat.card (Additive V) = 1024
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      e.finrank_eq,finrank_m22Code]
    decide
  have hprod : localTwoCore L z = C.pCoreIn 2 ⊔ V := by
    rw [←hEeq]
    exact hEV.symm
  have hcapV : Nat.card (C.pCoreIn 2 ⊓ V : Subgroup G) = 32 := by
    rw [inf_comm,←hEeq]
    exact (congrArg (fun A : Subgroup G => Nat.card A) hVE).trans hWcard
  exact ⟨hEcore,hEV,hVE,hcap,hWcard,
    m22_point_residual_image_core_card L V z hVC hprod hVc hcapV,
    (m22_point_residual_full_quotients L z hB c hc hcp).2⟩

end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows

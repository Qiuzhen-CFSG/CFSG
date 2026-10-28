module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.CenterPoint
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.BlockElementary
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four.CubicFixedPoints
public import Theory.GroupAction.ExtraspecialThirtyTwoCubic

/-!
# The actual quaternion closure and involution generation of W

A Sylow three-subgroup of the original H maps onto a Sylow subgroup of
its literal dotted quotient. The full orthogonal action has zero fixed
space on U/Z(U), while H centralizes the marked point Z(U). Thus the
Sylow's fixed subgroup on U is exactly its center. The cubic orbit count
for the extraspecial group of order thirty-two produces the actual two
quaternion factors. A noncentral involution in the original rank-two seed
identifies W with its centralizer, giving involution generation of W.

Source: Aschbacher--Smith, 14.3.18, printed pp.995--996, using 14.3.15.
-/

@[expose] public noncomputable section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}

/-- The full original orthogonal action determines the quaternion factors
inside the literal closure U. -/
theorem quaternion_closure_of_full_orthogonal (F : InvariantFlag T V 2)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F) (hZ : F.ZU=F.Vi 1) (hne : ¬ IsMulCommutative F.U)
    (hr : ChapterG.Section09.FittingRecognition.OrthogonalRealization F.terminalRepresentation ⊤) :
    Nonempty (QuaternionCentralProductData F.U) := by
  let : IsExtraspecial 2 F.U := extraspecial_of_center_point F d (by omega) hZ hne
  have hhat : Nat.card F.Uhat=16 := by
    obtain ⟨e,l,he⟩ := hr
    have hc := Nat.card_congr (l.trans ChapterG.Section09.FittingRecognition.Four.splitCoordinates).toEquiv
    change Nat.card (Additive F.Uhat)=Nat.card BinaryFourPlus.V at hc
    have hm : Nat.card (Additive F.Uhat)=Nat.card F.Uhat := Nat.card_congr Additive.toMul
    have hv : Nat.card BinaryFourPlus.V=16 := by rw [Nat.card_eq_fintype_card]; decide +kernel
    omega
  have hU : Nat.card F.U=32 := by
    have hh := (center F.U).card_eq_card_quotient_mul_card_subgroup
    rw [IsExtraspecial.center_order_p 2 F.U,hhat] at hh
    exact hh
  let P : Sylow 3 F.H := default
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  let P' := P.mapSurjective (f:=q) (QuotientGroup.mk'_surjective _)
  let action : F.H →* MulAut F.U := F.U.normalizerMonoidHom.comp
    (inclusion (le_normalizer_conjugateSpanBy V F.H))
  let : MulDistribMulAction P F.U := MulDistribMulAction.compHom F.U (action.comp (P : Subgroup F.H).subtype)
  apply Theory.GroupAction.quaternionCentralProduct_of_three_fixed_center P.isPGroup' hU
  intro u
  constructor
  · intro hfix
    have hdot : ∀ a ∈ (P' : Subgroup F.TerminalHdot),
        F.terminalRepresentation a (Additive.ofMul (QuotientGroup.mk' (center F.U) u))=
          Additive.ofMul (QuotientGroup.mk' (center F.U) u) := by
      rintro a ⟨b,hb,rfl⟩
      apply Additive.toMul.injective
      rw [F.terminalRepresentation_apply_mk]
      change F.terminalHatAction b (QuotientGroup.mk' (center F.U) u) =
        QuotientGroup.mk' (center F.U) u
      rw [F.terminalHatAction_apply_mk]
      exact congrArg (QuotientGroup.mk' (center F.U)) (hfix ⟨b,hb⟩)
    have hz := ChapterG.Section09.FittingRecognition.Four.sylow_three_fixed_eq_zero_of_full_orthogonal
      F.terminalRepresentation hr P' _ hdot
    apply (QuotientGroup.eq_one_iff u).mp
    exact hz
  · intro hu a
    apply Subtype.ext
    change ((a.val : F.H) : G) * (u : G) * (((a.val : F.H) : G))⁻¹=(u : G)
    have hp : (u : G) ∈ F.Vi 1 := by
      rw [←hZ]
      exact mem_map_of_mem F.U.subtype hu
    have hcentral : (a.val : F.H).val ∈ centralizer (F.Vi 1 : Set G) :=
      normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by omega)) a.val.property
    have hh := hcentral (u:G) hp
    calc
      _ = (u:G) * (((a.val : F.H) : G) * (((a.val : F.H) : G))⁻¹) := by rw [←hh]; group
      _ = (u:G) := by simp

/-- A noncentral involution in the actual rank-two seed realizes the original
W as its involution centralizer inside U. -/
theorem W_as_involution_centralizer_of_center_point (F : InvariantFlag T V 2)
    [IsElementaryAbelian 2 V] (hZ : F.ZU=F.Vi 1) :
    ∃ t : F.U, orderOf t=2 ∧ t ∉ center F.U ∧
      F.W=(centralizer ({t} : Set F.U)).map F.U.subtype := by
  classical
  have hV : Nat.card V=4 := by simpa only [F.last,show (2:ℕ)^2=4 from rfl] using F.card 2 le_rfl
  have hpoint : Nat.card (F.Vi 1)=2 := by simpa using F.card 1 (by omega)
  have hnle : ¬ V ≤ F.Vi 1 := by
    intro hh
    have hc := card_le_of_le hh
    omega
  obtain ⟨t,ht,hnt⟩ := SetLike.not_le_iff_exists.mp hnle
  have htU : t ∈ F.U := (show V ≤ F.U from le_conjugateSpanBy V F.H) ht
  let u : F.U := ⟨t,htU⟩
  have hnc : u ∉ center F.U := by
    intro hh
    apply hnt
    rw [←hZ]
    exact mem_map_of_mem F.U.subtype hh
  have htne : t ≠ 1 := by intro hh; exact hnt (hh ▸ one_mem _)
  have ht2 : t^2=1 := elemPow_eq_one_of_isElementaryAbelian (A:=V) t ht
  have hu2 : orderOf u=2 := orderOf_eq_prime (Subtype.ext ht2)
    (fun hh => htne (congrArg Subtype.val hh))
  let B := zpowers t ⊔ F.Vi 1
  have hBV : B ≤ V := sup_le (zpowers_le.mpr ht) (F.le_seed 1)
  have hPB : F.Vi 1 ≤ B := le_sup_right
  have hBgt : 2 < Nat.card B := by
    by_contra! hc
    have he : F.Vi 1=B := eq_of_le_of_card_ge hPB (by omega)
    exact hnt (he.symm ▸ (show t ∈ B from
      (show zpowers t ≤ B from le_sup_left) (mem_zpowers t)))
  have hBdiv : Nat.card B ∣ 4 := hV ▸ card_dvd_of_le hBV
  have hBbound : Nat.card B ≤ 4 := hV ▸ card_le_of_le hBV
  have hBne3 : Nat.card B ≠ 3 := by intro hh; rw [hh] at hBdiv; norm_num at hBdiv
  have hB : B=V := eq_of_le_of_card_ge hBV (by omega)
  refine ⟨u,hu2,hnc,?_⟩
  apply le_antisymm
  · intro w hw
    refine ⟨⟨w,hw.1⟩,?_,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact (hw.2 t (F.last.symm ▸ ht)).symm
  · rintro w ⟨a,ha,rfl⟩
    refine ⟨a.property,?_⟩
    have hat : t * (a:G)=(a:G) * t := by
      have hh := congrArg Subtype.val (mem_centralizer_singleton_iff.mp ha)
      exact hh.symm
    have hPC : F.Vi 1 ≤ centralizer ({(a:G)} : Set G) := by
      intro z hz
      obtain ⟨c,hc,hcz⟩ := (show z ∈ (center F.U).map F.U.subtype from
        (show z ∈ F.ZU from hZ.symm ▸ hz))
      apply mem_centralizer_singleton_iff.mpr
      exact hcz ▸ congrArg Subtype.val (mem_center_iff.mp hc a).symm
    have hVC : V ≤ centralizer ({(a:G)} : Set G) := by
      have hh : B ≤ centralizer ({(a:G)} : Set G) :=
        sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hat)) hPC
      exact hB.symm.le.trans hh
    intro z hz
    exact mem_centralizer_singleton_iff.mp (hVC (F.last ▸ hz))

/-- Involution generation of the actual W follows from the full original
orthogonal realization; no replacement for W is introduced. -/
theorem W_involution_generated_of_full_orthogonal (F : InvariantFlag T V 2)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F) (hZ : F.ZU=F.Vi 1) (hne : ¬ IsMulCommutative F.U)
    (hr : ChapterG.Section09.FittingRecognition.OrthogonalRealization F.terminalRepresentation ⊤) :
    closure {x : F.W | x^2=1}=⊤ := by
  obtain ⟨dU⟩ := quaternion_closure_of_full_orthogonal F d hZ hne hr
  obtain ⟨t,ht,hnc,hW⟩ := W_as_involution_centralizer_of_center_point F hZ
  exact block_W_involution_generated F dU t ht hnc hW
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition


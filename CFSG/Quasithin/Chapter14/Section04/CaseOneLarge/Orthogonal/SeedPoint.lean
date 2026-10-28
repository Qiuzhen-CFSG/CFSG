module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.SingularPoint
public import Theory.Representation.OrthogonalFourPlusMatrix.SylowSingularLine

/-!
# The original seed is a singular F₄-point

A binary plane invariant under a Sylow subgroup of SL₂(4) × SL₂(4)
is the fixed coefficient line. Indeed, a nonzero lower row generates
an entire two-dimensional binary displacement space under the first
upper unipotent group; equality with the plane would force that row
to vanish. The second factor gives the analogous column argument.
Sylow conjugacy transports this calculation to the original actor.

The original Sylow subgroup normalizes V, and V/Z(U) has order four.
Consequently its marked image is exactly the F₄-span of the same zᵍ
constructed in SingularPoint. This proves the seed-point identification
in 14.4.9 without assuming a Borel marking. The literal original quotient,
field coordinates, conjugator and O₂(H)=U conclusion are retained.
The escaping involution and subsequent diagonal-action construction remain
separate source deductions.

Source: Aschbacher--Smith, Lemma 14.4.9, printed pp.1009--1010;
refs/quasithin.pdf.
-/

public noncomputable section
open Matrix Subgroup Module Representation Representation.BinaryOffender
open ClassicalOrthogonal.FourPlusMatrix
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal

private theorem row_zero (W : Submodule (ZMod 2) Binary.V)
    (hd : finrank (ZMod 2) W = 2)
    (hstable : ∀ c : Binary.F, ∀ v ∈ W,
      Binary.action (Representation.SL2FourNatural.upper c,1) v ∈ W)
    (v : Binary.V) (hv : v ∈ W) : ∀ j, v 1 j = 0 := by
  by_contra hn
  obtain ⟨j,hj⟩ := not_forall.mp hn
  let N : Binary.V := !![v 1 0,v 1 1;0,0]
  have hN : N ≠ 0 := by
    intro h
    have hh := congrArg (fun M : Binary.V => M 0 j) h
    apply hj
    fin_cases j <;> simpa [N] using hh
  let f : Binary.F →ₗ[ZMod 2] Binary.V :=
    (LinearMap.toSpanSingleton Binary.F Binary.V N).restrictScalars (ZMod 2)
  have hf (c : Binary.F) : f c =
      Binary.action (Representation.SL2FourNatural.upper c,1) v - v := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [f,N,Binary.action_apply,Representation.SL2FourNatural.upper,
        Matrix.vecMul, dotProduct,Fin.sum_univ_two,add_sub_cancel_left]
  have hle : f.range ≤ W := by
    rintro _ ⟨c,rfl⟩
    rw [hf]
    exact W.sub_mem (hstable c v hv) hv
  have heq : f.range = W := Submodule.eq_of_le_of_finrank_eq hle (by
    rw [LinearMap.finrank_range_of_inj (smul_left_injective Binary.F hN),Binary.finrank_field,hd])
  obtain ⟨c,hc⟩ := (heq.symm ▸ hv : v ∈ f.range)
  have hh := congrArg (fun M : Binary.V => M 1 j) hc
  apply hj
  fin_cases j <;> simpa [f,N] using hh.symm

private theorem col_zero (W : Submodule (ZMod 2) Binary.V)
    (hd : finrank (ZMod 2) W = 2)
    (hstable : ∀ c : Binary.F, ∀ v ∈ W,
      Binary.action (1,(Representation.SL2FourNatural.upper c)⁻¹) v ∈ W)
    (v : Binary.V) (hv : v ∈ W) : ∀ i, v i 0 = 0 := by
  by_contra hn
  obtain ⟨i,hi⟩ := not_forall.mp hn
  let N : Binary.V := !![0,v 0 0;0,v 1 0]
  have hN : N ≠ 0 := by
    intro h
    have hh := congrArg (fun M : Binary.V => M i 1) h
    apply hi
    fin_cases i <;> simpa [N] using hh
  let f : Binary.F →ₗ[ZMod 2] Binary.V :=
    (LinearMap.toSpanSingleton Binary.F Binary.V N).restrictScalars (ZMod 2)
  have hf (c : Binary.F) : f c =
      Binary.action (1,(Representation.SL2FourNatural.upper c)⁻¹) v - v := by
    rw [Binary.action_apply,inv_inv]
    change f c = (1 : Binary.V) * v * (Representation.SL2FourNatural.upper c).val - v
    rw [one_mul]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [f,N,Representation.SL2FourNatural.upper,
        Matrix.mul_apply,Fin.sum_univ_two,mul_comm]
  have hle : f.range ≤ W := by
    rintro _ ⟨c,rfl⟩
    rw [hf]
    exact W.sub_mem (hstable c v hv) hv
  have heq : f.range = W := Submodule.eq_of_le_of_finrank_eq hle (by
    rw [LinearMap.finrank_range_of_inj (smul_left_injective Binary.F hN),Binary.finrank_field,hd])
  obtain ⟨c,hc⟩ := (heq.symm ▸ hv : v ∈ f.range)
  have hh := congrArg (fun M : Binary.V => M i 0) hc
  apply hi
  fin_cases i <;> simpa [f,N] using hh.symm

private theorem stable_plane_le_point (W : Submodule (ZMod 2) Binary.V)
    (hd : finrank (ZMod 2) W = 2)
    (hstable : ∀ a ∈ (Binary.upperPairSylow : Subgroup Binary.G),
      ∀ v ∈ W, Binary.action a v ∈ W) : W ≤ Binary.point := by
  have hu (c : Binary.F) : Representation.SL2FourNatural.upper c ∈
      SpecialLinearGroup.upperUnipotent Binary.F := by
    refine ⟨Multiplicative.ofAdd c,?_⟩
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [SpecialLinearGroup.upperUnipotentHom,SpecialLinearGroup.transvection_coe,
        Representation.SL2FourNatural.upper]
  intro v hv
  have hr := row_zero W hd (fun c => hstable _ ⟨hu c,one_mem _⟩) v hv
  have hc := col_zero W hd (fun c => hstable _ ⟨one_mem _,
    (SpecialLinearGroup.upperUnipotent Binary.F).inv_mem (hu c)⟩) v hv
  refine ⟨v 0 1,?_⟩
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Binary.pointMap,hr,hc]

private theorem stable_plane_scalar (P : Sylow 2 Binary.G)
    (W : Submodule (ZMod 2) Binary.V) (hd : finrank (ZMod 2) W = 2)
    (hstable : ∀ a ∈ P, ∀ v ∈ W, Binary.action a v ∈ W) :
    ∀ c : Binary.F, ∀ v ∈ W, c • v ∈ W := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Binary.G Binary.upperPairSylow P
  let W' := W.map (Binary.action g⁻¹)
  have hd' : finrank (ZMod 2) W' = 2 :=
    ((Binary.linearAction g⁻¹).finrank_map_eq W).trans hd
  have hm (a b : Binary.G) (v : Binary.V) :
      Binary.action (a*b) v = Binary.action a (Binary.action b v) :=
    congrArg (fun f : Module.End (ZMod 2) Binary.V => f v) (Binary.action.map_mul a b)
  have hs (a : Binary.G) (ha : a ∈ (Binary.upperPairSylow : Subgroup Binary.G))
      (v : Binary.V) (hv : v ∈ W') : Binary.action a v ∈ W' := by
    obtain ⟨w,hw,rfl⟩ := hv
    have ha' : g*a*g⁻¹ ∈ P := by
      rw [←hg]
      change g*a*g⁻¹ ∈ MulAut.conj g • (Binary.upperPairSylow : Set Binary.G)
      exact ⟨a,ha,rfl⟩
    refine ⟨Binary.action (g*a*g⁻¹) w,hstable _ ha' w hw,?_⟩
    rw [←hm,←hm]
    rw [mul_assoc g a g⁻¹,inv_mul_cancel_left]
  have hle := stable_plane_le_point W' hd' hs
  have hp : finrank (ZMod 2) Binary.point = 2 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Binary.point)
    rw [Binary.card_point,Nat.card_eq_fintype_card,ZMod.card] at hh
    exact (Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hh).symm
  have heq : W' = Binary.point := Submodule.eq_of_le_of_finrank_eq hle (hd'.trans hp.symm)
  intro c v hv
  have hv' : Binary.action g⁻¹ v ∈ Binary.point := heq ▸ ⟨v,hv,rfl⟩
  obtain ⟨a,ha⟩ := hv'
  have hc : c • Binary.action g⁻¹ v ∈ Binary.point := by
    refine ⟨c*a,?_⟩
    rw [←ha]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Binary.pointMap]
  rw [←heq] at hc
  obtain ⟨w,hw,he⟩ := hc
  have hsm : c • Binary.action g⁻¹ v = Binary.action g⁻¹ (c • v) :=
    ((matrixHom g⁻¹).map_smul c v).symm
  have hwv : w = c • v := (Binary.linearAction g⁻¹).injective (he.trans hsm)
  exact hwv ▸ hw

private theorem stable_plane_eq_field_line (P : Sylow 2 Binary.G)
    (W : Submodule (ZMod 2) Binary.V) (hd : finrank (ZMod 2) W = 2)
    (hstable : ∀ a ∈ P, ∀ v ∈ W, Binary.action a v ∈ W)
    (v : Binary.V) (hv : v ∈ W) (hv0 : v ≠ 0) :
    W = (Submodule.span Binary.F {v}).restrictScalars (ZMod 2) := by
  let f := (LinearMap.toSpanSingleton Binary.F Binary.V v).restrictScalars (ZMod 2)
  have hle : f.range ≤ W := by
    rintro _ ⟨c,rfl⟩
    exact stable_plane_scalar P W hd hstable c v hv
  have heq : f.range = W := Submodule.eq_of_le_of_finrank_eq hle (by
    rw [LinearMap.finrank_range_of_inj (smul_left_injective Binary.F hv0),Binary.finrank_field,hd])
  rw [←heq]
  ext w
  exact Submodule.mem_span_singleton.symm

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension CoreGeometry ClassicalOrthogonal ClassicalOrthogonal.FourPlusMatrix
open scoped IsMulCommutative
universe u

private theorem orthogonal_plane_field_line
    {H : Type*} [Group H] [Finite H] {U : Subgroup H} [U.Normal]
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (d : RankCore.SourceAction H U M)
    (K : Subgroup (H ⧸ pCore 2 H)) [K.Normal]
    (κ : K ≃* OmegaPlus 2 Binary.F) (e : M ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : ∀ (k : K) v, e (d.representation k v) =
      subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v))
    (T : Sylow 2 H) (A : Subgroup H)
    (hn : (T : Subgroup H) ≤ normalizer (A : Set H))
    (hd : finrank (ZMod 2) (d.image A) = 2)
    (v : M) (hv : v ∈ d.image A) (hv0 : v ≠ 0) :
    (d.image A).map e.toLinearMap =
      (Submodule.span Binary.F {e v}).restrictScalars (ZMod 2) := by
  let S := T.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal K
  let κm : K ≃* Binary.G := κ.trans elementaryEquiv.symm
  let E := e.trans Binary.binaryCoordinates
  have hm (k : K) (w : M) : E (d.representation k w) = Binary.action (κm k) (E w) := by
    change Binary.binaryCoordinates (e (d.representation k w)) = _
    rw [he]
    obtain ⟨a,ha⟩ := elementaryEquiv.surjective (κ k)
    have hκ : κm k = a := by
      change elementaryEquiv.symm (κ k) = a
      rw [←ha,elementaryEquiv.symm_apply_apply]
    rw [←ha,hκ]
    exact toOrthogonal_coordinates a (e w)
  have hs (k : K) (hk : k ∈ P) (w : M) (hw : w ∈ d.image A) :
      d.representation k w ∈ d.image A := by
    change k ∈ (P : Subgroup K) at hk
    rw [hP] at hk
    change (k : H ⧸ pCore 2 H) ∈ (T : Subgroup H).map (QuotientGroup.mk' (pCore 2 H)) at hk
    obtain ⟨t,ht,heq⟩ := hk
    rw [←heq]
    have hle : d.image A ≤ (d.image A).comap (d.representation (QuotientGroup.mk' (pCore 2 H) t)) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨a,ha,rfl⟩
      change d.representation (QuotientGroup.mk' (pCore 2 H) t) (d.vector a) ∈ d.image A
      rw [←d.conjugation]
      exact d.vector_mem_image A _ ((mem_normalizer_iff.mp (hn ht) (a : H)).mp ha)
    exact hle hw
  let W := (d.image A).map E.toLinearMap
  have hW := stable_plane_eq_field_line
    (P.mapSurjective (f := κm.toMonoidHom) κm.surjective) W
    ((E.finrank_map_eq _).trans hd) (by
      intro a ha w hw
      obtain ⟨k,hk,rfl⟩ := ha
      obtain ⟨y,hy,rfl⟩ := hw
      refine ⟨d.representation k y,hs k hk y hy,hm k y⟩)
    (E v) ⟨v,hv,rfl⟩ (fun hz => hv0 (E.injective (hz.trans E.map_zero.symm)))
  apply Submodule.map_injective_of_injective Binary.binaryCoordinates.injective
  rw [←Submodule.map_comp]
  change W = _
  rw [hW]
  ext w
  constructor
  · intro hw
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hw
    refine ⟨c • e v,Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _),?_⟩
    change coordinates (c • e v) = w
    rw [map_smul]
    exact hc
  · rintro ⟨w,hw,rfl⟩
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hw
    exact Submodule.mem_span_singleton.mpr ⟨c,((coordinates (F := Binary.F)).map_smul c (e v)).symm⟩

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable [IsMulCommutative V]
local instance (F : InvariantFlag T V 3) : (F.U.subgroupOf F.H).Normal := F.U_normal

/-- The original seed has precisely the totally singular F₄-point image
through the original right conjugate zᵍ. No seed-point equality, scalar
closure or Sylow-fixed-plane hypothesis is added to the source inputs. -/
theorem source_orthogonal_seed_point (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : letI := chosen.elementary
      letI := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v)) :
    F.H.pCoreIn 2 = F.U ∧ Nat.card V = 8 ∧ Nat.card (hatSpace F V) = 4 ∧
      ∃ z : G, orderOf z = 2 ∧ F.Vi 1 = zpowers z ∧
        F.H = centralizer ({z} : Set G) ∧
        ∃ hs : MulAut.conj g⁻¹ z ∈ F.U,
          let v := e (hatElement F ⟨MulAut.conj g⁻¹ z,hs⟩)
          MulAut.conj g⁻¹ z ∈ F.Vi 2 ∧ v ≠ 0 ∧
          formD 2 Binary.F v = 0 ∧
          (hatSpace F (F.Vi 2)).map e.toLinearMap = Submodule.span (ZMod 2) {v} ∧
          (hatSpace F V).map e.toLinearMap =
            (Submodule.span Binary.F {v}).restrictScalars (ZMod 2) ∧
          ∀ w ∈ (hatSpace F V).map e.toLinearMap, formD 2 Binary.F w = 0 := by
  let := chosen.elementary
  obtain ⟨hcore,hV,hhat,z,hzo,hzp,hH,hs,hs₂,hv0,hqv,hline,hsing⟩ :=
    source_orthogonal_singular_point d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he
  let hk := source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ
  have hd : finrank (ZMod 2) (hatSpace F V) = 2 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := hatSpace F V)
    rw [hhat,Nat.card_zmod] at hh
    exact (Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hh).symm
  have hn : ((T.subtype (F.invariant 1) : Sylow 2 F.H) : Subgroup F.H) ≤
      normalizer (V.subgroupOf F.H : Set F.H) := by
    intro t ht
    apply mem_normalizer_iff.mpr
    intro v
    have htV : (t : G) ∈ normalizer (V : Set G) := by simpa [F.last] using F.invariant 3 ht
    exact mem_normalizer_iff.mp htV (v : G)
  let K := (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))
  let : K.Normal := (inferInstance : (pResidual 2 F.H).Normal).map _ (QuotientGroup.mk'_surjective _)
  have hp := orthogonal_plane_field_line (sourceAction F hk) K κ e he
    (T.subtype (F.invariant 1)) (V.subgroupOf F.H) hn
    (by rw [sourceAction_image]; exact hd)
    (hatElement F ⟨MulAut.conj g⁻¹ z,hs⟩)
    (by rw [sourceAction_image]; exact ⟨⟨_,hs⟩,F.le_seed 2 hs₂,rfl⟩)
    (fun hh => hv0 (hh ▸ e.map_zero))
  rw [sourceAction_image] at hp
  refine ⟨hcore,hV,hhat,z,hzo,hzp,hH,hs,hs₂,hv0,hqv,hline,hp,?_⟩
  intro w hw
  rw [hp] at hw
  exact hsing w hw

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal

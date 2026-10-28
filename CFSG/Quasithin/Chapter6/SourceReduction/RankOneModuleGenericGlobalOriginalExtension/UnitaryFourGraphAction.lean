module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.UnitaryFourGraphLift
public import Theory.Representation.OrthogonalFourMinusRankOne.AmbientActions.ScalarCentralizer

/-!
# The full graph action on the original U₄ plane residual

An involutory automorphism inducing the specified quadratic quotient action
has the canonical action on the entire Hermitian two-core, by scalar
rigidity. Hermitian H¹ then corrects its remaining displacement by a core
element, so its action on the whole plane residual is the native graph
involution. Applying this to the already constructed original lift corrects
it inside the same O₂(L); its square vanishes in the proved C_S(L)=1.

The full original LS action is faithful and has exactly the inner-plus-graph
image. This constructs an isomorphism with the concrete native plane
residual semidirect C₂, preserving every element of the supplied residual
coordinates and the specified graph generator. Relative Sylow conjugacy
places an actual involution in the literal S, with its entire residual action
and its exact conjugate graph image retained under the same equivalence.

The results apply to every selected perfect R, either original orientation
and q=4. They assume the broad original marking, not a pure comparison,
core equality, S=T or R=O²(H). Both full endpoint maps and the whole odd
Borel squares still require assembly. The Chapter 12 application uses
reduced DGS restoration and the completed ordinary branch; DGS exhaustion,
prepared U₅, uniqueness and unconditional GlobalExit remain necessary.
Source: Aschbacher--Smith F.1.12, pp.263--264, I.1.6(3), p.408,
and 5.2.6--7, pp.650--651 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
open Representation.OrthogonalFourMinus.FiniteModel
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.OriginalUnitaryFour.GraphAction

private theorem graph_sq (m : ℕ) (hm : 1 ≤ m) : Extension.L2Aut m hm ^ 2=1 := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  have hh := DFunLike.congr_fun (Extension.projectiveAut_sq m hm) x.val
  change (Extension.L2Aut m hm (Extension.L2Aut m hm x)).val=x.val
  rw [Extension.L2Aut_val,Extension.L2Aut_val]
  exact hh

private theorem graph_field (m : ℕ) (hm : 1 ≤ m)
    (x : L2 m hm ⧸ pCore 2 (L2 m hm)) :
    L2QuotientEquivSL2 m hm (Extension.L2QuotientAut m hm x) =
      Matrix.SpecialLinearGroup.map (conjugation m).toRingHom (L2QuotientEquivSL2 m hm x) := by
  change planeSL2Equiv m (Extension.L2QuotientEquivMatrixSL2 m hm (Extension.L2QuotientAut m hm x)) = _
  rw [Extension.L2QuotientAut_field]
  ext i j
  exact planeFieldEquiv_conj m _

private def coreAddAut (m : ℕ) (hm : 1 ≤ m) [NeZero m] (α : MulAut (L2 m hm)) :
    Space m ≃+ Space m :=
  (MulAut.congr (L2TwoCoreEquiv m hm).symm ((MulAut.characteristic (pCore 2 (L2 m hm))) α)).toAdditive

private theorem coreAddAut_val (m : ℕ) (hm : 1 ≤ m) [NeZero m]
    (α : MulAut (L2 m hm)) (v : Space m) :
    (L2TwoCoreEquiv m hm (Multiplicative.ofAdd (coreAddAut m hm α v))).val =
      α (L2TwoCoreEquiv m hm (Multiplicative.ofAdd v)).val := by
  change ((L2TwoCoreEquiv m hm) ((L2TwoCoreEquiv m hm).symm _)).val = _
  rw [MulEquiv.apply_symm_apply]
  rfl

private theorem coreAddAut_graph (m : ℕ) (hm : 1 ≤ m) [NeZero m]
    (α : MulAut (L2 m hm)) (hsq : α^2=1)
    (hq : quotientAut (pCore 2 (L2 m hm)) α=Extension.L2QuotientAut m hm) :
    ∀ v, coreAddAut m hm α v =
      Representation.OrthogonalFourMinus.HermitianEquiv.conjugationLinear m v := by
  let Q := pCore 2 (L2 m hm)
  let e := L2TwoCoreEquiv m hm
  let q := L2QuotientEquivSL2 m hm
  let f := q.toMonoidHom.comp (QuotientGroup.mk' Q)
  have hfield (g : L2 m hm) : f (α g)=Matrix.SpecialLinearGroup.map (conjugation m).toRingHom (f g) := by
    have hh := congrArg q (DFunLike.congr_fun hq (QuotientGroup.mk' Q g))
    rw [quotientAut_apply_mk] at hh
    exact hh.trans (graph_field m hm _)
  apply Representation.OrthogonalFourMinus.RankOne.AmbientActions.involutive_field_lift_eq_conjugation
    m (coreAddAut m hm α).toAddMonoidHom
  · intro v
    apply Multiplicative.ofAdd.injective
    apply e.injective
    apply Subtype.ext
    exact (coreAddAut_val m hm α _).trans
      ((congrArg α (coreAddAut_val m hm α v)).trans (DFunLike.congr_fun hsq _))
  · intro a v
    obtain ⟨g,rfl⟩ := q.surjective.comp (QuotientGroup.mk'_surjective Q) a
    apply Multiplicative.ofAdd.injective
    apply e.injective
    apply Subtype.ext
    have he (g : L2 m hm) (v : Space m) :
        (e (Multiplicative.ofAdd (action m (f g) v))).val =
          g*(e (Multiplicative.ofAdd v)).val*g⁻¹ :=
      (congrArg Subtype.val (L2TwoCoreEquiv_conj m hm g (Multiplicative.ofAdd v))).symm
    calc
      _ = α (e (Multiplicative.ofAdd (action m (f g) v))).val := coreAddAut_val m hm α _
      _ = α g * α (e (Multiplicative.ofAdd v)).val * (α g)⁻¹ := by rw [he,map_mul,map_mul,map_inv]
      _ = α g * (e (Multiplicative.ofAdd (coreAddAut m hm α v))).val * (α g)⁻¹ :=
        congrArg (fun z => α g*z*(α g)⁻¹) (coreAddAut_val m hm α v).symm
      _ = (e (Multiplicative.ofAdd (action m (f (α g)) (coreAddAut m hm α v)))).val := (he _ _).symm
      _ = _ := congrArg (fun z => (e (Multiplicative.ofAdd
        (action m z (coreAddAut m hm α v)))).val) (hfield g)

/-- Involutory lifts of the same graph quotient differ only by an inner
core automorphism on the entire plane residual. -/
theorem plane_graph_correction (m : ℕ) (hm : 1 ≤ m)
    (α : MulAut (L2 m hm)) (hsq : α^2=1)
    (hq : quotientAut (pCore 2 (L2 m hm)) α=Extension.L2QuotientAut m hm) :
    ∃ v : pCore 2 (L2 m hm), MulAut.conj v.val * α=Extension.L2Aut m hm := by
  let : NeZero m := ⟨by omega⟩
  let Q := pCore 2 (L2 m hm)
  let q := L2QuotientEquivSL2 m hm
  let f := q.toMonoidHom.comp (QuotientGroup.mk' Q)
  let e := (L2TwoCoreEquiv m hm).symm
  let β := Extension.L2Aut m hm
  have hβ : quotientAut Q β=Extension.L2QuotientAut m hm := by
    apply MulEquiv.ext
    intro x
    induction x using QuotientGroup.induction_on with
    | H x =>
      exact (quotientAut_apply_mk Q β x).trans
        (QuotientGroup.congr_mk Q Q β (pCore_map_iso 2 β) x).symm
  have hcore (x : Q) : α x.val=β x.val := by
    obtain ⟨v,rfl⟩ := (L2TwoCoreEquiv m hm).surjective x
    have he := (coreAddAut_graph m hm α hsq hq v.toAdd).trans
      (coreAddAut_graph m hm β (graph_sq m hm) hβ v.toAdd).symm
    exact (coreAddAut_val m hm α v.toAdd).symm.trans
      ((congrArg (fun w : Space m => (L2TwoCoreEquiv m hm (Multiplicative.ofAdd w)).val) he).trans
        (coreAddAut_val m hm β v.toAdd))
  let δ := α*β⁻¹
  have hδ : quotientAut Q δ=1 := by
    change quotientAut Q (α*β⁻¹)=1
    rw [map_mul,map_inv,hq,hβ,mul_inv_cancel]
  have hf (g : L2 m hm) : f (δ g)=f g := by
    have hh := DFunLike.congr_fun hδ (QuotientGroup.mk' Q g)
    rw [quotientAut_apply_mk] at hh
    exact congrArg q hh
  have hfix (x : L2 m hm) (hx : x ∈ Q) : δ x=x := by
    have hmem : β⁻¹ x ∈ Q := by
      change β.symm x ∈ pCore 2 (L2 m hm)
      rw [←pCore_map_iso 2 β.symm]
      exact mem_map_of_mem β.symm.toMonoidHom hx
    change α (β⁻¹ x)=x
    rw [hcore ⟨_,hmem⟩]
    exact β.apply_symm_apply x
  have he (g : L2 m hm) (v : Space m) :
      (e.symm (Multiplicative.ofAdd (action m (f g) v)) : L2 m hm) =
        g*(e.symm (Multiplicative.ofAdd v) : L2 m hm)*g⁻¹ :=
    (congrArg Subtype.val (L2TwoCoreEquiv_conj m hm g (Multiplicative.ofAdd v))).symm
  let : Subsingleton (Representation.OneCohomology.H1 (action m)) := action_H1_subsingleton m
  obtain ⟨v,hv⟩ := Representation.OneCohomology.automorphism_inner_of_H1_zero Q f
    (q.surjective.comp (QuotientGroup.mk'_surjective Q))
    (by rw [MonoidHom.ker_comp_of_injective _ _ q.injective,QuotientGroup.ker_mk'])
    e (action m) he δ hf hfix
  refine ⟨v,?_⟩
  apply MulEquiv.ext
  intro x
  have hh := hv (β x)
  change α (β.symm (β x))=v.val⁻¹*β x*v.val at hh
  rw [β.symm_apply_apply] at hh
  change v.val*α x*v.val⁻¹=β x
  rw [hh]
  group

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.OriginalUnitaryFour.GraphAction

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
open ChapterF.GreenBook.LieModels.UnitaryFour

private theorem quotient_action_congr {X Y : Type*} [Group X] [Group Y]
    (a : X ≃* Y) (α : MulAut X) :
    quotientAut (pCore 2 Y) (MulAut.congr a α) =
      MulAut.congr (QuotientGroup.congr _ _ a (pCore_map_iso 2 a))
        (quotientAut (pCore 2 X) α) := by
  let q := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  apply MulEquiv.ext
  intro z
  obtain ⟨x,rfl⟩ := q.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 X)) z
  change quotientAut (pCore 2 Y) (MulAut.congr a α) (q (QuotientGroup.mk' (pCore 2 X) x)) =
    q (quotientAut (pCore 2 X) α (q.symm (q (QuotientGroup.mk' (pCore 2 X) x))))
  rw [q.symm_apply_apply]
  have hq (y : X) : q (QuotientGroup.mk' (pCore 2 X) y) =
      QuotientGroup.mk' (pCore 2 Y) (a y) :=
    QuotientGroup.congr_mk' _ _ a (pCore_map_iso 2 a) y
  rw [hq,quotientAut_apply_mk,quotientAut_apply_mk,hq]
  apply congrArg (QuotientGroup.mk' (pCore 2 Y))
  change a (α (a.symm (a x)))=a (α x)
  rw [a.symm_apply_apply]

private theorem conjugation_square {X : Type*} [Group X]
    (K : Subgroup X) (t : X) (ht : t ∈ normalizer (K : Set X)) (hsq : t^2=1) :
    (K.normalizerMonoidHom ⟨t,ht⟩)^2=1 := by
  have he : (⟨t,ht⟩ : normalizer (K : Set X))^2=1 := Subtype.ext hsq
  rw [←map_pow,he,map_one]

variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  (m : ℕ) (hm : 1 ≤ m) (point : Bool)
  (mark : OriginalUnitaryFour.Marking m hm point L R (sourceS L H))
include d h hTH hp mark

/-- The graph quotient lift can be corrected inside the same O₂(L) so
its action on the entire original L is the literal native graph action.
The residual equivalence may be specified in advance. -/
theorem original_unitaryFour_full_graph_action
    (a : L ≃* L2 m hm)
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=2) :
    ∃ t : (L ⊔ sourceS L H : Subgroup G), t.val ∉ L ∧ orderOf t.val=2 ∧
      ∀ x : L, (a.symm (Extension.L2Aut m hm (a x))).val=t.val*x.val*t.val⁻¹ := by
  let J := L ⊔ sourceS L H
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let q := aq.trans (OriginalUnitaryFour.planeQuotient m hm)
  have hn : J ≤ normalizer (L : Set G) := sup_le L.le_normalizer
    ((sourceS_le_sylow h.sylow_normalizes hTH).trans h.sylow_normalizes)
  obtain ⟨t,hout,ht,hact⟩ := d.original_unitaryFour_graph_involution h hTH hp m hm point mark q hi
  let c := L.normalizerMonoidHom ⟨t.val,hn t.property⟩
  let α := MulAut.congr a c
  have hcsq : c^2=1 := conjugation_square L t.val (hn t.property)
    (by simpa only [ht] using pow_orderOf_eq_one t.val)
  have hαsq : α^2=1 := by rw [←map_pow,hcsq,map_one]
  have hq : quotientAut (pCore 2 (L2 m hm)) α=Extension.L2QuotientAut m hm := by
    rw [quotient_action_congr]
    apply (MulAut.congr (OriginalUnitaryFour.planeQuotient m hm)).injective
    calc
      _ = MulAut.congr q (quotientAut (pCore 2 L) c) := by
        apply MulEquiv.ext
        intro x
        rfl
      _ = _ := hact
  obtain ⟨v,hv⟩ := OriginalUnitaryFour.GraphAction.plane_graph_correction m hm α hαsq hq
  let u : L := a.symm v.val
  have hu : u ∈ pCore 2 L := by
    rw [←pCore_map_iso 2 a.symm]
    exact mem_map_of_mem a.symm.toMonoidHom v.property
  let s : J := ⟨u.val*t.val,J.mul_mem ((show L ≤ J from le_sup_left) u.property) t.property⟩
  have huG : u.val ∈ L.pCoreIn 2 := mem_map_of_mem L.subtype hu
  have hfull (x : L) : (a.symm (Extension.L2Aut m hm (a x))).val=s.val*x.val*s.val⁻¹ := by
    have hh := DFunLike.congr_fun hv (a x)
    change v.val*a (c (a.symm (a x)))*v.val⁻¹=Extension.L2Aut m hm (a x) at hh
    rw [a.symm_apply_apply] at hh
    have hh' := congrArg (fun z : L2 m hm => (a.symm z).val) hh.symm
    simp only [map_mul,map_inv,a.symm_apply_apply,coe_mul,coe_inv] at hh'
    change (a.symm (Extension.L2Aut m hm (a x))).val = u.val*(c x).val*u.val⁻¹ at hh'
    rw [normalizerMonoidHom_apply_apply_coe] at hh'
    exact hh'.trans (by dsimp [s]; group)
  have hsout : s.val ∉ L := by
    intro hsL
    have hh := L.mul_mem (L.inv_mem u.property) hsL
    exact hout (by simpa only [s,inv_mul_cancel_left] using hh)
  have hsQ : s.val^2 ∈ L.pCoreIn 2 := by
    have htu := (mem_normalizer_iff.mp
      (normalizer_le_normalizer_characteristic_image L (pCore 2 L) (hn t.property)) u.val).mp huG
    have he : s.val^2=u.val*(t.val*u.val*t.val⁻¹) := by
      have ht2 : t.val^2=1 := by simpa only [ht] using pow_orderOf_eq_one t.val
      calc
        s.val^2 = u.val*(t.val*u.val*t.val⁻¹)*t.val^2 := by dsimp [s]; simp only [pow_two]; group
        _ = _ := by rw [ht2,mul_one]
    rw [he]
    exact (L.pCoreIn 2).mul_mem huG htu
  have hsC : s.val^2 ∈ centralizer (L : Set G) := by
    apply mem_centralizer_iff.mpr
    intro x hx
    let l : L := ⟨x,hx⟩
    have he := hfull (a.symm (Extension.L2Aut m hm (a l)))
    rw [a.apply_symm_apply] at he
    have hβ := DFunLike.congr_fun (OriginalUnitaryFour.GraphAction.graph_sq m hm) (a l)
    change Extension.L2Aut m hm (Extension.L2Aut m hm (a l))=a l at hβ
    rw [hβ,a.symm_apply_apply,hfull l] at he
    have he' : s.val^2*x*(s.val^2)⁻¹=x := by
      calc
        _ = s.val*(s.val*x*s.val⁻¹)*s.val⁻¹ := by simp only [pow_two]; group
        _ = x := he.symm
    exact (mul_inv_eq_iff_eq_mul.mp he').symm
  have hQS : L.pCoreIn 2 ≤ sourceS L H := by
    rw [←d.original_unitaryFour_left_core_eq h hTH hp m hm point mark]
    exact d.original_left_core_le_sourceS h hTH
  have hs2 : s.val^2=1 := mem_bot.mp
    ((d.original_unitaryFour_residual_centralizer_eq_bot h hTH hp m hm point mark).le ⟨hQS hsQ,hsC⟩)
  exact ⟨s,hsout,orderOf_eq_prime hs2 (fun he => hsout (he ▸ L.one_mem)),hfull⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour
namespace OriginalUnitaryFour
/-- The native plane residual with its specified graph automorphism. -/
@[expose] def planeGraphGroup (m : ℕ) (hm : 1 ≤ m) : Subgroup (MulAut (L2 m hm)) :=
  MulAut.innerSubgroup (L2 m hm) ⊔ zpowers (Extension.L2Aut m hm)
end OriginalUnitaryFour
namespace Preparation
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  (m : ℕ) (hm : 1 ≤ m) (point : Bool)
  (mark : OriginalUnitaryFour.Marking m hm point L R (sourceS L H))
  (a : L ≃* L2 m hm)

/-- The action of the whole original LS on the entire marked plane residual. -/
@[expose] def originalUnitaryFourResidualAction : (L ⊔ sourceS L H : Subgroup G) →* MulAut (L2 m hm) :=
  (MulAut.congr a).toMonoidHom.comp (L.normalizerMonoidHom.comp (inclusion
    (sup_le L.le_normalizer ((sourceS_le_sylow h.sylow_normalizes hTH).trans h.sylow_normalizes))))

/-- Original residual elements act by their exact native inner automorphisms. -/
theorem originalUnitaryFourResidualAction_left (x : L) :
    originalUnitaryFourResidualAction h hTH m hm a (inclusion le_sup_left x)=MulAut.conj (a x) := by
  change MulAut.congr a (L.normalizerMonoidHom _) = _
  have hc : L.normalizerMonoidHom ⟨x.val,L.le_normalizer x.property⟩ = MulAut.conj x := by
    apply MulEquiv.ext
    intro y
    rfl
  exact (congrArg (MulAut.congr a) hc).trans (MulAut.congr_conj a x)

include d h hTH hp mark in
/-- The full residual action is faithful on the same original LS. -/
theorem originalUnitaryFourResidualAction_injective :
    Function.Injective (originalUnitaryFourResidualAction h hTH m hm a) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro t ht
  have he : L.normalizerMonoidHom ⟨t.val,
      (sup_le L.le_normalizer ((sourceS_le_sylow h.sylow_normalizes hTH).trans h.sylow_normalizes)) t.property⟩=1 :=
    (MulAut.congr a).injective (ht.trans (map_one _).symm)
  have hc : t.val ∈ centralizer (L : Set G) := by
    apply mem_centralizer_iff.mpr
    intro x hx
    have hh := congrArg Subtype.val (DFunLike.congr_fun he (⟨x,hx⟩ : L))
    rw [normalizerMonoidHom_apply_apply_coe] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hcQ : t.val ∈ centralizer (L.pCoreIn 2 : Set G) :=
    centralizer_le (show (L.pCoreIn 2 : Set G) ⊆ L from pCoreIn_le 2 L) hc
  have htQ : t.val ∈ (L ⊔ sourceS L H).pCoreIn 2 :=
    (d.original_unitaryFour_left_core_eq_centralizer h hTH hp m hm point mark).ge ⟨t.property,hcQ⟩
  apply mem_bot.mpr
  apply Subtype.ext
  exact mem_bot.mp ((d.original_unitaryFour_residual_centralizer_eq_bot h hTH hp m hm point mark).le
    ⟨d.original_left_core_le_sourceS h hTH htQ,hc⟩)

include d h hTH hp mark in
/-- The graph generator is realized exactly on the whole residual, in the
faithful action of the same original LS. -/
theorem original_unitaryFour_residual_graph_generator
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=2) :
    ∃ t : (L ⊔ sourceS L H : Subgroup G), t.val ∉ L ∧ orderOf t.val=2 ∧
      originalUnitaryFourResidualAction h hTH m hm a t=Extension.L2Aut m hm := by
  obtain ⟨t,htL,ht,hfull⟩ := d.original_unitaryFour_full_graph_action h hTH hp m hm point mark a hi
  refine ⟨t,htL,ht,?_⟩
  apply MulEquiv.ext
  intro x
  apply a.symm.injective
  change a.symm (a ((L.normalizerMonoidHom _) (a.symm x))) = _
  rw [a.symm_apply_apply]
  apply Subtype.ext
  rw [normalizerMonoidHom_apply_apply_coe]
  have he := hfull (a.symm x)
  rw [a.apply_symm_apply] at he
  exact he.symm

include d h hTH hp mark in
/-- The image of the whole original LS is exactly the native graph extension
of the plane residual, not merely its quotient automorphism group. -/
theorem original_unitaryFour_residual_action_range
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=2) :
    (originalUnitaryFourResidualAction h hTH m hm a).range=OriginalUnitaryFour.planeGraphGroup m hm := by
  let J := L ⊔ sourceS L H
  let f := originalUnitaryFourResidualAction h hTH m hm a
  obtain ⟨t,htL,_,ht⟩ := d.original_unitaryFour_residual_graph_generator h hTH hp m hm point mark a hi
  have hidx : (L.subgroupOf J).index=2 := by
    let : (L.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
      (sup_le L.le_normalizer ((sourceS_le_sylow h.sylow_normalizes hTH).trans h.sylow_normalizes))
    have he := relIndex_sup_left ((sourceS L H).subgroupOf J) (L.subgroupOf J)
    rw [←subgroupOf_sup (show L ≤ J from le_sup_left)
      (show sourceS L H ≤ J from le_sup_right),relIndex_subgroupOf le_rfl,
      relIndex_subgroupOf (show sourceS L H ≤ J from le_sup_right)] at he
    change L.relIndex J=2
    rw [he,←inf_relIndex_right,inf_comm,d.left_intersection,hi]
  have hinner (x : J) (hx : x.val ∈ L) : f x ∈ OriginalUnitaryFour.planeGraphGroup m hm := by
    have he := originalUnitaryFourResidualAction_left h hTH m hm a (⟨x.val,hx⟩ : L)
    change f x=_ at he
    rw [he]
    exact (show MulAut.innerSubgroup (L2 m hm) ≤ OriginalUnitaryFour.planeGraphGroup m hm from le_sup_left)
      ⟨_,rfl⟩
  have htmem : f t ∈ OriginalUnitaryFour.planeGraphGroup m hm := by
    rw [ht]
    exact (show zpowers (Extension.L2Aut m hm) ≤ OriginalUnitaryFour.planeGraphGroup m hm from le_sup_right)
      (mem_zpowers _)
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    by_cases hx : x.val ∈ L
    · exact hinner x hx
    · have hxt : (x*t⁻¹).val ∈ L := (mul_mem_iff_of_index_two hidx).mpr
        (iff_of_false hx (by
          change t.val⁻¹ ∉ L
          simpa only [inv_mem_iff] using htL))
      have he : f x=f (x*t⁻¹)*f t := by rw [←map_mul,inv_mul_cancel_right]
      rw [he]
      exact (OriginalUnitaryFour.planeGraphGroup m hm).mul_mem (hinner _ hxt) htmem
  · apply sup_le
    · rintro _ ⟨x,rfl⟩
      obtain ⟨l,rfl⟩ := a.surjective x
      exact ⟨inclusion le_sup_left l,originalUnitaryFourResidualAction_left h hTH m hm a l⟩
    · exact zpowers_le.mpr ⟨t,ht⟩

/-- Exact recognition of the original left residual join with its native
graph action. The specified residual coordinates are retained pointwise. -/
def originalUnitaryFourGraphJoinEquiv
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=2) :
    (L ⊔ sourceS L H : Subgroup G) ≃* OriginalUnitaryFour.planeGraphGroup m hm :=
  (MonoidHom.ofInjective (d.originalUnitaryFourResidualAction_injective h hTH hp m hm point mark a)).trans
    (MulEquiv.subgroupCongr (d.original_unitaryFour_residual_action_range h hTH hp m hm point mark a hi))

theorem originalUnitaryFourGraphJoinEquiv_apply
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=2)
    (x : (L ⊔ sourceS L H : Subgroup G)) :
    (d.originalUnitaryFourGraphJoinEquiv h hTH hp m hm point mark a hi x).val =
      originalUnitaryFourResidualAction h hTH m hm a x := by rfl

theorem originalUnitaryFourGraphJoinEquiv_left
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=2) (x : L) :
    (d.originalUnitaryFourGraphJoinEquiv h hTH hp m hm point mark a hi (inclusion le_sup_left x)).val =
      MulAut.conj (a x) := originalUnitaryFourResidualAction_left h hTH m hm a x

include d h hTH hp mark in
/-- The actual source S contains an involution with the full residual graph
action, with its precise inner conjugating element of the same LS retained. -/
theorem original_unitaryFour_source_full_graph_involution
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=2) :
    ∃ t : sourceS L H, t.val ∉ L ∧ orderOf t.val=2 ∧
      ∃ c : (L ⊔ sourceS L H : Subgroup G),
        originalUnitaryFourResidualAction h hTH m hm a (inclusion le_sup_right t) =
          originalUnitaryFourResidualAction h hTH m hm a c * Extension.L2Aut m hm *
            (originalUnitaryFourResidualAction h hTH m hm a c)⁻¹ := by
  let J := L ⊔ sourceS L H
  obtain ⟨t,hout,ht,ha⟩ := d.original_unitaryFour_residual_graph_generator h hTH hp m hm point mark a hi
  have htJ : orderOf t=2 := (Subgroup.orderOf_coe t).symm.trans ht
  have hcyc : IsPGroup 2 (zpowers t) := IsPGroup.iff_card.mpr
    ⟨1,by rw [Nat.card_zpowers,htJ,pow_one]⟩
  have hs : Chapter1.IsSylowIn 2 (sourceS L H)
      (ChapterF.Source.parabolic ![L,R] (sourceS L H) 0) :=
    (d.hypothesisF11 h hTH).sylow_parabolic 0
  obtain ⟨P,hP⟩ := hs.restrict (show sourceS L H ≤ J from le_sup_right)
    (show J ≤ ChapterF.Source.parabolic ![L,R] (sourceS L H) 0 from le_sup_left)
  obtain ⟨Q,hQ⟩ := hcyc.exists_le_sylow
  obtain ⟨c,hc⟩ := MulAction.exists_smul_eq J Q P
  have hcP : c*t*c⁻¹ ∈ (P : Subgroup J) := by
    rw [←hc]
    exact ⟨t,hQ (mem_zpowers t),rfl⟩
  have hcS : (c : G)*t.val*(c : G)⁻¹ ∈ sourceS L H :=
    hP.le (mem_map_of_mem J.subtype hcP)
  let s : sourceS L H := ⟨(c : G)*t.val*(c : G)⁻¹,hcS⟩
  refine ⟨s,?_,?_,c,?_⟩
  · intro hL
    have hn : J ≤ normalizer (L : Set G) := sup_le L.le_normalizer
      ((sourceS_le_sylow h.sylow_normalizes hTH).trans h.sylow_normalizes)
    exact hout ((mem_normalizer_iff.mp (hn c.property) t.val).mpr hL)
  · exact (orderOf_injective (MulAut.conj c.val).toMonoidHom (MulAut.conj c.val).injective t.val).trans ht
  · change originalUnitaryFourResidualAction h hTH m hm a (c*t*c⁻¹)=_
    rw [map_mul,map_mul,map_inv,ha]

end Preparation
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.OriginalUnitaryFour
open ChapterF.GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
variable (m : ℕ) (hm : 1 ≤ m)

/-- The cyclic action uses the specified native graph automorphism. -/
@[expose] def planeGraphAction : UnitaryFourOuter.C2 →* MulAut (L2 m hm) :=
  QuaternionGroup.cyclicPowerHom 2 (Extension.L2Aut m hm) (by exact GraphAction.graph_sq m hm)

/-- The generator is the original specified graph automorphism. -/
theorem planeGraphAction_generator :
    planeGraphAction m hm UnitaryFourOuter.generator=Extension.L2Aut m hm := by
  exact QuaternionGroup.cyclicPowerHom_one _ _ _

/-- The concrete plane residual extended by the graph involution. -/
abbrev PlaneGraphExtension := L2 m hm ⋊[planeGraphAction m hm] UnitaryFourOuter.C2

private theorem plane_conj_injective :
    Function.Injective (MulAut.conj : L2 m hm →* MulAut (L2 m hm)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro x hx
  have hz : x ∈ center (L2 m hm) := by
    apply mem_center_iff.mpr
    intro y
    exact (mul_inv_eq_iff_eq_mul.mp (DFunLike.congr_fun hx y)).symm
  have hc : x ∈ pCore 2 (L2 m hm) := by
    rw [←L2TwoCore_centralizer m hm]
    exact center_le_centralizer (pCore 2 (L2 m hm) : Set (L2 m hm)) hz
  exact (L2TwoCore_inf_center m hm).le ⟨hc,hz⟩

private def planeGraphHom : PlaneGraphExtension m hm →* MulAut (L2 m hm) :=
  SemidirectProduct.lift MulAut.conj (planeGraphAction m hm) (by
    intro c
    apply MonoidHom.ext
    intro x
    apply MulEquiv.ext
    intro y
    change (planeGraphAction m hm c x)*y*(planeGraphAction m hm c x)⁻¹ =
      planeGraphAction m hm c (x*((planeGraphAction m hm c)⁻¹ y)*x⁻¹)
    rw [map_mul,map_mul,map_inv]
    exact congrArg (fun z => planeGraphAction m hm c x*z*(planeGraphAction m hm c x)⁻¹)
      ((planeGraphAction m hm c).apply_symm_apply y).symm)

private theorem planeGraphHom_injective : Function.Injective (planeGraphHom m hm) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro x hx
  change MulAut.conj x.left * planeGraphAction m hm x.right=1 at hx
  rcases UnitaryFourOuter.c2_cases x.right with hr | hr
  · rw [hr,map_one,mul_one] at hx
    have hl : x.left=1 := plane_conj_injective m hm (hx.trans (map_one _).symm)
    exact mem_bot.mpr (SemidirectProduct.ext hl hr)
  · rw [hr,planeGraphAction_generator] at hx
    have he : Extension.L2Aut m hm=MulAut.conj x.left⁻¹ := by
      rw [map_inv]
      calc
        _ = (MulAut.conj x.left)⁻¹*(MulAut.conj x.left*Extension.L2Aut m hm) := by group
        _ = _ := by rw [hx,mul_one]
    exact (Extension.L2Aut_ne_inner m hm _ he).elim

private theorem planeGraphHom_range : (planeGraphHom m hm).range=planeGraphGroup m hm := by
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    have hl : MulAut.conj x.left ∈ planeGraphGroup m hm :=
      (show MulAut.innerSubgroup (L2 m hm) ≤ planeGraphGroup m hm from le_sup_left) ⟨_,rfl⟩
    have hr : planeGraphAction m hm x.right ∈ planeGraphGroup m hm := by
      rcases UnitaryFourOuter.c2_cases x.right with hc | hc
      · rw [hc,map_one]; exact one_mem _
      · rw [hc,planeGraphAction_generator]
        exact (show zpowers (Extension.L2Aut m hm) ≤ planeGraphGroup m hm from le_sup_right) (mem_zpowers _)
    exact (planeGraphGroup m hm).mul_mem hl hr
  · apply sup_le
    · rintro _ ⟨x,rfl⟩
      refine ⟨SemidirectProduct.inl x,?_⟩
      change MulAut.conj x * planeGraphAction m hm 1=MulAut.conj x
      rw [map_one,mul_one]
    · apply zpowers_le.mpr
      refine ⟨SemidirectProduct.inr UnitaryFourOuter.generator,?_⟩
      change MulAut.conj (1 : L2 m hm)*planeGraphAction m hm UnitaryFourOuter.generator=Extension.L2Aut m hm
      rw [map_one,one_mul]
      exact QuaternionGroup.cyclicPowerHom_one _ _ _

/-- The concrete semidirect product acts faithfully, with exactly the
native inner-plus-graph image used in the original join recognition. -/
def planeGraphEquiv : PlaneGraphExtension m hm ≃* planeGraphGroup m hm := by
  exact (MonoidHom.ofInjective (planeGraphHom_injective m hm)).trans (MulEquiv.subgroupCongr (planeGraphHom_range m hm))

theorem planeGraphEquiv_inl (x : L2 m hm) :
    (planeGraphEquiv m hm (SemidirectProduct.inl x)).val=MulAut.conj x := by
  change MulAut.conj x * planeGraphAction m hm 1=MulAut.conj x
  rw [map_one,mul_one]

theorem planeGraphEquiv_graph :
    (planeGraphEquiv m hm (SemidirectProduct.inr UnitaryFourOuter.generator)).val=Extension.L2Aut m hm := by
  change MulAut.conj (1 : L2 m hm)*planeGraphAction m hm UnitaryFourOuter.generator=Extension.L2Aut m hm
  rw [map_one,one_mul]
  exact QuaternionGroup.cyclicPowerHom_one _ _ _

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.OriginalUnitaryFour

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
open ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  (m : ℕ) (hm : 1 ≤ m) (point : Bool)
  (mark : OriginalUnitaryFour.Marking m hm point L R (sourceS L H))
  (a : L ≃* L2 m hm)

/-- The original LS is the concrete native plane residual extended by its
specified graph involution, retaining the given L coordinates. -/
def originalUnitaryFourGraphExtensionEquiv
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=2) :
    (L ⊔ sourceS L H : Subgroup G) ≃* OriginalUnitaryFour.PlaneGraphExtension m hm :=
  (d.originalUnitaryFourGraphJoinEquiv h hTH hp m hm point mark a hi).trans
    (OriginalUnitaryFour.planeGraphEquiv m hm).symm

/-- The extension equivalence restricts to the unchanged residual map. -/
theorem originalUnitaryFourGraphExtensionEquiv_left
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=2) (x : L) :
    d.originalUnitaryFourGraphExtensionEquiv h hTH hp m hm point mark a hi (inclusion le_sup_left x) =
      SemidirectProduct.inl (a x) := by
  apply (OriginalUnitaryFour.planeGraphEquiv m hm).injective
  change OriginalUnitaryFour.planeGraphEquiv m hm
    ((OriginalUnitaryFour.planeGraphEquiv m hm).symm _) = _
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  exact (d.originalUnitaryFourGraphJoinEquiv_left h hTH hp m hm point mark a hi x).trans
    (OriginalUnitaryFour.planeGraphEquiv_inl m hm (a x)).symm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation


namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
open ChapterF.GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  (m : ℕ) (hm : 1 ≤ m) (point : Bool)
  (mark : OriginalUnitaryFour.Marking m hm point L R (sourceS L H))
  (a : L ≃* L2 m hm)
  (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=2)

theorem originalUnitaryFourGraphExtensionEquiv_action
    (x : (L ⊔ sourceS L H : Subgroup G)) :
    (OriginalUnitaryFour.planeGraphEquiv m hm
      (d.originalUnitaryFourGraphExtensionEquiv h hTH hp m hm point mark a hi x)).val =
        originalUnitaryFourResidualAction h hTH m hm a x := by
  change (OriginalUnitaryFour.planeGraphEquiv m hm
    ((OriginalUnitaryFour.planeGraphEquiv m hm).symm _)).val = _
  rw [MulEquiv.apply_symm_apply]
  exact d.originalUnitaryFourGraphJoinEquiv_apply h hTH hp m hm point mark a hi x

/-- The same source involution maps to the specified native graph generator. -/
theorem originalUnitaryFourGraphExtensionEquiv_graph :
    ∃ t : (L ⊔ sourceS L H : Subgroup G), t.val ∉ L ∧ orderOf t.val=2 ∧
      d.originalUnitaryFourGraphExtensionEquiv h hTH hp m hm point mark a hi t =
        SemidirectProduct.inr UnitaryFourOuter.generator := by
  obtain ⟨t,hout,ht,ha⟩ := d.original_unitaryFour_residual_graph_generator h hTH hp m hm point mark a hi
  refine ⟨t,hout,ht,?_⟩
  apply (OriginalUnitaryFour.planeGraphEquiv m hm).injective
  apply Subtype.ext
  exact (d.originalUnitaryFourGraphExtensionEquiv_action h hTH hp m hm point mark a hi t).trans
    (ha.trans (OriginalUnitaryFour.planeGraphEquiv_graph m hm).symm)

/-- The involution in the actual S has its literal conjugate graph image
under the same constructed extension equivalence. -/
theorem originalUnitaryFourGraphExtensionEquiv_source_graph :
    let e := d.originalUnitaryFourGraphExtensionEquiv h hTH hp m hm point mark a hi
    ∃ t : sourceS L H, t.val ∉ L ∧ orderOf t.val=2 ∧
      ∃ c : (L ⊔ sourceS L H : Subgroup G),
        e (inclusion le_sup_right t) = e c * SemidirectProduct.inr UnitaryFourOuter.generator * (e c)⁻¹ := by
  let e := d.originalUnitaryFourGraphExtensionEquiv h hTH hp m hm point mark a hi
  obtain ⟨t,hout,ht,c,hc⟩ := d.original_unitaryFour_source_full_graph_involution h hTH hp m hm point mark a hi
  refine ⟨t,hout,ht,c,?_⟩
  apply (OriginalUnitaryFour.planeGraphEquiv m hm).injective
  rw [map_mul,map_mul,map_inv]
  apply Subtype.ext
  change (OriginalUnitaryFour.planeGraphEquiv m hm (e (inclusion le_sup_right t))).val =
    (OriginalUnitaryFour.planeGraphEquiv m hm (e c)).val *
      (OriginalUnitaryFour.planeGraphEquiv m hm (SemidirectProduct.inr UnitaryFourOuter.generator)).val *
        (OriginalUnitaryFour.planeGraphEquiv m hm (e c)).val⁻¹
  rw [d.originalUnitaryFourGraphExtensionEquiv_action h hTH hp m hm point mark a hi,
    d.originalUnitaryFourGraphExtensionEquiv_action h hTH hp m hm point mark a hi,
    OriginalUnitaryFour.planeGraphEquiv_graph]
  exact hc

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation

module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOvercomponent
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSylow
public import Theory.SpecificGroups.PSL2.FieldDegreeOuterOrder
public import Theory.GroupTheory.PCoreQuotientJoinAction

/-!
# The original Sylow action on the right quotient field

Let K = O²(H) and S = O₂(N_G(L) ∩ H). When the compatible comparison
places S in both original factors, the existing Sylow geometry gives
S = T ∩ K and O₂(H) = O₂(K). Conjugation on K/O₂(K), followed by its
specified binary PSL₂ marking and the proved field projection, constructs
an actual homomorphism T → Aut(F).

The kernel is exactly S. Indeed an inner quotient action can be cancelled
by an element of K; the remaining actor lies in O₂(KT) = O₂(H) ≤ K.
Conversely every element of T ∩ K acts by an inner automorphism. Thus
|T:S| divides the right quotient's field degree. The companion applies
this to the actual G₂ and triality comparisons and discharges the
centralizer premise of their nonfusion proofs at odd original exponents.

This identifies the field coefficient on the right quotient. Relating
that coefficient to the action on Z(K) at even exponents remains required.
Source: Aschbacher–Smith F.4.29(2,7), printed pp.289–290, and F.4.35,
p.292 (`refs/quasithin.pdf`); the original application is 5.3.3, p.659.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem quotient_action_inner_iff
    {K U : Subgroup G} (hUK : U ≤ normalizer (K : Set G))
    (hU : IsPGroup 2 U) (hz : center (K ⧸ pCore 2 K) = ⊥)
    (hcore : (K ⊔ U : Subgroup G).pCoreIn 2 ≤ K)
    (x : (K ⊔ U : Subgroup G)) :
    pCoreJoinAction 2 hUK x ∈ MulAut.innerSubgroup (K ⧸ pCore 2 K) ↔ x.val ∈ K := by
  let f := pCoreJoinAction 2 hUK
  constructor
  · rintro ⟨z,hzinner⟩
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) z
    have he : f (inclusion le_sup_left k) = f x :=
      (pCoreJoinAction_on_component 2 hUK k).trans hzinner
    have hx : x * (inclusion le_sup_left k)⁻¹ ∈ f.ker := by
      change f (x * (inclusion le_sup_left k)⁻¹) = 1
      rw [map_mul,map_inv,he,mul_inv_cancel]
    rw [pCoreJoinAction_kernel 2 hUK hU] at hx
    · have hk := hcore (mem_map_of_mem (K ⊔ U).subtype hx)
      have hh := K.mul_mem hk k.property
      change (x.val * k.val⁻¹) * k.val ∈ K at hh
      simpa only [inv_mul_cancel_right] using hh
    · exact hz
  · intro hx
    let k : K := ⟨x.val,hx⟩
    have he : inclusion (show K ≤ K ⊔ U from le_sup_left) k = x := Subtype.ext rfl
    rw [←he,pCoreJoinAction_on_component]
    exact ⟨_,rfl⟩

/-- The field coefficient of the actual T-conjugation action on K/O₂(K). -/
@[expose] def residualSylowFieldAction
    {T : Sylow 2 G} {H : Subgroup G} (hTH : (T : Subgroup G) ≤ H)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (residual H ⧸ pCore 2 (residual H)) ≃* Theory.PSL2.Group F) :
    T →* (F ≃+* F) :=
  (Theory.PSL2.fieldProjection F).comp ((MulAut.congr e).toMonoidHom.comp
    ((pCoreJoinAction 2 (hTH.trans (le_normalizer_residual H))).comp
      (inclusion le_sup_right)))

omit [Finite G] in
/-- The coefficient retains its actual quotient marking: after transport by e,
every original Sylow actor is inner times its own field coefficient. -/
theorem residualSylowFieldAction_inner_field
    {T : Sylow 2 G} {H : Subgroup G} (hTH : (T : Subgroup G) ≤ H)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (residual H ⧸ pCore 2 (residual H)) ≃* Theory.PSL2.Group F) (t : T) :
    ∃ k : Theory.PSL2.Group F,
      MulAut.congr e (pCoreJoinAction 2 (hTH.trans (le_normalizer_residual H))
        (inclusion le_sup_right t)) =
      MulAut.conj k * Theory.PSL2.fieldAut (residualSylowFieldAction hTH e t) := by
  let a := MulAut.congr e (pCoreJoinAction 2 (hTH.trans (le_normalizer_residual H))
    (inclusion le_sup_right t))
  obtain ⟨k,σ,ha⟩ := Theory.PSL2.semilinear_coverage a
  have hk : Theory.PSL2.fieldProjection F (MulAut.conj k) = 1 := by
    rw [←MonoidHom.mem_ker,Theory.PSL2.fieldProjection_ker]
    exact ⟨k,rfl⟩
  have hs : residualSylowFieldAction hTH e t = σ := by
    change Theory.PSL2.fieldProjection F a = σ
    rw [ha,map_mul,hk,Theory.PSL2.fieldProjection_fieldAut,one_mul]
  exact ⟨k,hs.symm ▸ ha⟩

/-- The coefficient kernel is the original intersection core, rather than an
abstract subgroup of a model Sylow. -/
theorem Preparation.residual_sylow_field_kernel
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H)) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H)
    (hS : ∀ i : Fin 2, sourceS L H ≤ ![L,residual H] i)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (residual H ⧸ pCore 2 (residual H)) ≃* Theory.PSL2.Group F) :
    (residualSylowFieldAction hTH e).ker = (sourceS L H).subgroupOf (T : Subgroup G) := by
  have hz : center (residual H ⧸ pCore 2 (residual H)) = ⊥ := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [center_map_equiv,Subgroup.map_bot]
    apply bot_unique
    intro x hx
    apply Theory.PSL2.psl2_conj_eq_one_implies x
    ext y
    change x*y*x⁻¹=y
    rw [←mem_center_iff.mp hx y,mul_inv_cancel_right]
  have hc : (residual H ⊔ (T : Subgroup G)).pCoreIn 2 ≤ residual H := by
    rw [residual_sup_sylow T H hTH,residual_core_eq_of_sourceS_le h.sylow_normalizes hTH (hS 1)]
    exact pCoreIn_le 2 _
  have hs : sourceS L H = (T : Subgroup G) ⊓ residual H :=
    (d.ordinary_sylow_core_geometry h hTH hS).1 1
  ext t
  change Theory.PSL2.fieldProjection F
    ((MulAut.congr e) (pCoreJoinAction 2 (hTH.trans (le_normalizer_residual H))
      (inclusion le_sup_right t))) = 1 ↔ t.val ∈ sourceS L H
  rw [←MonoidHom.mem_ker,Theory.PSL2.fieldProjection_ker]
  have hi (a : MulAut (residual H ⧸ pCore 2 (residual H))) :
      MulAut.congr e a ∈ Theory.PSL2.inner F ↔
        a ∈ MulAut.innerSubgroup (residual H ⧸ pCore 2 (residual H)) := by
    change MulAut.congr e a ∈ MulAut.innerSubgroup (Theory.PSL2.Group F) ↔ _
    rw [←MulAut.map_innerSubgroup_congr e]
    exact mem_map_iff_mem (MulAut.congr e).injective
  rw [hi,quotient_action_inner_iff _ T.isPGroup' hz hc,hs]
  exact ⟨fun ht => ⟨t.property,ht⟩,fun ht => ht.2⟩

/-- The original Sylow/core index divides the actual right quotient's field degree. -/
theorem Preparation.residual_sylow_index_dvd
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B : Subgroup G} {n r : ℕ}
    (d : Preparation T L H A B (residual H)) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H)
    (hS : ∀ i : Fin 2, sourceS L H ≤ ![L,residual H] i)
    (he : ClassicalGroup.IsPSL (residual H ⧸ pCore 2 (residual H)) 2 (2^r)) :
    (sourceS L H).relIndex (T : Subgroup G) ∣ r := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := he
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  change ((sourceS L H).subgroupOf (T : Subgroup G)).index ∣ r
  rw [←d.residual_sylow_field_kernel h hTH hS e,index_ker]
  exact (residualSylowFieldAction hTH e).range.card_subgroup_dvd_card.trans
    (dvd_of_eq (FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two hF))


end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

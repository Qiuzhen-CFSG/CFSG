module

public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.TorusConstruction.CoveredCase.WholeSylow
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.TorusConstruction.CoveredCase.SuzukiModel
/-!
# The component action in the covered Suzuki branch

The actual central quotient sends T_L onto a Suzuki Sylow of order 64.
Its square-one center is the image of Ω₁(T_L). Thus the two commutator
layers are [T_L,T_L] ≤ Ω₁(T_L) and [T_L,Ω₁(T_L)] ≤ Z(L), and the
omega index is eight. An element centralizing omega has central square;
the lifting property then makes it involutory. This identifies the action
kernel on V with omega and proves that the component image has order eight.

Source: Aschbacher–Smith, 16.5.1, p.1194, and I.2.2(4), p.409;
Huppert–Blackburn, Finite Groups III, XI.3.1.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
open CFSG.Quasithin.Chapter16 CFSG.Quasithin.Chapter16.CoverAndSylowElimination
open CFSG.Quasithin.Chapter16.Intersections CFSG.Quasithin.Chapter16.Intersections.Bender
namespace CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.TorusConstruction.CoveredCase
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G} {z : G}

theorem component_quotient_facts (h : StandardSetup T z L) (d : SuzukiCoverInput T L) :
    (componentCenter L).relIndex (componentSylow T L) = 64 ∧
      ⁅componentSylow T L, componentSylow T L⁆ ≤ sylowOmega T L ∧
      ⁅componentSylow T L, sylowOmega T L⁆ ≤ componentCenter L := by
  obtain ⟨P,hP⟩ := h.toCentralComponentSetup.exists_component_sylow
  obtain ⟨e⟩ := d.quotient_model
  let π := QuotientGroup.mk' (center L)
  let Q := P.mapSurjective (f := π) (QuotientGroup.mk'_surjective _)
  let i : componentSylow T L →* L := inclusion inf_le_right
  have hi (x : componentSylow T L) : i x ∈ P := by
    change i x ∈ (P : Subgroup L)
    rw [hP]
    exact x.property.1
  let f : componentSylow T L →* Q := {
    toFun := fun x => ⟨π (i x), mem_map_of_mem π (hi x)⟩
    map_one' := Subtype.ext (by simp)
    map_mul' := fun x y => Subtype.ext (by simp) }
  have hf (x : componentSylow T L) : (f x : L ⧸ center L) = π (i x) := rfl
  have hsurj : Function.Surjective f := by
    rintro ⟨q,y,hy,rfl⟩
    have hyT : (y : G) ∈ T := by
      change y ∈ (P : Subgroup L) at hy
      rw [hP] at hy
      exact hy
    exact ⟨⟨y,hyT,y.property⟩, rfl⟩
  have hker : f.ker = (componentCenter L).subgroupOf (componentSylow T L) := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have hh : π (i x) = 1 := congrArg Subtype.val hx
      exact mem_map_of_mem L.subtype ((QuotientGroup.eq_one_iff (i x)).mp hh)
    · rintro ⟨y,hy,he⟩
      apply Subtype.ext
      change π (i x) = 1
      apply (QuotientGroup.eq_one_iff (i x)).mpr
      have hxy : i x = y := Subtype.ext he.symm
      rwa [hxy]
  obtain ⟨hcard,hsq,hderived⟩ := CFSG.Quasithin.CoveredSuzukiModel.sylow_facts e Q
  refine ⟨?_, ?_, ?_⟩
  · change ((componentCenter L).subgroupOf (componentSylow T L)).index = 64
    rw [← hker, index_ker, MonoidHom.range_eq_top.mpr hsurj, card_top, hcard]
  · apply commutator_le.mpr
    intro x hx y hy
    let xS : componentSylow T L := ⟨x,hx⟩
    let yS : componentSylow T L := ⟨y,hy⟩
    have hh : (π (i ⁅xS,yS⁆)) ^ 2 = 1 := by
      have hh := congrArg Subtype.val (hderived (f xS) (f yS))
      simpa only [← map_commutatorElement, ← map_pow, hf, Subgroup.coe_one] using hh
    have hsquare := d.sq_eq_one_of_quotient (i ⁅xS,yS⁆) hh
    exact (omegaOneAmbient_le_iff _ _).mp le_rfl _
      ((componentSylow T L).commutator_le_self (commutator_mem_commutator hx hy))
      (congrArg L.subtype hsquare)
  · let := d.omega_structure.1
    apply commutator_le.mpr
    intro x hx a ha
    let xS : componentSylow T L := ⟨x,hx⟩
    let aS : componentSylow T L := ⟨a,sylowOmega_le ha⟩
    have ha2 : aS ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian a ha)
    have hfa : f aS ∈ center Q := (hsq _).mpr (by rw [← map_pow, ha2, map_one])
    have hk : ⁅xS,aS⁆ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hfa _)
    rw [hker] at hk
    exact hk

theorem component_omega_index (h : StandardSetup T z L) (d : SuzukiCoverInput T L) :
    (sylowOmega T L).relIndex (componentSylow T L) = 8 := by
  have hh := relIndex_mul_relIndex (componentCenter L) (sylowOmega T L)
    (componentSylow T L) d.omega_structure.2.1 sylowOmega_le
  rw [d.omega_structure.2.2, (component_quotient_facts h d).1] at hh
  omega

theorem component_omega_self_centralizing (h : StandardSetup T z L) (d : SuzukiCoverInput T L) :
    componentSylow T L ⊓ centralizer (sylowOmega T L : Set G) = sylowOmega T L := by
  let := d.omega_structure.1
  apply le_antisymm
  · intro x hx
    have hsquare : x ^ 2 ∈ componentCenter L := by
      rw [← d.center_sylow]
      refine ⟨⟨x ^ 2,(componentSylow T L).pow_mem hx.1 2⟩, ?_, rfl⟩
      apply mem_center_iff.mpr
      intro y
      apply Subtype.ext
      have hc := (component_quotient_facts h d).2.1
        (commutator_mem_commutator hx.1 y.property)
      have hcomm := hx.2 ⁅x,(y:G)⁆ hc
      have hpow := elemPow_eq_one_of_isElementaryAbelian (p:=2) _ hc
      have hbracket : ⁅x ^ 2,(y:G)⁆ = 1 := by
        rw [pow_two, commutatorElement_mul_left_eq_conj_mul, ← hcomm]
        simpa only [mul_inv_cancel_right, ← pow_two] using hpow
      exact (commutatorElement_eq_one_iff_mul_comm.mp hbracket).symm
    have hx2 : x ^ 2 = 1 := by
      let xL : L := ⟨x,hx.1.2⟩
      have hcent : xL ^ 2 ∈ center L := by
        obtain ⟨c,hc,he⟩ := hsquare
        have heq : c = xL ^ 2 := Subtype.ext he
        rwa [← heq]
      exact congrArg L.subtype (d.sq_eq_one_of_quotient xL (by
        rw [← map_pow]
        exact (QuotientGroup.eq_one_iff _).mpr hcent))
    exact (omegaOneAmbient_le_iff _ _).mp le_rfl x hx.1 hx2
  · exact le_inf sylowOmega_le (sylowOmega T L).le_centralizer

theorem component_image_card (h : StandardSetup T z L) (d : SuzukiCoverInput T L)
    [IsElementaryAbelian 2 (benderSpace T L)] :
    Nat.card (inducedActor (benderSpace T L) (componentSylow T L)) = 8 := by
  let V := benderSpace T L
  let S := componentSylow T L
  have hSN : S ≤ normalizer (V : Set G) := (sylow_normalizes_factors h).1.trans' inf_le_left
  let f : S →* ActionImage V := V.normalizerMonoidHom.rangeRestrict.comp (inclusion hSN)
  have hrange : f.range = inducedActor V S := by
    ext a
    constructor
    · rintro ⟨s,rfl⟩
      exact ⟨inclusion hSN s,s.property,rfl⟩
    · rintro ⟨s,hs,rfl⟩
      exact ⟨⟨s,hs⟩,rfl⟩
  have hker : f.ker = (sylowOmega T L).subgroupOf S := by
    ext s
    rw [MonoidHom.mem_ker]
    constructor
    · intro hs
      have hh : (s:G) ∈ componentSylow T L ⊓ centralizer (sylowOmega T L : Set G) := by
        refine ⟨s.property, ?_⟩
        intro a ha
        have haV : a ∈ V := (show sylowOmega T L ≤ V from le_sup_right) ha
        have he := congrArg (fun b : ActionImage V => (b : MulAut V) ⟨a,haV⟩) hs
        have he' : (s:G)*a*(s:G)⁻¹ = a := congrArg Subtype.val he
        exact (mul_inv_eq_iff_eq_mul.mp he').symm
      rw [component_omega_self_centralizing h d] at hh
      exact hh
    · intro hs
      apply Subtype.ext
      apply MulEquiv.ext
      intro v
      apply Subtype.ext
      change (s:G)*(v:G)*(s:G)⁻¹ = v
      have hsV : (s:G) ∈ V := (show sylowOmega T L ≤ V from le_sup_right) hs
      have hc := V.le_centralizer hsV v v.property
      rw [← hc, mul_inv_cancel_right]
  rw [← hrange, ← index_ker, hker]
  exact component_omega_index h d

end CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.TorusConstruction.CoveredCase

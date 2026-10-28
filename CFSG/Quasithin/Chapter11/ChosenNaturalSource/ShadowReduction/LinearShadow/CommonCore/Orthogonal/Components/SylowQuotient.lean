module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal.Components.Local
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal.Inputs
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal.Normalizer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.PlaneAction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.Quotients
public import Theory.SpecificGroups.SL2.SylowConsequences
public import Theory.GroupTheory.PCoreRestriction
public import Theory.ElementaryAbelian.Join

/-!
# The literal elementary Sylow quotient T/P

The marked SL₃ flag puts T inside VL₂ once the original T lies in L.
Thus T=V(T∩L₂). Both factors have squares in P and commute modulo P,
so the actual quotient T/(P.subgroupOf T) is elementary abelian. The
original SL₃ and paired SL₂ markings give |T|=q⁶ and |P|=q⁴, hence
|T/P|=q². No splitting of the natural extension is assumed.

This discharges the quotient premise for the relative-component argument
on printed p.774 of Aschbacher--Smith. The original Sylow containment is
provided in odd degree by OddDegree.Sylow; the cubic parity argument and
final orthogonal assembly remain with this task.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H X A : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)}
    {f : InvariantFlag (.sl3 m)} {h : G}
    (d : OrthogonalInput D S m f H X A h)

include d

theorem source_flag_eq : f = SL3.flag D S m := by
  have hs : f.space = (SL3.flag D S m).space := by
    funext i
    exact (d.unique_flag i _ ((SL3.flag D S m).dimension i)
      ((SL3.flag D S m).invariant i)).symm
  have he (f₁ f₂ : InvariantFlag (.sl3 m)) (hsp : f₁.space = f₂.space) : f₁ = f₂ := by
    cases f₁
    cases f₂
    cases hsp
    rfl
  exact he f (SL3.flag D S m) hs

/-- The actual Sylow lies in the seed times the second flag residual. -/
theorem source_sylow_le_local_join_seed (hTL : (T : Subgroup G) ≤ L) :
    (T : Subgroup G) ≤ f.Li 1 ⊔ V := by
  rw [source_flag_eq d]
  let q := SL3.PlaneAction.alignedQuotient D S m
  have hi : ((T : Subgroup G).subgroupOf L).map q ≤
      (((SL3.flag D S m).Li 1).subgroupOf L).map q := by
    rw [SL3.PlaneAction.local_image]
    rintro _ ⟨t,ht,rfl⟩
    have ht' : (SL3.coordinates D S m).quotientMap t ∈
        (SL3.innerSylow D S m : Subgroup (Matrix.SpecialLinearGroup (Fin 3) S.field.Carrier)) := by
      rw [SL3.innerSylow_eq]
      exact mem_map_of_mem _ ht
    rw [← SL3.alignment_sylow] at ht'
    obtain ⟨u,hu,he⟩ := ht'
    have hq : q t = u := by
      change (MulAut.conj (SL3.alignment D S m)⁻¹)
        ((SL3.coordinates D S m).quotientMap t) = u
      rw [← he]
      simp only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv]
      group
    rw [hq]
    exact hu.2
  have hc := comap_mono (f := q) hi
  rw [comap_map_eq, comap_map_eq, SL3.PlaneAction.alignedQuotient_ker] at hc
  have hh := map_mono (f := L.subtype) ((le_sup_left :
    (T : Subgroup G).subgroupOf L ≤ (T : Subgroup G).subgroupOf L ⊔ pCore 2 L).trans hc)
  have hlocal : (SL3.flag D S m).Li 1 ≤ L := (localResidual_le _).trans inf_le_left
  rw [map_subgroupOf_eq_of_le hTL, Subgroup.map_sup,
    map_subgroupOf_eq_of_le hlocal] at hh
  exact hh.trans (sup_le_sup_left d.seed_core.le _)

/-- The source seed and the literal Sylow intersection generate T. -/
theorem source_sylow_eq_seed_join_local (hTL : (T : Subgroup G) ≤ L) :
    (T : Subgroup G) = V ⊔ ((T : Subgroup G) ⊓ f.Li 1) := by
  have hlocal : f.Li 1 ≤ L := (localResidual_le _).trans inf_le_left
  have hseed : V ≤ L := d.seed_core ▸ pCoreIn_le 2 L
  let VN := V.subgroupOf L
  let : VN.Normal := (normal_subgroupOf_iff_le_normalizer
    (d.seed_core ▸ pCoreIn_le 2 L)).mpr D.normalizes
  apply le_antisymm _ (sup_le D.le_sylow inf_le_left)
  intro t ht
  have hmem : (⟨t,hTL ht⟩ : L) ∈ (f.Li 1).subgroupOf L ⊔ VN := by
    change (⟨t,hTL ht⟩ : L) ∈ (f.Li 1).subgroupOf L ⊔ V.subgroupOf L
    rw [← subgroupOf_sup hlocal hseed]
    exact source_sylow_le_local_join_seed d hTL ht
  obtain ⟨l,hl,v,hv,he⟩ := mem_sup_of_normal_right.mp hmem
  have hlT : (l : G) ∈ (T : Subgroup G) := by
    have he' : (l : G) * (v : G) = t := congrArg Subtype.val he
    have hl' : (l : G) = t * (v : G)⁻¹ := (eq_mul_inv_iff_mul_eq.mpr he')
    rw [hl']
    exact (T : Subgroup G).mul_mem ht ((T : Subgroup G).inv_mem (D.le_sylow hv))
  have he' : (l : G) * (v : G) = t := congrArg Subtype.val he
  rw [← he']
  exact (V ⊔ ((T : Subgroup G) ⊓ f.Li 1)).mul_mem
    (mem_sup_right ⟨hlT,hl⟩) (mem_sup_left hv)

/-- The two factors commute modulo their common two-core. -/
theorem source_seed_local_commutator : ⁅V,f.Li 1⁆ ≤ pairCore V H h := by
  have hle : f.Li 1 ≤ L := (localResidual_le _).trans inf_le_left
  have hc : ⁅V,f.Li 1⁆ ≤ f.Li 1 ⊓ V :=
    le_inf (le_normalizer_iff_commutator_le_right.mp
      (D.le_sylow.trans (f.sylow_normalizes_Li 1)))
      (le_normalizer_iff_commutator_le_left.mp (hle.trans D.normalizes))
  exact hc.trans ((d.seed_core ▸ inf_pCoreIn_le_of_le 2 hle).trans d.local_core.le)

/-- Squares in the original L₂-Sylow already lie in P. -/
theorem source_local_sylow_square (x : G) (hx : x ∈ (T : Subgroup G) ⊓ f.Li 1) :
    x ^ 2 ∈ pairCore V H h := by
  obtain ⟨R,hR⟩ := NormalSylowQuotientAction.intersection_sylow T (f.Li 1)
    (f.sylow_normalizes_Li 1)
  let e := (SL3.flagLocalCoreEquiv S m f 1).trans
    (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := S.field.Carrier)).symm
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (f.Li 1)))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let R' := R.mapSurjective hq
  let u : R' := ⟨q ⟨x,hx.2⟩, by
    exact mem_map_of_mem q (by rw [hR]; exact hx.1)⟩
  let eu := Matrix.SpecialLinearGroup.sylowEquivAdditive S.field.Carrier 2 R'
  have hu : u ^ 2 = 1 := by
    apply eu.symm.injective
    rw [map_pow,map_one]
    change Multiplicative.ofAdd (2 • (eu.symm u).toAdd) = Multiplicative.ofAdd 0
    rw [two_smul,CharTwo.add_self_eq_zero]
  have hxq : q ((⟨x,hx.2⟩ : f.Li 1) ^ 2) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val hu
  have hxcore : (⟨x,hx.2⟩ : f.Li 1) ^ 2 ∈ pCore 2 (f.Li 1) := by
    apply (QuotientGroup.eq_one_iff _).mp
    exact e.injective (hxq.trans e.map_one.symm)
  rw [← d.local_core]
  exact mem_map_of_mem (f.Li 1).subtype hxcore


omit d in
/-- The aligned projection retains the original Sylow, with no changed lift. -/
theorem source_aligned_sylow_image :
    ((T : Subgroup G).subgroupOf L).map (SL3.PlaneAction.alignedQuotient D S m) =
      Matrix.PSL3.LinearThree.unipotentSL S.field.Carrier := by
  change ((T : Subgroup G).subgroupOf L).map
    ((MulAut.conj (SL3.alignment D S m)⁻¹).toMonoidHom.comp
      (SL3.coordinates D S m).quotientMap) = _
  rw [← map_map, ← SL3.innerSylow_eq, ← SL3.alignment_sylow, map_map]
  have he : (MulAut.conj (SL3.alignment D S m)⁻¹).toMonoidHom.comp
      (MulAut.conj (SL3.alignment D S m)).toMonoidHom = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro x
    simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MonoidHom.id_apply,
      MulAut.conj_apply,inv_inv]
    group
  rw [he,map_id]

/-- The kernel and image orders give the order of the original Sylow. -/
theorem source_sylow_card (hTL : (T : Subgroup G) ≤ L) :
    Nat.card T = (2 ^ S.field.degree) ^ 6 := by
  let q := SL3.PlaneAction.alignedQuotient D S m
  let r := q.comp (inclusion hTL)
  have hr : r.range = ((T : Subgroup G).subgroupOf L).map q := by
    ext a
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨inclusion hTL t,t.property,rfl⟩
    · rintro ⟨t,ht,rfl⟩
      exact ⟨⟨t,ht⟩,rfl⟩
  have hk : r.ker = V.subgroupOf (T : Subgroup G) := by
    ext t
    change q (inclusion hTL t) = 1 ↔ (t : G) ∈ V
    rw [← MonoidHom.mem_ker,SL3.PlaneAction.alignedQuotient_ker,← d.seed_core]
    exact (mem_map_iff_mem (f := L.subtype) L.subtype_injective).symm
  have hkcard : Nat.card r.ker = (2 ^ S.field.degree) ^ 3 := by
    rw [hk,Nat.card_congr (subgroupOfEquivOfLe D.le_sylow).toEquiv,
      Nat.card_congr (SL3.naturalEquiv D S m).toEquiv]
    change Nat.card (Fin 3 → S.field.Carrier) = _
    rw [Nat.card_fun,Nat.card_fin,S.field.card_eq]
  have hrcard : Nat.card r.range = (2 ^ S.field.degree) ^ 3 := by
    rw [hr,source_aligned_sylow_image (D := D) (S := S) (m := m),
      Matrix.PSL3.LinearThree.card_unipotentSL,S.field.card_eq]
  calc
    Nat.card T = Nat.card r.ker * Nat.card r.range := by
      rw [← index_ker,r.ker.card_mul_index]
    _ = (2 ^ S.field.degree) ^ 6 := by rw [hkcard,hrcard,← pow_add]

omit d in
private theorem elementary_of_squares {Q : Type*} [Group Q]
    (hs : ∀ x : Q, x ^ 2 = 1) : IsElementaryAbelian 2 Q where
  toIsMulCommutative := ⟨⟨fun x y => Commute.of_orderOf_dvd_two
    (fun a => orderOf_dvd_of_pow_eq_one (hs a)) x y⟩⟩
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs

omit d in
private theorem elementary_quotient_of_join {Q : Type*} [Group Q]
    (B C N : Subgroup Q) [N.Normal] (hgen : B ⊔ C = ⊤)
    (hB : ∀ b ∈ B, b ^ 2 ∈ N) (hC : ∀ c ∈ C, c ^ 2 ∈ N)
    (hc : ⁅B,C⁆ ≤ N) : IsElementaryAbelian 2 (Q ⧸ N) := by
  let π := QuotientGroup.mk' N
  have hel (E : Subgroup Q) (hs : ∀ e ∈ E, e ^ 2 ∈ N) :
      IsElementaryAbelian 2 (E.map π) := by
    apply elementary_of_squares
    rintro ⟨x,e,he,rfl⟩
    apply Subtype.ext
    change π e ^ 2 = 1
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (N := N) (e ^ 2)).mpr (hs e he)
  let : IsElementaryAbelian 2 (B.map π) := hel B hB
  let : IsElementaryAbelian 2 (C.map π) := hel C hC
  have hcomm : ⁅B.map π,C.map π⁆ = ⊥ := by
    rw [← map_commutator]
    exact (Subgroup.map_eq_bot_iff _).mpr ((QuotientGroup.ker_mk' N).symm ▸ hc)
  have hj : IsElementaryAbelian 2 (B.map π ⊔ C.map π : Subgroup (Q ⧸ N)) := by
    rw [sup_comm]
    exact IsElementaryAbelian.sup_of_le_centralizer
      (commutator_eq_bot_iff_le_centralizer.mp hcomm)
  have ht : B.map π ⊔ C.map π = ⊤ := by
    rw [← Subgroup.map_sup,hgen,map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
  let : IsElementaryAbelian 2 (⊤ : Subgroup (Q ⧸ N)) := ht ▸ hj
  exact elementary_of_squares (fun x =>
    elemPow_eq_one_of_isElementaryAbelian (A := (⊤ : Subgroup (Q ⧸ N))) x (mem_top x))

/-- Elementary structure on the literal quotient, after the source Sylow placement. -/
theorem source_sylow_quotient_elementary (hTL : (T : Subgroup G) ≤ L) :
    let := source_pairCore_normal_sylow d
    IsElementaryAbelian 2 ((T : Subgroup G) ⧸ (pairCore V H h).subgroupOf T) := by
  let := source_pairCore_normal_sylow d
  let := D.elementary
  apply elementary_quotient_of_join (V.subgroupOf T)
    (((T : Subgroup G) ⊓ f.Li 1).subgroupOf T) ((pairCore V H h).subgroupOf T)
  · rw [← subgroupOf_sup D.le_sylow inf_le_left,← source_sylow_eq_seed_join_local d hTL]
    exact subgroupOf_self _
  · intro x hx
    change (x : G) ^ 2 ∈ pairCore V H h
    rw [elemPow_eq_one_of_isElementaryAbelian (A := V) (x : G) hx]
    exact one_mem _
  · intro x hx
    exact source_local_sylow_square d x hx
  · apply commutator_le.mpr
    intro x hx y hy
    exact source_seed_local_commutator d (commutator_mem_commutator hx hy.2)

/-- The order calculation uses P itself, not the two-core of its normalizer. -/
theorem source_sylow_quotient_card (hTL : (T : Subgroup G) ≤ L) :
    let := source_pairCore_normal_sylow d
    Nat.card ((T : Subgroup G) ⧸ (pairCore V H h).subgroupOf T) =
      (2 ^ S.field.degree) ^ 2 := by
  let := source_pairCore_normal_sylow d
  have hc := card_eq_card_quotient_mul_card_subgroup ((pairCore V H h).subgroupOf T)
  rw [source_sylow_card d hTL,
    Nat.card_congr (subgroupOfEquivOfLe (source_pairCore_le_sylow d)).toEquiv,
    source_pairCore_card d] at hc
  apply Nat.eq_of_mul_eq_mul_right (pow_pos (pow_pos (by decide : 0 < 2) _) 4)
  exact hc.symm.trans (by rw [← pow_add])

/-- The exact quotient premise for relative-component nonenlargement. -/
theorem source_sylow_quotient (hTL : (T : Subgroup G) ≤ L) :
    let := source_pairCore_normal_sylow d
    IsElementaryAbelian 2 ((T : Subgroup G) ⧸ (pairCore V H h).subgroupOf T) ∧
      Nat.card ((T : Subgroup G) ⧸ (pairCore V H h).subgroupOf T) =
        (2 ^ S.field.degree) ^ 2 :=
  ⟨source_sylow_quotient_elementary d hTL,source_sylow_quotient_card d hTL⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore

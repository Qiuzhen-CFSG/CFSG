module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.ActorFusion.Inputs
public import GorensteinWalter.PGL2DerivedSubgroup
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.SpecificGroups.PSL2.FiveProjectivePermutation

/-!
# Intrinsic linear marking and transport of characteristic-five actors

The supplied product comparison sends the local derived group to PSL₂(5) × 1.
The actual central involution necessarily has coordinates (1, σ), since PGL₂
has trivial center. Its nontrivial field coordinate separates the two cosets
of the derived group inside the inverse image of PSL₂(5). This identifies
the required intersection with the original linear kernel without asserting
that the entire linear subgroup is preserved by an arbitrary comparison.
Sylow restriction to the derived group of order sixty gives the small order.

The final transport retains the supplied comparison, projection, and common
Sylow subgroup. It pulls an actual S₅ × C₂ conjugator back to the specified
centralizer. Only the isolated finite graph-spreading calculation remains
explicit; this file does not assert its existence or unconditional fusion.

Source: Aschbacher--Smith, E.1.5, E.1.8 and E.1.14(6), printed pp.210--214,
with the last citing Aschbacher (1982), Lemma 4.10. This is a local input to
that source argument, whose ambient hypotheses and assembly remain separate.
-/

public section
noncomputable section
open Subgroup GorensteinWalter Matrix
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.Frame
variable {F : Type*} [Field F] [Finite F] {σ : F ≃+* F}
variable (c : Frame σ) (hF : Nat.card F = 5 ^ 2) (hσ : orderOf σ = 2)

include hF hσ in
private theorem fixed_card : Nat.card (FixedPoints.subfield (zpowers σ) F) = 5 :=
  fixedSubfield_card hF σ ((orderOf_eq_prime_iff (x := σ)).mp hσ).1
    ((orderOf_eq_prime_iff (x := σ)).mp hσ).2

private theorem derived_coordinates (i : Bool) :
    (commutator (c.centralizerAt i)).map (c.productCoordinates hF hσ i).toMonoidHom =
      ((ProjectiveSpecialLinearGroup.toPGL (n := Fin 2)
        (R := FixedPoints.subfield (zpowers σ) F)).range).prod ⊥ := by
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (MulEquiv.surjective _)]
  change commutator (_ × _) = _
  rw [commutator_def, ← Subgroup.top_prod_top, Subgroup.commutator_prod_prod]
  change (commutator (PGL2 (FixedPoints.subfield (zpowers σ) F))).prod
    (commutator (zpowers σ)) = _
  rw [commutator_eq_bot (zpowers σ)]
  congr 1
  exact pgl2_commutator_eq_psl2_range_of_card_gt_three _
    ⟨5, 1, by decide, by decide, le_rfl, by simpa using fixed_card hF hσ⟩
    (by rw [fixed_card hF hσ]; decide)

private theorem derived_mem_iff (i : Bool) (x : c.centralizerAt i) :
    x ∈ commutator (c.centralizerAt i) ↔
      (c.productCoordinates hF hσ i x).1 ∈
        (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2)
          (R := FixedPoints.subfield (zpowers σ) F)).range ∧
      (c.productCoordinates hF hσ i x).2 = 1 := by
  have h := derived_coordinates c hF hσ i
  have hm := congrArg (fun U => c.productCoordinates hF hσ i x ∈ U) h
  simpa only [Subgroup.mem_map_equiv, Subgroup.mem_prod, Subgroup.mem_bot,
    MulEquiv.symm_apply_apply] using hm.to_iff

include hF in
private theorem derived_linear (i : Bool) :
    (commutator (c.centralizerAt i)).map (c.centralizerAt i).subtype ≤
      pGammaL2LinearKernel F (innerModel F σ) := by
  let : CommGroup (F ≃+* F) :=
    (finiteField_ringAut_isCyclic_of_oddPrimePower F
      ⟨5, 2, by decide, by decide, by decide, hF⟩).commGroup
  rintro _ ⟨x, hx, rfl⟩
  apply (mem_pGammaL2LinearKernel_iff F (innerModel F σ) _).mpr
  exact Abelianization.commutator_subset_ker
    ((pGammaL2FieldProjection F (innerModel F σ)).comp
      (c.centralizerAt i).subtype) hx

private def markedInvolution (i : Bool) : c.centralizerAt i :=
  ⟨c.involution i, by
    rw [centralizerAt, mem_centralizer_iff]
    intro y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    rfl⟩

omit [Finite F] in
private theorem markedInvolution_field (i : Bool) :
    pGammaL2FieldProjection F (innerModel F σ) (c.markedInvolution i) = σ := by
  cases i
  · rfl
  · change (c.z : PGammaL2 F).right * σ = σ
    rw [c.z_linear, one_mul]

private theorem involution_coordinates (i : Bool) :
    c.productCoordinates hF hσ i (c.markedInvolution i) =
      (1, ⟨σ, mem_zpowers σ⟩) := by
  let e := c.productCoordinates hF hσ i
  let v := c.markedInvolution i
  have hc : v ∈ center (c.centralizerAt i) := by
    rw [mem_center_iff]
    intro x
    apply Subtype.ext
    exact ((mem_centralizer_iff.mp x.property) _ (Set.mem_singleton _)).symm
  have hf : (e v).1 = 1 := by
    apply mem_bot.mp
    rw [← pgl2_center_eq_bot (FixedPoints.subfield (zpowers σ) F)]
    rw [mem_center_iff]
    intro x
    have hm := congrArg (fun z => (e z).1)
      ((mem_center_iff.mp hc) (e.symm (x, 1)))
    simpa only [map_mul, Prod.fst_mul, MulEquiv.apply_symm_apply] using hm
  have hv : v ≠ 1 := by
    intro h
    have he := congrArg (fun x : c.centralizerAt i =>
      pGammaL2FieldProjection F (innerModel F σ) x) h
    have hn := ((orderOf_eq_prime_iff (x := σ)).mp hσ).2
    exact hn ((markedInvolution_field c i).symm.trans he)
  have hs : ((e v).2 : F ≃+* F) = σ := by
    rcases fieldAut_eq_one_or (by decide : Nat.Prime 5) hF σ
      ((orderOf_eq_prime_iff (x := σ)).mp hσ).2 (e v).2 with h | h
    · have ht : (e v).2 = 1 := Subtype.ext h
      apply False.elim
      apply hv
      apply e.injective
      simpa only [map_one] using Prod.ext hf ht
    · exact h
  exact Prod.ext hf (Subtype.ext hs)

/-- The local derived subgroup is exactly the linear part of the inverse
image of the fixed-field PSL₂ layer, for the supplied comparison. -/
theorem local_linear_iff_derived (i : Bool) (x : c.centralizerAt i)
    (hx : c.projection hF hσ i x ∈
      (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2)
        (R := FixedPoints.subfield (zpowers σ) F)).range) :
    (x : innerModel F σ) ∈ pGammaL2LinearKernel F (innerModel F σ) ↔
      x ∈ commutator (c.centralizerAt i) := by
  constructor
  · intro hl
    let e := c.productCoordinates hF hσ i
    let y := e.symm ((e x).1, 1)
    have hy : y ∈ commutator (c.centralizerAt i) := by
      apply (derived_mem_iff c hF hσ i y).mpr
      change (e (e.symm _)).1 ∈ _ ∧ (e (e.symm _)).2 = 1
      rw [e.apply_symm_apply]
      exact ⟨hx, rfl⟩
    have hyL : (y : innerModel F σ) ∈ pGammaL2LinearKernel F (innerModel F σ) :=
      derived_linear c hF i ⟨y, hy, rfl⟩
    rcases fieldAut_eq_one_or (by decide : Nat.Prime 5) hF σ
      ((orderOf_eq_prime_iff (x := σ)).mp hσ).2 (e x).2 with ht | ht
    · exact (derived_mem_iff c hF hσ i x).mpr ⟨hx, Subtype.ext ht⟩
    · have heq : x = y * c.markedInvolution i := by
        apply e.injective
        rw [map_mul, involution_coordinates c hF hσ i]
        change e x = e (e.symm _) * _
        rw [e.apply_symm_apply]
        exact Prod.ext (by simp) (by simpa using Subtype.ext ht)
      have hq := congrArg (fun z : c.centralizerAt i =>
        pGammaL2FieldProjection F (innerModel F σ) z) heq
      change pGammaL2FieldProjection F (innerModel F σ) x =
        pGammaL2FieldProjection F (innerModel F σ) y *
        pGammaL2FieldProjection F (innerModel F σ) (c.markedInvolution i) at hq
      rw [(mem_pGammaL2LinearKernel_iff _ _ _).mp hl,
        (mem_pGammaL2LinearKernel_iff _ _ _).mp hyL,
        markedInvolution_field, one_mul] at hq
      exact (((orderOf_eq_prime_iff (x := σ)).mp hσ).2 hq.symm).elim
  · intro hx
    exact derived_linear c hF i ⟨x, hx, rfl⟩

/-- The literal large subgroup meets the original linear kernel in the
literal small subgroup. No marking of the whole linear subgroup is used. -/
theorem local_linear_marking (i : Bool) :
    c.large hF hσ i ⊓ pGammaL2LinearKernel F (innerModel F σ) =
      c.small hF hσ i := by
  apply le_antisymm
  · rintro x ⟨hx, hlin⟩
    obtain ⟨y, hy, hyx⟩ := hx.2
    exact ⟨hx, y, (local_linear_iff_derived c hF hσ i y hy).mp
      (by change (c.centralizerAt i).subtype y ∈ _; rwa [hyx]), hyx⟩
  · exact le_inf (c.small_le_large hF hσ i)
      (inf_le_right.trans (derived_linear c hF i))


include hF hσ in
private theorem derived_card (i : Bool) :
    Nat.card (commutator (c.centralizerAt i)) = 60 := by
  let K := FixedPoints.subfield (zpowers σ) F
  have hc : Nat.card (PSL2 K) = 60 := by
    have h := ProjectiveSpecialLinearGroup.psl2_card_twice (F := K)
      (by rw [fixed_card hF hσ]; decide)
    rw [fixed_card hF hσ] at h
    norm_num at h
    change Nat.card (PSL2 K) * 2 = 120 at h
    omega
  have hr : Nat.card (ProjectiveSpecialLinearGroup.toPGL
      (n := Fin 2) (R := K)).range = 60 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective
      ProjectiveSpecialLinearGroup.toPGL_injective, Subgroup.card_top]
    exact hc
  rw [← Subgroup.card_map_of_injective (f := (c.productCoordinates hF hσ i).toMonoidHom)
      (c.productCoordinates hF hσ i).injective,
    derived_coordinates c hF hσ i,
    Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
    Subgroup.card_bot, mul_one]
  exact hr

private theorem small_eq_derived_intersection (i : Bool) :
    c.small hF hσ i = (c.T : Subgroup _) ⊓
      (commutator (c.centralizerAt i)).map (c.centralizerAt i).subtype := by
  apply le_antisymm
  · exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
  · rintro x ⟨hT, y, hy, rfl⟩
    refine ⟨⟨hT, y, ?_, rfl⟩, y, hy, rfl⟩
    exact ((derived_mem_iff c hF hσ i y).mp hy).1

variable [Finite (innerModel F σ)]

/-- The distinguished small subgroup is the Sylow four-group in the
local derived group of order sixty. -/
theorem local_small_card (i : Bool) : Nat.card (c.small hF hσ i) = 4 := by
  let P := c.T.subtype (c.sylow_le i)
  let D := commutator (c.centralizerAt i)
  obtain ⟨Q, hQ⟩ := P.exists_sylow_map_eq_inf_of_normal D
  have hcard : Nat.card (Q : Subgroup D) = 4 := by
    rw [Q.card_eq_multiplicity, derived_card c hF hσ i]
    decide +kernel
  have hmap : ((Q : Subgroup D).map D.subtype).map (c.centralizerAt i).subtype =
      c.small hF hσ i := by
    rw [hQ, small_eq_derived_intersection, Subgroup.map_inf _ _ _
      (c.centralizerAt i).subtype_injective]
    change ((c.T : Subgroup _).subgroupOf (c.centralizerAt i)).map
      (c.centralizerAt i).subtype ⊓ _ = _
    rw [Subgroup.map_subgroupOf_eq_of_le (c.sylow_le i)]
  rw [← hmap, Subgroup.card_map_of_injective Subtype.val_injective,
    Subgroup.card_map_of_injective Subtype.val_injective]
  exact hcard

namespace ActorFusion
/-- The finite symmetric-group calculation left after intrinsic marking.
The first projection has order four and is even; the subgroup is not
contained in the zero graph. The witness is an actual product element. -/
@[expose] def SymmetricSpreading (Z : Type*) [Group Z] : Prop :=
  ∀ (P : Sylow 2 (Equiv.Perm (Fin 5) × Z))
    (B : Subgroup (Equiv.Perm (Fin 5) × Z)),
    B ≤ (P : Subgroup _) →
    Nat.card (B.map (MonoidHom.fst _ _)) = 4 →
    B.map (MonoidHom.fst _ _) ≤ alternatingGroup (Fin 5) →
    ¬ B ≤ (alternatingGroup (Fin 5)).prod ⊥ →
    ∃ g : Equiv.Perm (Fin 5) × Z,
      B.map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup _) ∧
      (P : Subgroup _) ⊓ (alternatingGroup (Fin 5)).prod ⊤ ≤
        B ⊔ B.map (MulAut.conj g).toMonoidHom
end ActorFusion

/-- Transport a concrete symmetric-product conjugator through the supplied
comparison, retaining its actual ambient value and the common Sylow. -/
theorem local_spread_of_symmetricSpreading
    (hspread : ActorFusion.SymmetricSpreading (zpowers σ))
    (i : Bool) (A : Subgroup (innerModel F σ)) (hA : c.Eligible A)
    (hn : ¬ c.IsPositioned hF hσ i A)
    (hlin : ¬ A ≤ pGammaL2LinearKernel F (innerModel F σ)) :
    ∃ g ∈ c.centralizerAt i,
      A.map (MulAut.conj g).toMonoidHom ≤ (c.T : Subgroup _) ∧
      c.large hF hσ i ≤ A ⊔ A.map (MulAut.conj g).toMonoidHom := by
  let C := c.centralizerAt i
  let K := FixedPoints.subfield (zpowers σ) F
  let ε : PGL2 K ≃* Equiv.Perm (Fin 5) :=
    (Theory.PSL2.exists_pgl2_five_equiv K (fixed_card hF hσ)).some
  let e := (c.productCoordinates hF hσ i).trans
    (MulEquiv.prodCongr ε (MulEquiv.refl (zpowers σ)))
  let P := (c.T.subtype (c.sylow_le i)).mapSurjective (f := e.toMonoidHom) e.surjective
  let B := (A.subgroupOf C).map e.toMonoidHom
  have hAC : A ≤ C := hA.2.1.trans (c.sylow_le i)
  have hε (x : PGL2 K) : ε x ∈ alternatingGroup (Fin 5) ↔
      x ∈ (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
    rw [← Theory.PSL2.pgl2_five_equiv_maps_psl K (fixed_card hF hσ) ε]
    simp only [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hfirst : B.map (MonoidHom.fst _ _) =
      ((A.subgroupOf C).map (c.projection hF hσ i)).map ε.toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hBT : B ≤ (P : Subgroup _) :=
    map_mono (subgroupOf_mono C hA.2.1)
  have hcard : Nat.card (B.map (MonoidHom.fst _ _)) = 4 := by
    rw [hfirst, Subgroup.card_map_of_injective ε.injective]
    exact ((hA.not_isPositioned_iff c hF hσ i).mp hn).1
  have heven : B.map (MonoidHom.fst _ _) ≤ alternatingGroup (Fin 5) := by
    rw [hfirst, ← Theory.PSL2.pgl2_five_equiv_maps_psl K (fixed_card hF hσ) ε]
    exact map_mono ((hA.not_isPositioned_iff c hF hσ i).mp hn).2
  have hnonzero : ¬ B ≤ (alternatingGroup (Fin 5)).prod ⊥ := by
    intro hz
    apply hlin
    intro x hx
    let y : C := ⟨x, hAC hx⟩
    have hb : e y ∈ B := ⟨y, hx, rfl⟩
    have hy := hz hb
    have hd : y ∈ commutator C := (derived_mem_iff c hF hσ i y).mpr
      ⟨(hε _).mp hy.1, hy.2⟩
    exact derived_linear c hF i ⟨y, hd, rfl⟩
  obtain ⟨g, hgP, hgjoin⟩ := hspread P B hBT hcard heven hnonzero
  let t : C := e.symm g
  have hj (x : C) : e (t * x * t⁻¹) = g * e x * g⁻¹ := by
    simp only [map_mul, map_inv, t, e.apply_symm_apply]
  have hinv (x : C) : e.symm (g * e x * g⁻¹) = t * x * t⁻¹ := by
    apply e.injective
    rw [e.apply_symm_apply, hj]
  refine ⟨t, t.property, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    let y : C := ⟨x, hAC hx⟩
    have hb : g * e y * g⁻¹ ∈ B.map (MulAut.conj g).toMonoidHom :=
      ⟨e y, ⟨y, hx, rfl⟩, rfl⟩
    have hp := hgP hb
    change g * e y * g⁻¹ ∈
      ((c.T : Subgroup _).subgroupOf C).map e.toMonoidHom at hp
    rw [Subgroup.mem_map_equiv, hinv] at hp
    exact hp
  · intro x hx
    let y : C := ⟨x, c.sylow_le i hx.1⟩
    have hL : e y ∈ (P : Subgroup _) ⊓ (alternatingGroup (Fin 5)).prod ⊤ := by
      refine ⟨⟨y, hx.1, rfl⟩, ?_, trivial⟩
      apply (hε _).mpr
      obtain ⟨z, hz, hzx⟩ := hx.2
      have hzy : z = y := Subtype.ext hzx
      exact hzy ▸ hz
    have hget : (B ⊔ B.map (MulAut.conj g).toMonoidHom).map
        (C.subtype.comp e.symm.toMonoidHom) ≤
        A ⊔ A.map (MulAut.conj (t : innerModel F σ)).toMonoidHom := by
      rw [Subgroup.map_sup]
      apply sup_le
      · rintro _ ⟨b, ⟨z, hz, rfl⟩, rfl⟩
        apply (le_sup_left : A ≤ A ⊔ A.map
          (MulAut.conj (t : innerModel F σ)).toMonoidHom)
        simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          e.symm_apply_apply, Subgroup.coe_subtype] using
          (show (z : innerModel F σ) ∈ A from hz)
      · rintro _ ⟨b, ⟨d, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
        apply (le_sup_right : A.map (MulAut.conj (t : innerModel F σ)).toMonoidHom ≤
          A ⊔ A.map (MulAut.conj (t : innerModel F σ)).toMonoidHom)
        refine ⟨z, hz, ?_⟩
        change (t : innerModel F σ) * z * (t : innerModel F σ)⁻¹ =
          ((e.symm (g * e z * g⁻¹) : C) : innerModel F σ)
        rw [hinv]
        rfl
    have hv := hget ⟨e y, hgjoin hL, rfl⟩
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      e.symm_apply_apply, Subgroup.coe_subtype] using hv

/-- All characteristic-five local clauses, with only the isolated finite
symmetric-product calculation left explicit. Its unconditional producer
must be supplied before this task's final assembly is complete. -/
theorem localCalculation_of_symmetricSpreading
    (hspread : ActorFusion.SymmetricSpreading (zpowers σ)) :
    ActorFusion.LocalCalculation c hF hσ where
  small_card := local_small_card c hF hσ
  linear_marking := local_linear_marking c hF hσ
  spread := local_spread_of_symmetricSpreading c hF hσ hspread

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.Frame

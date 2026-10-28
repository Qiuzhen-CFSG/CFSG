module
public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.TwoCoreParabolics
public import Theory.SpecificGroups.PSL3.BinaryOddCenterCover.FullTorusFixer
public import Theory.GroupTheory.GeneralizedFitting.TwoCoreImageComparison

/-!
# The overlap two-core in nontrivial scalar covers at field four

In an odd central cover of PSL₃(4), the overlap two-core centralizes the
covering center: both are normal in the overlap and have coprime orders.
Its projective action also fixes the full Borel torus modulo the unipotent
radical, by the normality of the two-core. The field-four torus-fixer theorem
therefore excludes diagram movement when the covering center is nontrivial.
Consequently both whole parabolics are preserved over the prescribed map.

The source application uses the exclusion of the intrinsic PSL₃(4) quotient
to retain a nontrivial scalar center. No replacement of the cover by its
projective image is made. Source: Aschbacher–Smith 5.1.11(3), 5.2.1–2,
printed pp.635,646–649 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Matrix.PSL3.LinearThree.OuterExtensions
open Matrix.PSL3.CartanActions
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {G : Type*} [Group G]

omit [CharP F 2] in
private theorem twoCore_fixes_torus {n : ℕ}
    (hF : Nat.card F = 2 ^ n)
    (N M : Subgroup G) [N.Normal] (e : PSL(3,F) ≃* N)
    (hM : M.comap (N.subtype.comp e.toMonoidHom) = borel F)
    (s : M) (hs : s ∈ pCore 2 M) :
    (borel F).map (markedAction N e s.val).toMonoidHom = borel F ∧
    ∀ x ∈ torus F, markedAction N e s.val x * x⁻¹ ∈ unipotent F := by
  let f := N.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := N.subtype_injective.comp e.injective
  let j : borel F →* M :=
    (f.comp (borel F).subtype).codRestrict M (fun x => by
      change f x.val ∈ M
      exact (show x.val ∈ M.comap f from hM.symm ▸ x.property))
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (hf (congrArg (fun z : M => z.val) h))
  have hcore : (pCore 2 M).comap j ≤ pCore 2 (borel F) :=
    le_sSup ⟨inferInstance,pCore_isPGroup.comap_of_injective j hj⟩
  let a := markedAction N e s.val
  have hB := markedAction_preserves_borel N M e hM s.property
  refine ⟨hB,?_⟩
  change ∀ x ∈ torus F, a x * x⁻¹ ∈ unipotent F

  intro x hx
  let t : borel F := ⟨x,torus_le_borel F hx⟩
  let b : borel F := ⟨a x,hB.le (mem_map_of_mem _ t.property)⟩
  have hb : b * t⁻¹ ∈ pCore 2 (borel F) := by
    apply hcore
    change j (b * t⁻¹) ∈ pCore 2 M
    have he : j (b * t⁻¹) = s * j t * s⁻¹ * (j t)⁻¹ := by
      apply Subtype.ext
      change f (a x * x⁻¹) = s.val * f x * s.val⁻¹ * (f x)⁻¹
      rw [map_mul,map_inv]
      exact congrArg (fun z => z * (f x)⁻¹) (markedAction_apply N e s.val x)
    rw [he]
    exact (commutator_le_left (pCore 2 M) ⊤)
      (commutator_mem_commutator hs (mem_top (j t)))
  rw [BorelQuotient.twoCore_eq F hF] at hb
  exact hb

variable {X Y : Type*} [Group X] [Group Y] [Finite X]

/-- In a nontrivial odd scalar cover at field four, the overlap two-core
preserves each projective parabolic over the original quotient map. -/
theorem twoCore_normalizes_parabolic_four_cover
    (hF : Nat.card F = 4) (C M : Subgroup X) [C.Normal] [IsQuasisimple C]
    (q : X →* Y) (hq : Function.Surjective q)
    (hk : q.ker = (center C).map C.subtype) (hkM : q.ker ≤ M)
    (ho : Odd (Nat.card (center C))) (hz : center C ≠ ⊥)
    (e : PSL(3,F) ≃* C.map q)
    (hM : (M.map q).comap ((C.map q).subtype.comp e.toMonoidHom) = borel F)
    (i : Bool) :
    (M.pCoreIn 2).map q ≤ normalizer ((RootPlaneGeometry.parabolic F i).map
      ((C.map q).subtype.comp e.toMonoidHom) : Set Y) := by
  let N := C.map q
  let : N.Normal := Normal.map inferInstance q hq
  let r := e.symm.toMonoidHom.comp (q.subgroupMap C)
  have hr : Function.Surjective r := e.symm.surjective.comp (q.subgroupMap_surjective C)
  have hzP : center PSL(3,F) = ⊥ := Group.IsPerfect.center_quotient_center_eq_bot SL(3,F)
  let ec : C ⧸ center C ≃* PSL(3,F) :=
    (IsQuasisimple.centralQuotientEquiv r hr).trans
      ((QuotientGroup.quotientMulEquivOfEq hzP).trans QuotientGroup.quotientBot)
  have hec (x : C) : ec (QuotientGroup.mk x) = r x := rfl
  have hcM : (center C).map C.subtype ≤ M := hk ▸ hkM
  let Z := q.ker.subgroupOf M
  have hZodd : Odd (Nat.card Z) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hkM).toEquiv,hk,
      card_map_of_injective C.subtype_injective]
    exact ho
  have hcentral : pCore 2 M ≤ centralizer (Z : Set M) := by
    obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := M)).exists_card_eq
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply commutator_eq_bot_of_disjoint
    apply disjoint_of_coprime_natCard
    rw [hk]
    exact hZodd.coprime_two_right.symm.pow_left k
  rintro _ ⟨s,hs,rfl⟩
  obtain ⟨s0,hs,rfl⟩ := hs
  let a := C.normalizerMonoidHom ⟨s0.val,normalizer_eq_top (H := C) ▸ mem_top _⟩
  let b := markedAction N e (q s0.val)
  let v := q.subgroupMap M s0
  have hv : v ∈ pCore 2 (M.map q) := by
    exact (le_sSup ⟨Normal.map inferInstance _ (q.subgroupMap_surjective M),
      pCore_isPGroup.map _⟩ : (pCore 2 M).map (q.subgroupMap M) ≤ pCore 2 (M.map q)) (mem_map_of_mem _ hs)
  obtain ⟨hB,hfix⟩ := twoCore_fixes_torus (n := 2) (by simpa using hF) N (M.map q) e hM v hv
  have hcomm (x : C) : b (ec (QuotientGroup.mk x)) = ec (QuotientGroup.mk (a x)) := by
    rw [hec,hec]
    apply e.injective
    apply Subtype.ext
    rw [markedAction_apply]
    change q s0.val * (e (e.symm (q.subgroupMap C x))).val * (q s0.val)⁻¹ =
      (e (e.symm (q.subgroupMap C (a x)))).val
    simp only [e.apply_symm_apply]
    change q s0.val * q x.val * (q s0.val)⁻¹ = q (s0.val * x.val * s0.val⁻¹)
    simp only [map_mul,map_inv]
  have hcenter (z : C) (hz : z ∈ center C) : a z = z := by
    have hzM : z.val ∈ M := hcM (mem_map_of_mem _ hz)
    have hzZ : (⟨z.val,hzM⟩ : M) ∈ Z := by
      change z.val ∈ q.ker
      rw [hk]
      exact mem_map_of_mem _ hz
    have hc := mem_centralizer_iff.mp (hcentral hs) _ hzZ
    apply Subtype.ext
    change s0.val * z.val * s0.val⁻¹ = z.val
    have hh := congrArg Subtype.val hc
    change z.val * s0.val = s0.val * z.val at hh
    rw [←hh,mul_inv_cancel_right]
  have hd : PreservesPointType F b ∧ PreservesLineType F b := by
    by_contra hh
    exact hz (BinaryOddCenterCover.FullTorusFixer.center_eq_bot_of_diagram_moving_torus_fixer
      hF ec ho a b hcomm hcenter hB hfix hh)
  have hdiag : diagramAction F (n := 2) (by decide) (by simpa using hF) b = 1 := by
    change b ∈ (diagramAction F (n := 2) (by decide) (by simpa using hF)).ker
    rw [diagramAction_ker]
    exact (mem_diagramTrivial_iff F b).mpr hd
  have hU := FullTorusFixer.map_unipotent_of_map_borel (n := 2) (by simpa using hF) b hB
  have hp := Matrix.PSL3Even.MinimalParabolicWitness.map_parabolic_of_preserves_unipotent
    F (n := 2) (by decide) (by simpa using hF) b hU i
  rw [hdiag] at hp
  apply mem_normalizer_iff_map_conj_eq.mpr
  calc
    _ = ((RootPlaneGeometry.parabolic F i).map b.toMonoidHom).map
        (N.subtype.comp e.toMonoidHom) := by
      rw [Subgroup.map_map,Subgroup.map_map]
      congr 1
      ext x
      exact (markedAction_apply N e (q s0.val) x).symm
    _ = _ := by rw [hp]; rfl
end Matrix.PSL3.LinearThree.OuterExtensions

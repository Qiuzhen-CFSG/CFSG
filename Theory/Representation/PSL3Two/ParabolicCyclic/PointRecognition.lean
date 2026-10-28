module

public import Theory.Representation.PSL3Two.ParabolicCyclic.Seed

/-!
# Natural recognition from a point-fixed parabolic seed

A nonzero cyclic vector fixed by the point parabolic of SL₃(2), whose
line-parabolic orbit spans a plane, generates the actual natural module.
The point stabilizer gives an equivariant map from the point permutation
module. The two-dimensional seed relation transports to every Fano line,
since every ordered pair of distinct nonzero vectors extends to a determinant-one
basis. Thus the map on nonzero vectors extends by zero to a linear equivariant
map from the natural module. Point transitivity proves injectivity, and cyclic
generation proves surjectivity.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Lemma H.5.5,
printed p.386 (PDF p.397). The natural module called V there is `W` here.
-/

@[expose] public section

open Representation Matrix
namespace BinaryLinearThree.ParabolicCyclic
open FanoDecomposition FanoCoreStructure
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The coordinate point parabolic is exactly the stabilizer of the marked Fano point. -/
theorem pointParabolic_stabilizer_iff : ∀ g : Group,
    g ∈ Matrix.PSL3Two.pointParabolicSL ↔
      pointPerm g Matrix.PSL3Two.flagPoint = Matrix.PSL3Two.flagPoint := by
  simp only [Matrix.PSL3Two.mem_pointParabolicSL_iff, Subtype.ext_iff]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem pair_completion : ∀ p q : Point, p ≠ q → ∃ v : Vector,
    (Matrix.of ![p.val, q.val, v]).transpose.det = 1 := by
  decide +kernel

private theorem pair_reachable (p q : Point) (hpq : p ≠ q) :
    ∃ g : Group, pointPerm g Matrix.PSL3Two.flagPoint = p ∧
      pointPerm g (pointPerm lineCycle Matrix.PSL3Two.flagPoint) = q := by
  obtain ⟨v, hv⟩ := pair_completion p q hpq
  let g : Group := ⟨(Matrix.of ![p.val, q.val, v]).transpose, hv⟩
  refine ⟨g, ?_, ?_⟩
  · apply Subtype.ext
    change (Matrix.of ![p.val, q.val, v]).transpose *ᵥ ![1,0,0] = p.val
    ext i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · apply Subtype.ext
    change (Matrix.of ![p.val, q.val, v]).transpose *ᵥ ![0,1,0] = q.val
    ext i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

private theorem single_action (g : Group) (p : Point) :
    pointRepresentation g (Pi.single p 1) = Pi.single (pointPerm g p) 1 := by
  ext q
  change (Pi.single p (1 : ZMod 2) : Point → ZMod 2) ((pointPerm g).symm q) =
    (Pi.single (pointPerm g p) (1 : ZMod 2) : Point → ZMod 2) q
  simp only [Pi.single_apply, Equiv.symm_apply_eq]

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

/-- A point-fixed cyclic vector is the marked image of a point-permutation quotient. -/
theorem point_quotient (ρ : Representation (ZMod 2) Group M) (m : M)
    (hfixed : ∀ g ∈ Matrix.PSL3Two.pointParabolicSL, ρ g m = m)
    (hgen : orbitSpan ρ ⊤ m = ⊤) :
    ∃ f : pointRepresentation.IntertwiningMap ρ,
      Function.Surjective f ∧ f (Pi.single Matrix.PSL3Two.flagPoint 1) = m := by
  exact cyclic_permutation_quotient pointPerm Matrix.PSL3Two.flagPoint
    Matrix.PSL3Two.pointParabolicSL pointParabolic_stabilizer_iff
    SimpleHeadQuotientObstruction.point_reachable ρ m hfixed hgen

private theorem point_value_add
    (ρ : Representation (ZMod 2) Group M) (m : M)
    (hfixed : ∀ g ∈ Matrix.PSL3Two.borelSL, ρ g m = m)
    (hdim : Module.finrank (ZMod 2) (orbitSpan ρ Matrix.PSL3Two.lineParabolicSL m) = 2)
    (f : pointRepresentation.IntertwiningMap ρ)
    (hf : f (Pi.single Matrix.PSL3Two.flagPoint 1) = m)
    (p q r : Point) (hsum : p.val + q.val = r.val) :
    f (Pi.single p 1) + f (Pi.single q 1) = f (Pi.single r 1) := by
  let u (p : Point) := f (Pi.single p 1)
  have hu (g : Group) (p : Point) : u (pointPerm g p) = ρ g (u p) := by
    dsimp [u]
    rw [← single_action, f.isIntertwining]
  have hpq : p ≠ q := by
    intro he
    have hz : r.val = 0 := by simpa [he, ZModModule.add_self] using hsum.symm
    exact r.property hz
  obtain ⟨g, hgp, hgq⟩ := pair_reachable p q hpq
  have hc : (pointPerm (lineCycle ^ 2) Matrix.PSL3Two.flagPoint).val =
      Matrix.PSL3Two.flagPoint.val +
        (pointPerm lineCycle Matrix.PSL3Two.flagPoint).val := by decide
  have hgr : pointPerm g (pointPerm (lineCycle ^ 2) Matrix.PSL3Two.flagPoint) = r := by
    apply Subtype.ext
    change W g (pointPerm (lineCycle ^ 2) Matrix.PSL3Two.flagPoint).val = r.val
    rw [hc, map_add]
    exact (congrArg₂ (fun p q : Point => p.val + q.val) hgp hgq).trans hsum
  have hs : u Matrix.PSL3Two.flagPoint +
      u (pointPerm lineCycle Matrix.PSL3Two.flagPoint) +
      u (pointPerm (lineCycle ^ 2) Matrix.PSL3Two.flagPoint) = 0 := by
    rw [hu, hu]
    change f (Pi.single Matrix.PSL3Two.flagPoint 1) +
      ρ lineCycle (f (Pi.single Matrix.PSL3Two.flagPoint 1)) +
      ρ (lineCycle ^ 2) (f (Pi.single Matrix.PSL3Two.flagPoint 1)) = 0
    rw [hf]
    exact seed_relation ρ m hfixed hdim
  have ht := congrArg (ρ g) hs
  rw [map_add, map_add, map_zero, ← hu, ← hu, ← hu, hgp, hgq, hgr] at ht
  have hh := congrArg (· + u r) ht
  simpa only [add_assoc, ZModModule.add_self, add_zero, zero_add] using hh

private noncomputable def pointExtension (u : Point → M) (v : Vector) : M :=
  if h : v = 0 then 0 else u ⟨v, h⟩

omit [Module (ZMod 2) M] in
@[simp] private theorem pointExtension_zero (u : Point → M) : pointExtension u 0 = 0 := by
  simp [pointExtension]

omit [Module (ZMod 2) M] in
@[simp] private theorem pointExtension_point (u : Point → M) (p : Point) :
    pointExtension u p.val = u p := by
  simp [pointExtension, p.property]

private theorem pointExtension_add (u : Point → M)
    (hu : ∀ p q r : Point, p.val + q.val = r.val → u p + u q = u r)
    (v w : Vector) : pointExtension u (v + w) = pointExtension u v + pointExtension u w := by
  by_cases hv : v = 0
  · simp [hv]
  by_cases hw : w = 0
  · simp [hw]
  by_cases hvw : v + w = 0
  · have he : v = w := by
      have hh := congrArg (· + w) hvw
      simpa only [add_assoc, ZModModule.add_self, add_zero, zero_add] using hh
    simp [he, ZModModule.add_self]
  · simpa only [pointExtension, dif_neg hvw, dif_neg hv, dif_neg hw] using
      (hu ⟨v,hv⟩ ⟨w,hw⟩ ⟨v+w,hvw⟩ rfl).symm

private noncomputable def pointExtensionLinear (u : Point → M)
    (hu : ∀ p q r : Point, p.val + q.val = r.val → u p + u q = u r) :
    Vector →ₗ[ZMod 2] M where
  toFun := pointExtension u
  map_add' := pointExtension_add u hu
  map_smul' c v := by
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl <;> simp

/-- H.5.5: the source point-fixed cyclic seed hypotheses recognize the actual natural module. -/
theorem point_seed_equiv_natural (ρ : Representation (ZMod 2) Group M) (m : M)
    (hm : m ≠ 0)
    (hfixed : ∀ g ∈ Matrix.PSL3Two.pointParabolicSL, ρ g m = m)
    (hgen : orbitSpan ρ ⊤ m = ⊤)
    (hdim : Module.finrank (ZMod 2) (orbitSpan ρ Matrix.PSL3Two.lineParabolicSL m) = 2) :
    Nonempty (ρ.Equiv W) := by
  classical
  obtain ⟨f, _, hf⟩ := point_quotient ρ m hfixed hgen
  have hB : ∀ g ∈ Matrix.PSL3Two.borelSL, ρ g m = m :=
    fun g hg => hfixed g hg.1
  let u (p : Point) := f (Pi.single p 1)
  have hu (g : Group) (p : Point) : u (pointPerm g p) = ρ g (u p) := by
    dsimp [u]
    rw [← single_action, f.isIntertwining]
  let F : W.IntertwiningMap ρ := {
    toLinearMap := pointExtensionLinear u (point_value_add ρ m hB hdim f hf)
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro v
      change pointExtension u (W g v) = ρ g (pointExtension u v)
      by_cases hv : v = 0
      · simp [hv]
      let p : Point := ⟨v, hv⟩
      change pointExtension u (pointPerm g p).val = ρ g (pointExtension u p.val)
      rw [pointExtension_point, pointExtension_point, hu] }
  have hF (p : Point) : F p.val = u p := pointExtension_point u p
  have hFm : F Matrix.PSL3Two.flagPoint.val = m := (hF _).trans hf
  have hinj : Function.Injective F := by
    apply LinearMap.ker_eq_bot.mp
    apply le_bot_iff.mp
    intro v hv
    change v = 0
    by_contra hn
    obtain ⟨g, hg⟩ := SimpleHeadQuotientObstruction.point_reachable ⟨v, hn⟩
    have hgv : W g Matrix.PSL3Two.flagPoint.val = v := congrArg Subtype.val hg
    have hz : F (W g Matrix.PSL3Two.flagPoint.val) = 0 := by
      rw [hgv]
      exact hv
    rw [F.isIntertwining, hFm] at hz
    exact hm ((ρ.apply_bijective g).1 (hz.trans (map_zero (ρ g)).symm))
  have hsurj : Function.Surjective F := by
    apply LinearMap.range_eq_top.mp
    apply top_unique
    rw [← hgen]
    apply Submodule.span_le.mpr
    rintro _ ⟨g, _, rfl⟩
    refine ⟨W g Matrix.PSL3Two.flagPoint.val, ?_⟩
    change F (W g Matrix.PSL3Two.flagPoint.val) = ρ g m
    rw [F.isIntertwining, hFm]
  exact ⟨(F.ofBijective ⟨hinj, hsurj⟩).symm⟩

end BinaryLinearThree.ParabolicCyclic

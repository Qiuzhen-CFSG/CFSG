module
public import Theory.Representation.G2BinaryPointMovement
/-!
# Moving planes in the binary point-parabolic core

The E-coordinate of a unipotent actor vanishes when its Weyl conjugate stays
unipotent. An actor in that core moving the marked three-space therefore
moves the hyperplane onto a plane through the marked line. Three explicit
point-parabolic actors fuse these planes. This supplies the concrete linear
step used in Aschbacher–Smith 13.3.18, printed p.895.
-/

public section
namespace Atlas.G2.Natural.BinaryPointFlag
open Atlas.G2.Restricted.NaturalCoordinates Atlas.G2.Explicit Subgroup
open Representation.BinaryOffender

private theorem weylR_inverse : (weylR:Model F)⁻¹=weylR :=
  inv_eq_of_mul_eq_one_left (by simpa [pow_two] using (weylR_sq (K:=F)))

/-- The point-normalized unipotent core has no rootE coordinate. -/
theorem point_core_coordinate (t:Fin 6→F)
    (h: (weylR:Model F)*unipotentProduct t*weylR⁻¹∈unipotent) : t 4=0 := by
  rw [unipotent_eq_range] at h
  obtain ⟨s,hs⟩:=h
  have he:=congrArg
    (fun a:Model F=>Restricted.NaturalCoordinates.action F a (Pi.single 1 1) 2) hs
  simpa [weylR_inverse,unipotentProduct,map_mul,Module.End.mul_apply] using he.symm

/-- On the marked seed, only the two extreme quotient coordinates can move. -/
theorem point_core_fixes_seed_of_zero (t:Fin 6→F) (ht:t 4=0)
    (hd:t 3=0) (hf:t 5=0) (v:W) (hv:v∈seed) :
    Restricted.NaturalCoordinates.action F (unipotentProduct t) v=v := by
  obtain ⟨v3,v4,v5⟩:=(mem_seed v).mp hv
  ext i
  fin_cases i <;> simp [unipotentProduct,map_mul,Module.End.mul_apply,ht,hd,hf,v3,v4,v5]

/-- The point-core actors send every hyperplane displacement into the seed. -/
theorem point_core_hyperplane_displacement (t:Fin 6→F) (ht:t 4=0)
    (v:W) (hv:v∈hyperplane) :
    Restricted.NaturalCoordinates.action F (unipotentProduct t) v-v∈seed := by
  have v5: v 5=0 := (mem_hyperplane v).mp hv
  rw [mem_seed]
  simp [unipotentProduct,map_mul,Module.End.mul_apply,ht,v5]

/-- A point-core actor moving V₃ supplies its central line and a second
independent seed vector in the actual hyperplane displacement space. -/
theorem point_core_moving_plane (A Q:Subgroup (Model F))
    (hAQ:A≤Q) (hQ:Q≤unipotent)
    (hR:(weylR:Model F)∈normalizer (Q:Set (Model F)))
    (hm:∃x∈A,∃v∈seed,Restricted.NaturalCoordinates.action F x v≠v) :
    let M:=subspaceCommutator (Restricted.NaturalCoordinates.action F) hyperplane A
    Pi.single (0:Fin 6) (1:F)∈M ∧
      ∃w∈M,w∈seed ∧ (w 1≠0 ∨ w 2≠0) := by
  dsimp only
  let M:=subspaceCommutator (Restricted.NaturalCoordinates.action F) hyperplane A
  obtain ⟨x,hx,v,hv,hmove⟩:=hm
  have hxu:=hQ (hAQ hx)
  rw [unipotent_eq_range] at hxu
  obtain ⟨t,rfl⟩:=hxu
  have ht:t 4=0:=point_core_coordinate t
    (hQ ((mem_normalizer_iff.mp hR _).mp (hAQ hx)))
  have hd_or: t 3=1 ∨ t 5=1 := by
    by_contra hn
    push Not at hn
    have hd:t 3=0:=((by decide +kernel : ∀x:F,x=0∨x=1) _).resolve_right hn.1
    have hf:t 5=0:=((by decide +kernel : ∀x:F,x=0∨x=1) _).resolve_right hn.2
    exact hmove (point_core_fixes_seed_of_zero t ht hd hf v hv)
  have hM (w:W) (hw:w∈hyperplane) :
      Restricted.NaturalCoordinates.action F (unipotentProduct t) w-w∈M :=
    Submodule.subset_span ⟨unipotentProduct t,hx,w,hw,rfl⟩
  rcases hd_or with hd|hf
  · have he:Restricted.NaturalCoordinates.action F (unipotentProduct t) (Pi.single 2 1)-
        Pi.single 2 1=Pi.single 0 1 := by
      ext i
      fin_cases i <;> simp [unipotentProduct,map_mul,Module.End.mul_apply,ht,hd]
    refine ⟨he ▸ hM (Pi.single 2 1) (by simp),
      Restricted.NaturalCoordinates.action F (unipotentProduct t) (Pi.single 4 1)-Pi.single 4 1,
      hM _ (by simp),point_core_hyperplane_displacement t ht _ (by simp),Or.inl ?_⟩
    simp [unipotentProduct,map_mul,Module.End.mul_apply,ht,hd]
  · have he:Restricted.NaturalCoordinates.action F (unipotentProduct t) (Pi.single 1 1)-
        Pi.single 1 1=Pi.single 0 1 := by
      ext i
      fin_cases i <;> simp [unipotentProduct,map_mul,Module.End.mul_apply,ht,hf]
    refine ⟨he ▸ hM (Pi.single 1 1) (by simp),
      Restricted.NaturalCoordinates.action F (unipotentProduct t) (Pi.single 3 1)-Pi.single 3 1,
      hM _ (by simp),point_core_hyperplane_displacement t ht _ (by simp),Or.inr ?_⟩
    simp [unipotentProduct,map_mul,Module.End.mul_apply,ht,hf]

/-- The plane marked by the original first two natural coordinates. -/
def plane : Submodule F W := Submodule.span F {Pi.single 0 1,Pi.single 1 1}

/-- The marked source plane belongs to its original three-space. -/
theorem plane_le_seed : plane≤seed := by
  apply Submodule.span_le.mpr
  rintro w (rfl|hw)
  · simp
  · rw [Set.mem_singleton_iff] at hw
    rw [hw]
    simp

/-- The literal point-parabolic actors fuse the three planes through the
marked line, retaining the same displacement subspace and action maps. -/
theorem fuse_seed_plane (S:Submodule F W)
    (h0:Pi.single (0:Fin 6) (1:F)∈S) (w:W) (hw:w∈S)
    (hs:w∈seed) (hn:w 1≠0 ∨ w 2≠0) :
    ∃a∈BinaryParabolicPair.derivedSecondAmbient,
      plane≤S.map (Restricted.NaturalCoordinates.action F a) := by
  obtain ⟨w3,w4,w5⟩:=(mem_seed w).mp hs
  have finish (a:Model F) (ha:a∈BinaryParabolicPair.derivedSecondAmbient)
      (hf:Restricted.NaturalCoordinates.action F a (Pi.single 0 1)=Pi.single 0 1)
      (he:Restricted.NaturalCoordinates.action F a w=w 0•Pi.single 0 1+Pi.single 1 1) :
      ∃a∈BinaryParabolicPair.derivedSecondAmbient,
        plane≤S.map (Restricted.NaturalCoordinates.action F a) := by
    have h0m:Pi.single (0:Fin 6) (1:F)∈S.map (Restricted.NaturalCoordinates.action F a) :=
      ⟨_,h0,hf⟩
    have h1m:Pi.single (1:Fin 6) (1:F)∈S.map (Restricted.NaturalCoordinates.action F a) := by
      have hwm:Restricted.NaturalCoordinates.action F a w∈S.map (Restricted.NaturalCoordinates.action F a) := ⟨w,hw,rfl⟩
      have hh:Restricted.NaturalCoordinates.action F a w-w 0•Pi.single 0 1=Pi.single 1 1 := by
        rw [he,add_sub_cancel_left]
      exact hh ▸ (S.map _).sub_mem hwm ((S.map _).smul_mem _ h0m)
    refine ⟨a,ha,Submodule.span_le.mpr ?_⟩
    intro v hv
    rcases hv with rfl|hv
    · exact h0m
    · exact (Set.mem_singleton_iff.mp hv).symm ▸ h1m
  by_cases h1:w 1=0
  · have h2:w 2=1:=((by decide +kernel : ∀x:F,x=0∨x=1) _).resolve_left
      (hn.resolve_left (not_not_intro h1))
    refine finish weylR point_actor_membership.2.1 ?_ ?_
    · ext i;fin_cases i <;> simp
    · ext i;fin_cases i <;> simp [h1,h2,w3,w4,w5]
  · have h1':w 1=1:=((by decide +kernel : ∀x:F,x=0∨x=1) _).resolve_left h1
    rcases (by decide +kernel : ∀x:F,x=0∨x=1) (w 2) with h2|h2
    · refine finish 1 (Subgroup.one_mem _) ?_ ?_
      · simp
      · ext i;fin_cases i <;> simp [h1',h2,w3,w4,w5]
    · refine finish (weylR*rootE 1)
        (BinaryParabolicPair.derivedSecondAmbient.mul_mem point_actor_membership.2.1 point_actor_membership.1) ?_ ?_
      · ext i;fin_cases i <;> simp [map_mul,Module.End.mul_apply]
      · have h11:(1:F)+1=0:=by decide
        ext i;fin_cases i <;> simp [map_mul,Module.End.mul_apply,h1',h2,w3,w4,w5,h11]

/-- A genuinely moving elementary-conjugate actor produces the original
plane after an actual point-parabolic conjugation. -/
theorem cross_displacement_contains_conjugate_plane (A Q:Subgroup (Model F))
    (hAQ:A≤Q) (hQ:Q≤unipotent)
    (hR:(weylR:Model F)∈normalizer (Q:Set (Model F)))
    (hm:∃x∈A,∃v∈seed,Restricted.NaturalCoordinates.action F x v≠v) :
    ∃a∈BinaryParabolicPair.derivedSecondAmbient,
      plane≤(subspaceCommutator (Restricted.NaturalCoordinates.action F) hyperplane A).map
        (Restricted.NaturalCoordinates.action F a) := by
  obtain ⟨h0,w,hw,hs,hn⟩:=point_core_moving_plane A Q hAQ hQ hR hm
  exact fuse_seed_plane _ h0 w hw hs hn
end Atlas.G2.Natural.BinaryPointFlag

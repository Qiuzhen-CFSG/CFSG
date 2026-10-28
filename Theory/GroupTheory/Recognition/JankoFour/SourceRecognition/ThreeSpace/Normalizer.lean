module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.Commutator
public import Theory.ElementaryAbelian.ExtraspecialNormalCommutator

/-!
# Fusion inside the three-space normalizer

Each of the first two extraspecial cores normalizes the original three-space.
Their inner conjugations interchange the two marked central involutions.
The original cubic scalar cycles the three nonzero quotient vectors; inner
core fusion supplies both elements over each vector. Thus every nonidentity
element of the actual three-space is conjugate to z inside its ambient
normalizer. Transporting the original core by these very conjugators proves
that all seven cores contain and normalize the same three-space.

Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*,
Invent. Math. 105 (1991), the passage from (4.3)(2) to (4.4), p.597,
DOI 10.1007/BF01232280. This constructs the fusion and core-containment
inputs for K; it does not yet assert the special-core or tensor description.
-/

@[expose] public section
open Subgroup Sporadic.Mathieu
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Janko4.InvolutionCentralizers.First.QuotientExtension
open M22TripleCover.Ambient
open scoped commutatorElement
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open VectorOrbits
variable {G : Type*} [Group G] [Finite G] {z : G}

private theorem mem_marker_line {x y : G} (hx : orderOf x = 2)
    (hy : y ∈ zpowers x) : y = 1 ∨ y = x := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf,hx] at hy
  obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hy
  have hn2 := Finset.mem_range.mp hn
  interval_cases n <;> simp_all

private theorem type_of_conj (h : IsTypeJ4 z) {r : G} (hr : IsConj z r) : IsTypeJ4 r := by
  obtain ⟨g,rfl⟩ := isConj_iff.mp hr
  exact type_map h (MulAut.conj g)

theorem core_normalizes_between (h : IsTypeJ4 z) (Z : Subgroup G)
    (hZ : Z ≤ ambientCore z) (hz : z ∈ Z) :
    ambientCore z ≤ normalizer (Z : Set G) := by
  let : IsExtraspecial 2 (ambientCore z) :=
    IsExtraspecial.of_mulEquiv (LocalGeometry.coreEquivAmbient z) h.extraspecial
  apply extraspecial_le_normalizer_of_center_le (ambientCore z) Z hZ
  intro q hq
  have hm : (q : G) ∈ zpowers z := by
    rw [← LocalGeometry.ambientCore_center_image h]
    exact mem_map_of_mem _ hq
  exact (zpowers_le.mpr hz) hm

/-- The core itself supplies the nontrivial flip of each noncentral coset. -/
theorem exists_core_flip (h : IsTypeJ4 z) {u : G}
    (huQ : u ∈ ambientCore z) (hu1 : u ≠ 1) (huz : u ≠ z) :
    ∃ q ∈ ambientCore z, q * u * q⁻¹ = z * u := by
  let Q := ambientCore z
  let : IsExtraspecial 2 Q :=
    IsExtraspecial.of_mulEquiv (LocalGeometry.coreEquivAmbient z) h.extraspecial
  let U : Q := ⟨u,huQ⟩
  let Z : Q := ⟨z,marker_mem_ambientCore z⟩
  have hUc : U ∉ center Q := by
    intro hc
    have hm : u ∈ zpowers z := by
      rw [← LocalGeometry.ambientCore_center_image h]
      exact mem_map_of_mem Q.subtype hc
    exact (mem_marker_line h.involution hm).elim hu1 huz
  have hZc : Z ∈ center Q := by
    apply mem_center_iff.mpr
    intro q
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (LocalGeometry.ambientCore_le z q.property)
  have he : QuotientGroup.mk' (center Q) U = QuotientGroup.mk' (center Q) (Z*U) := by
    rw [map_mul,(show QuotientGroup.mk' (center Q) Z = 1 from (QuotientGroup.eq_one_iff Z).mpr hZc),one_mul]
  obtain ⟨q,hq⟩ := isConj_iff.mp (IsExtraspecial.isConj_of_center_quotient_eq_prime (p := 2) hUc he)
  exact ⟨q,q.property,congrArg Subtype.val hq⟩

variable (h : IsTypeJ4 z)
variable (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
variable (X : Sylow 3 (LocalGeometry.CubicLift.subgroup e))
variable [IsExtraspecial 2 (core z)]

private theorem marker_mem_scalarPlane : z ∈ ambientScalarPlane h e X := by
  have hm : z ∈ (center (core z)).map (coreInclusion z) := by
    rw [coreInclusion,← Subgroup.map_map,LocalGeometry.core_center_image h]
    exact mem_zpowers z
  exact map_mono (center_le_scalarPlane h e X) hm

private theorem native_noncentral (r : core z)
    (hr : coreNativeEquiv h e X
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) r)) ≠ 0) : r ∉ center (core z) := by
  intro hc
  have he : Additive.ofMul (QuotientGroup.mk' (center (core z)) r) =
      (0 : CoreSpace (z := z)) := congrArg Additive.ofMul ((QuotientGroup.eq_one_iff r).mpr hc)
  exact hr (by rw [he,map_zero])

private theorem native_line_cases (v : M22TripleCover.BinarySpace) (hv : v ∈ ThreeSpace.Native.line) :
    v = 0 ∨ v = vector 4 ∨ v = vector 1467 ∨ v = vector 1471 := by
  obtain ⟨u,rfl⟩ := hv
  have hc : ∀ u : Fin 2 → ZMod 2,
      ThreeSpace.Native.lineMap u = 0 ∨ ThreeSpace.Native.lineMap u = vector 4 ∨
      ThreeSpace.Native.lineMap u = vector 1467 ∨ ThreeSpace.Native.lineMap u = vector 1471 := by
    decide +kernel
  exact hc u

omit [Finite G] in
private theorem fusion_trans (N : Subgroup G) {x y z : G}
    (hxy : ∃ a ∈ N, a*x*a⁻¹=y) (hyz : ∃ b ∈ N, b*y*b⁻¹=z) :
    ∃ c ∈ N, c*x*c⁻¹=z := by
  obtain ⟨a,ha,ea⟩ := hxy
  obtain ⟨b,hb,eb⟩ := hyz
  refine ⟨b*a,N.mul_mem hb ha,?_⟩
  calc
    _ = b*(a*x*a⁻¹)*b⁻¹ := by group
    _ = z := by rw [ea,eb]

/-- Equal nonzero native vectors fuse by an element of the original core,
hence by an element normalizing the actual three-space. -/
private theorem scalarPlane_core_fusion (r q : core z)
    (hr : coreNativeEquiv h e X
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) r)) ≠ 0)
    (he : coreNativeEquiv h e X (Additive.ofMul (QuotientGroup.mk' (center (core z)) r)) =
      coreNativeEquiv h e X (Additive.ofMul (QuotientGroup.mk' (center (core z)) q))) :
    ∃ n ∈ normalizer (ambientScalarPlane h e X : Set G),
      n * ((r : centralizer z) : G) * n⁻¹ = ((q : centralizer z) : G) := by
  have hcoset := congrArg Additive.toMul ((coreNativeEquiv h e X).injective he)
  obtain ⟨n,hn⟩ := isConj_iff.mp (IsExtraspecial.isConj_of_center_quotient_eq_prime
    (p := 2) (native_noncentral h e X r hr) hcoset)
  refine ⟨((n : centralizer z) : G),scalarPlane_core_normalizes h e X
    (mem_map_of_mem (centralizer z).subtype n.property),?_⟩
  exact congrArg (fun q : core z => ((q : centralizer z) : G)) hn

/-- The two original cores fuse the first two markers inside N_G(Z). -/
theorem scalarPlane_marker_fusion (r : core z)
    (hr : IsConj z ((r : centralizer z) : G)) (hne : ((r : centralizer z) : G) ≠ z)
    (hmark : coreNativeEquiv h e X
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) r)) = VectorOrbits.decode 4)
    (a : centralizer z)
    (ha : coreAmbientHom h e X (QuotientGroup.mk' (core z) a) = scalarElement) :
    ∃ n ∈ normalizer (ambientScalarPlane h e X : Set G),
      n * z * n⁻¹ = ((r : centralizer z) : G) := by
  let R : G := ((r : centralizer z) : G)
  let Z := ambientScalarPlane h e X
  let N := normalizer (Z : Set G)
  have htype : IsTypeJ4 R := type_of_conj h hr
  have hZr : Z ≤ ambientCore R := by
    change ambientScalarPlane h e X ≤ ambientCore R
    rw [ambientScalarPlane_eq_triple h e X r hr hne hmark a ha]
    exact inf_le_left.trans inf_le_right
  have hz : z ∈ Z := marker_mem_scalarPlane h e X
  have hrZ : R ∈ Z := by
    change R ∈ ambientScalarPlane h e X
    rw [ambientScalarPlane_eq_triple h e X r hr hne hmark a ha,
      triple_core_eq_closure h e X r hr hne hmark a ha]
    exact subset_closure (by simp [R])
  have hQr : ambientCore R ≤ N := core_normalizes_between htype Z hZr hrZ
  have hR1 : R ≠ 1 := fun he => by have hi := htype.involution; simp [he] at hi
  have hz1 : z ≠ 1 := fun he => by have hi := h.involution; simp [he] at hi
  obtain ⟨b,hb,eb⟩ := exists_core_flip h (mem_map_of_mem _ r.property) hR1 hne
  change b*R*b⁻¹=z*R at eb
  obtain ⟨c,hc,ec⟩ := exists_core_flip htype (hZr hz) hz1 (Ne.symm hne)
  have hcmt : R*z = z*R := mem_centralizer_singleton_iff.mp (r : centralizer z).property
  refine ⟨b⁻¹*c,N.mul_mem (N.inv_mem (scalarPlane_core_normalizes h e X hb)) (hQr hc),?_⟩
  calc
    _ = b⁻¹*(c*z*c⁻¹)*b := by group
    _ = b⁻¹*(b*R*b⁻¹)*b := by rw [ec,hcmt,eb]
    _ = R := by group

/-- Every nonidentity element of the original three-space is conjugate to z
by an element of its actual ambient normalizer. -/
theorem scalarPlane_normalizer_transitive (r : core z)
    (hr : IsConj z ((r : centralizer z) : G)) (hne : ((r : centralizer z) : G) ≠ z)
    (hmark : coreNativeEquiv h e X
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) r)) = VectorOrbits.decode 4)
    (a : centralizer z)
    (ha : coreAmbientHom h e X (QuotientGroup.mk' (core z) a) = scalarElement) :
    ∀ t ∈ ambientScalarPlane h e X, t ≠ 1 →
      ∃ n ∈ normalizer (ambientScalarPlane h e X : Set G), n*z*n⁻¹=t := by
  let N := normalizer (ambientScalarPlane h e X : Set G)
  have hzR := scalarPlane_marker_fusion h e X r hr hne hmark a ha
  have haN : (a : G) ∈ N := scalarPlane_cubic_normalizes h e X a ha
  have hra : coreNativeEquiv h e X
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) (MulAut.conjNormal a r))) = vector 1467 := by
    have he := coreAmbientHom_intertwines h e X (QuotientGroup.mk' (core z) a)
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) r))
    rw [coreBinaryRepresentation_apply,toMul_ofMul,coreQuotientAction_mk,ha,hmark] at he
    rw [he,ThreeSpace.Native.scalar_action]
    decide +kernel
  have hrai := scalar_conjugate_mark h e X r hmark a ha
  rintro t ⟨q,hq,rfl⟩ hq1
  rcases native_line_cases _ hq with hv | hv | hv | hv
  · have he : QuotientGroup.mk' (center (core z)) q = 1 :=
      congrArg Additive.toMul ((coreNativeEquiv h e X).injective
        (hv.trans (map_zero (coreNativeEquiv h e X)).symm))
    have hc := (QuotientGroup.eq_one_iff q).mp he
    have hm : ((q : centralizer z) : G) ∈ zpowers z := by
      rw [← LocalGeometry.core_center_image h]
      exact mem_map_of_mem _ (mem_map_of_mem _ hc)
    have hqz := (mem_marker_line h.involution hm).resolve_left hq1
    refine ⟨1,N.one_mem,?_⟩
    simpa only [one_mul,inv_one,mul_one,coreInclusion,MonoidHom.comp_apply,
      Subgroup.subtype_apply] using hqz.symm
  · apply fusion_trans N hzR
    exact scalarPlane_core_fusion h e X r q
      (by rw [hmark]; decide +kernel) (hmark.trans hv.symm)
  · apply fusion_trans N hzR
    apply fusion_trans N (y := ((MulAut.conjNormal a r : centralizer z) : G))
    · exact ⟨a,haN,rfl⟩
    · exact scalarPlane_core_fusion h e X (MulAut.conjNormal a r) q
        (by rw [hra]; decide +kernel) (hra.trans hv.symm)
  · apply fusion_trans N hzR
    apply fusion_trans N (y := ((MulAut.conjNormal a⁻¹ r : centralizer z) : G))
    · exact ⟨(a : G)⁻¹,N.inv_mem haN,by simp⟩
    · exact scalarPlane_core_fusion h e X (MulAut.conjNormal a⁻¹ r) q
        (by rw [hrai]; decide +kernel) (hrai.trans hv.symm)

/-- Each of the seven original cores contains the same three-space. -/
theorem scalarPlane_le_each_core (r : core z)
    (hr : IsConj z ((r : centralizer z) : G)) (hne : ((r : centralizer z) : G) ≠ z)
    (hmark : coreNativeEquiv h e X
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) r)) = VectorOrbits.decode 4)
    (a : centralizer z)
    (ha : coreAmbientHom h e X (QuotientGroup.mk' (core z) a) = scalarElement) :
    ∀ t ∈ ambientScalarPlane h e X, t ≠ 1 → ambientScalarPlane h e X ≤ ambientCore t := by
  intro t ht ht1
  obtain ⟨n,hn,he⟩ := scalarPlane_normalizer_transitive h e X r hr hne hmark a ha t ht ht1
  have hle : ambientScalarPlane h e X ≤ ambientCore z := by
    rintro _ ⟨q,_,rfl⟩
    exact mem_map_of_mem (centralizer z).subtype q.property
  have hm := Subgroup.map_mono (f := (MulAut.conj n).toMonoidHom) hle
  have hnmap : (ambientScalarPlane h e X).map (MulAut.conj n).toMonoidHom =
      ambientScalarPlane h e X := mem_normalizer_iff_map_conj_eq.mp hn
  rw [hnmap,ambientCore_map] at hm
  change ambientScalarPlane h e X ≤ ambientCore (n*z*n⁻¹) at hm
  rwa [he] at hm

/-- Every original core at a nonzero point normalizes the same three-space. -/
theorem scalarPlane_each_core_normalizes (r : core z)
    (hr : IsConj z ((r : centralizer z) : G)) (hne : ((r : centralizer z) : G) ≠ z)
    (hmark : coreNativeEquiv h e X
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) r)) = VectorOrbits.decode 4)
    (a : centralizer z)
    (ha : coreAmbientHom h e X (QuotientGroup.mk' (core z) a) = scalarElement) :
    ∀ t ∈ ambientScalarPlane h e X, t ≠ 1 →
      ambientCore t ≤ normalizer (ambientScalarPlane h e X : Set G) := by
  intro t ht ht1
  obtain ⟨n,_,he⟩ := scalarPlane_normalizer_transitive h e X r hr hne hmark a ha t ht ht1
  exact core_normalizes_between (type_of_conj h (isConj_iff.mpr ⟨n,he⟩))
    (ambientScalarPlane h e X) (scalarPlane_le_each_core h e X r hr hne hmark a ha t ht ht1) ht

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition

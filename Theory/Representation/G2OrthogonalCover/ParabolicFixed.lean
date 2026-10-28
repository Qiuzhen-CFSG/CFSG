module
public import Theory.Representation.G2OrthogonalCover.Quotients
public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Quotient
public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic.Quotient
public import Theory.AtlasPort.LinearGroups.G2.Perfectness
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.GroupTheory.SylowKernelCore

/-!
# Fixed-space commutators for the two G₂ parabolic residuals

The short residual's two-core fixes only the first natural plane. Its inverse
image in the trace-zero Cayley cover is the singular plane plus the scalar
radical, and the short residual preserves both summands. The long residual's
two-core fixes the first natural line; the long residual fixes its entire
inverse image. Thus neither residual produces a globally fixed vector by
moving vectors fixed by its own two-core.

The universal binary cover maps onto every perfect central natural cover.
Perfectness of G₂(F) for |F| > 2 gives the full-group actor from the existing
derived-group universal-cover API. The same original projection transports
the complementary singular plane through arbitrary binary central quotients.
Conjugation transports the literal subgroup two-core, and the final theorem
applies the result to a fully moved subspace inside that core's fixed space.

Source: Aschbacher--Smith, Proposition 9.4.1, printed p.735 / PDF p.752 of
`refs/quasithin.pdf`, the G₂(4) Cayley-cover fixed-space argument, using
I.2.3(1), printed p.413 / PDF p.424. Root coordinates come from the attributed
ATLAS imports. No equality between the residual core and a larger parabolic
core is assumed or needed.
-/

@[expose] public section
noncomputable section
open Atlas.SplitOctonion Representation Representation.OneCohomology
open Representation.BinaryOffender Subgroup
namespace Atlas.G2.Natural.OrthogonalCover.ParabolicFixed
open Explicit LieParabolicSetup SylowFlag
variable (F : Type*) [Field F] [CharP F 2] [Algebra (ZMod 2) F]

abbrev fullBinaryNatural := restrictScalars (k := ZMod 2) (Natural.action F)
abbrev fullBinaryAction := restrictScalars (k := ZMod 2) (traceZeroAction F)

omit [Algebra (ZMod 2) F] in
private theorem natural_short_fixed (v : Space F)
    (h : ∀ q ∈ radical₁ (F := F), Natural.action F q v = v) :
    v ∈ naturalPlane F := by
  let c := Restricted.NaturalCoordinates.equiv F v
  have hc (q : Model F) (hq : q ∈ radical₁) :
      Restricted.NaturalCoordinates.action F q c = c := by
    change Restricted.NaturalCoordinates.equiv F
      (Natural.action F q ((Restricted.NaturalCoordinates.equiv F).symm c)) = c
    rw [show (Restricted.NaturalCoordinates.equiv F).symm c = v from
      (Restricted.NaturalCoordinates.equiv F).symm_apply_apply v, h q hq]
  have ha := hc (rootA 1) ⟨![1,0,0,0,0,0], by simp, by simp [unipotentProduct]⟩
  have hb := hc (rootB 1) ⟨![0,1,0,0,0,0], by simp, by simp [unipotentProduct]⟩
  have hd := hc (rootD 1) ⟨![0,0,0,1,0,0], by simp, by simp [unipotentProduct]⟩
  have h2 : c 2 = 0 := by simpa using congrFun hd 0
  have h3 : c 3 = 0 := by simpa using congrFun hb 0
  have h4 : c 4 = 0 := by simpa using congrFun ha 0
  have h5 : c 5 = 0 := by simpa using congrFun ha 1
  apply (mem_naturalPlane F v).mpr
  refine ⟨c 0,c 1,?_⟩
  change c = _
  ext i
  fin_cases i <;> simp [h2,h3,h4,h5]

omit [Algebra (ZMod 2) F] in
private theorem natural_long_fixed (v : Space F)
    (h : ∀ q ∈ radical₂ (F := F), Natural.action F q v = v) :
    v ∈ N1 F := by
  let c := Restricted.NaturalCoordinates.equiv F v
  have hc (q : Model F) (hq : q ∈ radical₂) :
      Restricted.NaturalCoordinates.action F q c = c := by
    change Restricted.NaturalCoordinates.equiv F
      (Natural.action F q ((Restricted.NaturalCoordinates.equiv F).symm c)) = c
    rw [show (Restricted.NaturalCoordinates.equiv F).symm c = v from
      (Restricted.NaturalCoordinates.equiv F).symm_apply_apply v, h q hq]
  have ha := hc (rootA 1) ⟨![1,0,0,0,0,0], by simp, by simp [unipotentProduct]⟩
  have hb := hc (rootB 1) ⟨![0,1,0,0,0,0], by simp, by simp [unipotentProduct]⟩
  have hd := hc (rootD 1) ⟨![0,0,0,1,0,0], by simp, by simp [unipotentProduct]⟩
  have hf := hc (rootF 1) ⟨![0,0,0,0,0,1], by simp, by simp [unipotentProduct]⟩
  have h1 : c 1 = 0 := by simpa using congrFun hf 0
  have h2 : c 2 = 0 := by simpa using congrFun hd 0
  have h3 : c 3 = 0 := by simpa using congrFun hb 0
  have h4 : c 4 = 0 := by simpa using congrFun ha 0
  have h5 : c 5 = 0 := by simpa using congrFun ha 1
  apply (mem_N1 F v).mpr
  refine ⟨c 0,?_⟩
  change c = _
  ext i
  fin_cases i <;> simp [h1,h2,h3,h4,h5]

private theorem short_plane_invariant (g : Model F) (hg : g ∈ local₁)
    (x : TraceZero F) (hx : x ∈ singularPlane F) :
    traceZeroAction F g x ∈ singularPlane F := by
  have hS : local₁ (F := F) ≤
      subspaceStabilizer (fullBinaryAction F) ((singularPlane F).restrictScalars (ZMod 2)) := by
    apply sup_le
    · apply le_subspaceStabilizer
      intro g hg x hx
      rw [unipotent_eq_range] at hg
      obtain ⟨t,rfl⟩ := hg
      obtain ⟨v,rfl⟩ := hx
      exact ⟨_,(unipotent_plane F t v).symm⟩
    · apply (closure_le _).mpr
      rintro g (rfl : g = weylS)
      have hs (x : TraceZero F) (hx : x ∈ singularPlane F) :
          traceZeroAction F weylS x ∈ singularPlane F := by
        obtain ⟨v,rfl⟩ := hx
        refine ⟨![v 1,v 0],?_⟩
        apply Subtype.ext
        ext i
        fin_cases i <;>
          simp [traceZeroAction_val,planeLift,weylS,weylSEquiv,weylSLinear,weylSApply,
            CharTwo.neg_eq]
      intro x
      refine ⟨fun hx => ?_, hs x⟩
      have hh := hs _ hx
      change traceZeroAction F weylS (traceZeroAction F weylS x) ∈ singularPlane F at hh
      have hw : (weylS : Model F) * weylS = 1 := by simpa [pow_two] using (weylS_sq (K := F))
      rw [← Module.End.mul_apply,← map_mul,hw,map_one] at hh
      exact hh
  exact (hS hg x).mpr hx

omit [Algebra (ZMod 2) F] in
private theorem long_point_fixed (g : Model F) (hg : g ∈ local₂) :
    traceZeroAction F g (pointVector F) = pointVector F := by
  let K : Subgroup (Model F) :=
    { carrier := {g | traceZeroAction F g (pointVector F) = pointVector F}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        change traceZeroAction F (a*b) (pointVector F) = pointVector F
        rw [map_mul,Module.End.mul_apply,hb,ha]
      inv_mem' := by
        intro a ha
        have h := congrArg (traceZeroAction F a⁻¹) ha
        simpa using h.symm }
  have hK : local₂ (F := F) ≤ K := by
    apply sup_le
    · intro g hg
      rw [unipotent_eq_range] at hg
      obtain ⟨t,rfl⟩ := hg
      change traceZeroAction F (unipotentProduct t) (planeLift F ![1,0]) = _
      rw [unipotent_plane]
      simp [pointVector]
    · apply (closure_le _).mpr
      rintro g (rfl : g = weylR)
      change traceZeroAction F weylR (pointVector F) = pointVector F
      apply Subtype.ext
      ext i
      fin_cases i <;>
        simp [traceZeroAction_val,pointVector,planeLift,weylR,weylREquiv,weylRLinear,weylRApply,
          CharTwo.neg_eq]
  exact hK hg

variable [Finite F]
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {σ : Representation (ZMod 2) (Model F) W}
  (p : σ.IntertwiningMap (fullBinaryNatural F))

/-- The universal-cover quotient with the full G₂ actor, for fields larger than F₂. -/
theorem exists_full_quotient (hq : 2 < Nat.card F) (hp : IsCover p) :
    ∃ f : (fullBinaryAction F).IntertwiningMap σ, Function.Surjective f ∧
      ∀ x, p (f x) = mk F x := by
  let : Group.IsPerfect (Model F) := Atlas.G2.isPerfect hq
  have hg (g : Model F) : g ∈ commutator (Model F) := by
    rw [Group.IsPerfect.commutator_eq_top]
    trivial
  let pD : Representation.IntertwiningMap (σ.comp (commutator (Model F)).subtype) (binaryNatural F) :=
    p.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _
      (fun g x => LinearMap.congr_fun (p.isIntertwining' g.val) x)
  have hpD : IsCover pD := by
    refine ⟨hp.1,fun x hx g => hp.2.1 hx g.val,?_⟩
    apply top_unique
    rw [← hp.2.2]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,x⟩,rfl⟩
    exact Coinvariants.sub_mem_ker (ρ := σ.comp (commutator (Model F)).subtype) ⟨g,hg g⟩ x
  obtain ⟨f,hf,hover⟩ := exists_quotient F pD hpD
  let fG : (fullBinaryAction F).IntertwiningMap σ :=
    f.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _
      (fun g x => LinearMap.congr_fun (f.isIntertwining' ⟨g,hg g⟩) x)
  exact ⟨fG,hf,hover⟩

omit [Finite F] [FiniteDimensional (ZMod 2) W] in
private theorem full_fixed_le_kernel : fixed σ ≤ p.toLinearMap.ker := by
  intro w hw
  have h : p w ∈ fixed (binaryNatural F) := by
    intro g
    change fullBinaryNatural F g.val (p w) = p w
    rw [← p.isIntertwining,hw g.val]
  rw [binaryNatural_fixed_eq_bot] at h
  exact h

omit [Algebra (ZMod 2) F] [Finite F] in
private theorem scalar_fixed (g : Model F) (x : TraceZero F) (hx : x ∈ scalarLine F) :
    traceZeroAction F g x = x := by
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [map_smul,traceZeroAction_identity]

omit [Finite F] [FiniteDimensional (ZMod 2) W] in
private theorem plane_image_disjoint
    (f : (fullBinaryAction F).IntertwiningMap σ) (hover : ∀ x,p (f x) = mk F x) :
    Disjoint (((singularPlane F).restrictScalars (ZMod 2)).map f.toLinearMap)
      p.toLinearMap.ker := by
  apply Submodule.disjoint_def.mpr
  rintro w ⟨x,hx,rfl⟩ hw
  have hs : x ∈ scalarLine F := (Submodule.Quotient.mk_eq_zero _).mp (by
    change mk F x = 0
    rw [← hover]
    exact hw)
  rw [Submodule.disjoint_def.mp (singularPlane_disjoint_scalar F) x hx hs,map_zero]

/-- In every binary central natural cover, short-residual commutators on the
fixed space of its literal two-core are disjoint from the global fixed space. -/
theorem short_disjoint (hq : 2 < Nat.card F) (hp : IsCover p) :
    Disjoint (fixed σ)
      (subspaceCommutator σ (fixedSpace σ ((local₁ (F := F)).pCoreIn 2)) local₁) := by
  obtain ⟨f,hf,hover⟩ := exists_full_quotient F p hq hp
  apply ((plane_image_disjoint F p f hover).symm.mono_left (full_fixed_le_kernel F p)).mono_right
  apply Submodule.span_le.mpr
  rintro _ ⟨g,hg,w,hw,rfl⟩
  have hn : p w ∈ naturalPlane F := by
    apply natural_short_fixed F
    intro q hq
    change fullBinaryNatural F q (p w) = p w
    rw [← p.isIntertwining]
    exact congrArg p (hw ⟨q,by rwa [local₁_pCore]⟩)
  obtain ⟨x,rfl⟩ := hf w
  have hx : x ∈ singularPlane F ⊔ scalarLine F := by
    rw [← naturalPlane_preimage]
    change mk F x ∈ naturalPlane F
    rwa [← hover]
  obtain ⟨c,hc,z,hz,rfl⟩ := Submodule.mem_sup.mp hx
  refine ⟨traceZeroAction F g c - c,
    (singularPlane F).sub_mem (short_plane_invariant F g hg c hc) hc,?_⟩
  calc
    f (traceZeroAction F g c - c) = f (fullBinaryAction F g (c+z) - (c+z)) := by
      apply congrArg f
      change _ = traceZeroAction F g (c+z) - (c+z)
      rw [map_add,scalar_fixed F g z hz]
      abel
    _ = σ g (f (c+z)) - f (c+z) := by rw [map_sub,f.isIntertwining]

/-- The long residual fixes the entire two-core fixed space in every cover. -/
theorem long_fixed (hq : 2 < Nat.card F) (hp : IsCover p) :
    fixedSpace σ ((local₂ (F := F)).pCoreIn 2) ≤ fixedSpace σ local₂ := by
  obtain ⟨f,hf,hover⟩ := exists_full_quotient F p hq hp
  intro w hw g
  have hn : p w ∈ N1 F := by
    apply natural_long_fixed F
    intro q hq
    change fullBinaryNatural F q (p w) = p w
    rw [← p.isIntertwining]
    exact congrArg p (hw ⟨q,by rwa [local₂_pCoreIn]⟩)
  obtain ⟨x,rfl⟩ := hf w
  have hx : x ∈ P F ⊔ scalarLine F := by
    rw [← N1_preimage]
    change mk F x ∈ N1 F
    rwa [← hover]
  obtain ⟨c,hc,z,hz,rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hc
  change σ g.val (f _) = f _
  rw [← f.isIntertwining]
  congr 1
  change traceZeroAction F g.val (a • pointVector F + z) = _
  rw [map_add,map_smul,long_point_fixed F g.val g.property,scalar_fixed F g.val z hz]

/-- Long-residual commutators vanish; in particular they are disjoint from
the global fixed space. -/
theorem long_disjoint (hq : 2 < Nat.card F) (hp : IsCover p) :
    Disjoint (fixed σ)
      (subspaceCommutator σ (fixedSpace σ ((local₂ (F := F)).pCoreIn 2)) local₂) := by
  rw [(subspaceCommutator_eq_bot_iff _ _ _).mpr (long_fixed F p hq hp)]
  exact disjoint_bot_right

/-- Conjugate local residuals retain their own two-core and the literal
cover projection. Their core-fixed commutators miss the global fixed space. -/
theorem cover_core_fixed_commutator_disjoint (hq : 2 < Nat.card F) (hp : IsCover p)
    (B : Subgroup (Model F)) (g : Model F)
    (hB : B.map (MulAut.conj g).toMonoidHom = local₁ ∨
      B.map (MulAut.conj g).toMonoidHom = local₂) :
    Disjoint (subspaceCommutator σ (fixedSpace σ (B.pCoreIn 2)) B) (fixed σ) := by
  have hact (b : Model F) (w : W) :
      σ ((MulAut.conj g) b) (σ g w) = σ g (σ b w) := by
    rw [← Module.End.mul_apply,← map_mul,← Module.End.mul_apply,← map_mul]
    congr 2
    simp [MulAut.conj_apply,mul_assoc]
  let B' := B.map (MulAut.conj g).toMonoidHom
  have hd : Disjoint (fixed σ)
      (subspaceCommutator σ (fixedSpace σ (B'.pCoreIn 2)) B') := by
    rcases hB with hB | hB
    · change Disjoint (fixed σ) (subspaceCommutator σ (fixedSpace σ
        ((B.map (MulAut.conj g).toMonoidHom).pCoreIn 2)) (B.map (MulAut.conj g).toMonoidHom))
      rw [hB]
      exact short_disjoint F p hq hp
    · change Disjoint (fixed σ) (subspaceCommutator σ (fixedSpace σ
        ((B.map (MulAut.conj g).toMonoidHom).pCoreIn 2)) (B.map (MulAut.conj g).toMonoidHom))
      rw [hB]
      exact long_disjoint F p hq hp
  have hm : subspaceCommutator σ (fixedSpace σ (B.pCoreIn 2)) B ≤
      (subspaceCommutator σ (fixedSpace σ (B'.pCoreIn 2)) B').comap (σ g) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨b,hb,w,hw,rfl⟩
    have hw' : σ g w ∈ fixedSpace σ (B'.pCoreIn 2) := by
      intro q
      have hq : q.val ∈ (B.pCoreIn 2).map (MulAut.conj g).toMonoidHom := by
        rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective]
        exact q.property
      obtain ⟨r,hr,he⟩ := hq
      change σ q.val (σ g w) = σ g w
      rw [← he]
      change σ ((MulAut.conj g) r) (σ g w) = σ g w
      rw [hact]
      exact congrArg (σ g) (hw ⟨r,hr⟩)
    change σ g (σ b w - w) ∈
      subspaceCommutator σ (fixedSpace σ (B'.pCoreIn 2)) B'
    rw [map_sub,← hact]
    exact Submodule.subset_span ⟨(MulAut.conj g) b,
      mem_map_of_mem (MulAut.conj g).toMonoidHom hb,σ g w,hw',rfl⟩
  apply Submodule.disjoint_def.mpr
  intro w hw hf
  apply Submodule.disjoint_def.mp hd w hf
  have h := hm hw
  rw [Submodule.mem_comap] at h
  rwa [hf g] at h

/-- A fully moved subspace centralized by the residual two-core has no
nonzero globally fixed vector. This is the nonsplit-submodule consumer. -/
theorem cover_moved_subspace_disjoint (hq : 2 < Nat.card F) (hp : IsCover p)
    (B : Subgroup (Model F)) (g : Model F)
    (hB : B.map (MulAut.conj g).toMonoidHom = local₁ ∨
      B.map (MulAut.conj g).toMonoidHom = local₂)
    (A : Submodule (ZMod 2) W) (hA : A ≤ fixedSpace σ (B.pCoreIn 2))
    (hm : subspaceCommutator σ A B = A) : Disjoint A (fixed σ) := by
  apply (cover_core_fixed_commutator_disjoint F p hq hp B g hB).mono_left
  rw [← hm]
  apply Submodule.span_mono
  rintro _ ⟨b,hb,w,hw,rfl⟩
  exact ⟨b,hb,w,hA hw,rfl⟩

end Atlas.G2.Natural.OrthogonalCover.ParabolicFixed

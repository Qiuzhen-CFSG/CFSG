module

public import Theory.Representation.G2NaturalOffenders.Coordinates
public import Theory.Representation.G2OrthogonalCover
public import Theory.AtlasPort.LinearGroups.G2.LieSylowCenter
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# Long-root centralizers on the actual G₂ Weyl cover

The long-root groups inside the A–B plane have order q and corank 2n in
A–B–C. Their fixed spaces span the trace-zero hyperplane with final octonion
coordinate zero. Its commutator with A–B–C is the singular three-space on
the first three coordinates. The full preimage of the natural three-space
also contains the scalar radical, which this commutator misses.

We prove the corrected identity with that scalar summand, and show that in
any quotient over the same natural projection the summand can be dropped
exactly when its image is zero. This distinguishes a natural-quotient
calculation from an assertion about the entire central cover. Chapter 11's
RootCover application retains the original projection and central space.

Source: Aschbacher–Smith, B.4.6(3), printed p.88, and its use in 11.2.2(5),
printed p.768. The equality with the full preimage is not a consequence of
those local cover hypotheses. This does not refute the full Chapter 11
ambient theorem. Coordinates are the existing attributed ATLAS root maps;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff. No new ATLAS text is
copied here.
-/

@[expose] public noncomputable section

open Atlas.SplitOctonion Representation Representation.BinaryOffender Subgroup
namespace Atlas.G2.Natural.RootCentralizers
open Explicit
variable (F : Type*) [Field F] [CharP F 2] [Algebra (ZMod 2) F]

abbrev coverAction := restrictScalars (k := ZMod 2) (traceZeroAction F)

def hyperplane : Submodule F (TraceZero F) :=
  LinearMap.ker ((LinearMap.proj (7 : Fin 8)).comp (TraceZero F).subtype)

def threeLift : Submodule F (TraceZero F) where
  carrier := {x | x.val 3 = 0 ∧ x.val 4 = 0 ∧ x.val 5 = 0 ∧ x.val 6 = 0 ∧ x.val 7 = 0}
  zero_mem' := by simp
  add_mem' := by rintro x y ⟨h3,h4,h5,h6,h7⟩ ⟨j3,j4,j5,j6,j7⟩; simp_all
  smul_mem' := by rintro a x ⟨h3,h4,h5,h6,h7⟩; simp_all

theorem commutator_le_threeLift :
    subspaceCommutator (coverAction F) ((hyperplane F).restrictScalars (ZMod 2))
      (EvenTwoRank.elementary F) ≤ (threeLift F).restrictScalars (ZMod 2) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨g,hg,x,hx,rfl⟩
  obtain ⟨p,rfl⟩ := hg
  have h7 : x.val 7 = 0 := hx
  change traceZeroAction F (EvenTwoRank.elementaryEmbedding F p) x - x ∈ threeLift F
  change _ ∧ _ ∧ _ ∧ _ ∧ _
  simp [EvenTwoRank.elementaryEmbedding, EvenTwoRank.elementaryParameters,
    unipotentProduct, traceZeroAction_val, rootA, rootB, rootC,
    rootAEquiv, rootBEquiv, rootCEquiv, rootALinear, rootBLinear, rootCLinear,
    rootAApply, rootBApply, rootCApply, h7, CharTwo.neg_eq]

theorem identity_not_mem_commutator :
    identity F ∉ subspaceCommutator (coverAction F) ((hyperplane F).restrictScalars (ZMod 2))
      (EvenTwoRank.elementary F) := by
  intro h
  have hh := (commutator_le_threeLift F h).1
  simp [identity, unit] at hh


/-- The actual long-root groups in the distinguished long-root plane. -/
def longRoots : Set (Subgroup (Model F)) :=
  {Z | Z ≤ longRootLocal ∧ ∃ g : Model F,
    Z = LieParabolicSetup.highestRoot.map (MulAut.conj g).toMonoidHom}

/-- The span of the original fixed spaces of these root groups. -/
def fixedSpan : Submodule (ZMod 2) (TraceZero F) :=
  ⨆ Z ∈ longRoots F, fixedSpace (coverAction F) Z

omit [CharP F 2] [Algebra (ZMod 2) F] in
/-- Every selected root lies in the actual elementary A-B-C actor. -/
theorem root_le_elementary {Z : Subgroup (Model F)} (hZ : Z ∈ longRoots F) :
    Z ≤ EvenTwoRank.elementary F := by
  intro z hz
  obtain ⟨p,rfl⟩ := hZ.1 hz
  exact (EvenTwoRank.elementary F).mul_mem
    (NaturalOffenders.rootA_mem_elementary p.toAdd.1)
    (NaturalOffenders.rootB_mem_elementary p.toAdd.2)

omit [CharP F 2] [Algebra (ZMod 2) F] in
/-- The root subgroup has the order of the coefficient field, by its literal
conjugate embedding. -/
theorem root_card {Z : Subgroup (Model F)} (hZ : Z ∈ longRoots F) :
    Nat.card Z = Nat.card F := by
  obtain ⟨-,g,rfl⟩ := hZ
  exact (Nat.card_congr (LieParabolicSetup.highestRoot.equivMapOfInjective
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).toEquiv).symm.trans
      LieParabolicSetup.card_highestRoot

omit [CharP F 2] [Algebra (ZMod 2) F] in
/-- The exact corank used in the r-bound is 2n, inside the q³ actor. -/
theorem root_corank [Finite F] {n : ℕ} (hc : Nat.card F = 2^n)
    {Z : Subgroup (Model F)} (hZ : Z ∈ longRoots F) :
    Nat.log 2 (Z.relIndex (EvenTwoRank.elementary F)) = 2*n := by
  have hp : Nat.card Z * Z.relIndex (EvenTwoRank.elementary F) =
      Nat.card (EvenTwoRank.elementary F) := by
    simpa only [relIndex_bot_left] using relIndex_mul_relIndex
      (⊥ : Subgroup (Model F)) Z (EvenTwoRank.elementary F) bot_le (root_le_elementary F hZ)
  rw [root_card F hZ,EvenTwoRank.elementary_card,hc] at hp
  have he : (2^n) * 2^(2*n) = (2^n)^3 := by
    rw [← pow_add,← pow_mul]
    congr 1
    omega
  have hi : Z.relIndex (EvenTwoRank.elementary F) = 2^(2*n) :=
    Nat.eq_of_mul_eq_mul_left (by positivity) (hp.trans he.symm)
  rw [hi,Nat.log_pow Nat.one_lt_two]

omit [CharP F 2] [Algebra (ZMod 2) F] in
private theorem first_mem : LieParabolicSetup.highestRoot ∈ longRoots F := by
  refine ⟨?_,1,?_⟩
  · rintro _ ⟨a,rfl⟩
    exact rootA_mem_longRootLocal a.toAdd
  · ext g
    simp

omit [CharP F 2] [Algebra (ZMod 2) F] in
private theorem second_mem :
    LieParabolicSetup.highestRoot.map (MulAut.conj weylR).toMonoidHom ∈ longRoots F := by
  refine ⟨?_,weylR,rfl⟩
  rintro _ ⟨_,⟨a,rfl⟩,rfl⟩
  change MulAut.conj weylR (rootA a.toAdd) ∈ longRootLocal
  rw [MulAut.conj_apply, weylR_rootA]
  exact rootB_mem_longRootLocal _

omit [CharP F 2] in
private theorem fixed_le_hyperplane (Z : Subgroup (Model F)) (hZ : Z ∈ longRoots F) :
    fixedSpace (coverAction F) Z ≤ (hyperplane F).restrictScalars (ZMod 2) := by
  intro x hx
  obtain ⟨hZ,g,rfl⟩ := hZ
  let a : Model F := MulAut.conj g (rootA (1 : F))
  have ha : a ∈ LieParabolicSetup.highestRoot.map (MulAut.conj g).toMonoidHom :=
    mem_map_of_mem _ ⟨Multiplicative.ofAdd 1,rfl⟩
  have hne : a ≠ 1 := by
    intro he
    have hh : rootA (1 : F) = 1 := (MulAut.conj g).injective (he.trans (map_one _).symm)
    exact one_ne_zero (rootA_injective (hh.trans rootA_zero.symm))
  obtain ⟨p,hp⟩ := hZ ha
  have hf := hx ⟨a,ha⟩
  change traceZeroAction F a x = x at hf
  rw [← hp] at hf
  have h1 := congrArg (fun w : TraceZero F => w.val 1) hf
  have h2 := congrArg (fun w : TraceZero F => w.val 2) hf
  change x.val 7 = 0
  by_contra h7
  have hp1 : p.toAdd.1 = 0 := by
    have hh : x.val 1 + p.toAdd.1 * x.val 7 = x.val 1 := by
      simpa [longRootHom,traceZeroAction_val,rootA,rootB,rootAEquiv,rootBEquiv,
        rootALinear,rootBLinear,rootAApply,rootBApply] using h1
    exact (mul_eq_zero.mp (add_eq_left.mp hh)).resolve_right h7
  have hp2 : p.toAdd.2 = 0 := by
    have hh : x.val 2 + p.toAdd.2 * x.val 7 = x.val 2 := by
      simpa [longRootHom,traceZeroAction_val,rootA,rootB,rootAEquiv,rootBEquiv,
        rootALinear,rootBLinear,rootAApply,rootBApply] using h2
    exact (mul_eq_zero.mp (add_eq_left.mp hh)).resolve_right h7
  apply hne
  rw [← hp]
  simp [longRootHom,hp1,hp2]

omit [CharP F 2] in
/-- The two coordinate roots already span the full root-centralizer hyperplane. -/
theorem fixedSpan_eq_hyperplane :
    fixedSpan F = (hyperplane F).restrictScalars (ZMod 2) := by
  apply le_antisymm
  · exact iSup_le fun Z => iSup_le fun hZ => fixed_le_hyperplane F Z hZ
  · intro x hx
    have h7 : x.val 7 = 0 := hx
    let y : TraceZero F := ⟨![0,0,0,0,0,0,x.val 6,0],by simp [trace]⟩
    have hx' : x-y ∈ fixedSpace (coverAction F) LieParabolicSetup.highestRoot := by
      rintro ⟨_,a,rfl⟩
      change traceZeroAction F (rootA a.toAdd) (x-y) = x-y
      apply Subtype.ext
      ext i
      fin_cases i <;> simp [traceZeroAction_val,rootA,rootAEquiv,rootALinear,
        rootAApply,y,h7]
    have hy : y ∈ fixedSpace (coverAction F)
        (LieParabolicSetup.highestRoot.map (MulAut.conj weylR).toMonoidHom) := by
      rintro ⟨_,_,⟨a,rfl⟩,rfl⟩
      change traceZeroAction F (MulAut.conj weylR (rootA a.toAdd)) y = y
      rw [MulAut.conj_apply, weylR_rootA]
      apply Subtype.ext
      ext i
      fin_cases i <;> simp [traceZeroAction_val,rootB,rootBEquiv,rootBLinear,rootBApply,y]
    have hxS : x-y ∈ fixedSpan F :=
      (show fixedSpace (coverAction F) LieParabolicSetup.highestRoot ≤ fixedSpan F from
        le_iSup_of_le LieParabolicSetup.highestRoot
          (le_iSup_of_le (first_mem F) le_rfl)) hx'
    have hyS : y ∈ fixedSpan F :=
      (show fixedSpace (coverAction F)
          (LieParabolicSetup.highestRoot.map (MulAut.conj weylR).toMonoidHom) ≤ fixedSpan F from
        le_iSup_of_le _ (le_iSup_of_le (second_mem F) le_rfl)) hy
    simpa only [sub_add_cancel] using (fixedSpan F).add_mem hxS hyS

/-- The full preimage of the upper natural three-space. -/
def threePreimage : Submodule (ZMod 2) (TraceZero F) :=
  ((NaturalOffenders.upper (F := F)).comap
    (Restricted.NaturalCoordinates.projection F)).restrictScalars (ZMod 2)


private def fifthVector (t : F) : TraceZero F :=
  ⟨![0,0,0,0,0,t,0,0],by simp [trace]⟩

private def sixthVector (t : F) : TraceZero F :=
  ⟨![0,0,0,0,0,0,t,0],by simp [trace]⟩

/-- The correct commutator in the cover is the singular three-space, with no
scalar-radical summand. -/
theorem commutator_eq_threeLift :
    subspaceCommutator (coverAction F) (fixedSpan F) (EvenTwoRank.elementary F) =
      (threeLift F).restrictScalars (ZMod 2) := by
  rw [fixedSpan_eq_hyperplane]
  apply le_antisymm (commutator_le_threeLift F)
  intro x hx
  obtain ⟨h3,h4,h5,h6,h7⟩ := hx
  have hm (a : Model F) (ha : a ∈ EvenTwoRank.elementary F) (y : TraceZero F)
      (hy : y.val 7 = 0) : coverAction F a y-y ∈
      subspaceCommutator (coverAction F) ((hyperplane F).restrictScalars (ZMod 2))
        (EvenTwoRank.elementary F) := Submodule.subset_span ⟨a,ha,y,hy,rfl⟩
  have h0 := hm (rootA 1) (NaturalOffenders.rootA_mem_elementary 1)
    (sixthVector F (x.val 0)) rfl
  have h1 := hm (rootC 1) (NaturalOffenders.rootC_mem_elementary 1)
    (fifthVector F (x.val 1)) rfl
  have h2 := hm (rootC 1) (NaturalOffenders.rootC_mem_elementary 1)
    (sixthVector F (x.val 2)) rfl
  have he : (coverAction F (rootA 1) (sixthVector F (x.val 0))-sixthVector F (x.val 0)) +
      (coverAction F (rootC 1) (fifthVector F (x.val 1))-fifthVector F (x.val 1)) +
      (coverAction F (rootC 1) (sixthVector F (x.val 2))-sixthVector F (x.val 2)) = x := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [coverAction,restrictScalars,traceZeroAction_val,
      rootA,rootC,rootAEquiv,rootCEquiv,rootALinear,rootCLinear,rootAApply,rootCApply,
      fifthVector,sixthVector,CharTwo.neg_eq,h3,h4,h5,h6,h7]
  rw [← he]
  exact Submodule.add_mem _ (Submodule.add_mem _ h0 h1) h2

/-- Restoring the scalar radical gives precisely the full natural preimage. -/
theorem threePreimage_eq_sup : threePreimage F =
    (threeLift F).restrictScalars (ZMod 2) ⊔ (scalarLine F).restrictScalars (ZMod 2) := by
  apply le_antisymm
  · intro x hx
    have h5 : x.val 5 = 0 := hx.1
    have h6 : x.val 6 = 0 := hx.2.1
    have h7 : x.val 7 = 0 := hx.2.2
    have h34 : x.val 4 = x.val 3 := by
      have hh : x.val 3 + x.val 4 = 0 := x.property
      simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_right hh
    apply Submodule.mem_sup.mpr
    refine ⟨x - x.val 3 • identity F,?_,x.val 3 • identity F,?_,sub_add_cancel _ _⟩
    · change _ ∧ _ ∧ _ ∧ _ ∧ _
      simp [identity,unit,h34,h5,h6,h7]
    · exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · apply sup_le
    · intro x hx
      exact ⟨hx.2.2.1,hx.2.2.2.1,hx.2.2.2.2⟩
    · intro x hx
      obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hx
      change (a • identity F).val 5 = 0 ∧ (a • identity F).val 6 = 0 ∧
        (a • identity F).val 7 = 0
      simp [identity,unit]

/-- The central-cover version of the root-span identity retains a necessary
scalar term. -/
theorem root_commutator_sup_scalar :
    subspaceCommutator (coverAction F) (fixedSpan F) (EvenTwoRank.elementary F) ⊔
      (scalarLine F).restrictScalars (ZMod 2) = threePreimage F := by
  rw [commutator_eq_threeLift,threePreimage_eq_sup]

theorem identity_mem_threePreimage : identity F ∈ threePreimage F := by
  simp [threePreimage,NaturalOffenders.upper,Restricted.NaturalCoordinates.projection,identity,unit]


/-- The three-space complementary to the radical stays disjoint from it after
binary scalar restriction. -/
theorem threeLift_disjoint_scalar : Disjoint ((threeLift F).restrictScalars (ZMod 2))
    ((scalarLine F).restrictScalars (ZMod 2)) := by
  apply Submodule.disjoint_def.mpr
  intro x hx hz
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hz
  have ha : a = 0 := by simpa [identity,unit] using hx.1
  simp [ha]

/-- In a quotient over the same natural projection, identifying the root
commutator with the full third preimage is equivalent to killing the entire
scalar radical. This isolates the missing premise in that proposed identity. -/
theorem root_commutator_image_eq_iff {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (p : TraceZero F →ₗ[ZMod 2] W)
    (hker : p.ker ≤ (scalarLine F).restrictScalars (ZMod 2)) :
    (subspaceCommutator (coverAction F) (fixedSpan F) (EvenTwoRank.elementary F)).map p =
      (threePreimage F).map p ↔ ((scalarLine F).restrictScalars (ZMod 2)).map p = ⊥ := by
  rw [commutator_eq_threeLift,threePreimage_eq_sup,Submodule.map_sup]
  have hd := Submodule.disjoint_map_of_ker_le_right (threeLift_disjoint_scalar F) hker
  constructor
  · intro he
    apply bot_unique
    have hle : ((scalarLine F).restrictScalars (ZMod 2)).map p ≤
        ((threeLift F).restrictScalars (ZMod 2)).map p := le_sup_right.trans_eq he.symm
    exact (le_inf hle le_rfl).trans hd.le_bot
  · intro he
    rw [he,sup_bot_eq]


omit [CharP F 2] in
/-- Equivariant transport of this actual root commutator to any quotient of
the Weyl module, with the actor and scalar restriction unchanged. -/
theorem map_root_commutator {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) (Model F) W}
    (p : (coverAction F).IntertwiningMap σ) :
    (subspaceCommutator (coverAction F) (fixedSpan F) (EvenTwoRank.elementary F)).map
      p.toLinearMap = subspaceCommutator σ ((fixedSpan F).map p.toLinearMap)
        (EvenTwoRank.elementary F) := by
  apply le_antisymm
  · rw [subspaceCommutator,Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_,⟨a,ha,w,hw,rfl⟩,rfl⟩
    have he : p.toLinearMap (coverAction F a w) = σ a (p.toLinearMap w) :=
      LinearMap.congr_fun (p.isIntertwining' a) w
    rw [map_sub,he]
    exact Submodule.subset_span ⟨a,ha,p w,⟨w,hw,rfl⟩,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,_,⟨w,hw,rfl⟩,rfl⟩
    refine ⟨coverAction F a w-w,Submodule.subset_span ⟨a,ha,w,hw,rfl⟩,?_⟩
    have he : p.toLinearMap (coverAction F a w) = σ a (p.toLinearMap w) :=
      LinearMap.congr_fun (p.isIntertwining' a) w
    rw [map_sub,he]

/-- The actual root-centralizer commutator cannot equal the full third preimage
in the Weyl cover: it misses the nonzero central identity vector. -/
theorem root_commutator_ne_threePreimage :
    subspaceCommutator (coverAction F) (fixedSpan F) (EvenTwoRank.elementary F) ≠
      threePreimage F := by
  rw [fixedSpan_eq_hyperplane]
  intro he
  exact identity_not_mem_commutator F (he.symm ▸ identity_mem_threePreimage F)

end Atlas.G2.Natural.RootCentralizers

module

public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoBlocks
public import Theory.Representation.BinaryNaturalDual.RadicalCore
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.Representation.DualCommutator

/-!
# Binary parabolic natural and contragredient modules

For the unipotent radical at a nonzero proper subspace S, the natural fixed
space is S and the dual fixed space is ann(S). Restriction to S and the
contragredient action on the literal quotient V/S compute their component
commutators. Transvections generate each large natural block; annihilator
duality gives the corresponding statement for its dual. Products and arbitrary
finite multiplicities are computed coordinatewise, with actual linear
coordinates on the resulting submodules.

The end-parabolic markings are constructed from the two diagonal actions and
the intrinsic two-core. `LeftComponent` and `RightComponent` record the group
markings needed for other components; they contain no desired module conclusion.
The natural and dual actions agree with literal matrix multiplication and
inverse transpose through the canonical binary matrix isomorphism.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, C.4.8, printed p.154, natural/dual branches of
B.5.1(1)(i),(iii),(iv), with B.4.2(9). This file supplies the linear calculation;
source component recognition and the central-extension reduction are separate
obligations. The radical fixed-space proofs reuse `BinaryLinear.Parabolics`
and `BinaryNaturalDual.RadicalCore`.
-/

@[expose] public section
namespace Representation.BinaryParabolicNatural
open BinaryLinear BinaryOffender
variable {G V X : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup X] [Module (ZMod 2) X]

/-- The literal natural action of the binary linear group. -/
def natural (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] :
    Representation (ZMod 2) (BinaryLinear.GL V) V :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom

/-- The subspace in the final parabolic calculation, using actual fixed vectors
and the span of actual action differences. -/
noncomputable def fixedCommutator (ρ : Representation (ZMod 2) G V)
    (R M : Subgroup G) : Submodule (ZMod 2) V :=
  subspaceCommutator ρ (BinaryOffender.fixedSpace ρ R) M

/-- An equivariant linear map carries the commutator of a subspace onto the
commutator of its image. Surjectivity on the whole ambient space is unnecessary. -/
theorem commutator_map (ρ : Representation (ZMod 2) G V)
    (σ : Representation (ZMod 2) G X) (f : V →ₗ[ZMod 2] X)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) (S : Submodule (ZMod 2) V) (M : Subgroup G) :
    (subspaceCommutator ρ S M).map f = subspaceCommutator σ (S.map f) M := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, v, hv, rfl⟩
    change f (ρ g v - v) ∈ subspaceCommutator σ (S.map f) M
    rw [map_sub, hf]
    exact Submodule.subset_span ⟨g, hg, f v, ⟨v, hv, rfl⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, _, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨ρ g v - v, Submodule.subset_span ⟨g, hg, v, hv, rfl⟩,
      by rw [map_sub, hf]⟩

/-- On the whole space, subgroup commutators are Mathlib's coinvariant kernel. -/
theorem commutator_top (ρ : Representation (ZMod 2) G V) (M : Subgroup G) :
    subspaceCommutator ρ ⊤ M = Coinvariants.ker (ρ.comp M.subtype) := by
  unfold subspaceCommutator Coinvariants.ker
  congr 1
  ext v
  constructor
  · rintro ⟨g, hg, w, _, rfl⟩
    exact ⟨(⟨g, hg⟩, w), rfl⟩
  · rintro ⟨⟨g, w⟩, rfl⟩
    exact ⟨g, g.property, w, Submodule.mem_top, rfl⟩

/-- The radical's natural fixed space is its defining subspace. -/
theorem natural_fixed (S : Submodule (ZMod 2) V) (hS : S ≠ ⊥) :
    BinaryOffender.fixedSpace (natural V) (radical S) = S := by
  ext v
  change (∀ g : radical S, g.val v = v) ↔ v ∈ S
  simpa only [Subtype.forall] using (mem_iff_fixed_radical hS v).symm

/-- The radical's contragredient fixed space is the annihilator of that subspace. -/
theorem dual_fixed (S : Submodule (ZMod 2) V) (hS : S ≠ ⊤) :
    BinaryOffender.fixedSpace (natural V).dual (radical S) = S.dualAnnihilator := by
  ext f
  change (∀ g : radical S, g.val.symm.dualMap f = f) ↔ _
  exact (by
    simpa only [Subtype.forall] using BinaryNaturalDual.dual_fixed_radical_iff S hS f)

/-- A nonzero vector in a binary space of dimension at least two is an actual
transvection displacement. -/
theorem exists_natural_displacement [FiniteDimensional (ZMod 2) V]
    (hd : 2 ≤ Module.finrank (ZMod 2) V) (w : V) :
    ∃ (g : BinaryLinear.GL V) (v : V), g v - v = w := by
  by_cases hw : w = 0
  · exact ⟨1, 0, by simp [hw]⟩
  have hline : Submodule.span (ZMod 2) {w} ≠ ⊤ := by
    intro h
    have hh := finrank_span_singleton (K := ZMod 2) hw
    rw [h, finrank_top] at hh
    omega
  obtain ⟨v, _, hv⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hline)
  obtain ⟨q, hqv, hqw⟩ := (Submodule.span (ZMod 2) {w}).exists_le_ker_of_notMem hv
  have hq0 : q w = 0 := hqw (Submodule.mem_span_singleton_self w)
  have hq1 : q v = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hqv
  exact ⟨transvection w q hq0, v, by change v + q v • w - v = w; simp [hq1]⟩

/-- The full general linear group generates its natural module by commutators. -/
theorem natural_coinvariants [FiniteDimensional (ZMod 2) V]
    (hd : 2 ≤ Module.finrank (ZMod 2) V) : Coinvariants.ker (natural V) = ⊤ := by
  apply top_unique
  intro w _
  obtain ⟨g, v, hv⟩ := exists_natural_displacement hd w
  exact Coinvariants.mem_ker_of_eq g v w hv

/-- A surjective change of acting group leaves the commutator space unchanged. -/
theorem coinvariants_comp_surjective {H : Type*} [Group H]
    (ρ : Representation (ZMod 2) H V) (f : G →* H) (hf : Function.Surjective f) :
    Coinvariants.ker (ρ.comp f) = Coinvariants.ker ρ := by
  apply le_antisymm <;> apply Submodule.span_le.mpr
  · rintro _ ⟨⟨g, v⟩, rfl⟩
    exact Coinvariants.sub_mem_ker (f g) v
  · rintro _ ⟨⟨g, v⟩, rfl⟩
    obtain ⟨h, rfl⟩ := hf g
    exact Coinvariants.sub_mem_ker (ρ := ρ.comp f) h v



/-- Restriction of a subgroup of the parabolic to its marked subspace. -/
def subspaceActor (S : Submodule (ZMod 2) V) {M : Subgroup (BinaryLinear.GL V)}
    (hM : M ≤ parabolic S) : M →* BinaryLinear.GL S :=
  (SmallParabolicLevi.subspaceAction S).comp (Subgroup.inclusion hM)

/-- The same subgroup's action on the literal quotient by the marked subspace. -/
def quotientActor (S : Submodule (ZMod 2) V) {M : Subgroup (BinaryLinear.GL V)}
    (hM : M ≤ parabolic S) : M →* BinaryLinear.GL (V ⧸ S) :=
  (SmallParabolicLevi.quotientAction S).comp (Subgroup.inclusion hM)

/-- A linear intertwiner into an ambient representation identifies the image
of the coinvariant kernel with the actual subgroup commutator of its range. -/
theorem commutator_range (ρ : Representation (ZMod 2) G V) (M : Subgroup G)
    (σ : Representation (ZMod 2) M X) (f : X →ₗ[ZMod 2] V)
    (hf : ∀ (g : M) x, f (σ g x) = ρ g.val (f x)) :
    (Coinvariants.ker σ).map f = subspaceCommutator ρ f.range M := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, x⟩, rfl⟩
    change f (σ g x - x) ∈ subspaceCommutator ρ f.range M
    rw [map_sub, hf]
    exact Submodule.subset_span ⟨g, g.property, f x, ⟨x, rfl⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, _, ⟨x, rfl⟩, rfl⟩
    refine ⟨σ ⟨g, hg⟩ x - x, Coinvariants.sub_mem_ker (ρ := σ) ⟨g, hg⟩ x, ?_⟩
    rw [map_sub, hf]

/-- The natural calculation retains the exact action of the component on S. -/
theorem natural_commutator_formula (S : Submodule (ZMod 2) V) (hS : S ≠ ⊥)
    {M : Subgroup (BinaryLinear.GL V)} (hM : M ≤ parabolic S) :
    fixedCommutator (natural V) (radical S) M =
      (Coinvariants.ker ((natural S).comp (subspaceActor S hM))).map S.subtype := by
  rw [fixedCommutator, natural_fixed S hS]
  simpa only [Submodule.range_subtype] using
    (commutator_range (natural V) M ((natural S).comp (subspaceActor S hM))
      S.subtype (fun _ _ => rfl)).symm

/-- The dual calculation retains the contragredient action on the literal V/S.
The embedding is precomposition with V → V/S, not an arbitrary dimension match. -/
theorem dual_commutator_formula (S : Submodule (ZMod 2) V) (hS : S ≠ ⊤)
    {M : Subgroup (BinaryLinear.GL V)} (hM : M ≤ parabolic S) :
    fixedCommutator (natural V).dual (radical S) M =
      (Coinvariants.ker (Representation.dual ((natural (V ⧸ S)).comp (quotientActor S hM)))).map
        S.mkQ.dualMap := by
  rw [fixedCommutator, dual_fixed S hS]
  have hr : S.mkQ.dualMap.range = S.dualAnnihilator := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, Submodule.ker_mkQ]
  rw [← hr]
  apply (commutator_range _ _ _ _ _).symm
  intro g f
  ext v
  rfl

/-- If the component induces the full linear group on S, the natural fixed
space is already generated by its component commutators. -/
theorem natural_commutator_eq [FiniteDimensional (ZMod 2) V]
    (S : Submodule (ZMod 2) V) (hS : S ≠ ⊥)
    {M : Subgroup (BinaryLinear.GL V)} (hM : M ≤ parabolic S)
    (hsurj : Function.Surjective (subspaceActor S hM))
    (hd : 2 ≤ Module.finrank (ZMod 2) S) :
    fixedCommutator (natural V) (radical S) M = S := by
  rw [natural_commutator_formula S hS hM, coinvariants_comp_surjective _ _ hsurj,
    natural_coinvariants hd, Submodule.map_top, Submodule.range_subtype]

/-- A component trivial on the first block has zero natural fixed-space commutator. -/
theorem natural_commutator_zero (S : Submodule (ZMod 2) V) (hS : S ≠ ⊥)
    {M : Subgroup (BinaryLinear.GL V)} (hM : M ≤ parabolic S)
    (htriv : ∀ g, subspaceActor S hM g = 1) :
    fixedCommutator (natural V) (radical S) M = ⊥ := by
  rw [fixedCommutator, natural_fixed S hS, subspaceCommutator_eq_bot_iff]
  intro v hv g
  exact congrArg Subtype.val (LinearEquiv.congr_fun (htriv g) ⟨v, hv⟩)

/-- A component trivial on the quotient block has zero dual fixed-space commutator. -/
theorem dual_commutator_zero (S : Submodule (ZMod 2) V) (hS : S ≠ ⊤)
    {M : Subgroup (BinaryLinear.GL V)} (hM : M ≤ parabolic S)
    (htriv : ∀ g, quotientActor S hM g = 1) :
    fixedCommutator (natural V).dual (radical S) M = ⊥ := by
  rw [dual_commutator_formula S hS hM]
  have hc : Coinvariants.ker (Representation.dual ((natural (V ⧸ S)).comp (quotientActor S hM))) = ⊥ := by
    apply bot_unique
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, f⟩, rfl⟩
    change _ = 0
    apply sub_eq_zero.mpr
    apply LinearMap.ext
    intro v
    change f (quotientActor S hM g⁻¹ v) = f v
    rw [htriv]
    rfl
  rw [hc, Submodule.map_bot]

/-- The natural binary linear group has no fixed vectors in dimension at least two. -/
theorem natural_invariants [FiniteDimensional (ZMod 2) V]
    (hd : 2 ≤ Module.finrank (ZMod 2) V) : (natural V).invariants = ⊥ := by
  apply bot_unique
  intro v hv
  by_contra hv0
  have hline : Submodule.span (ZMod 2) {v} ≠ ⊤ := by
    intro h
    have hh := finrank_span_singleton (K := ZMod 2) hv0
    rw [h, finrank_top] at hh
    omega
  obtain ⟨w, _, hw⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hline)
  have hw0 : w ≠ 0 := fun h => hw (h ▸ Submodule.zero_mem _)
  have hvw : v ∉ Submodule.span (ZMod 2) {w} := by
    rintro h
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
    have ha0 : a ≠ 0 := by intro ha0; exact hv0 (by simpa [ha0] using ha.symm)
    have ha1 : a = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ ha0
    have he : w = v := by simpa [ha1] using ha
    exact hw (he.symm ▸ Submodule.mem_span_singleton_self v)
  obtain ⟨q, hqv, hqw⟩ := (Submodule.span (ZMod 2) {w}).exists_le_ker_of_notMem hvw
  have hq0 : q w = 0 := hqw (Submodule.mem_span_singleton_self w)
  have hq1 : q v = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hqv
  have he := hv (transvection w q hq0)
  change v + q v • w = v at he
  rw [hq1, one_smul] at he
  exact hw0 (add_eq_left.mp he)

/-- The dual natural module is likewise generated by the full linear group. -/
theorem dual_coinvariants [FiniteDimensional (ZMod 2) V]
    (hd : 2 ≤ Module.finrank (ZMod 2) V) : Coinvariants.ker (natural V).dual = ⊤ := by
  have he := (natural V).invariants_eq_dual_commutator_coannihilator
  rw [natural_invariants hd] at he
  have hh := congrArg Submodule.dualAnnihilator he
  rw [Submodule.dualAnnihilator_bot, Subspace.dualCoannihilator_dualAnnihilator_eq] at hh
  exact hh.symm

/-- A full quotient-block action generates the whole dual radical-fixed space. -/
theorem dual_commutator_eq [FiniteDimensional (ZMod 2) V]
    (S : Submodule (ZMod 2) V) (hS : S ≠ ⊤)
    {M : Subgroup (BinaryLinear.GL V)} (hM : M ≤ parabolic S)
    (hsurj : Function.Surjective (quotientActor S hM))
    (hd : 2 ≤ Module.finrank (ZMod 2) (V ⧸ S)) :
    fixedCommutator (natural V).dual (radical S) M = S.dualAnnihilator := by
  rw [dual_commutator_formula S hS hM]
  have he : Representation.dual ((natural (V ⧸ S)).comp (quotientActor S hM)) =
      (natural (V ⧸ S)).dual.comp (quotientActor S hM) := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro v
    change f (quotientActor S hM g⁻¹ v) = f ((quotientActor S hM g)⁻¹ v)
    rw [map_inv]
  rw [he]
  rw [coinvariants_comp_surjective _ _ hsurj, dual_coinvariants hd,
    Submodule.map_top, LinearMap.range_dualMap_eq_dualAnnihilator_ker, Submodule.ker_mkQ]


/-- Fixed spaces commute with a direct product of representations. -/
theorem fixed_prod (ρ : Representation (ZMod 2) G V)
    (σ : Representation (ZMod 2) G X) (R : Subgroup G) :
    BinaryOffender.fixedSpace (ρ.prod σ) R =
      (BinaryOffender.fixedSpace ρ R).prod (BinaryOffender.fixedSpace σ R) := by
  ext v
  change (∀ g : R, (ρ g.val v.1, σ g.val v.2) = v) ↔
    (∀ g : R, ρ g.val v.1 = v.1) ∧ ∀ g : R, σ g.val v.2 = v.2
  simp only [Prod.ext_iff, forall_and]

/-- Commutators of a direct product split into the two actual embedded summands. -/
theorem commutator_prod (ρ : Representation (ZMod 2) G V)
    (σ : Representation (ZMod 2) G X) (S : Submodule (ZMod 2) V)
    (T : Submodule (ZMod 2) X) (M : Subgroup G) :
    subspaceCommutator (ρ.prod σ) (S.prod T) M =
      (subspaceCommutator ρ S M).prod (subspaceCommutator σ T M) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, v, hv, rfl⟩
    exact ⟨Submodule.subset_span ⟨g, hg, v.1, hv.1, rfl⟩,
      Submodule.subset_span ⟨g, hg, v.2, hv.2, rfl⟩⟩
  · let C := subspaceCommutator (ρ.prod σ) (S.prod T) M
    have hl : subspaceCommutator ρ S M ≤ C.comap (LinearMap.inl (ZMod 2) V X) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨g, hg, v, hv, rfl⟩
      change (ρ g v - v, 0) ∈ C
      have h : (ρ.prod σ) g (v, 0) - (v, 0) ∈ C :=
        Submodule.subset_span ⟨g, hg, (v, 0), ⟨hv, T.zero_mem⟩, rfl⟩
      simpa using h
    have hr : subspaceCommutator σ T M ≤ C.comap (LinearMap.inr (ZMod 2) V X) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨g, hg, v, hv, rfl⟩
      change (0, σ g v - v) ∈ C
      have h : (ρ.prod σ) g (0, v) - (0, v) ∈ C :=
        Submodule.subset_span ⟨g, hg, (0, v), ⟨S.zero_mem, hv⟩, rfl⟩
      simpa using h
    intro v hv
    simpa using C.add_mem (hl hv.1) (hr hv.2)

/-- The entire fixed-space commutator construction commutes with direct products. -/
theorem fixedCommutator_prod (ρ : Representation (ZMod 2) G V)
    (σ : Representation (ZMod 2) G X) (R M : Subgroup G) :
    fixedCommutator (ρ.prod σ) R M =
      (fixedCommutator ρ R M).prod (fixedCommutator σ R M) := by
  rw [fixedCommutator, fixed_prod, commutator_prod]
  rfl

/-- A finite family of identical representations, with the action on each coordinate. -/
def copies (ι : Type*) (ρ : Representation (ZMod 2) G V) :
    Representation (ZMod 2) G (ι → V) where
  toFun g := LinearMap.pi fun i => (ρ g).comp (LinearMap.proj i)
  map_one' := by ext v i; exact LinearMap.congr_fun ρ.map_one (v i)
  map_mul' g h := by ext v i; exact LinearMap.congr_fun (ρ.map_mul g h) (v i)

/-- The same subspace in each coordinate of a family. -/
def copySpace (ι : Type*) (S : Submodule (ZMod 2) V) : Submodule (ZMod 2) (ι → V) :=
  Submodule.pi Set.univ fun _ => S

@[simp] theorem mem_copySpace (ι : Type*) (S : Submodule (ZMod 2) V) (v : ι → V) :
    v ∈ copySpace ι S ↔ ∀ i, v i ∈ S := by
  simp [copySpace, Submodule.mem_pi]

/-- Fixed vectors in a family are computed separately in every summand. -/
theorem fixed_copies (ι : Type*) (ρ : Representation (ZMod 2) G V) (R : Subgroup G) :
    BinaryOffender.fixedSpace (copies ι ρ) R = copySpace ι (BinaryOffender.fixedSpace ρ R) := by
  ext v
  rw [mem_copySpace]
  constructor
  · intro hv i g
    exact congrFun (hv g) i
  · intro hv g
    funext i
    exact hv i g

/-- The commutator of any finite number of identical summands is computed coordinatewise. -/
theorem commutator_copies (ι : Type*) [Fintype ι] (ρ : Representation (ZMod 2) G V)
    (S : Submodule (ZMod 2) V) (M : Subgroup G) :
    subspaceCommutator (copies ι ρ) (copySpace ι S) M =
      copySpace ι (subspaceCommutator ρ S M) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, v, hv, rfl⟩
    change _ ∈ copySpace ι (subspaceCommutator ρ S M)
    rw [mem_copySpace]
    intro i
    exact Submodule.subset_span ⟨g, hg, v i, (mem_copySpace _ _ _).mp hv i, rfl⟩
  · let C := subspaceCommutator (copies ι ρ) (copySpace ι S) M
    have hs (i : ι) : subspaceCommutator ρ S M ≤
        C.comap (LinearMap.single (ZMod 2) (fun _ : ι => V) i) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨g, hg, v, hv, rfl⟩
      change Pi.single i (ρ g v - v) ∈ C
      have hv' : Pi.single i v ∈ copySpace ι S := by
        rw [mem_copySpace]
        intro j
        by_cases hj : j = i
        · simpa [hj] using hv
        · simp [Pi.single_eq_of_ne hj]
      have he : copies ι ρ g (Pi.single i v) - Pi.single i v =
          Pi.single i (ρ g v - v) := by
        funext j
        by_cases hj : j = i
        · subst j; simp [copies]
        · simp [copies, Pi.single_eq_of_ne hj]
      rw [← he]
      exact Submodule.subset_span ⟨g, hg, Pi.single i v, hv', rfl⟩
    intro v hv
    have hh : (∑ i, Pi.single i (v i)) ∈ C :=
      C.sum_mem fun i _ => hs i ((mem_copySpace _ _ _).mp hv i)
    simpa only [Finset.univ_sum_single] using hh

/-- In particular, the source's at most n−1 isomorphic natural summands require
no irreducibility assumption. The formula holds for every finite multiplicity. -/
theorem fixedCommutator_copies (ι : Type*) [Fintype ι]
    (ρ : Representation (ZMod 2) G V) (R M : Subgroup G) :
    fixedCommutator (copies ι ρ) R M = copySpace ι (fixedCommutator ρ R M) := by
  rw [fixedCommutator, fixed_copies, commutator_copies]
  rfl


/-- Geometric data for a component acting on the large first block. No module
fixed-space or commutator conclusion occurs among these hypotheses. -/
structure LeftComponent (S : Submodule (ZMod 2) V) (M : Subgroup (BinaryLinear.GL V)) where
  inside : M ≤ parabolic S
  core : (pCore 2 M).map M.subtype = radical S
  large : Function.Surjective (subspaceActor S inside)
  small : ∀ g, quotientActor S inside g = 1

/-- The opposite orientation, with the large factor on the quotient block. -/
structure RightComponent (S : Submodule (ZMod 2) V) (M : Subgroup (BinaryLinear.GL V)) where
  inside : M ≤ parabolic S
  core : (pCore 2 M).map M.subtype = radical S
  small : ∀ g, subspaceActor S inside g = 1
  large : Function.Surjective (quotientActor S inside)

/-- The natural and dual fixed spaces for the component's intrinsic two-core. -/
theorem component_fixed (S : Submodule (ZMod 2) V) (hS : S ≠ ⊥) (hSt : S ≠ ⊤)
    (M : Subgroup (BinaryLinear.GL V))
    (hcore : (pCore 2 M).map M.subtype = radical S) :
    BinaryOffender.fixedSpace (natural V) ((pCore 2 M).map M.subtype) = S ∧
    BinaryOffender.fixedSpace (natural V).dual ((pCore 2 M).map M.subtype) =
      S.dualAnnihilator := by
  rw [hcore]
  exact ⟨natural_fixed S hS, dual_fixed S hSt⟩

/-- For the large first block the natural contribution is S and the dual contribution is zero. -/
theorem left_calculation [FiniteDimensional (ZMod 2) V]
    {S : Submodule (ZMod 2) V} {M : Subgroup (BinaryLinear.GL V)}
    (d : LeftComponent S M) (hS : S ≠ ⊥) (hSt : S ≠ ⊤)
    (hd : 2 ≤ Module.finrank (ZMod 2) S) :
    fixedCommutator (natural V) ((pCore 2 M).map M.subtype) M = S ∧
    fixedCommutator (natural V).dual ((pCore 2 M).map M.subtype) M = ⊥ := by
  rw [d.core]
  exact ⟨natural_commutator_eq S hS d.inside d.large hd,
    dual_commutator_zero S hSt d.inside d.small⟩

/-- For the large quotient block only the dual contribution survives. -/
theorem right_calculation [FiniteDimensional (ZMod 2) V]
    {S : Submodule (ZMod 2) V} {M : Subgroup (BinaryLinear.GL V)}
    (d : RightComponent S M) (hS : S ≠ ⊥) (hSt : S ≠ ⊤)
    (hd : 2 ≤ Module.finrank (ZMod 2) (V ⧸ S)) :
    fixedCommutator (natural V) ((pCore 2 M).map M.subtype) M = ⊥ ∧
    fixedCommutator (natural V).dual ((pCore 2 M).map M.subtype) M =
      S.dualAnnihilator := by
  rw [d.core]
  exact ⟨natural_commutator_zero S hS d.inside d.small,
    dual_commutator_eq S hSt d.inside d.large hd⟩

/-- The actual surviving natural module, identified by the inclusion into V. -/
noncomputable def leftEquiv [FiniteDimensional (ZMod 2) V]
    {S : Submodule (ZMod 2) V} {M : Subgroup (BinaryLinear.GL V)}
    (d : LeftComponent S M) (hS : S ≠ ⊥) (hd : 2 ≤ Module.finrank (ZMod 2) S) :
    fixedCommutator (natural V) ((pCore 2 M).map M.subtype) M ≃ₗ[ZMod 2] S :=
  LinearEquiv.ofEq _ _ (by rw [d.core]; exact natural_commutator_eq S hS d.inside d.large hd)

/-- The equivalence retains the literal component action. -/
theorem leftEquiv_equivariant [FiniteDimensional (ZMod 2) V]
    {S : Submodule (ZMod 2) V} {M : Subgroup (BinaryLinear.GL V)}
    (d : LeftComponent S M) (hS : S ≠ ⊥) (hd : 2 ≤ Module.finrank (ZMod 2) S)
    (g : M) (v : S) :
    ((leftEquiv d hS hd).symm (subspaceActor S d.inside g v) : V) =
      g.val ((leftEquiv d hS hd).symm v : V) := rfl

/-- The surviving dual module is the actual dual of V/S, by precomposition
with the quotient map. -/
noncomputable def rightEquiv [FiniteDimensional (ZMod 2) V]
    {S : Submodule (ZMod 2) V} {M : Subgroup (BinaryLinear.GL V)}
    (d : RightComponent S M) (hSt : S ≠ ⊤)
    (hd : 2 ≤ Module.finrank (ZMod 2) (V ⧸ S)) :
    fixedCommutator (natural V).dual ((pCore 2 M).map M.subtype) M ≃ₗ[ZMod 2]
      Module.Dual (ZMod 2) (V ⧸ S) :=
  (LinearEquiv.ofEq _ _ (by
    rw [d.core]
    exact dual_commutator_eq S hSt d.inside d.large hd)).trans
      S.dualQuotEquivDualAnnihilator.symm

/-- Equivariance uses the inverse of the same marked quotient action. -/
theorem rightEquiv_equivariant [FiniteDimensional (ZMod 2) V]
    {S : Submodule (ZMod 2) V} {M : Subgroup (BinaryLinear.GL V)}
    (d : RightComponent S M) (hSt : S ≠ ⊤)
    (hd : 2 ≤ Module.finrank (ZMod 2) (V ⧸ S))
    (g : M) (f : Module.Dual (ZMod 2) (V ⧸ S)) :
    ((rightEquiv d hSt hd).symm ((quotientActor S d.inside g).symm.dualMap f) :
      Module.Dual (ZMod 2) V) =
      (natural V).dual g.val ((rightEquiv d hSt hd).symm f : Module.Dual (ZMod 2) V) := by
  ext v
  change f ((quotientActor S d.inside g)⁻¹ (S.mkQ v)) = f (S.mkQ (g.val⁻¹ v))
  rw [← map_inv]
  rfl

/-- A marking of the ambient representation transports the actual radical fixed space. -/
theorem fixed_map_equiv (ρ : Representation (ZMod 2) G V)
    (σ : Representation (ZMod 2) G X) (e : V ≃ₗ[ZMod 2] X)
    (he : ∀ g v, e (ρ g v) = σ g (e v)) (R : Subgroup G) :
    (BinaryOffender.fixedSpace ρ R).map e.toLinearMap = BinaryOffender.fixedSpace σ R := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩ g
    exact (he g.val v).symm.trans (congrArg e (hv g))
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro g
    apply e.injective
    change e (ρ g.val (e.symm x)) = e (e.symm x)
    rw [he, e.apply_symm_apply]
    exact hx g

/-- The bridge only assumes the original representation marking, never a description of W. -/
theorem fixedCommutator_map_equiv (ρ : Representation (ZMod 2) G V)
    (σ : Representation (ZMod 2) G X) (e : V ≃ₗ[ZMod 2] X)
    (he : ∀ g v, e (ρ g v) = σ g (e v)) (R M : Subgroup G) :
    (fixedCommutator ρ R M).map e.toLinearMap = fixedCommutator σ R M := by
  rw [fixedCommutator, commutator_map ρ σ e.toLinearMap he, fixed_map_equiv ρ σ e he]
  rfl


/-- Coordinates of a subspace in every summand, with no dimension-only identification. -/
def copySpaceEquiv (ι : Type*) (S : Submodule (ZMod 2) V) :
    copySpace ι S ≃ₗ[ZMod 2] (ι → S) where
  toFun v i := ⟨v.val i, (mem_copySpace _ _ _).mp v.property i⟩
  invFun v := ⟨fun i => (v i : V), (mem_copySpace _ _ _).mpr fun i => (v i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Actual coordinates on the commutator of the finite direct sum. -/
noncomputable def copiesEquiv (ι : Type*) [Fintype ι]
    (ρ : Representation (ZMod 2) G V) (R M : Subgroup G) :
    fixedCommutator (copies ι ρ) R M ≃ₗ[ZMod 2] (ι → fixedCommutator ρ R M) :=
  (LinearEquiv.ofEq _ _ (fixedCommutator_copies ι ρ R M)).trans
    (copySpaceEquiv ι (fixedCommutator ρ R M))

/-- Natural-plus-dual with a large first block: only the natural summand survives. -/
theorem left_doubled [FiniteDimensional (ZMod 2) V]
    {S : Submodule (ZMod 2) V} {M : Subgroup (BinaryLinear.GL V)}
    (d : LeftComponent S M) (hS : S ≠ ⊥) (hSt : S ≠ ⊤)
    (hd : 2 ≤ Module.finrank (ZMod 2) S) :
    fixedCommutator ((natural V).prod (natural V).dual)
      ((pCore 2 M).map M.subtype) M = S.prod ⊥ := by
  rw [fixedCommutator_prod, (left_calculation d hS hSt hd).1,
    (left_calculation d hS hSt hd).2]

/-- Natural-plus-dual with a large quotient block: only the dual summand survives. -/
theorem right_doubled [FiniteDimensional (ZMod 2) V]
    {S : Submodule (ZMod 2) V} {M : Subgroup (BinaryLinear.GL V)}
    (d : RightComponent S M) (hS : S ≠ ⊥) (hSt : S ≠ ⊤)
    (hd : 2 ≤ Module.finrank (ZMod 2) (V ⧸ S)) :
    fixedCommutator ((natural V).prod (natural V).dual)
      ((pCore 2 M).map M.subtype) M = (⊥ : Submodule (ZMod 2) V).prod S.dualAnnihilator := by
  rw [fixedCommutator_prod, (right_calculation d hS hSt hd).1,
    (right_calculation d hS hSt hd).2]

/-- Any finite multiplicity of the surviving natural representation has explicit coordinates. -/
noncomputable def leftCopiesEquiv [FiniteDimensional (ZMod 2) V]
    (ι : Type*) [Fintype ι]
    {S : Submodule (ZMod 2) V} {M : Subgroup (BinaryLinear.GL V)}
    (d : LeftComponent S M) (hS : S ≠ ⊥) (hd : 2 ≤ Module.finrank (ZMod 2) S) :
    fixedCommutator (copies ι (natural V)) ((pCore 2 M).map M.subtype) M ≃ₗ[ZMod 2]
      (ι → S) :=
  (copiesEquiv ι (natural V) _ M).trans (LinearEquiv.piCongrRight fun _ => leftEquiv d hS hd)

/-- Any finite multiplicity of the surviving dual representation has explicit quotient-dual coordinates. -/
noncomputable def rightCopiesEquiv [FiniteDimensional (ZMod 2) V]
    (ι : Type*) [Fintype ι]
    {S : Submodule (ZMod 2) V} {M : Subgroup (BinaryLinear.GL V)}
    (d : RightComponent S M) (hSt : S ≠ ⊤)
    (hd : 2 ≤ Module.finrank (ZMod 2) (V ⧸ S)) :
    fixedCommutator (copies ι (natural V).dual) ((pCore 2 M).map M.subtype) M ≃ₗ[ZMod 2]
      (ι → Module.Dual (ZMod 2) (V ⧸ S)) :=
  (copiesEquiv ι (natural V).dual _ M).trans
    (LinearEquiv.piCongrRight fun _ => rightEquiv d hSt hd)

/-- In matrix coordinates the natural action is literal multiplication by the matrix. -/
theorem matrix_natural_apply (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) (v : Fin n → ZMod 2) :
    natural (Fin n → ZMod 2) (BinaryLinear.OuterCyclic.matrixEquivLinear n g) v =
      (g : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec v := rfl

/-- The contragredient acts by inverse transpose under the actual dot-product coordinates. -/
theorem matrix_dual_apply (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) (w : Fin n → ZMod 2) :
    (natural (Fin n → ZMod 2)).dual (BinaryLinear.OuterCyclic.matrixEquivLinear n g)
      (dotProductEquiv (ZMod 2) (Fin n) w) =
    dotProductEquiv (ZMod 2) (Fin n)
      ((((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)).transpose).mulVec w) := by
  apply LinearMap.ext
  intro v
  change dotProduct w ((BinaryLinear.OuterCyclic.matrixEquivLinear n g).symm v) = _
  have hi : (BinaryLinear.OuterCyclic.matrixEquivLinear n g).symm v =
      ((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)).mulVec v := by
    change (BinaryLinear.OuterCyclic.matrixEquivLinear n g)⁻¹ v = _
    rw [← map_inv]
    rfl
  rw [hi, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  rfl


/-- The binary linear group in dimension one is trivial. -/
theorem linear_one_trivial (hd : Module.finrank (ZMod 2) V = 1)
    (g : BinaryLinear.GL V) : g = 1 := by
  ext v
  change g v = v
  by_cases hv : v = 0
  · simp [hv]
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' v hv).mp hd (g v)
  have ha0 : a ≠ 0 := by
    intro h
    exact hv (g.map_eq_zero_iff.mp (by simpa [h] using ha.symm))
  have ha1 : a = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ ha0
  simpa only [ha1, one_smul] using ha.symm

/-- The full line parabolic has the marked right-block action and its genuine
intrinsic two-core. This constructs the model inputs, rather than assuming them. -/
theorem rightEndMarking [FiniteDimensional (ZMod 2) V]
    (S : Submodule (ZMod 2) V) (hS : Module.finrank (ZMod 2) S = 1) :
    RightComponent S (parabolic S) where
  inside := le_rfl
  core := SmallParabolicLevi.map_twoCore_eq_radical S
  small g := linear_one_trivial hS (subspaceActor S le_rfl g)
  large := by
    intro b
    obtain ⟨g, hg⟩ := SmallParabolicLevi.blockAction_surjective S (1, b)
    exact ⟨g, congrArg Prod.snd hg⟩

/-- The full hyperplane parabolic has the marked left-block action and its genuine two-core. -/
theorem leftEndMarking [FiniteDimensional (ZMod 2) V]
    (S : Submodule (ZMod 2) V) (hS : Module.finrank (ZMod 2) (V ⧸ S) = 1) :
    LeftComponent S (parabolic S) where
  inside := le_rfl
  core := SmallParabolicLevi.map_twoCore_eq_radical S
  large := by
    intro a
    obtain ⟨g, hg⟩ := SmallParabolicLevi.blockAction_surjective S (a, 1)
    exact ⟨g, congrArg Prod.fst hg⟩
  small g := linear_one_trivial hS (quotientActor S le_rfl g)

/-- The line-parabolic calculation, applicable in degrees four and five with
quotient degrees three and four. The natural-plus-dual and finite-sum formulas
follow through `right_doubled` and `fixedCommutator_copies`. -/
theorem line_parabolic_calculation [FiniteDimensional (ZMod 2) V]
    (S : Submodule (ZMod 2) V) (hS : S ≠ ⊥) (hSt : S ≠ ⊤)
    (hline : Module.finrank (ZMod 2) S = 1)
    (hd : 2 ≤ Module.finrank (ZMod 2) (V ⧸ S)) :
    fixedCommutator (natural V) ((pCore 2 (parabolic S)).map (parabolic S).subtype)
      (parabolic S) = ⊥ ∧
    fixedCommutator (natural V).dual ((pCore 2 (parabolic S)).map (parabolic S).subtype)
      (parabolic S) = S.dualAnnihilator :=
  right_calculation (rightEndMarking S hline) hS hSt hd

/-- The hyperplane-parabolic calculation in the opposite orientation. -/
theorem hyperplane_parabolic_calculation [FiniteDimensional (ZMod 2) V]
    (S : Submodule (ZMod 2) V) (hS : S ≠ ⊥) (hSt : S ≠ ⊤)
    (hhyper : Module.finrank (ZMod 2) (V ⧸ S) = 1)
    (hd : 2 ≤ Module.finrank (ZMod 2) S) :
    fixedCommutator (natural V) ((pCore 2 (parabolic S)).map (parabolic S).subtype)
      (parabolic S) = S ∧
    fixedCommutator (natural V).dual ((pCore 2 (parabolic S)).map (parabolic S).subtype)
      (parabolic S) = ⊥ :=
  left_calculation (leftEndMarking S hhyper) hS hSt hd


/-- Restricting along an arbitrary actor map computes fixed vectors on the exact
image subgroup; surjectivity on the whole ambient group is unnecessary. -/
theorem fixed_comp {H : Type*} [Group H]
    (ρ : Representation (ZMod 2) H V) (f : G →* H) (R : Subgroup G) :
    BinaryOffender.fixedSpace (ρ.comp f) R = BinaryOffender.fixedSpace ρ (R.map f) := by
  ext v
  constructor
  · intro hv
    rintro ⟨_, g, hg, rfl⟩
    exact hv ⟨g, hg⟩
  · intro hv g
    exact hv ⟨f g.val, ⟨g.val, g.property, rfl⟩⟩

/-- The subgroup commutator also uses exactly the image of the original actor. -/
theorem commutator_comp {H : Type*} [Group H]
    (ρ : Representation (ZMod 2) H V) (f : G →* H)
    (S : Submodule (ZMod 2) V) (M : Subgroup G) :
    subspaceCommutator (ρ.comp f) S M = subspaceCommutator ρ S (M.map f) := by
  unfold subspaceCommutator
  congr 1
  ext v
  constructor
  · rintro ⟨g, hg, w, hw, rfl⟩
    exact ⟨f g, ⟨g, hg, rfl⟩, w, hw, rfl⟩
  · rintro ⟨_, ⟨g, hg, rfl⟩, w, hw, rfl⟩
    exact ⟨g, hg, w, hw, rfl⟩

/-- Fixed-space commutators are compatible with the literal image subgroups. -/
theorem fixedCommutator_comp {H : Type*} [Group H]
    (ρ : Representation (ZMod 2) H V) (f : G →* H) (R M : Subgroup G) :
    fixedCommutator (ρ.comp f) R M = fixedCommutator ρ (R.map f) (M.map f) := by
  rw [fixedCommutator, fixed_comp, commutator_comp]
  rfl

/-- The source bridge keeps the original actor map, representation coordinates,
and both subgroup images. It assumes no fixed-space or W description. -/
theorem marked_fixedCommutator {H : Type*} [Group H]
    (σ : Representation (ZMod 2) G X) (ρ : Representation (ZMod 2) H V)
    (f : G →* H) (e : X ≃ₗ[ZMod 2] V)
    (he : ∀ g x, e (σ g x) = ρ (f g) (e x))
    (R M : Subgroup G) (R' M' : Subgroup H)
    (hR : R.map f = R') (hM : M.map f = M') :
    (fixedCommutator σ R M).map e.toLinearMap = fixedCommutator ρ R' M' := by
  rw [fixedCommutator_map_equiv σ (ρ.comp f) e he, fixedCommutator_comp, hR, hM]

/-- The natural finite-sum equivalence retains the original action in every coordinate. -/
theorem leftCopiesEquiv_equivariant [FiniteDimensional (ZMod 2) V]
    (ι : Type*) [Fintype ι]
    {S : Submodule (ZMod 2) V} {M : Subgroup (BinaryLinear.GL V)}
    (d : LeftComponent S M) (hS : S ≠ ⊥) (hd : 2 ≤ Module.finrank (ZMod 2) S)
    (g : M) (v : ι → S) :
    ((leftCopiesEquiv ι d hS hd).symm (fun i => subspaceActor S d.inside g (v i)) : ι → V) =
      copies ι (natural V) g.val ((leftCopiesEquiv ι d hS hd).symm v : ι → V) := rfl

/-- The dual finite-sum equivalence retains the original contragredient action. -/
theorem rightCopiesEquiv_equivariant [FiniteDimensional (ZMod 2) V]
    (ι : Type*) [Fintype ι]
    {S : Submodule (ZMod 2) V} {M : Subgroup (BinaryLinear.GL V)}
    (d : RightComponent S M) (hSt : S ≠ ⊤)
    (hd : 2 ≤ Module.finrank (ZMod 2) (V ⧸ S))
    (g : M) (v : ι → Module.Dual (ZMod 2) (V ⧸ S)) :
    ((rightCopiesEquiv ι d hSt hd).symm
      (fun i => (quotientActor S d.inside g).symm.dualMap (v i)) : ι → Module.Dual (ZMod 2) V) =
      copies ι (natural V).dual g.val
        ((rightCopiesEquiv ι d hSt hd).symm v : ι → Module.Dual (ZMod 2) V) := by
  funext i
  exact rightEquiv_equivariant d hSt hd g (v i)

end Representation.BinaryParabolicNatural

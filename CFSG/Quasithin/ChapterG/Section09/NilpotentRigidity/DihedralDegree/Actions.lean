module

public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralDegree.Spaces
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralDegree.Kernel

/-!
# Faithful actions on the two smaller spaces

For a distinguished dihedral factor with rotation `x` and reflection `a`,
A.1.44 gives `V = C_V(x) ⊕ U ⊕ Uˣ`, where `U = C_[V,x](a)`.
Partition the other factors according to whether their rotations act
nontrivially on `[V,x]`. The selected factors act faithfully on `U`:
commutation with `x` propagates a kernel on `U` to `Uˣ`. The remaining
factors act faithfully on `C_V(x)`, since their rotations already fix
`[V,x]`. Both faithfulness arguments use the normal-kernel detection lemma.

This constructs the smaller-product actions in Aschbacher--Smith G.9.2,
printed p.352. Only the genuine A.1.44 splitting is supplied as an input.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralDegree

open DihedralGroup

universe v

variable {ι : Type} [DecidableEq ι] {p : ι → ℕ}
  {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]

abbrev factorRep (σ : Representation (ZMod 2) (∀ i, DihedralGroup (p i)) W) (i : ι) :=
  σ.comp (MonoidHom.mulSingle (fun j => DihedralGroup (p j)) i)

theorem factorRep_injective
    (σ : Representation (ZMod 2) (∀ i, DihedralGroup (p i)) W)
    (hf : Function.Injective σ) (i : ι) : Function.Injective (factorRep σ i) := by
  apply hf.comp
  intro g h he
  have := congrFun he i
  simpa using this

def subproductHom (s : Finset ι) :
    (∀ j : s, DihedralGroup (p j)) →* ∀ i, DihedralGroup (p i) where
  toFun g i := if hi : i ∈ s then g ⟨i, hi⟩ else 1
  map_one' := by ext i; dsimp; split <;> rfl
  map_mul' g h := by ext i; dsimp; split <;> simp

theorem subproductHom_single (s : Finset ι) (j : s) (x : DihedralGroup (p j)) :
    subproductHom (p := p) s (Pi.mulSingle j x) = Pi.mulSingle j.val x := by
  ext i
  by_cases hi : i = j.val
  · subst i
    simp [subproductHom, j.property]
  · have hne (h : i ∈ s) : (⟨i, h⟩ : s) ≠ j := fun he => hi (congrArg Subtype.val he)
    simp [subproductHom, Pi.mulSingle_eq_of_ne hi, hne]

theorem subproduct_commutes (s : Finset ι) (i : ι) (hi : i ∉ s)
    (g : ∀ j : s, DihedralGroup (p j)) (x : DihedralGroup (p i)) :
    Commute (subproductHom s g) (Pi.mulSingle i x) := by
  change _ * _ = _ * _
  ext j
  by_cases hj : j = i
  · subst j; simp [subproductHom, hi]
  · simp [Pi.mulSingle_eq_of_ne hj]

theorem ker_sub_one_stable (f t : Module.End (ZMod 2) W) (hc : Commute f t) :
    LinearMap.ker (t - 1) ≤ (LinearMap.ker (t - 1)).comap f := by
  intro w hw
  have hw' : t w = w := by simpa [LinearMap.mem_ker, sub_eq_zero] using hw
  have hcomm : t (f w) = f (t w) := congrArg (fun a : Module.End (ZMod 2) W => a w) hc.eq.symm
  simp [LinearMap.mem_ker, hcomm, hw']

theorem commuting_moved_stable {q : ℕ}
    (τ : Representation (ZMod 2) (DihedralGroup q) W)
    (f : Module.End (ZMod 2) W) (hc : ∀ g, Commute f (τ g)) :
    rotationMoved τ ≤ (rotationMoved τ).comap f := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g, w⟩, rfl⟩
  change f (τ g w - w) ∈ rotationMoved τ
  have hcomm : f (τ g w) = τ g (f w) :=
    congrArg (fun a : Module.End (ZMod 2) W => a w) (hc g).eq
  rw [map_sub, hcomm]
  exact Representation.Coinvariants.sub_mem_ker
    (ρ := τ.comp (Subgroup.zpowers (r 1)).subtype) g (f w)

theorem fixes_sup (f : Module.End (ZMod 2) W) (C M : Submodule (ZMod 2) W)
    (hC : ∀ w ∈ C, f w = w) (hM : ∀ w ∈ M, f w = w) :
    ∀ w ∈ C ⊔ M, f w = w := by
  intro w hw
  obtain ⟨c, hc, m, hm, rfl⟩ := Submodule.mem_sup.mp hw
  simp only [map_add, hC c hc, hM m hm]

theorem fixes_half_sum (f t : Module.End (ZMod 2) W)
    (U : Submodule (ZMod 2) W) (hc : Commute f t)
    (hU : ∀ w ∈ U, f w = w) : ∀ w ∈ U ⊔ U.map t, f w = w := by
  apply fixes_sup f U (U.map t) hU
  rintro w ⟨u, hu, rfl⟩
  have h := congrArg (fun a : Module.End (ZMod 2) W => a u) hc.eq
  change f (t u) = t u
  change f (t u) = t (f u) at h
  rw [h, hU u hu]

variable [Fintype ι]

/-- The two actual restricted actions in the source induction. The indices
in `J` act faithfully on the reflection half-space; all other indices except
the distinguished one act faithfully on its rotation fixed space. -/
structure SplitActions
    (σ : Representation (ZMod 2) (∀ i, DihedralGroup (p i)) W) (i : ι) where
  J : Finset ι
  excluded : i ∉ J
  fixed_stable : ∀ g,
    rotationFixed (factorRep σ i) ≤ (rotationFixed (factorRep σ i)).comap
      ((σ.comp (subproductHom ((Finset.univ.erase i) \ J))) g)
  half_stable : ∀ g,
    reflectionHalf (factorRep σ i) ≤ (reflectionHalf (factorRep σ i)).comap
      ((σ.comp (subproductHom J)) g)
  fixed_faithful : Function.Injective (Representation.subrepresentation
    (σ.comp (subproductHom ((Finset.univ.erase i) \ J)))
    (rotationFixed (factorRep σ i)) fixed_stable)
  half_faithful : Function.Injective (Representation.subrepresentation
    (σ.comp (subproductHom J)) (reflectionHalf (factorRep σ i)) half_stable)

theorem exists_splitActions [FiniteDimensional (ZMod 2) W]
    (split : DihedralSplittingTheorem.{v})
    (hp : ∀ i, (p i).Prime) (ho : ∀ i, Odd (p i))
    (σ : Representation (ZMod 2) (∀ i, DihedralGroup (p i)) W)
    (hf : Function.Injective σ) (i : ι) : Nonempty (SplitActions σ i) := by
  classical
  let τ := factorRep σ i
  let C := rotationFixed τ
  let M := rotationMoved τ
  let U := reflectionHalf τ
  let J := (Finset.univ.erase i).filter
    (fun j => ∃ w ∈ M, σ (Pi.mulSingle j (r 1)) w ≠ w)
  let I := Finset.univ.erase i \ J
  have hiJ : i ∉ J := by simp [J]
  have hiI : i ∉ I := by simp [I]
  have hcomm (s : Finset ι) (hi : i ∉ s)
      (g : ∀ j : s, DihedralGroup (p j)) (x : DihedralGroup (p i)) :
      Commute (σ (subproductHom s g)) (τ x) :=
    (subproduct_commutes s i hi g x).map σ
  have hC : ∀ g, C ≤ C.comap ((σ.comp (subproductHom I)) g) := by
    intro g
    exact ker_sub_one_stable _ _ (hcomm I hiI g (r 1))
  have hU : ∀ g, U ≤ U.comap ((σ.comp (subproductHom J)) g) := by
    intro g w hw
    exact ⟨commuting_moved_stable τ _ (hcomm J hiJ g) hw.1,
      ker_sub_one_stable _ _ (hcomm J hiJ g (sr 0)) hw.2⟩
  have hs := split W (p i) (hp i) (ho i) τ (factorRep_injective σ hf i)
  refine ⟨⟨J, hiJ, hC, hU, ?_, ?_⟩⟩
  · apply injective_of_rotations_ne_one (fun j : I => hp j) (fun j : I => ho j)
    intro j hj
    have hfixC : ∀ w ∈ C, σ (Pi.mulSingle j.val (r 1)) w = w := by
      intro w hw
      have h := congrArg (fun a : Module.End (ZMod 2) C => (a ⟨w, hw⟩ : W)) hj
      simpa [Representation.subrepresentation, subproductHom_single] using h
    have hjI := Finset.mem_sdiff.mp j.property
    have hfixM : ∀ w ∈ M, σ (Pi.mulSingle j.val (r 1)) w = w := by
      intro w hw
      by_contra hn
      exact hjI.2 (Finset.mem_filter.mpr ⟨hjI.1, w, hw, hn⟩)
    have he : σ (Pi.mulSingle j.val (r 1)) = σ 1 := by
      ext w
      have hw : w ∈ C ⊔ M := by rw [hs.1.sup_eq_top]; trivial
      simpa using fixes_sup _ C M hfixC hfixM w hw
    have h := congrArg (fun g => orderOf (g j.val)) (hf he)
    simp [orderOf_r_one, (hp j).ne_one] at h
  · apply injective_of_rotations_ne_one (fun j : J => hp j) (fun j : J => ho j)
    intro j hj
    have hfixU : ∀ w ∈ U, σ (Pi.mulSingle j.val (r 1)) w = w := by
      intro w hw
      have h := congrArg (fun a : Module.End (ZMod 2) U => (a ⟨w, hw⟩ : W)) hj
      simpa [Representation.subrepresentation, subproductHom_single] using h
    obtain ⟨w, hw, hn⟩ := (Finset.mem_filter.mp j.property).2
    apply hn
    have hji : j.val ≠ i := (Finset.mem_erase.mp (Finset.mem_filter.mp j.property).1).1
    have hc : Commute (σ (Pi.mulSingle j.val (r 1))) (τ (r 1)) :=
      (Pi.mulSingle_commute hji (r 1) (r 1)).map σ
    apply fixes_half_sum _ _ U hc hfixU
    rwa [hs.2.2]

end CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralDegree

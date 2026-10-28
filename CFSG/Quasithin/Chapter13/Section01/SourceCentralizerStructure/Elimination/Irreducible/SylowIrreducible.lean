module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Irreducible.CharacteristicTwo
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Irreducible.Normality
public import CFSG.Quasithin.Chapter13.Section01.RadicalNormality.Embedding
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.SymmetricFive
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.RadicalStabilizers.SylowImage
public import Theory.GroupAction.QuaternionPrimePlane

/-!
# The Sylow-irreducible half of the escaping-component sieve

The selected centralizer Sylow gives a genuine local join. A quaternion in
its original odd Frattini image survives the complement-normalizer transport,
so the intrinsic 1.3.4 theorem leaves the odd linear-three quotient. The
ordinary and characteristic-two exclusions then contradict that row.

The same module constructs the literal S₃ quotient from a genuine symmetric-five
marking. The original 13.1.10 action alternatives are retained as SieveActions;
their producer is qt-d-1317-module-orbits. This proves the source exclusion
conditional on those earlier actions, not their classification. The reducible
Sylow case and its model selection remain with qt-d-1317-centralizer-irreducible.
The final two theorems apply this reduction to the actual centralizer and TI
consumers, retaining the separate reducible component-normalizer branch.

Source: Aschbacher–Smith, 13.1.12(3), printed pp.874–875, using 1.3.4.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.Section02 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

@[expose] def SylowRadicalIrreducible (h : Context T L p) (u : G) : Prop :=
  ∀ A : Subgroup (XiFrattiniQuotient (XiP p L)),
    (∀ t : ((T : Subgroup G) ⊓ centralizer ({u} : Set G) : Subgroup G), ∀ a ∈ A,
      xiFrattiniAction ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) (XiP p L)
        (XiP_invariant p (inf_le_left.trans h.sylow_normalizes)) t a ∈ A) →
      A = ⊥ ∨ A = ⊤

@[expose] def componentStabilizerFrattiniAction (L : Subgroup G) (p : ℕ) (u : G) :=
  xiFrattiniAction (L ⊓ centralizer ({u} : Set G)) (XiP p L)
    (inf_le_left.trans (XiP_invariant p L.le_normalizer))

@[expose] def SymmetricThreeStabilizerQuotient (L : Subgroup G) (p : ℕ) (u : G) : Prop :=
  ∃ f : (componentStabilizerFrattiniAction L p u).range →* Equiv.Perm (Fin 3),
    Function.Surjective f

structure SieveActions (h : Context T L p) : Prop where
  quaternion : ∀ u : G, Selected T L u →
    ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
    SylowRadicalIrreducible h u →
    ∃ f : QuaternionGroup 2 →*
      (xiFrattiniAction ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) (XiP p L)
        (XiP_invariant p (inf_le_left.trans h.sylow_normalizes))).range,
      Function.Injective f
  symmetric_three : ∀ u : G, Selected T L u →
    ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
    ¬ SylowRadicalIrreducible h u → SymmetricThreeStabilizerQuotient L p u

/-- The original quaternion image makes the selected Sylow action irreducible. -/
theorem Context.sylow_radical_irreducible_of_quaternion (h : Context T L p)
    {u : G} (hq : ∃ f : QuaternionGroup 2 →*
      (xiFrattiniAction ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) (XiP p L)
        (XiP_invariant p (inf_le_left.trans h.sylow_normalizes))).range,
        Function.Injective f) : SylowRadicalIrreducible h u := by
  obtain ⟨_,he,hc⟩ := SourceNonquasisimple.ModuleOrbits.radical_frattini_plane
    h.hypothesis.simpleQTKE h.maximal.1.1 h.nonquasisimple h.odd h.divides
  let := he
  let ρ := xiFrattiniAction ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) (XiP p L)
    (XiP_invariant p (inf_le_left.trans h.sylow_normalizes))
  obtain ⟨f,hf⟩ := hq
  intro A hA
  apply QuaternionGroup.faithful_plane_irreducible h.odd hc
    (ρ.range.subtype.comp f) (ρ.range.subtype_injective.comp hf) A
  intro q a ha
  obtain ⟨t,ht⟩ := (f q).property
  change (f q : MulAut (XiFrattiniQuotient (XiP p L))) a ∈ A
  rw [←ht]
  exact hA t a ha

/-- The marked S5 branch induces an actual S3 quotient of the original stabilizer action. -/
theorem Context.symmetric_three_stabilizer_of_marking (h : Context T L p)
    (d : SourceNonquasisimple.ModuleOrbits.SymmetricFiveMarking T L)
    {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G)) :
    SymmetricThreeStabilizerQuotient L p u := by
  let C := L ⊓ centralizer ({u} : Set G)
  let J := L ⊔ (T : Subgroup G)
  let τ : C →* Equiv.Perm (Fin 5) :=
    d.quotient.comp (inclusion (show C ≤ J from inf_le_left.trans le_sup_left))
  let σ := componentStabilizerFrattiniAction L p u
  have hk : σ.ker ≤ τ.ker := by
    intro x hx
    let xL : L := ⟨x,x.property.1⟩
    have hxL : xL ∈ (xiFrattiniAction L (XiP p L)
        (XiP_invariant p L.le_normalizer)).ker := by
      rw [MonoidHom.mem_ker]
      have he := SourceNonquasisimple.ModuleOrbits.xiFrattiniAction_restrict
        (show C ≤ L from inf_le_left) (XiP_invariant p L.le_normalizer) x
      exact he.symm.trans hx
    have hxR := SourceNonquasisimple.ModuleOrbits.component_frattini_kernel_le_radical
      h.hypothesis.simpleQTKE h.maximal.1.1 h.nonquasisimple h.odd h.divides hxL
    rw [← d.component_kernel_eq_radical h.hypothesis h.many h.maximal h.nonquasisimple] at hxR
    exact hxR
  let f : σ.range →* τ.range := σ.rangeRestrict.liftOfSurjective
    σ.rangeRestrict_surjective ⟨τ.rangeRestrict,by
      simpa only [MonoidHom.ker_rangeRestrict] using hk⟩
  have he (x : C) : f (σ.rangeRestrict x) = τ.rangeRestrict x := by
    simp [f]
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x,rfl⟩ := τ.rangeRestrict_surjective y
    exact ⟨σ.rangeRestrict x,he x⟩
  have hr : τ.range = (C.subgroupOf J).map d.quotient := by
    rw [MonoidHom.range_comp, inclusion_range]
  obtain ⟨j⟩ := ((d.centralizer_orbit h.hypothesis h.maximal h.nonquasisimple
    ⟨u,s.mem⟩ (fun hh => s.ne_one (congrArg Subtype.val hh)) s.local_sylow).2 hnt).1
  let j' : τ.range ≃* Equiv.Perm (Fin 3) := (MulEquiv.subgroupCongr hr).trans j
  exact ⟨j'.toMonoidHom.comp f,j'.surjective.comp hf⟩

omit [Fact p.Prime] in
/-- The selected involution gives a nontrivial normal two-subgroup in each local join. -/
theorem Context.selected_join_mem_H (h : Context T L p) {u : G} (s : Selected T L u)
    {A : Subgroup G} (hA : A ≤ centralizer ({u} : Set G)) :
    A ⊔ ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) ∈ Chapter1.H G := by
  let J := A ⊔ ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
  have huT : u ∈ (T : Subgroup G) ⊓ centralizer ({u} : Set G) :=
    ⟨h.moved_le_sylow s.mem, mem_centralizer_singleton_iff.mpr rfl⟩
  have huJ : zpowers u ≤ J := zpowers_le.mpr (mem_sup_right huT)
  have hc : J ≤ centralizer (zpowers u : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
    exact sup_le hA inf_le_right
  have hp : IsPGroup 2 (zpowers u) := IsPGroup.of_card (n := 1) (by
    simpa only [Nat.card_zpowers, pow_one] using h.involution s.mem s.ne_one)
  have hle := le_pCoreIn_of_normalizes hp huJ
    (hc.trans (centralizer_le_normalizer (zpowers u : Set G)))
  intro hz
  apply s.ne_one
  have hu := hle (mem_zpowers u)
  simpa only [J,hz,mem_bot] using hu

/-- The actual Sylow action gives membership in the original Xi family. -/
theorem Context.xi_of_sylow_radical_irreducible (h : Context T L p)
    {u : G} (s : Selected T L u) (hi : SylowRadicalIrreducible h u) :
    XiP p L ∈ Xi G ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) := by
  have hshape := (Chapter13.Section01.RadicalConjugateRigidity.maximal_radical_structure
    h.hypothesis.simpleQTKE T h.maximal.1 h.nonquasisimple h.odd h.divides).1
  exact ⟨XiP_isPPerfect p L, XiP_invariant p (inf_le_left.trans h.sylow_normalizes),
    h.selected_join_mem_H s ((h.radical_le_local s).trans inf_le_right),
    ⟨p, Fact.out, h.odd, hshape⟩, hi⟩

omit [Fact p.Prime] in
/-- Restrict the original component and full centralizer Sylow to their literal join. -/
theorem Context.component_local_at_selected (h : Context T L p)
    {u : G} (s : Selected T L u) {K : Subgroup G} (e : Escape T L p u K) :
    K ∈ Chapter1.L G ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) := by
  have hjoin : K ⊔ ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) ≤
      centralizer ({u} : Set G) := sup_le e.component.1 inf_le_right
  exact ⟨e.component.2.subgroupOf_of_le le_sup_left hjoin,
    e.full_sylow.restrict le_sup_right hjoin, h.selected_join_mem_H s e.component.1⟩

/-- A quaternion in the original Frattini image survives complement-normalizer transport. -/
theorem Context.automizer_not_cyclic_of_sylow_quaternion (h : Context T L p)
    {u : G} (s : Selected T L u) (hi : SylowRadicalIrreducible h u)
    (P : Sylow p (XiP p L))
    (hq : ∃ f : QuaternionGroup 2 →*
      (xiFrattiniAction ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) (XiP p L)
        (XiP_invariant p (inf_le_left.trans h.sylow_normalizes))).range,
      Function.Injective f) :
    ¬ IsCyclic (automizer ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
      ((P : Subgroup (XiP p L)).map (XiP p L).subtype)) := by
  let X := XiP p L
  let S := (T : Subgroup G) ⊓ centralizer ({u} : Set G)
  let P₀ := (P : Subgroup X).map X.subtype
  let N := S ⊓ normalizer P₀
  have hX := h.xi_of_sylow_radical_irreducible s hi
  have hn : S ≤ normalizer X := hX.invariant
  have hshape := (Chapter13.Section01.RadicalConjugateRigidity.maximal_radical_structure
    h.hypothesis.simpleQTKE T h.maximal.1 h.nonquasisimple h.odd h.divides).1
  have hSX : IsSylowIn 2 S (X ⊔ S) := s.local_sylow.restrict le_sup_right
    (sup_le (h.radical_le_local s) (inf_le_inf_right _ h.sylow_normalizes))
  let j := hX.sylowFrattiniEquiv h.odd hshape P
  let ρ := frattiniConjugationAction N P₀ inf_le_right
  let σ := xiFrattiniAction S X hn
  have he : ∀ t : S, ∃ n : N, ∀ a, j (ρ n a) = σ t (j a) := by
    intro t
    have hN : N ≤ normalizer (X.pCoreIn 2 : Set G) :=
      inf_le_left.trans (hn.trans
        (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))
    have ht : (t : G) ∈ X.pCoreIn 2 ⊔ N := hX.normalizer_factor hSX hshape P ▸ t.property
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ hN] at ht
    obtain ⟨c,hc,n,hnN,hcn⟩ := ht
    let cS : S := ⟨c,hX.pCoreIn_le_of_isSylowIn hSX hc⟩
    let nS : S := ⟨n,hnN.1⟩
    have ht' : t = cS * nS := Subtype.ext hcn.symm
    refine ⟨⟨n,hnN⟩,?_⟩
    intro a
    change j (ρ ⟨n,hnN⟩ a) = xiFrattiniAction S X hn t (j a)
    rw [ht',map_mul]
    change j (ρ ⟨n,hnN⟩ a) = xiFrattiniAction S X hn cS
      (xiFrattiniAction S X hn nS (j a))
    rw [hX.core_fixes_frattini cS hc]
    exact hX.sylowFrattiniEquiv_equivariant h.odd hshape P ⟨n,hnN⟩ a
  apply RadicalActions.automizer_not_isCyclic_of_frattini
  intro hcyc
  let _ := hcyc
  obtain ⟨f,hf⟩ := hq
  let c := MulAut.congr j
  let f₀ := c.symm.toMonoidHom.comp (σ.range.subtype.comp f)
  have hf₀ : Function.Injective f₀ :=
    c.symm.injective.comp (σ.range.subtype_injective.comp hf)
  have hm (x : QuaternionGroup 2) : f₀ x ∈ ρ.range := by
    obtain ⟨t,ht⟩ := (f x).property
    obtain ⟨n,hn'⟩ := he t
    refine ⟨n,?_⟩
    apply c.injective
    change c (ρ n) = c (c.symm (f x))
    rw [c.apply_symm_apply,← ht]
    ext b : 1
    change j (ρ n (j.symm b)) = σ t b
    rw [hn',j.apply_symm_apply]
  let f₁ := f₀.codRestrict ρ.range hm
  have hf₁ : Function.Injective f₁ := fun x y hxy => hf₀ (congrArg Subtype.val hxy)
  let _ := isCyclic_of_injective f₁ hf₁
  let _ : CommGroup (QuaternionGroup 2) := IsCyclic.commGroup
  have hc := mul_comm (QuaternionGroup.a 1 : QuaternionGroup 2) (QuaternionGroup.xa 0)
  have hnc : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 ≠
      QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by decide
  exact hnc hc

/-- Intrinsic 1.3.4 and the noncyclic automizer leave the original linear-three quotient. -/
theorem Context.linear_three_of_sylow_radical_irreducible (h : Context T L p)
    {u : G} (s : Selected T L u) {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u)
    (hs : SylowRadicalIrreducible h u) (P : Sylow p (XiP p L))
    (hc : ¬ IsCyclic (automizer ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
      ((P : Subgroup (XiP p L)).map (XiP p L).subtype))) :
    LinearThreeModel p (XiQuotient K) := by
  let S := (T : Subgroup G) ⊓ centralizer ({u} : Set G)
  let J := K ⊔ S
  have hJ : J ≤ centralizer ({u} : Set G) := sup_le e.component.1 inf_le_right
  have hK := h.component_local_at_selected s e
  have hn : S ≤ normalizer (K : Set G) :=
    (inf_le_inf_right _ h.sylow_normalizes).trans (h.local_normalizes_component s e hi)
  have hXK := h.radical_le_component s e hi
  have hshape := (Chapter13.Section01.RadicalConjugateRigidity.maximal_radical_structure
    h.hypothesis.simpleQTKE T h.maximal.1 h.nonquasisimple h.odd h.divides).1
  have d := localInput_of_mem_Xi (h.xi_of_sylow_radical_irreducible s hs)
    hK.2.1 (sup_le_sup_right hXK S) h.odd hshape P
  have hsq : IsSQTK KnownSimple.IsKnownSimple J :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hJ)).mp
      ((h.hypothesis.simpleQTKE.involution_centralizer_sqtk
        (h.involution s.mem s.ne_one)).subgroup (J.subgroupOf (centralizer ({u} : Set G))))
  rcases RadicalNormality.normal_or_linear_three hK hn hXK d hsq h.prime_gt_three hc with
    hnorm | ⟨_, hm, _⟩
  · exact (e.escapes ((normal_subgroupOf_iff_le_normalizer hXK).mp hnorm)).elim
  · exact hm

/-- The Sylow-irreducible half of the source sieve, retaining its earlier action input. -/
theorem Context.irreducibleComponentModels_of_sylow_irreducible (h : Context T L p)
    (a : SieveActions h) {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G))
    {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u) (hs : SylowRadicalIrreducible h u) :
    IrreducibleComponentModels p K := by
  let P : Sylow p (XiP p L) := default
  exact Or.inl (h.linear_three_of_sylow_radical_irreducible s e hi hs P
    (h.automizer_not_cyclic_of_sylow_quaternion s hs P (a.quaternion u s hnt hs)))

/-- The source Sylow-irreducible branch is impossible once its earlier
quaternion action is supplied. Every model exclusion is discharged here. -/
theorem Context.not_escape_of_sylow_irreducible (h : Context T L p)
    (a : SieveActions h) (c : Control T L p) {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G))
    {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u) (hs : SylowRadicalIrreducible h u) :
    False :=
  h.not_escape_of_models c s hnt e hi
    (h.irreducibleComponentModels_of_sylow_irreducible a s hnt e hi hs)

/-- The remaining source branch has reducible Sylow action and the literal
S₃ stabilizer quotient. The earlier actions retain their original producer. -/
theorem Context.sylow_reducible_and_symmetric_three (h : Context T L p)
    (a : SieveActions h) (c : Control T L p) {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G))
    {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u) :
    ¬ SylowRadicalIrreducible h u ∧ SymmetricThreeStabilizerQuotient L p u := by
  have hs := fun hs => h.not_escape_of_sylow_irreducible a c s hnt e hi hs
  exact ⟨hs,a.symmetric_three u s hnt hs⟩

/-- The literal centralizer consumer, reduced to the remaining S₃ source
branch and the separate reducible component-normalizer branch. -/
theorem Context.centralizer_le_of_sylow_reducible_exclusion (h : Context T L p)
    (o : OrbitFacts T L p) (c : Control T L p) (a : SieveActions h)
    (hirr : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ComponentNormalizerIrreducible L K p u →
        ¬ SylowRadicalIrreducible h u → SymmetricThreeStabilizerQuotient L p u → False)
    (hred : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ¬ ComponentNormalizerIrreducible L K p u → False)
    {u : G} (hu : u ∈ normalizerMoved L) (hne : u ≠ 1) :
    centralizer ({u} : Set G) ≤ normalizer (L : Set G) := by
  apply h.centralizer_le_of_component_exclusions o c _ hred hu hne
  intro v s hnt K e hi
  obtain ⟨hs,hS3⟩ := h.sylow_reducible_and_symmetric_three a c s hnt e hi
  exact hirr v s hnt K e hi hs hS3

/-- The TI application of the same source reduction, with the actual moved
subgroup and its normalizer. This does not assert the remaining exclusions. -/
theorem Context.ti_of_sylow_reducible_exclusion (h : Context T L p)
    (o : OrbitFacts T L p) (c : Control T L p) (a : SieveActions h)
    (hirr : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ComponentNormalizerIrreducible L K p u →
        ¬ SylowRadicalIrreducible h u → SymmetricThreeStabilizerQuotient L p u → False)
    (hred : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ¬ ComponentNormalizerIrreducible L K p u → False) :
    ChapterI.Section06To08.IsTISubgroup (normalizerMoved L) ∧
      normalizer (normalizerMoved L : Set G) = normalizer (L : Set G) := by
  apply h.ti_of_component_exclusions o c _ hred
  intro v s hnt K e hi
  obtain ⟨hs,hS3⟩ := h.sylow_reducible_and_symmetric_three a c s hnt e hi
  exact hirr v s hnt K e hi hs hS3

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination


